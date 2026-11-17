import NLisp.CNameResolution

namespace NLisp.CMacroCopy

structure Atom where
  name : String
  origin : Option Nat
  token : Nat
  deriving DecidableEq, Repr

inductive Tree where
  | atom : Atom → Tree
  | list : List Tree → Tree
  deriving Repr

/- Use the nested structural recursor. A sizeOf-based well-founded comparator
would compute the size of every string/character during kernel reduction. -/
noncomputable def treeDecEq : DecidableEq Tree :=
  Tree.rec
    (motive_1 := fun a => ∀ b, Decidable (a = b))
    (motive_2 := fun xs => ∀ ys, Decidable (xs = ys))
    (fun x b => match b with
      | .atom y => match decEq x y with
        | isTrue h => isTrue (congrArg Tree.atom h)
        | isFalse h => isFalse (fun e => h (Tree.atom.inj e))
      | .list _ => isFalse (by intro h; cases h))
    (fun _ ih b => match b with
      | .atom _ => isFalse (by intro h; cases h)
      | .list ys => match ih ys with
        | isTrue h => isTrue (congrArg Tree.list h)
        | isFalse h => isFalse (fun e => h (Tree.list.inj e)))
    (fun ys => match ys with
      | [] => isTrue rfl
      | _ :: _ => isFalse (by intro h; cases h))
    (fun _ _ ih tailIH ys => match ys with
      | [] => isFalse (by intro h; cases h)
      | y :: ys => match ih y, tailIH ys with
        | isTrue h, isTrue t => isTrue (by cases h; cases t; rfl)
        | isFalse h, _ => isFalse (fun e => h (List.cons.inj e).1)
        | _, isFalse h => isFalse (fun e => h (List.cons.inj e).2))

noncomputable instance : DecidableEq Tree := treeDecEq

abbrev Holes := List (String × Tree)
abbrev Renames := List (String × Atom)

def lookup (name : String) : List (String × α) → Option α
  | [] => none
  | (key, value) :: tail => if name = key then some value else lookup name tail

def named (tree : Tree) (name : String) : Bool :=
  match tree with
  | .atom a => a.name == name
  | _ => false

def binder (holes : Holes) (renames : Renames) (fresh : Nat) (tree : Tree) :
    Option (Tree × Renames × Nat) :=
  match tree with
  | .atom a =>
      if (lookup a.name holes).isSome then none else
      let next := fresh + 1
      let b : Atom := ⟨"#%nlisp" ++ toString next, a.origin, 3 * next + 2⟩
      some (.atom b, (a.name, b) :: renames, next)
  | _ => none

/- A bounded functional specification of C's copy_template. It checks the
raw substitution, before recursively expanding newly produced macro calls.
Literal data and type annotations are retained; atom origins and binder
freshening are modeled explicitly. -/
structure Operations where
  copy : Nat → Holes → Renames → Nat → Tree → Option (Tree × Nat)
  copyMany : Nat → Holes → Renames → Nat → List Tree → Option (List Tree × Nat)
  copyParameters : Holes → Renames → Nat → List Tree → Option (List Tree × Renames × Nat)
  copyBindings : Nat → Holes → Renames → Renames → Nat → List Tree → Option (List Tree × Renames × Nat)
  copyPattern : Holes → Renames → Nat → List Tree → Option (List Tree × Renames × Nat)
  copyCases : Nat → Holes → Renames → Nat → List Tree → Option (List Tree × Nat)

/- One structural recursion on fuel, shared by all six operations. This avoids
reducing well-founded recursion proofs while checking a closed certificate. -/
def operations : Nat → Operations
  | 0 => ⟨fun _ _ _ _ _ => none, fun _ _ _ _ _ => none,
      fun _ _ _ _ => none, fun _ _ _ _ _ _ => none,
      fun _ _ _ _ => none, fun _ _ _ _ _ => none⟩
  | fuel + 1 =>
      let previous := operations fuel
      { copy := fun origin holes renames fresh tree =>
          match tree with
          | .atom a =>
              match lookup a.name renames with
              | some b => some (.atom ⟨b.name, a.origin, b.token⟩, fresh)
              | none => match lookup a.name holes with
                | some argument => some (argument, fresh)
                | none => some (.atom {a with origin := some origin}, fresh)
          | .list items => do
              match items with
              | [head, .list parameters, result, body] =>
                  if named head "lambda" then
                    let (parameters', names, next) ← previous.copyParameters holes renames fresh parameters
                    let (body', final) ← previous.copy origin holes names next body
                    return (.list [head, .list parameters', result, body'], final)
                  else if named head "match" then
                    let (scrutinee', next) ← previous.copy origin holes renames fresh (.list parameters)
                    let (cases, final) ← previous.copyCases origin holes renames next [result, body]
                    return (.list (head :: scrutinee' :: cases), final)
                  else
                    let (items', next) ← previous.copyMany origin holes renames fresh items
                    return (.list items', next)
              | [head, .list bindings, body] =>
                  if named head "let" then
                    let (bindings', names, next) ← previous.copyBindings origin holes renames renames fresh bindings
                    let (body', final) ← previous.copy origin holes names next body
                    return (.list [head, .list bindings', body'], final)
                  else if named head "match" then
                    let (scrutinee', next) ← previous.copy origin holes renames fresh (.list bindings)
                    let (cases, final) ← previous.copyCases origin holes renames next [body]
                    return (.list (head :: scrutinee' :: cases), final)
                  else
                    let (items', next) ← previous.copyMany origin holes renames fresh items
                    return (.list items', next)
              | head :: scrutinee :: firstCase :: tail =>
                  if named head "match" then
                    let (scrutinee', next) ← previous.copy origin holes renames fresh scrutinee
                    let (cases, final) ← previous.copyCases origin holes renames next (firstCase :: tail)
                    return (.list (head :: scrutinee' :: cases), final)
                  else
                    let (items', next) ← previous.copyMany origin holes renames fresh items
                    return (.list items', next)
              | _ =>
                  let (items', next) ← previous.copyMany origin holes renames fresh items
                  return (.list items', next)
        copyMany := fun origin holes renames fresh trees =>
          match trees with
          | [] => some ([], fresh)
          | head :: tail => do
              let (head', next) ← previous.copy origin holes renames fresh head
              let (tail', final) ← previous.copyMany origin holes renames next tail
              return (head' :: tail', final)
        copyParameters := fun holes renames fresh trees =>
          match trees with
          | [] => some ([], renames, fresh)
          | .list [name, type] :: tail => do
              let (name', names, next) ← binder holes renames fresh name
              let (tail', finalNames, final) ← previous.copyParameters holes names next tail
              return (.list [name', type] :: tail', finalNames, final)
          | _ => none
        copyBindings := fun origin holes outside names fresh trees =>
          match trees with
          | [] => some ([], names, fresh)
          | .list [.list [name, type], value] :: tail => do
              let (name', names', next) ← binder holes names fresh name
              let (value', afterValue) ← previous.copy origin holes outside next value
              let (tail', finalNames, final) ← previous.copyBindings origin holes outside names' afterValue tail
              return (.list [.list [name', type], value'] :: tail', finalNames, final)
          | _ => none
        copyPattern := fun holes names fresh trees =>
          match trees with
          | [] => some ([], names, fresh)
          | head :: tail => do
              let (head', names', next) ← binder holes names fresh head
              let (tail', finalNames, final) ← previous.copyPattern holes names' next tail
              return (head' :: tail', finalNames, final)
        copyCases := fun origin holes names fresh trees =>
          match trees with
          | [] => some ([], fresh)
          | .list [.list pattern, body] :: tail => do
              match pattern with
              | [] =>
                  let (body', next) ← previous.copy origin holes names fresh body
                  let (tail', final) ← previous.copyCases origin holes names next tail
                  return (.list [.list [], body'] :: tail', final)
              | constructor :: parameters =>
                  let (parameters', localNames, next) ← previous.copyPattern holes names fresh parameters
                  let (body', afterBody) ← previous.copy origin holes localNames next body
                  let (tail', final) ← previous.copyCases origin holes names afterBody tail
                  return (.list [.list (constructor :: parameters'), body'] :: tail', final)
          | _ => none }

def copy (fuel : Nat) := (operations fuel).copy
def copyMany (fuel : Nat) := (operations fuel).copyMany
def copyParameters (fuel : Nat) := (operations fuel).copyParameters
def copyBindings (fuel : Nat) := (operations fuel).copyBindings
def copyPattern (fuel : Nat) := (operations fuel).copyPattern
def copyCases (fuel : Nat) := (operations fuel).copyCases

noncomputable def checkCopy (fuel origin : Nat) (holes : Holes) (fresh : Nat) (template actual : Tree)
    (final : Nat) : Bool := decide (copy fuel origin holes [] fresh template = some (actual, final))

theorem checkCopy_sound (accepted : checkCopy fuel origin holes fresh template actual final = true) :
    copy fuel origin holes [] fresh template = some (actual, final) :=
  of_decide_eq_true accepted

theorem capture_uses_definition_origin (a : Atom) (origin fresh : Nat) :
    copy 1 origin [] [] fresh (.atom a) =
      some (.atom {a with origin := some origin}, fresh) := rfl

theorem hole_keeps_argument (name : String) (argument : Tree) (a : Atom)
    (same : a.name = name) :
    copy 1 origin [(name, argument)] [] fresh (.atom a) = some (argument, fresh) := by
  simp [copy, operations, lookup, same]

end NLisp.CMacroCopy
