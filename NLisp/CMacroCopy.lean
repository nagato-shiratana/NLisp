import NLisp.CNameResolution
import NLisp.Lexical

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

/- Count the full constructor payload of a syntax tree. The nested recursor
keeps this measure independent of the sizes of atom names and numeric fields. -/
noncomputable def treeNodeCount : Tree → Nat :=
  Tree.rec
    (motive_1 := fun _ => Nat)
    (motive_2 := fun _ => Nat)
    (fun _ => 1)
    (fun _ children => children + 1)
    0
    (fun _ _ head tail => head + tail)

noncomputable def treeListNodeCount : List Tree → Nat :=
  Tree.rec_1
    (motive_1 := fun _ => Nat)
    (motive_2 := fun _ => Nat)
    (fun _ => 1)
    (fun _ children => children + 1)
    0
    (fun _ _ head tail => head + tail)

theorem treeNodeCount_list (trees : List Tree) :
    treeNodeCount (.list trees) = treeListNodeCount trees + 1 := rfl

private theorem treeNodeCount_positive (tree : Tree) : 0 < treeNodeCount tree := by
  cases tree <;> simp [treeNodeCount]

theorem treeNodeCount_le_treeListNodeCount_of_mem {tree : Tree} {trees : List Tree}
    (member : tree ∈ trees) : treeNodeCount tree ≤ treeListNodeCount trees := by
  induction trees with
  | nil => simp at member
  | cons head tail ih =>
      change treeNodeCount tree ≤ treeNodeCount head + treeListNodeCount tail
      simp only [List.mem_cons] at member
      rcases member with same | member
      · cases same
        exact Nat.le_add_right _ _
      · have headPositive := treeNodeCount_positive head
        have tailBound := ih member
        omega

inductive TreeChild : Tree → Tree → Prop where
  | listMember (child : Tree) (children : List Tree) :
      child ∈ children → TreeChild child (.list children)

theorem treeChild_nodeCount_decreases {child parent : Tree}
    (edge : TreeChild child parent) : treeNodeCount child < treeNodeCount parent := by
  cases edge with
  | listMember children member =>
      rw [treeNodeCount_list]
      exact Nat.lt_succ_of_le (treeNodeCount_le_treeListNodeCount_of_mem member)

theorem treeListNodeCount_cons_tail_decreases (head : Tree) (tail : List Tree) :
    treeListNodeCount tail < treeListNodeCount (head :: tail) := by
  change treeListNodeCount tail < treeNodeCount head + treeListNodeCount tail
  have headPositive := treeNodeCount_positive head
  omega

theorem treeListNodeCount_append (left right : List Tree) :
    treeListNodeCount (left ++ right) = treeListNodeCount left + treeListNodeCount right := by
  induction left with
  | nil => simp [treeListNodeCount]
  | cons head tail ih =>
      change treeNodeCount head + treeListNodeCount (tail ++ right) =
        (treeNodeCount head + treeListNodeCount tail) + treeListNodeCount right
      rw [ih]
      exact (Nat.add_assoc _ _ _).symm

theorem option_map_eq_bind_some {α β : Type} (result : Option α) (f : α → β) :
    result.map f = result.bind (fun value => some (f value)) := by
  cases result <;> rfl

/- Conservative structural cost for an equality decision: charge one unit for
every constructor in the left operand, even when the comparison would stop at
an earlier mismatch. Atom payload comparisons and their bit cost are excluded. -/
noncomputable def treeEqWithWorstCaseCost (left right : Tree) : Bool × Nat :=
  (decide (left = right), treeNodeCount left)

theorem treeEqWithWorstCaseCost_result (left right : Tree) :
    (treeEqWithWorstCaseCost left right).1 = decide (left = right) := rfl

theorem treeEqWithWorstCaseCost_cost (left right : Tree) :
    (treeEqWithWorstCaseCost left right).2 = treeNodeCount left := rfl

abbrev Holes := List (String × Tree)
abbrev Renames := List (String × Atom)

def lookup (name : String) : List (String × α) → Option α
  | [] => none
  | (key, value) :: tail => if name = key then some value else lookup name tail

/- Instrumented environment lookup: one unit is charged for each examined key,
including the successful key. String comparison itself is treated as one unit
here; its bit cost is outside this structural model. -/
def lookupWithCost (name : String) : List (String × α) → Option α × Nat
  | [] => (none, 0)
  | (key, value) :: tail =>
      if name = key then (some value, 1)
      else
        let (result, cost) := lookupWithCost name tail
        (result, cost + 1)

theorem lookupWithCost_result (name : String) (entries : List (String × α)) :
    (lookupWithCost name entries).1 = lookup name entries := by
  induction entries with
  | nil => rfl
  | cons entry tail ih =>
      rcases entry with ⟨key, value⟩
      by_cases same : name = key
      · simp [lookupWithCost, lookup, same]
      · simp [lookupWithCost, lookup, same, ih]

theorem lookupWithCost_cost_le_length (name : String) (entries : List (String × α)) :
    (lookupWithCost name entries).2 ≤ entries.length := by
  induction entries with
  | nil => simp [lookupWithCost]
  | cons entry tail ih =>
      rcases entry with ⟨key, value⟩
      by_cases same : name = key
      · simp [lookupWithCost, same]
      · simp [lookupWithCost, same, List.length_cons]
        omega

theorem lookupWithCost_miss_scans_all (name : String) (entries : List (String × α))
    (missing : lookup name entries = none) :
    (lookupWithCost name entries).2 = entries.length := by
  induction entries with
  | nil => rfl
  | cons entry tail ih =>
      rcases entry with ⟨key, value⟩
      by_cases same : name = key
      · simp [lookup, same] at missing
      · have tailMissing : lookup name tail = none := by
          simpa [lookup, same] using missing
        simp [lookupWithCost, lookup, same, ih tailMissing, List.length_cons]

theorem lookup_isSome_of_mem_keys (name : String) (entries : List (String × α))
    (member : name ∈ entries.map Prod.fst) : (lookup name entries).isSome = true := by
  induction entries with
  | nil => simp at member
  | cons entry tail ih =>
      rcases entry with ⟨key, value⟩
      simp only [List.map_cons, List.mem_cons] at member
      by_cases same : name = key
      · simp [lookup, same]
      · simp only [lookup, same]
        apply ih
        rcases member with equal | rest
        · exact False.elim (same equal)
        · exact rest

theorem lookup_some_implies_mem_keys (name : String) (entries : List (String × α))
    (value : α) (found : lookup name entries = some value) :
    name ∈ entries.map Prod.fst := by
  induction entries with
  | nil => simp [lookup] at found
  | cons entry tail ih =>
      rcases entry with ⟨key, entryValue⟩
      by_cases same : name = key
      · simp [lookup, same]
      · have tailFound : lookup name tail = some value := by
          simpa [lookup, same] using found
        simp only [List.map_cons, List.mem_cons]
        exact Or.inr (ih tailFound)

def named (tree : Tree) (name : String) : Bool :=
  match tree with
  | .atom a => a.name == name
  | _ => false

def binder (holes : Holes) (renames : Renames) (fresh : Nat) (tree : Tree) :
    Option (Tree × Renames × Nat) :=
  match tree with
  | .atom a =>
      if !Lexical.identifier a.name || (lookup a.name holes).isSome then none else
      let next := fresh + 1
      let b : Atom := ⟨"#%nlisp" ++ toString next, a.origin, 3 * next + 2⟩
      some (.atom b, (a.name, b) :: renames, next)
  | _ => none

/- Instrument the environment lookup performed by `binder`. Identifier
validation is not charged here; if it succeeds, one unit is charged for each
hole key examined by the structural lookup model above. -/
def binderWithLookupCost (holes : Holes) (renames : Renames) (fresh : Nat)
    (tree : Tree) : Option (Tree × Renames × Nat) × Nat :=
  match tree with
  | .atom a =>
      if !Lexical.identifier a.name then (none, 0) else
      let (found, cost) := lookupWithCost a.name holes
      if found.isSome then (none, cost) else
      let next := fresh + 1
      let b : Atom := ⟨"#%nlisp" ++ toString next, a.origin, 3 * next + 2⟩
      (some (.atom b, (a.name, b) :: renames, next), cost)
  | .list _ => (none, 0)

theorem binderWithLookupCost_result (holes : Holes) (renames : Renames)
    (fresh : Nat) (tree : Tree) :
    (binderWithLookupCost holes renames fresh tree).1 = binder holes renames fresh tree := by
  cases tree with
  | list items => rfl
  | atom a =>
      by_cases valid : Lexical.identifier a.name = true
      · by_cases found : (lookup a.name holes).isSome = true
        · simp [binderWithLookupCost, binder, valid, found, lookupWithCost_result]
        · simp [binderWithLookupCost, binder, valid, found, lookupWithCost_result]
      · simp [binderWithLookupCost, binder, valid]

theorem binderWithLookupCost_cost_le_holes (holes : Holes) (renames : Renames)
    (fresh : Nat) (tree : Tree) :
    (binderWithLookupCost holes renames fresh tree).2 ≤ holes.length := by
  cases tree with
  | list items => simp [binderWithLookupCost]
  | atom a =>
      by_cases valid : Lexical.identifier a.name = true
      · by_cases found : (lookupWithCost a.name holes).1.isSome = true
        · simpa [binderWithLookupCost, valid, found] using
            lookupWithCost_cost_le_length a.name holes
        · simpa [binderWithLookupCost, valid, found] using
            lookupWithCost_cost_le_length a.name holes
      · simp [binderWithLookupCost, valid]

theorem binderScanStep_cost_le (cost holeCount tailLength : Nat)
    (costBound : cost ≤ holeCount) :
    cost + 1 ≤ (tailLength + 1) * (holeCount + 1) + 1 := by
  have productNonnegative : 0 ≤ tailLength * (holeCount + 1) := Nat.zero_le _
  calc
    cost + 1 ≤ holeCount + 1 := Nat.add_le_add_right costBound 1
    _ ≤ holeCount + (tailLength * (holeCount + 1)) + 2 := by omega
    _ = (tailLength + 1) * (holeCount + 1) + 1 := by
      simp [Nat.succ_mul]
      omega

theorem binder_success_counter (holes : Holes) (renames : Renames) (fresh : Nat)
    (tree : Tree) (copied : Tree) (names : Renames) (final : Nat)
    (accepted : binder holes renames fresh tree = some (copied, names, final)) :
    ∃ atom, copied = .atom atom ∧ final = fresh + 1 ∧ atom.token = 3 * final + 2 := by
  cases tree with
  | list items => simp [binder] at accepted
  | atom original =>
      simp only [binder] at accepted
      split at accepted
      · simp at accepted
      · simp only [Option.some.injEq, Prod.mk.injEq, Tree.atom.injEq] at accepted
        rcases accepted with ⟨rfl, _, rfl⟩
        exact ⟨_, rfl, rfl, rfl⟩

/- C stores generated identities in size_t using 3*counter+2. The C helper
rejects a step when the next counter would make that identity unrepresentable. -/
def nextFreshScope (sizeMax fresh : Nat) : Option Nat :=
  if fresh < (sizeMax - 2) / 3 then some (fresh + 1) else none

theorem nextFreshScope_identity_fits (sizeMax fresh final : Nat)
    (sizeMax_ge_two : 2 ≤ sizeMax)
    (step : nextFreshScope sizeMax fresh = some final) :
    final = fresh + 1 ∧ 3 * final + 2 ≤ sizeMax := by
  unfold nextFreshScope at step
  split at step
  · simp only [Option.some.injEq] at step
    subst final
    constructor
    · rfl
    · omega
  · simp at step

theorem binder_success_identity_fits_c_range (sizeMax : Nat) (holes : Holes)
    (renames : Renames) (fresh : Nat) (tree copied : Tree)
    (names : Renames) (final : Nat)
    (accepted : binder holes renames fresh tree = some (copied, names, final))
    (sizeMax_ge_two : 2 ≤ sizeMax)
    (freshStep : nextFreshScope sizeMax fresh = some final) :
    ∃ atom, copied = .atom atom ∧ final = fresh + 1 ∧ atom.token ≤ sizeMax := by
  obtain ⟨atom, shape, counter, token⟩ :=
    binder_success_counter holes renames fresh tree copied names final accepted
  obtain ⟨_, identityFits⟩ :=
    nextFreshScope_identity_fits sizeMax fresh final sizeMax_ge_two freshStep
  refine ⟨atom, shape, counter, ?_⟩
  rw [token]
  exact identityFits

theorem sequential_binders_have_distinct_tokens
    (firstHoles : Holes) (firstRenames : Renames) (fresh : Nat) (firstTree : Tree)
    (firstOutput : Tree) (middleRenames : Renames) (middle : Nat)
    (firstAccepted : binder firstHoles firstRenames fresh firstTree =
      some (firstOutput, middleRenames, middle))
    (secondHoles : Holes) (secondTree : Tree) (secondOutput : Tree)
    (finalRenames : Renames) (final : Nat)
    (secondAccepted : binder secondHoles middleRenames middle secondTree =
      some (secondOutput, finalRenames, final)) :
    ∃ firstAtom secondAtom,
      firstOutput = .atom firstAtom ∧ secondOutput = .atom secondAtom ∧
      firstAtom.token ≠ secondAtom.token := by
  obtain ⟨firstAtom, firstShape, firstCounter, firstToken⟩ :=
    binder_success_counter firstHoles firstRenames fresh firstTree firstOutput
      middleRenames middle firstAccepted
  obtain ⟨secondAtom, secondShape, secondCounter, secondToken⟩ :=
    binder_success_counter secondHoles middleRenames middle secondTree secondOutput
      finalRenames final secondAccepted
  refine ⟨firstAtom, secondAtom, firstShape, secondShape, ?_⟩
  rw [firstToken, secondToken, firstCounter] at *
  omega

def macroNames (rules : List (Nat × Tree)) : List String :=
  rules.filterMap (fun (_, rule) => match rule with
    | .list [.list (.atom head :: _), _, _, _] => some head.name
    | _ => none)

def parameterNames : List Tree → Option (List String)
  | [] => some []
  | .list [.atom a, _] :: tail => do return a.name :: (← parameterNames tail)
  | _ => none

def bindingNames : List Tree → Option (List String)
  | [] => some []
  | .list [.list [.atom a, _], _] :: tail => do return a.name :: (← bindingNames tail)
  | _ => none

def patternNames : List Tree → Option (List String)
  | [] => some []
  | .atom a :: tail => do return a.name :: (← patternNames tail)
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
def operations (macros : List String) : Nat → Operations
  | 0 => ⟨fun _ _ _ _ _ => none, fun _ _ _ _ _ => none,
      fun _ _ _ _ => none, fun _ _ _ _ _ _ => none,
      fun _ _ _ _ => none, fun _ _ _ _ _ => none⟩
  | fuel + 1 =>
      let previous := operations macros fuel
      { copy := fun origin holes renames fresh tree =>
          match tree with
          | .atom a =>
              match lookup a.name renames with
              | some b => some (.atom ⟨b.name, a.origin, b.token⟩, fresh)
              | none => match lookup a.name holes with
                | some argument => some (argument, fresh)
                | none => some (.atom {a with origin := some origin}, fresh)
          | .list items => do
              let ordinary := do
                match items with
                | [head, .list parameters, result, body] =>
                    if named head "lambda" then
                      let originals ← parameterNames parameters
                      if !Lexical.distinctNames originals then none else
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
                      let originals ← bindingNames bindings
                      if !Lexical.distinctNames originals then none else
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
              match items with
              | .atom head :: arguments =>
                  if macros.contains head.name && (lookup head.name holes).isNone then
                    let (arguments', final) ← previous.copyMany origin holes renames fresh arguments
                    pure (.list (.atom {head with origin := some origin} :: arguments'), final)
                  else ordinary
              | _ => ordinary
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
                  let originals ← patternNames parameters
                  if !Lexical.distinctNames originals then none else
                  let (parameters', localNames, next) ← previous.copyPattern holes names fresh parameters
                  let (body', afterBody) ← previous.copy origin holes localNames next body
                  let (tail', final) ← previous.copyCases origin holes names afterBody tail
                  return (.list [.list (constructor :: parameters'), body'] :: tail', final)
          | _ => none }

def copy (fuel : Nat) := (operations [] fuel).copy
def copyMany (fuel : Nat) := (operations [] fuel).copyMany
def copyParameters (fuel : Nat) := (operations [] fuel).copyParameters
def copyBindings (fuel : Nat) := (operations [] fuel).copyBindings
def copyPattern (fuel : Nat) := (operations [] fuel).copyPattern
def copyCases (fuel : Nat) := (operations [] fuel).copyCases

def copyWithMacros (macros : List String) (fuel : Nat) := (operations macros fuel).copy
def copyManyWithMacros (macros : List String) (fuel : Nat) :=
  (operations macros fuel).copyMany
def copyBindingsWithMacros (macros : List String) (fuel : Nat) :=
  (operations macros fuel).copyBindings
def copyPatternWithMacros (macros : List String) (fuel : Nat) :=
  (operations macros fuel).copyPattern
def copyCasesWithMacros (macros : List String) (fuel : Nat) :=
  (operations macros fuel).copyCases

/- Partial cost model for parameter-binder copying. Each parameter-list node
costs one unit for the structural scan, and binder lookup charges the number
of examined hole keys. Type payload copying/validation is not included. -/
def copyParametersWithLookupCost : Nat → Holes → Renames → Nat → List Tree →
    Option (List Tree × Renames × Nat) × Nat
  | 0, _, _, _, _ => (none, 1)
  | fuel + 1, holes, renames, fresh, [] => (some ([], renames, fresh), 1)
  | fuel + 1, holes, renames, fresh, .list [name, type] :: tail =>
      let binderResult := binderWithLookupCost holes renames fresh name
      match binderResult.1 with
      | none => (none, binderResult.2 + 1)
      | some (nameCopy, names, next) =>
          let tailResult := copyParametersWithLookupCost fuel holes names next tail
          (tailResult.1.map (fun (tailCopy, finalNames, final) =>
            (.list [nameCopy, type] :: tailCopy, finalNames, final)), binderResult.2 + tailResult.2 + 1)
  | fuel + 1, _, _, _, _ :: _ => (none, 1)

theorem copyParametersWithLookupCost_result (fuel : Nat) (holes : Holes)
    (renames : Renames) (fresh : Nat) (trees : List Tree) :
    (copyParametersWithLookupCost fuel holes renames fresh trees).1 =
      copyParameters fuel holes renames fresh trees := by
  induction fuel generalizing holes renames fresh trees with
  | zero => rfl
  | succ fuel ih =>
      cases trees with
      | nil => rfl
      | cons head tail =>
          cases head with
          | atom atom => rfl
          | list items =>
              cases items with
              | nil => rfl
              | cons name rest =>
                  cases rest with
                  | nil => rfl
                  | cons type extra =>
                      cases extra with
                      | cons extraHead extraTail => rfl
                      | nil =>
                          cases lookupResult : binderWithLookupCost holes renames fresh name with
                          | mk binderResult binderCost =>
                              have binderResultEq : binder holes renames fresh name = binderResult := by
                                have resultEq := binderWithLookupCost_result holes renames fresh name
                                simpa [lookupResult] using resultEq.symm
                              cases binderResult with
                              | none => simp [copyParametersWithLookupCost, copyParameters,
                                  operations, lookupResult, binderResultEq]
                              | some result =>
                                  rcases result with ⟨nameCopy, names, next⟩
                                  cases tailResult : copyParametersWithLookupCost fuel holes names next tail with
                                  | mk tailEntries tailCost =>
                                      have tailEntriesEq :
                                          tailEntries = copyParameters fuel holes names next tail := by
                                        have tailEquality := ih holes names next tail
                                        rw [tailResult] at tailEquality
                                        exact tailEquality
                                      simp only [copyParametersWithLookupCost, lookupResult,
                                        tailResult]
                                      rw [tailEntriesEq, option_map_eq_bind_some]
                                      simp [copyParametersWithLookupCost, copyParameters,
                                        operations, lookupResult, binderResultEq, tailResult,
                                        Option.bind]

theorem copyParametersWithLookupCost_cost_le (fuel : Nat) (holes : Holes)
    (renames : Renames) (fresh : Nat) (trees : List Tree) :
    (copyParametersWithLookupCost fuel holes renames fresh trees).2 ≤
      trees.length * (holes.length + 1) + 1 := by
  induction fuel generalizing holes renames fresh trees with
  | zero => simp [copyParametersWithLookupCost]
  | succ fuel ih =>
      cases trees with
      | nil => simp [copyParametersWithLookupCost]
      | cons head tail =>
          cases head with
          | atom atom => simp [copyParametersWithLookupCost, List.length_cons]
          | list items =>
              cases items with
              | nil => simp [copyParametersWithLookupCost, List.length_cons]
              | cons name rest =>
                  cases rest with
                  | nil => simp [copyParametersWithLookupCost, List.length_cons]
                  | cons type extra =>
                      cases extra with
                      | cons extraHead extraTail =>
                          simp [copyParametersWithLookupCost, List.length_cons]
                      | nil =>
                          cases lookupResult : binderWithLookupCost holes renames fresh name with
                          | mk binderResult binderCost =>
                              have binderBound := binderWithLookupCost_cost_le_holes
                                holes renames fresh name
                              have costBound : binderCost ≤ holes.length := by
                                simpa [lookupResult] using binderBound
                              cases binderResult with
                              | none =>
                                  simp only [copyParametersWithLookupCost, lookupResult,
                                    List.length_cons]
                                  exact binderScanStep_cost_le binderCost holes.length
                                    tail.length costBound
                              | some result =>
                                  rcases result with ⟨nameCopy, names, next⟩
                                  cases tailResult : copyParametersWithLookupCost
                                      fuel holes names next tail with
                                  | mk tailEntries tailCost =>
                                      have tailBound := ih holes names next tail
                                      rw [tailResult] at tailBound
                                      simp only [copyParametersWithLookupCost, lookupResult,
                                        tailResult, List.length_cons]
                                      have combinedBound :
                                          binderCost + tailCost ≤ holes.length +
                                            (tail.length * (holes.length + 1) + 1) :=
                                        Nat.add_le_add costBound tailBound
                                      calc
                                        binderCost + tailCost + 1 ≤
                                            holes.length +
                                              (tail.length * (holes.length + 1) + 1) + 1 :=
                                          Nat.add_le_add_right combinedBound 1
                                        _ = (tail.length + 1) * (holes.length + 1) + 1 := by
                                          simp [Nat.succ_mul]
                                          omega

def copyPatternWithLookupCost (macros : List String) : Nat → Holes → Renames → Nat → List Tree →
    Option (List Tree × Renames × Nat) × Nat
  | 0, _, _, _, _ => (none, 1)
  | fuel + 1, holes, renames, fresh, [] => (some ([], renames, fresh), 1)
  | fuel + 1, holes, renames, fresh, head :: tail =>
      let binderResult := binderWithLookupCost holes renames fresh head
      match binderResult.1 with
      | none => (none, binderResult.2 + 1)
      | some (headCopy, names, next) =>
          let tailResult := copyPatternWithLookupCost macros fuel holes names next tail
          (tailResult.1.map (fun (tailCopy, finalNames, final) =>
            (headCopy :: tailCopy, finalNames, final)), binderResult.2 + tailResult.2 + 1)

theorem copyPatternWithLookupCost_result (macros : List String) (fuel : Nat) (holes : Holes)
    (renames : Renames) (fresh : Nat) (trees : List Tree) :
    (copyPatternWithLookupCost macros fuel holes renames fresh trees).1 =
      copyPatternWithMacros macros fuel holes renames fresh trees := by
  induction fuel generalizing holes renames fresh trees with
  | zero => rfl
  | succ fuel ih =>
      cases trees with
      | nil => rfl
      | cons head tail =>
          cases lookupResult : binderWithLookupCost holes renames fresh head with
          | mk binderResult binderCost =>
              have binderResultEq : binder holes renames fresh head = binderResult := by
                have resultEq := binderWithLookupCost_result holes renames fresh head
                simpa [lookupResult] using resultEq.symm
              cases binderResult with
              | none => simp [copyPatternWithLookupCost, copyPatternWithMacros, operations,
                  lookupResult, binderResultEq]
              | some result =>
                  rcases result with ⟨headCopy, names, next⟩
                  cases tailResult : copyPatternWithLookupCost macros fuel holes names next tail with
                  | mk tailEntries tailCost =>
                      have tailEntriesEq :
                          tailEntries = (operations macros fuel).copyPattern holes names next tail := by
                        have tailEquality := ih holes names next tail
                        rw [tailResult] at tailEquality
                        exact tailEquality
                      simp only [copyPatternWithLookupCost, lookupResult, tailResult]
                      rw [tailEntriesEq, option_map_eq_bind_some]
                      simp [copyPatternWithLookupCost, copyPatternWithMacros, operations,
                        lookupResult, binderResultEq, tailResult, Option.bind]

theorem copyPatternWithLookupCost_cost_le (macros : List String) (fuel : Nat) (holes : Holes)
    (renames : Renames) (fresh : Nat) (trees : List Tree) :
    (copyPatternWithLookupCost macros fuel holes renames fresh trees).2 ≤
      trees.length * (holes.length + 1) + 1 := by
  induction fuel generalizing holes renames fresh trees with
  | zero => simp [copyPatternWithLookupCost]
  | succ fuel ih =>
      cases trees with
      | nil => simp [copyPatternWithLookupCost]
      | cons head tail =>
          cases lookupResult : binderWithLookupCost holes renames fresh head with
          | mk binderResult binderCost =>
              have binderBound := binderWithLookupCost_cost_le_holes
                holes renames fresh head
              have costBound : binderCost ≤ holes.length := by
                simpa [lookupResult] using binderBound
              cases binderResult with
              | none =>
                  simp only [copyPatternWithLookupCost, lookupResult, List.length_cons]
                  exact binderScanStep_cost_le binderCost holes.length tail.length costBound
              | some result =>
                  rcases result with ⟨headCopy, names, next⟩
                  cases tailResult : copyPatternWithLookupCost macros fuel holes names next tail with
                  | mk tailEntries tailCost =>
                      have tailBound := ih holes names next tail
                      rw [tailResult] at tailBound
                      simp only [copyPatternWithLookupCost, lookupResult, tailResult,
                        List.length_cons]
                      have combinedBound :
                          binderCost + tailCost ≤ holes.length +
                            (tail.length * (holes.length + 1) + 1) :=
                        Nat.add_le_add costBound tailBound
                      calc
                        binderCost + tailCost + 1 ≤
                            holes.length + (tail.length * (holes.length + 1) + 1) + 1 :=
                          Nat.add_le_add_right combinedBound 1
                        _ = (tail.length + 1) * (holes.length + 1) + 1 := by
                          simp [Nat.succ_mul]
                          omega

/- Partial cost model for let binding rows. Binder lookup and binding-row
traversal are counted; the initializer copy is executed by the ordinary
implementation and its internal work is deliberately excluded. -/
def copyBindingsWithBinderLookupCost (macros : List String) : Nat → Nat → Holes →
    Renames → Renames → Nat → List Tree →
    Option (List Tree × Renames × Nat) × Nat
  | 0, _, _, _, _, _, _ => (none, 1)
  | fuel + 1, origin, holes, outside, names, fresh, [] =>
      (some ([], names, fresh), 1)
  | fuel + 1, origin, holes, outside, names, fresh,
      .list [.list [name, type], value] :: tail =>
      let binderResult := binderWithLookupCost holes names fresh name
      match binderResult.1 with
      | none => (none, binderResult.2 + 1)
      | some (nameCopy, names', next) =>
          match copyWithMacros macros fuel origin holes outside next value with
          | none => (none, binderResult.2 + 1)
          | some (valueCopy, afterValue) =>
              let tailResult := copyBindingsWithBinderLookupCost macros fuel origin holes
                outside names' afterValue tail
              (tailResult.1.map (fun (tailCopy, finalNames, final) =>
                (.list [.list [nameCopy, type], valueCopy] :: tailCopy, finalNames, final)),
                binderResult.2 + tailResult.2 + 1)
  | fuel + 1, _, _, _, _, _, _ :: _ => (none, 1)

theorem copyBindingsWithBinderLookupCost_result (macros : List String) (fuel origin : Nat)
    (holes : Holes) (outside names : Renames) (fresh : Nat) (trees : List Tree) :
    (copyBindingsWithBinderLookupCost macros fuel origin holes outside names fresh trees).1 =
      copyBindingsWithMacros macros fuel origin holes outside names fresh trees := by
  induction fuel generalizing origin holes outside names fresh trees with
  | zero => rfl
  | succ fuel ih =>
      cases trees with
      | nil => rfl
      | cons head tail =>
          cases head with
          | atom atom => simp [copyBindingsWithBinderLookupCost, copyBindingsWithMacros, operations]
          | list rows =>
              cases rows with
              | nil => simp [copyBindingsWithBinderLookupCost, copyBindingsWithMacros, operations]
              | cons binding rest =>
                  cases rest with
                  | nil => simp [copyBindingsWithBinderLookupCost, copyBindingsWithMacros, operations]
                  | cons value extra =>
                      cases extra with
                      | cons extraHead extraTail =>
                          simp [copyBindingsWithBinderLookupCost, copyBindingsWithMacros, operations]
                      | nil =>
                          cases binding with
                          | atom atom =>
                              simp [copyBindingsWithBinderLookupCost, copyBindingsWithMacros, operations]
                          | list fields =>
                              cases fields with
                              | nil =>
                                  simp [copyBindingsWithBinderLookupCost, copyBindingsWithMacros, operations]
                              | cons name restFields =>
                                  cases restFields with
                                  | nil =>
                                      simp [copyBindingsWithBinderLookupCost, copyBindingsWithMacros, operations]
                                  | cons type fieldTail =>
                                      cases fieldTail with
                                      | cons extraField extraFields =>
                                          simp [copyBindingsWithBinderLookupCost,
                                            copyBindingsWithMacros, operations]
                                      | nil =>
                                          cases lookupResult : binderWithLookupCost holes names fresh name with
                                          | mk binderResult binderCost =>
                                              have binderResultEq : binder holes names fresh name = binderResult := by
                                                have resultEq := binderWithLookupCost_result holes names fresh name
                                                simpa [lookupResult] using resultEq.symm
                                              cases binderResult with
                                              | none => simp [copyBindingsWithBinderLookupCost,
                                                  copyBindingsWithMacros, operations, lookupResult,
                                                  binderResultEq]
                                              | some result =>
                                                  rcases result with ⟨nameCopy, names', next⟩
                                                  cases valueResult : copyWithMacros macros fuel origin
                                                      holes outside next value with
                                                  | none =>
                                                      have valueResultEq :
                                                          (operations macros fuel).copy origin holes
                                                            outside next value = none := by
                                                        simpa [copyWithMacros] using valueResult
                                                      simp only [copyBindingsWithBinderLookupCost,
                                                        lookupResult, valueResult]
                                                      simp [copyBindingsWithMacros, operations,
                                                        binderResultEq, valueResultEq,
                                                        copyWithMacros, Option.bind]
                                                  | some copiedValue =>
                                                      rcases copiedValue with ⟨valueCopy, afterValue⟩
                                                      have valueResultEq :
                                                          (operations macros fuel).copy origin holes
                                                            outside next value = some (valueCopy, afterValue) := by
                                                        simpa [copyWithMacros] using valueResult
                                                      cases tailResult : copyBindingsWithBinderLookupCost
                                                          macros fuel origin holes outside names' afterValue tail with
                                                      | mk tailEntries tailCost =>
                                                          have tailEntriesEq :
                                                              tailEntries = (operations macros fuel).copyBindings
                                                                origin holes outside names' afterValue tail := by
                                                            have tailEquality := ih origin holes outside
                                                              names' afterValue tail
                                                            rw [tailResult] at tailEquality
                                                            exact tailEquality
                                                          simp only [copyBindingsWithBinderLookupCost,
                                                            lookupResult, valueResult, tailResult]
                                                          simp [copyBindingsWithMacros, operations,
                                                            binderResultEq, valueResultEq,
                                                            tailEntriesEq, option_map_eq_bind_some,
                                                            copyWithMacros, Option.bind]

theorem copyBindingsWithBinderLookupCost_cost_le (macros : List String) (fuel origin : Nat)
    (holes : Holes) (outside names : Renames) (fresh : Nat) (trees : List Tree) :
    (copyBindingsWithBinderLookupCost macros fuel origin holes outside names fresh trees).2 ≤
      trees.length * (holes.length + 1) + 1 := by
  induction fuel generalizing origin holes outside names fresh trees with
  | zero => simp [copyBindingsWithBinderLookupCost]
  | succ fuel ih =>
      cases trees with
      | nil => simp [copyBindingsWithBinderLookupCost]
      | cons head tail =>
          cases head with
          | atom atom => simp [copyBindingsWithBinderLookupCost, List.length_cons]
          | list rows =>
              cases rows with
              | nil => simp [copyBindingsWithBinderLookupCost, List.length_cons]
              | cons binding rest =>
                  cases rest with
                  | nil => simp [copyBindingsWithBinderLookupCost, List.length_cons]
                  | cons value extra =>
                      cases extra with
                      | cons extraHead extraTail =>
                          simp [copyBindingsWithBinderLookupCost, List.length_cons]
                      | nil =>
                          cases binding with
                          | atom atom => simp [copyBindingsWithBinderLookupCost, List.length_cons]
                          | list fields =>
                              cases fields with
                              | nil => simp [copyBindingsWithBinderLookupCost, List.length_cons]
                              | cons name restFields =>
                                  cases restFields with
                                  | nil => simp [copyBindingsWithBinderLookupCost, List.length_cons]
                                  | cons type fieldTail =>
                                      cases fieldTail with
                                      | cons extraField extraFields =>
                                          simp [copyBindingsWithBinderLookupCost, List.length_cons]
                                      | nil =>
                                          cases lookupResult : binderWithLookupCost holes names fresh name with
                                          | mk binderResult binderCost =>
                                              have binderBound := binderWithLookupCost_cost_le_holes
                                                holes names fresh name
                                              have costBound : binderCost ≤ holes.length := by
                                                simpa [lookupResult] using binderBound
                                              cases binderResult with
                                              | none =>
                                                  simp only [copyBindingsWithBinderLookupCost,
                                                    lookupResult, List.length_cons]
                                                  exact binderScanStep_cost_le binderCost
                                                    holes.length tail.length costBound
                                              | some result =>
                                                  rcases result with ⟨nameCopy, names', next⟩
                                                  cases valueResult : copyWithMacros macros fuel origin
                                                      holes outside next value with
                                                  | none =>
                                                      simp only [copyBindingsWithBinderLookupCost,
                                                        lookupResult, valueResult, List.length_cons]
                                                      exact binderScanStep_cost_le binderCost
                                                        holes.length tail.length costBound
                                                  | some copiedValue =>
                                                      rcases copiedValue with ⟨valueCopy, afterValue⟩
                                                      cases tailResult : copyBindingsWithBinderLookupCost
                                                          macros fuel origin holes outside names'
                                                          afterValue tail with
                                                      | mk tailEntries tailCost =>
                                                          have tailBound := ih origin holes outside
                                                            names' afterValue tail
                                                          rw [tailResult] at tailBound
                                                          simp only [copyBindingsWithBinderLookupCost,
                                                            lookupResult, valueResult, tailResult,
                                                            List.length_cons]
                                                          have combinedBound :
                                                              binderCost + tailCost ≤ holes.length +
                                                                (tail.length * (holes.length + 1) + 1) :=
                                                            Nat.add_le_add costBound tailBound
                                                          calc
                                                            binderCost + tailCost + 1 ≤
                                                                holes.length +
                                                                  (tail.length * (holes.length + 1) + 1) + 1 :=
                                                              Nat.add_le_add_right combinedBound 1
                                                            _ = (tail.length + 1) *
                                                                (holes.length + 1) + 1 := by
                                                              simp [Nat.succ_mul]
                                                              omega

def counterTokens (fresh : Nat) : Nat → List Nat
  | 0 => []
  | count + 1 => (3 * (fresh + 1) + 2) :: counterTokens (fresh + 1) count

theorem copy_atom_keeps_counter (fuel origin : Nat) (holes : Holes) (renames : Renames)
    (fresh : Nat) (atom : Atom) (copied : Tree) (final : Nat)
    (accepted : copy fuel origin holes renames fresh (.atom atom) = some (copied, final)) :
    final = fresh := by
  cases fuel with
  | zero => simp [copy, operations] at accepted
  | succ fuel =>
      simp only [copy, operations] at accepted
      split at accepted
      · simp_all
      · split at accepted <;> simp_all

theorem copyWithMacros_atom_keeps_counter (macros : List String) (fuel origin : Nat)
    (holes : Holes) (renames : Renames) (fresh : Nat) (atom : Atom)
    (copied : Tree) (final : Nat)
    (accepted : copyWithMacros macros fuel origin holes renames fresh (.atom atom) =
      some (copied, final)) : final = fresh := by
  cases fuel with
  | zero => simp [copyWithMacros, operations] at accepted
  | succ fuel =>
      simp only [copyWithMacros, operations] at accepted
      split at accepted
      · simp_all
      · split at accepted <;> simp_all

inductive AtomicTrees : List Tree → Prop where
  | nil : AtomicTrees []
  | cons (atom : Atom) (tail : List Tree) : AtomicTrees tail →
      AtomicTrees (.atom atom :: tail)

theorem copyMany_atomic_counter (fuel origin : Nat) (holes : Holes) (renames : Renames)
    (fresh : Nat) (trees outputs : List Tree) (final : Nat) (atomic : AtomicTrees trees)
    (accepted : copyMany fuel origin holes renames fresh trees = some (outputs, final)) :
    final = fresh := by
  induction atomic generalizing fuel origin holes renames fresh outputs final with
  | nil =>
      cases fuel with
      | zero => simp [copyMany, operations] at accepted
      | succ fuel =>
          simp only [copyMany, operations] at accepted
          have tupleEq := Option.some.inj accepted
          have finalEq := congrArg (fun result : List Tree × Nat => result.2) tupleEq
          simpa using finalEq.symm
  | @cons atom tail _tailAtomic ih =>
      cases fuel with
      | zero => simp [copyMany, operations] at accepted
      | succ fuel =>
          simp only [copyMany, operations] at accepted
          generalize headResult : (operations [] fuel).copy origin holes renames fresh
            (.atom atom) = headOption at accepted
          cases headOption with
          | none => simp [headResult] at accepted
          | some headOutput =>
              rcases headOutput with ⟨headCopy, middle⟩
              generalize tailResult : (operations [] fuel).copyMany origin holes renames
                middle tail = tailOption at accepted
              cases tailOption with
              | none => simp [headResult, tailResult] at accepted
              | some tailOutput =>
                  rcases tailOutput with ⟨tailCopies, finalCounter⟩
                  have acceptedParts := accepted
                  simp [headResult, tailResult] at acceptedParts
                  have finalEq : finalCounter = final := acceptedParts.2
                  have headCounter := copy_atom_keeps_counter fuel origin holes renames fresh
                    atom headCopy middle headResult
                  have tailCounter := ih fuel origin holes renames middle tailCopies finalCounter
                    (by
                      change (operations [] fuel).copyMany origin holes renames middle tail =
                        some (tailCopies, finalCounter)
                      exact tailResult)
                  rw [← finalEq, tailCounter, headCounter]

theorem copyManyWithMacros_atomic_counter (macros : List String) (fuel origin : Nat)
    (holes : Holes) (renames : Renames) (fresh : Nat) (trees outputs : List Tree)
    (final : Nat) (atomic : AtomicTrees trees)
    (accepted : copyManyWithMacros macros fuel origin holes renames fresh trees =
      some (outputs, final)) : final = fresh := by
  induction atomic generalizing fuel origin holes renames fresh outputs final with
  | nil =>
      cases fuel with
      | zero => simp [copyManyWithMacros, operations] at accepted
      | succ fuel =>
          simp only [copyManyWithMacros, operations] at accepted
          have tupleEq := Option.some.inj accepted
          have finalEq := congrArg (fun result : List Tree × Nat => result.2) tupleEq
          simpa using finalEq.symm
  | @cons atom tail _tailAtomic ih =>
      cases fuel with
      | zero => simp [copyManyWithMacros, operations] at accepted
      | succ fuel =>
          simp only [copyManyWithMacros, operations] at accepted
          generalize headResult : (operations macros fuel).copy origin holes renames fresh
            (.atom atom) = headOption at accepted
          cases headOption with
          | none => simp [headResult] at accepted
          | some headOutput =>
              rcases headOutput with ⟨headCopy, middle⟩
              generalize tailResult : (operations macros fuel).copyMany origin holes renames
                middle tail = tailOption at accepted
              cases tailOption with
              | none => simp [headResult, tailResult] at accepted
              | some tailOutput =>
                  rcases tailOutput with ⟨tailCopies, finalCounter⟩
                  have acceptedParts := accepted
                  simp [headResult, tailResult] at acceptedParts
                  have finalEq : finalCounter = final := acceptedParts.2
                  have headCounter := copyWithMacros_atom_keeps_counter macros fuel origin
                    holes renames fresh atom headCopy middle headResult
                  have tailCounter := ih fuel origin holes renames middle tailCopies finalCounter
                    (by
                      change (operations macros fuel).copyMany origin holes renames middle tail =
                        some (tailCopies, finalCounter)
                      exact tailResult)
                  rw [← finalEq, tailCounter, headCounter]

theorem copy_single_atom_list_keeps_counter (fuel origin : Nat) (holes : Holes)
    (renames : Renames) (fresh : Nat) (atom : Atom) (copied : Tree) (final : Nat)
    (accepted : copy fuel origin holes renames fresh (.list [.atom atom]) =
      some (copied, final)) : final = fresh := by
  cases fuel with
  | zero => simp [copy, operations] at accepted
  | succ fuel =>
      cases copied with
      | atom copiedAtom => simp [copy, operations] at accepted
      | list copiedItems =>
          have acceptedCopy := accepted
          simp [copy, operations] at acceptedCopy
          rcases acceptedCopy with ⟨result, manyRun, itemsEq, finalEq⟩
          have manyAccepted : copyMany fuel origin holes renames fresh [.atom atom] =
              some (copiedItems, final) := by
            change (operations [] fuel).copyMany origin holes renames fresh [.atom atom] = _
            rw [manyRun]
            cases result
            simp_all
          exact copyMany_atomic_counter fuel origin holes renames fresh [.atom atom]
            copiedItems final (AtomicTrees.cons atom [] AtomicTrees.nil) manyAccepted

theorem copy_two_atom_list_keeps_counter (fuel origin : Nat) (holes : Holes)
    (renames : Renames) (fresh : Nat) (head argument : Atom)
    (copied : Tree) (final : Nat)
    (accepted : copy fuel origin holes renames fresh (.list [.atom head, .atom argument]) =
      some (copied, final)) : final = fresh := by
  cases fuel with
  | zero => simp [copy, operations] at accepted
  | succ fuel =>
      cases copied with
      | atom copiedAtom => simp [copy, operations] at accepted
      | list copiedItems =>
          have acceptedCopy := accepted
          simp [copy, operations, named] at acceptedCopy
          rcases acceptedCopy with ⟨result, manyRun, itemsEq, finalEq⟩
          have manyAccepted : copyMany fuel origin holes renames fresh
              [.atom head, .atom argument] = some (copiedItems, final) := by
            change (operations [] fuel).copyMany origin holes renames fresh
              [.atom head, .atom argument] = _
            rw [manyRun]
            cases result
            simp_all
          exact copyMany_atomic_counter fuel origin holes renames fresh
            [.atom head, .atom argument] copiedItems final
            (AtomicTrees.cons head [.atom argument]
              (AtomicTrees.cons argument [] AtomicTrees.nil)) manyAccepted

theorem copy_three_atom_list_keeps_counter (fuel origin : Nat) (holes : Holes)
    (renames : Renames) (fresh : Nat) (head first second : Atom)
    (copied : Tree) (final : Nat)
    (accepted : copy fuel origin holes renames fresh
      (.list [.atom head, .atom first, .atom second]) = some (copied, final))
    (headNotMatch : head.name ≠ "match") : final = fresh := by
  cases fuel with
  | zero => simp [copy, operations] at accepted
  | succ fuel =>
      cases copied with
      | atom copiedAtom => simp [copy, operations, named, headNotMatch] at accepted
      | list copiedItems =>
          have acceptedCopy := accepted
          simp [copy, operations, named, headNotMatch] at acceptedCopy
          rcases acceptedCopy with ⟨result, manyRun, itemsEq, finalEq⟩
          have manyAccepted : copyMany fuel origin holes renames fresh
              [.atom head, .atom first, .atom second] = some (copiedItems, final) := by
            change (operations [] fuel).copyMany origin holes renames fresh
              [.atom head, .atom first, .atom second] = _
            rw [manyRun]
            cases result
            simp_all
          exact copyMany_atomic_counter fuel origin holes renames fresh
            [.atom head, .atom first, .atom second] copiedItems final
            (AtomicTrees.cons head [.atom first, .atom second]
              (AtomicTrees.cons first [.atom second]
                (AtomicTrees.cons second [] AtomicTrees.nil))) manyAccepted

theorem copy_four_atom_list_keeps_counter (fuel origin : Nat) (holes : Holes)
    (renames : Renames) (fresh : Nat) (head first second third : Atom)
    (copied : Tree) (final : Nat)
    (accepted : copy fuel origin holes renames fresh
      (.list [.atom head, .atom first, .atom second, .atom third]) = some (copied, final))
    (headNotMatch : head.name ≠ "match") : final = fresh := by
  cases fuel with
  | zero => simp [copy, operations] at accepted
  | succ fuel =>
      cases copied with
      | atom copiedAtom => simp [copy, operations, named, headNotMatch] at accepted
      | list copiedItems =>
          have acceptedCopy := accepted
          simp [copy, operations, named, headNotMatch] at acceptedCopy
          rcases acceptedCopy with ⟨result, manyRun, itemsEq, finalEq⟩
          have manyAccepted : copyMany fuel origin holes renames fresh
              [.atom head, .atom first, .atom second, .atom third] =
                some (copiedItems, final) := by
            change (operations [] fuel).copyMany origin holes renames fresh
              [.atom head, .atom first, .atom second, .atom third] = _
            rw [manyRun]
            cases result
            simp_all
          exact copyMany_atomic_counter fuel origin holes renames fresh
            [.atom head, .atom first, .atom second, .atom third] copiedItems final
            (AtomicTrees.cons head [.atom first, .atom second, .atom third]
              (AtomicTrees.cons first [.atom second, .atom third]
                (AtomicTrees.cons second [.atom third]
                  (AtomicTrees.cons third [] AtomicTrees.nil)))) manyAccepted

inductive CounterSafeInitializer : Tree → Prop where
  | atom (value : Atom) : CounterSafeInitializer (.atom value)
  | singletonList (value : Atom) : CounterSafeInitializer (.list [.atom value])
  | pairList (head argument : Atom) :
      CounterSafeInitializer (.list [.atom head, .atom argument])
  | tripleList (head first second : Atom) (headNotMatch : head.name ≠ "match") :
      CounterSafeInitializer (.list [.atom head, .atom first, .atom second])
  | quadrupleList (head first second third : Atom) (headNotMatch : head.name ≠ "match") :
      CounterSafeInitializer (.list [.atom head, .atom first, .atom second, .atom third])

inductive AtomicBindingInputs : List Tree → Prop where
  | nil : AtomicBindingInputs []
  | cons (name type value : Tree) (safe : CounterSafeInitializer value) (tail : List Tree) :
      AtomicBindingInputs tail →
      AtomicBindingInputs (.list [.list [name, type], value] :: tail)

inductive AtomBindingInputs : List Tree → Prop where
  | nil : AtomBindingInputs []
  | cons (name type value : Atom) (tail : List Tree) : AtomBindingInputs tail →
      AtomBindingInputs (.list [.list [.atom name, .atom type], .atom value] :: tail)

def CounterPreservingInitializer (macros : List String) (value : Tree) : Prop :=
  ∀ (fuel origin : Nat) (holes : Holes) (renames : Renames) (fresh : Nat)
    (copied : Tree) (final : Nat),
    copyWithMacros macros fuel origin holes renames fresh value = some (copied, final) →
      final = fresh

inductive CounterPreservingBindings (macros : List String) : List Tree → Prop where
  | nil : CounterPreservingBindings macros []
  | cons (name type value : Tree) (preserves : CounterPreservingInitializer macros value)
      (tail : List Tree) (tailSafe : CounterPreservingBindings macros tail) :
      CounterPreservingBindings macros (.list [.list [name, type], value] :: tail)

def counterPreservingCaseCount : List Tree → Nat
  | [] => 0
  | .list [.list [], _] :: tail => counterPreservingCaseCount tail
  | .list [.list (_ :: parameters), _] :: tail =>
      parameters.length + counterPreservingCaseCount tail
  | _ => 0

inductive CounterPreservingCases (macros : List String) : List Tree → Prop where
  | nil : CounterPreservingCases macros []
  | emptyPattern (body : Tree) (bodySafe : CounterPreservingInitializer macros body)
      (tail : List Tree) (tailSafe : CounterPreservingCases macros tail) :
      CounterPreservingCases macros (.list [.list [], body] :: tail)
  | boundPattern (constructor : Tree) (parameters : List Tree) (body : Tree)
      (bodySafe : CounterPreservingInitializer macros body) (tail : List Tree)
      (tailSafe : CounterPreservingCases macros tail) :
      CounterPreservingCases macros
        (.list [.list (constructor :: parameters), body] :: tail)

theorem counterSafeInitializer_preserving (value : Tree)
    (safe : CounterSafeInitializer value) : CounterPreservingInitializer [] value := by
  intro fuel origin holes renames fresh copied final accepted
  cases safe with
  | atom atom =>
      exact copy_atom_keeps_counter fuel origin holes renames fresh atom copied final accepted
  | singletonList atom =>
      exact copy_single_atom_list_keeps_counter fuel origin holes renames fresh atom copied final
        accepted
  | pairList head argument =>
      exact copy_two_atom_list_keeps_counter fuel origin holes renames fresh head argument copied
        final accepted
  | tripleList head first second headNotMatch =>
      exact copy_three_atom_list_keeps_counter fuel origin holes renames fresh head first second
        copied final accepted headNotMatch
  | quadrupleList head first second third headNotMatch =>
      exact copy_four_atom_list_keeps_counter fuel origin holes renames fresh head first second
        third copied final accepted headNotMatch

theorem atomic_binding_inputs_counter_preserving (bindings : List Tree)
    (atomic : AtomicBindingInputs bindings) : CounterPreservingBindings [] bindings := by
  induction atomic with
  | nil => exact .nil
  | @cons name type value safe tail _tailAtomic ih =>
      exact .cons name type value (counterSafeInitializer_preserving value safe) tail ih

theorem atom_initializer_counter_preserving (macros : List String) (value : Atom) :
    CounterPreservingInitializer macros (.atom value) := by
  intro fuel origin holes renames fresh copied final accepted
  exact copyWithMacros_atom_keeps_counter macros fuel origin holes renames fresh
    value copied final accepted

theorem atom_binding_inputs_counter_preserving (macros : List String) (bindings : List Tree)
    (atomic : AtomBindingInputs bindings) : CounterPreservingBindings macros bindings := by
  induction atomic with
  | nil => exact .nil
  | @cons name type value tail _tailAtomic ih =>
      exact .cons (.atom name) (.atom type) (.atom value)
        (atom_initializer_counter_preserving macros value) tail ih

theorem copyBindingsWithMacros_preserving_counter (macros : List String)
    (fuel origin : Nat) (holes : Holes) (outside names : Renames) (fresh : Nat)
    (bindings outputs : List Tree) (finalNames : Renames) (final : Nat)
    (safe : CounterPreservingBindings macros bindings)
    (accepted : copyBindingsWithMacros macros fuel origin holes outside names fresh bindings =
      some (outputs, finalNames, final)) :
    final = fresh + bindings.length := by
  induction safe generalizing fuel origin holes outside names fresh outputs finalNames final with
  | nil =>
      cases fuel with
      | zero => simp [copyBindingsWithMacros, operations] at accepted
      | succ fuel =>
          simp only [copyBindingsWithMacros, operations] at accepted
          have tupleEq := Option.some.inj accepted
          have finalEq := congrArg (fun result : List Tree × Renames × Nat => result.2.2) tupleEq
          simpa using finalEq.symm
  | @cons name type value preserves tail _tailSafe ih =>
      cases fuel with
      | zero => simp [copyBindingsWithMacros, operations] at accepted
      | succ fuel =>
          simp only [copyBindingsWithMacros, operations] at accepted
          generalize binderResult : binder holes names fresh name = binderOption at accepted
          cases binderOption with
          | none => simp [binderResult] at accepted
          | some result =>
              rcases result with ⟨nameCopy, names', next⟩
              generalize valueResult : (operations macros fuel).copy origin holes outside next
                value = valueOption at accepted
              cases valueOption with
              | none => simp [binderResult, valueResult] at accepted
              | some result =>
                  rcases result with ⟨valueCopy, afterValue⟩
                  generalize tailResult : (operations macros fuel).copyBindings origin holes
                    outside names' afterValue tail = tailOption at accepted
                  cases tailOption with
                  | none => simp [binderResult, valueResult, tailResult] at accepted
                  | some result =>
                      rcases result with ⟨tailCopies, endNames, endCounter⟩
                      have acceptedParts := accepted
                      simp [binderResult, valueResult, tailResult] at acceptedParts
                      have finalEq : endCounter = final := acceptedParts.2.2
                      have binderFacts := binder_success_counter holes names fresh name
                        nameCopy names' next (by simp [binderResult])
                      rcases binderFacts with ⟨freshAtom, _shape, nextEq, _tokenEq⟩
                      have valueCounter := preserves fuel origin holes outside next valueCopy
                        afterValue valueResult
                      have tailCounter := ih fuel origin holes outside names' afterValue tailCopies
                        endNames endCounter (by
                          change (operations macros fuel).copyBindings origin holes outside names'
                            afterValue tail = some (tailCopies, endNames, endCounter)
                          exact tailResult)
                      rw [← finalEq, tailCounter, valueCounter, nextEq]
                      simp only [List.length_cons]
                      omega

inductive CounterPreservingTrees (macros : List String) : List Tree → Prop where
  | nil : CounterPreservingTrees macros []
  | cons (tree : Tree) (preserves : CounterPreservingInitializer macros tree)
      (tail : List Tree) (tailSafe : CounterPreservingTrees macros tail) :
      CounterPreservingTrees macros (tree :: tail)

theorem copyManyWithMacros_preserving_counter (macros : List String) (fuel origin : Nat)
    (holes : Holes) (renames : Renames) (fresh : Nat) (trees outputs : List Tree)
    (final : Nat) (safe : CounterPreservingTrees macros trees)
    (accepted : copyManyWithMacros macros fuel origin holes renames fresh trees =
      some (outputs, final)) : final = fresh := by
  induction safe generalizing fuel origin holes renames fresh outputs final with
  | nil =>
      cases fuel with
      | zero => simp [copyManyWithMacros, operations] at accepted
      | succ fuel =>
          simp only [copyManyWithMacros, operations] at accepted
          have tupleEq := Option.some.inj accepted
          have finalEq := congrArg (fun result : List Tree × Nat => result.2) tupleEq
          simpa using finalEq.symm
  | @cons tree preserves tail _tailSafe ih =>
      cases fuel with
      | zero => simp [copyManyWithMacros, operations] at accepted
      | succ fuel =>
          simp only [copyManyWithMacros, operations] at accepted
          generalize headResult : (operations macros fuel).copy origin holes renames fresh tree =
            headOption at accepted
          cases headOption with
          | none => simp [headResult] at accepted
          | some headOutput =>
              rcases headOutput with ⟨headCopy, middle⟩
              generalize tailResult : (operations macros fuel).copyMany origin holes renames
                middle tail = tailOption at accepted
              cases tailOption with
              | none => simp [headResult, tailResult] at accepted
              | some tailOutput =>
                  rcases tailOutput with ⟨tailCopies, finalCounter⟩
                  have acceptedParts := accepted
                  simp [headResult, tailResult] at acceptedParts
                  have finalEq : finalCounter = final := acceptedParts.2
                  have headCounter := preserves fuel origin holes renames fresh headCopy middle
                    headResult
                  have tailCounter := ih fuel origin holes renames middle tailCopies finalCounter
                    (by
                      change (operations macros fuel).copyMany origin holes renames middle tail =
                        some (tailCopies, finalCounter)
                      exact tailResult)
                  rw [← finalEq, tailCounter, headCounter]

def counterNeutralListHead (macros : List String) : List Tree → Bool
  | .atom head :: _ =>
      !(macros.contains head.name) && head.name != "match" &&
        head.name != "let" && head.name != "lambda"
  | _ => true

theorem copyNeutralList_uses_copyMany (macros : List String) (fuel origin : Nat)
    (holes : Holes) (renames : Renames) (fresh : Nat) (items : List Tree)
    (headSafe : counterNeutralListHead macros items = true) :
    (operations macros (fuel + 1)).copy origin holes renames fresh (.list items) = (do
      let (copies, final) ← (operations macros fuel).copyMany origin holes renames fresh items
      pure (.list copies, final)) := by
  cases items with
  | nil => simp only [operations]
  | cons first tail =>
      cases first with
      | list nested =>
          cases tail with
          | nil => simp only [operations] at *
          | cons second tail =>
              cases tail with
              | nil => simp only [operations] at *
              | cons third tail =>
                  cases tail with
                  | nil =>
                      simp only [operations] at *
                      cases second <;> simp_all [named]
                  | cons fourth tail =>
                      cases tail with
                      | nil =>
                          simp only [operations] at *
                          cases second <;> simp_all [named]
                      | cons fifth tail => simp only [operations] at *; simp_all [named]
      | atom head =>
          cases tail with
          | nil => simp only [operations] at *; simp_all [named, counterNeutralListHead]
          | cons second tail =>
              cases tail with
              | nil => simp only [operations] at *; simp_all [named, counterNeutralListHead]
              | cons third tail =>
                  cases tail with
                  | nil =>
                      simp only [operations] at *
                      cases second <;> simp_all [named, counterNeutralListHead]
                  | cons fourth tail =>
                      cases tail with
                      | nil =>
                          simp only [operations] at *
                          cases second <;> simp_all [named, counterNeutralListHead]
                      | cons fifth tail => simp only [operations] at *; simp_all [named, counterNeutralListHead]

mutual
  inductive CounterNeutralTree (macros : List String) : Tree → Prop where
    | atom (value : Atom) : CounterNeutralTree macros (.atom value)
    | list (items : List Tree) (headSafe : counterNeutralListHead macros items = true)
        (children : CounterNeutralTrees macros items) :
        CounterNeutralTree macros (.list items)

  inductive CounterNeutralTrees (macros : List String) : List Tree → Prop where
    | nil : CounterNeutralTrees macros []
    | cons (head : Tree) (headSafe : CounterNeutralTree macros head)
        (tail : List Tree) (tailSafe : CounterNeutralTrees macros tail) :
        CounterNeutralTrees macros (head :: tail)
end

theorem counterNeutralTree_preserving (macros : List String) (value : Tree)
    (safe : CounterNeutralTree macros value) : CounterPreservingInitializer macros value := by
  refine CounterNeutralTree.rec
    (motive_1 := fun value _ => CounterPreservingInitializer macros value)
    (motive_2 := fun trees _ => CounterPreservingTrees macros trees)
    ?_ ?_ ?_ ?_ safe
  · intro atom
    exact atom_initializer_counter_preserving macros atom
  · intro items headSafe _children childrenIH
    intro fuel origin holes renames fresh copied final accepted
    cases fuel with
    | zero => simp [copyWithMacros, operations] at accepted
    | succ fuel =>
        change (operations macros (fuel + 1)).copy origin holes renames fresh (.list items) =
          some (copied, final) at accepted
        rw [copyNeutralList_uses_copyMany macros fuel origin holes renames fresh items headSafe]
          at accepted
        cases copied with
        | atom atom => simp at accepted
        | list copiedItems =>
            generalize manyRun : (operations macros fuel).copyMany origin holes renames
                fresh items = manyOption at accepted
            cases manyOption with
            | none => simp [manyRun] at accepted
            | some result =>
                rcases result with ⟨manyCopies, middle⟩
                have manyAccepted : copyManyWithMacros macros fuel origin holes renames fresh
                    items = some (manyCopies, middle) := by
                  change (operations macros fuel).copyMany origin holes renames fresh items = _
                  exact manyRun
                have middleEq := copyManyWithMacros_preserving_counter macros fuel origin holes
                  renames fresh items manyCopies middle childrenIH manyAccepted
                simp [manyRun] at accepted
                omega
  · exact CounterPreservingTrees.nil
  · intro head _headSafe tail _tailSafe headIH tailIH
    exact .cons head headIH tail tailIH

theorem copyWithMacros_single_atom_list_keeps_counter (macros : List String)
    (fuel origin : Nat) (holes : Holes) (renames : Renames) (fresh : Nat)
    (atom : Atom) (copied : Tree) (final : Nat)
    (accepted : copyWithMacros macros fuel origin holes renames fresh (.list [.atom atom]) =
      some (copied, final)) : final = fresh := by
  cases fuel with
  | zero => simp [copyWithMacros, operations] at accepted
  | succ fuel =>
      cases copied with
      | atom copiedAtom =>
          simp only [copyWithMacros, operations] at accepted
          split at accepted <;> simp_all
      | list copiedItems =>
          simp only [copyWithMacros, operations] at accepted
          split at accepted
          · generalize manyRun : (operations macros fuel).copyMany origin holes renames fresh [] =
              manyOption at accepted
            cases manyOption with
            | none => simp [manyRun] at accepted
            | some result =>
                rcases result with ⟨manyCopies, middle⟩
                have acceptedShape := accepted
                simp [manyRun] at acceptedShape
                have manyAccepted : copyManyWithMacros macros fuel origin holes renames fresh [] =
                    some (manyCopies, middle) := by
                  change (operations macros fuel).copyMany origin holes renames fresh [] = _
                  exact manyRun
                have middleEq := copyManyWithMacros_atomic_counter macros fuel origin holes renames
                  fresh [] manyCopies middle AtomicTrees.nil manyAccepted
                omega
          · generalize manyRun : (operations macros fuel).copyMany origin holes renames fresh
              [.atom atom] = manyOption at accepted
            cases manyOption with
            | none => simp [manyRun] at accepted
            | some result =>
                rcases result with ⟨manyCopies, middle⟩
                have acceptedShape := accepted
                simp [manyRun] at acceptedShape
                have manyAccepted : copyManyWithMacros macros fuel origin holes renames fresh
                    [.atom atom] = some (manyCopies, middle) := by
                  change (operations macros fuel).copyMany origin holes renames fresh [.atom atom] = _
                  exact manyRun
                have middleEq := copyManyWithMacros_atomic_counter macros fuel origin holes renames
                  fresh [.atom atom] manyCopies middle
                  (AtomicTrees.cons atom [] AtomicTrees.nil) manyAccepted
                omega

theorem singleton_atom_list_counter_preserving (macros : List String) (value : Atom) :
    CounterPreservingInitializer macros (.list [.atom value]) := by
  intro fuel origin holes renames fresh copied final accepted
  exact copyWithMacros_single_atom_list_keeps_counter macros fuel origin holes renames fresh
    value copied final accepted

theorem copyWithMacros_two_atom_list_keeps_counter (macros : List String)
    (fuel origin : Nat) (holes : Holes) (renames : Renames) (fresh : Nat)
    (head argument : Atom) (copied : Tree) (final : Nat)
    (accepted : copyWithMacros macros fuel origin holes renames fresh
      (.list [.atom head, .atom argument]) = some (copied, final)) : final = fresh := by
  cases fuel with
  | zero => simp [copyWithMacros, operations] at accepted
  | succ fuel =>
      cases copied with
      | atom copiedAtom =>
          simp only [copyWithMacros, operations] at accepted
          split at accepted <;> simp_all
      | list copiedItems =>
          simp only [copyWithMacros, operations] at accepted
          split at accepted
          · generalize manyRun : (operations macros fuel).copyMany origin holes renames fresh
              [.atom argument] = manyOption at accepted
            cases manyOption with
            | none => simp [manyRun] at accepted
            | some result =>
                rcases result with ⟨manyCopies, middle⟩
                have acceptedShape := accepted
                simp [manyRun] at acceptedShape
                have manyAccepted : copyManyWithMacros macros fuel origin holes renames fresh
                    [.atom argument] = some (manyCopies, middle) := by
                  change (operations macros fuel).copyMany origin holes renames fresh
                    [.atom argument] = _
                  exact manyRun
                have middleEq := copyManyWithMacros_atomic_counter macros fuel origin holes renames
                  fresh [.atom argument] manyCopies middle
                  (AtomicTrees.cons argument [] AtomicTrees.nil) manyAccepted
                omega
          · generalize manyRun : (operations macros fuel).copyMany origin holes renames fresh
              [.atom head, .atom argument] = manyOption at accepted
            cases manyOption with
            | none => simp [manyRun] at accepted
            | some result =>
                rcases result with ⟨manyCopies, middle⟩
                have acceptedShape := accepted
                simp [manyRun] at acceptedShape
                have manyAccepted : copyManyWithMacros macros fuel origin holes renames fresh
                    [.atom head, .atom argument] = some (manyCopies, middle) := by
                  change (operations macros fuel).copyMany origin holes renames fresh
                    [.atom head, .atom argument] = _
                  exact manyRun
                have middleEq := copyManyWithMacros_atomic_counter macros fuel origin holes renames
                  fresh [.atom head, .atom argument] manyCopies middle
                  (AtomicTrees.cons head [.atom argument]
                    (AtomicTrees.cons argument [] AtomicTrees.nil)) manyAccepted
                omega

theorem pair_atom_list_counter_preserving (macros : List String) (head argument : Atom) :
    CounterPreservingInitializer macros (.list [.atom head, .atom argument]) := by
  intro fuel origin holes renames fresh copied final accepted
  exact copyWithMacros_two_atom_list_keeps_counter macros fuel origin holes renames fresh
    head argument copied final accepted

theorem copyWithMacros_three_atom_list_keeps_counter (macros : List String)
    (fuel origin : Nat) (holes : Holes) (renames : Renames) (fresh : Nat)
    (head first second : Atom) (copied : Tree) (final : Nat)
    (accepted : copyWithMacros macros fuel origin holes renames fresh
      (.list [.atom head, .atom first, .atom second]) = some (copied, final))
    (headNotMatch : head.name ≠ "match") : final = fresh := by
  cases fuel with
  | zero => simp [copyWithMacros, operations] at accepted
  | succ fuel =>
      cases copied with
      | atom copiedAtom =>
          simp only [copyWithMacros, operations] at accepted
          split at accepted <;> simp_all [named, headNotMatch]
      | list copiedItems =>
          simp only [copyWithMacros, operations] at accepted
          split at accepted
          · generalize manyRun : (operations macros fuel).copyMany origin holes renames fresh
              [.atom first, .atom second] = manyOption at accepted
            cases manyOption with
            | none => simp [manyRun] at accepted
            | some result =>
                rcases result with ⟨manyCopies, middle⟩
                have acceptedShape := accepted
                simp [manyRun] at acceptedShape
                have manyAccepted : copyManyWithMacros macros fuel origin holes renames fresh
                    [.atom first, .atom second] = some (manyCopies, middle) := by
                  change (operations macros fuel).copyMany origin holes renames fresh
                    [.atom first, .atom second] = _
                  exact manyRun
                have middleEq := copyManyWithMacros_atomic_counter macros fuel origin holes renames
                  fresh [.atom first, .atom second] manyCopies middle
                  (AtomicTrees.cons first [.atom second]
                    (AtomicTrees.cons second [] AtomicTrees.nil)) manyAccepted
                omega
          · have acceptedOrdinary := accepted
            simp [named, headNotMatch] at acceptedOrdinary
            generalize manyRun : (operations macros fuel).copyMany origin holes renames fresh
              [.atom head, .atom first, .atom second] = manyOption at acceptedOrdinary
            cases manyOption with
            | none => simp [manyRun] at acceptedOrdinary
            | some result =>
                rcases result with ⟨manyCopies, middle⟩
                have acceptedShape := acceptedOrdinary
                simp [manyRun] at acceptedShape
                have manyAccepted : copyManyWithMacros macros fuel origin holes renames fresh
                    [.atom head, .atom first, .atom second] = some (manyCopies, middle) := by
                  change (operations macros fuel).copyMany origin holes renames fresh
                    [.atom head, .atom first, .atom second] = _
                  exact manyRun
                have middleEq := copyManyWithMacros_atomic_counter macros fuel origin holes renames
                  fresh [.atom head, .atom first, .atom second] manyCopies middle
                  (AtomicTrees.cons head [.atom first, .atom second]
                    (AtomicTrees.cons first [.atom second]
                      (AtomicTrees.cons second [] AtomicTrees.nil))) manyAccepted
                omega

theorem triple_atom_list_counter_preserving (macros : List String)
    (head first second : Atom) (headNotMatch : head.name ≠ "match") :
    CounterPreservingInitializer macros (.list [.atom head, .atom first, .atom second]) := by
  intro fuel origin holes renames fresh copied final accepted
  exact copyWithMacros_three_atom_list_keeps_counter macros fuel origin holes renames fresh
    head first second copied final accepted headNotMatch

theorem copyWithMacros_four_atom_list_keeps_counter (macros : List String)
    (fuel origin : Nat) (holes : Holes) (renames : Renames) (fresh : Nat)
    (head first second third : Atom) (copied : Tree) (final : Nat)
    (accepted : copyWithMacros macros fuel origin holes renames fresh
      (.list [.atom head, .atom first, .atom second, .atom third]) = some (copied, final))
    (headNotMatch : head.name ≠ "match") : final = fresh := by
  cases fuel with
  | zero => simp [copyWithMacros, operations] at accepted
  | succ fuel =>
      cases copied with
      | atom copiedAtom =>
          simp only [copyWithMacros, operations] at accepted
          split at accepted <;> simp_all [named, headNotMatch]
      | list copiedItems =>
          simp only [copyWithMacros, operations] at accepted
          split at accepted
          · generalize manyRun : (operations macros fuel).copyMany origin holes renames fresh
              [.atom first, .atom second, .atom third] = manyOption at accepted
            cases manyOption with
            | none => simp [manyRun] at accepted
            | some result =>
                rcases result with ⟨manyCopies, middle⟩
                have acceptedShape := accepted
                simp [manyRun] at acceptedShape
                have manyAccepted : copyManyWithMacros macros fuel origin holes renames fresh
                    [.atom first, .atom second, .atom third] = some (manyCopies, middle) := by
                  change (operations macros fuel).copyMany origin holes renames fresh
                    [.atom first, .atom second, .atom third] = _
                  exact manyRun
                have middleEq := copyManyWithMacros_atomic_counter macros fuel origin holes renames
                  fresh [.atom first, .atom second, .atom third] manyCopies middle
                  (AtomicTrees.cons first [.atom second, .atom third]
                    (AtomicTrees.cons second [.atom third]
                      (AtomicTrees.cons third [] AtomicTrees.nil))) manyAccepted
                omega
          · have acceptedOrdinary := accepted
            simp [named, headNotMatch] at acceptedOrdinary
            generalize manyRun : (operations macros fuel).copyMany origin holes renames fresh
              [.atom head, .atom first, .atom second, .atom third] = manyOption at acceptedOrdinary
            cases manyOption with
            | none => simp [manyRun] at acceptedOrdinary
            | some result =>
                rcases result with ⟨manyCopies, middle⟩
                have acceptedShape := acceptedOrdinary
                simp [manyRun] at acceptedShape
                have manyAccepted : copyManyWithMacros macros fuel origin holes renames fresh
                    [.atom head, .atom first, .atom second, .atom third] =
                      some (manyCopies, middle) := by
                  change (operations macros fuel).copyMany origin holes renames fresh
                    [.atom head, .atom first, .atom second, .atom third] = _
                  exact manyRun
                have middleEq := copyManyWithMacros_atomic_counter macros fuel origin holes renames
                  fresh [.atom head, .atom first, .atom second, .atom third] manyCopies middle
                  (AtomicTrees.cons head [.atom first, .atom second, .atom third]
                    (AtomicTrees.cons first [.atom second, .atom third]
                      (AtomicTrees.cons second [.atom third]
                        (AtomicTrees.cons third [] AtomicTrees.nil)))) manyAccepted
                omega

theorem quadruple_atom_list_counter_preserving (macros : List String)
    (head first second third : Atom) (headNotMatch : head.name ≠ "match") :
    CounterPreservingInitializer macros
      (.list [.atom head, .atom first, .atom second, .atom third]) := by
  intro fuel origin holes renames fresh copied final accepted
  exact copyWithMacros_four_atom_list_keeps_counter macros fuel origin holes renames fresh
    head first second third copied final accepted headNotMatch

def atomTrees : List Atom → List Tree
  | [] => []
  | head :: tail => .atom head :: atomTrees tail

def atomTreesAtomic : (atoms : List Atom) → AtomicTrees (atomTrees atoms)
  | [] => .nil
  | head :: tail => .cons head (atomTrees tail) (atomTreesAtomic tail)

def atomTreesHeadNotMatch : List Atom → Prop
  | [] => True
  | head :: _ => head.name ≠ "match"

theorem copyWithMacros_atomTrees_keeps_counter (macros : List String)
    (fuel origin : Nat) (holes : Holes) (renames : Renames) (fresh : Nat)
    (atoms : List Atom) (headSafe : atomTreesHeadNotMatch atoms)
    (copied : Tree) (final : Nat)
    (accepted : copyWithMacros macros fuel origin holes renames fresh (.list (atomTrees atoms)) =
      some (copied, final)) : final = fresh := by
  cases atoms with
  | nil =>
      cases fuel with
      | zero => simp [copyWithMacros, operations] at accepted
      | succ fuel =>
          cases copied with
          | atom atom => simp [copyWithMacros, operations, atomTrees] at accepted
          | list items =>
              simp only [copyWithMacros, operations, atomTrees] at accepted
              generalize manyRun : (operations macros fuel).copyMany origin holes renames fresh
                [] = manyOption at accepted
              cases manyOption with
              | none => simp [manyRun] at accepted
              | some result =>
                  rcases result with ⟨manyCopies, middle⟩
                  have manyAccepted : copyManyWithMacros macros fuel origin holes renames fresh [] =
                      some (manyCopies, middle) := by
                    change (operations macros fuel).copyMany origin holes renames fresh [] = _
                    exact manyRun
                  have counter := copyManyWithMacros_atomic_counter macros fuel origin holes renames
                    fresh [] manyCopies middle .nil manyAccepted
                  simp [manyRun] at accepted
                  omega
  | cons head tail =>
      cases tail with
      | nil =>
          simpa [atomTrees] using
            (copyWithMacros_single_atom_list_keeps_counter macros fuel origin holes renames fresh
              head copied final accepted)
      | cons second rest =>
          cases rest with
          | nil =>
              simpa [atomTrees] using
                (copyWithMacros_two_atom_list_keeps_counter macros fuel origin holes renames fresh
                  head second copied final accepted)
          | cons third rest =>
              have headNotMatch : head.name ≠ "match" := by
                simpa [atomTreesHeadNotMatch] using headSafe
              have tailAtomic : AtomicTrees (.atom second :: .atom third :: atomTrees rest) :=
                .cons second (.atom third :: atomTrees rest)
                  (.cons third (atomTrees rest) (atomTreesAtomic rest))
              have allAtomic : AtomicTrees (.atom head :: .atom second :: .atom third :: atomTrees rest) :=
                .cons head (.atom second :: .atom third :: atomTrees rest) tailAtomic
              cases fuel with
              | zero => simp [copyWithMacros, operations] at accepted
              | succ fuel =>
                  cases copied with
                  | atom atom =>
                      simp only [copyWithMacros, operations, atomTrees] at accepted
                      split at accepted <;> simp_all [named, headNotMatch]
                  | list items =>
                      simp only [copyWithMacros, operations, atomTrees] at accepted
                      split at accepted
                      · generalize manyRun : (operations macros fuel).copyMany origin holes renames fresh
                          (.atom second :: .atom third :: atomTrees rest) = manyOption at accepted
                        cases manyOption with
                        | none => simp [manyRun] at accepted
                        | some result =>
                            rcases result with ⟨manyCopies, middle⟩
                            have manyAccepted : copyManyWithMacros macros fuel origin holes renames fresh
                                (.atom second :: .atom third :: atomTrees rest) =
                                  some (manyCopies, middle) := by
                              change (operations macros fuel).copyMany origin holes renames fresh
                                (.atom second :: .atom third :: atomTrees rest) = _
                              exact manyRun
                            have counter := copyManyWithMacros_atomic_counter macros fuel origin holes
                              renames fresh (.atom second :: .atom third :: atomTrees rest)
                              manyCopies middle tailAtomic manyAccepted
                            simp [manyRun] at accepted
                            omega
                      · have ordinary := accepted
                        simp [named, headNotMatch] at ordinary
                        generalize manyRun : (operations macros fuel).copyMany origin holes renames fresh
                          (.atom head :: .atom second :: .atom third :: atomTrees rest) = manyOption at ordinary
                        cases manyOption with
                        | none => simp [manyRun] at ordinary
                        | some result =>
                            rcases result with ⟨manyCopies, middle⟩
                            have manyAccepted : copyManyWithMacros macros fuel origin holes renames fresh
                                (.atom head :: .atom second :: .atom third :: atomTrees rest) =
                                  some (manyCopies, middle) := by
                              change (operations macros fuel).copyMany origin holes renames fresh
                                (.atom head :: .atom second :: .atom third :: atomTrees rest) = _
                              exact manyRun
                            have counter := copyManyWithMacros_atomic_counter macros fuel origin holes renames
                              fresh (.atom head :: .atom second :: .atom third :: atomTrees rest)
                              manyCopies middle allAtomic manyAccepted
                            simp [manyRun] at ordinary
                            omega

theorem copyWithMacros_singleton_child_preserves_counter (macros : List String)
    (fuel origin : Nat) (holes : Holes) (renames : Renames) (fresh : Nat)
    (child : Tree) (childSafe : CounterPreservingInitializer macros child)
    (copied : Tree) (final : Nat)
    (accepted : copyWithMacros macros fuel origin holes renames fresh (.list [child]) =
      some (copied, final)) : final = fresh := by
  cases child with
  | atom atom =>
      exact copyWithMacros_single_atom_list_keeps_counter macros fuel origin holes renames fresh
        atom copied final accepted
  | list children =>
      cases fuel with
      | zero => simp [copyWithMacros, operations] at accepted
      | succ fuel =>
          cases copied with
          | atom atom => simp [copyWithMacros, operations] at accepted
          | list copiedChildren =>
              simp only [copyWithMacros, operations] at accepted
              generalize manyRun : (operations macros fuel).copyMany origin holes renames fresh
                [.list children] = manyOption at accepted
              cases manyOption with
              | none => simp [manyRun] at accepted
              | some result =>
                  rcases result with ⟨manyCopies, middle⟩
                  have manyAccepted : copyManyWithMacros macros fuel origin holes renames fresh
                      [.list children] = some (manyCopies, middle) := by
                    change (operations macros fuel).copyMany origin holes renames fresh
                      [.list children] = _
                    exact manyRun
                  have manySafe : CounterPreservingTrees macros [.list children] :=
                    .cons (.list children) childSafe [] .nil
                  have middleEq := copyManyWithMacros_preserving_counter macros fuel origin holes
                    renames fresh [.list children] manyCopies middle manySafe manyAccepted
                  simp [manyRun] at accepted
                  omega

theorem copyWithMacros_pair_child_preserves_counter (macros : List String)
    (fuel origin : Nat) (holes : Holes) (renames : Renames) (fresh : Nat)
    (head : Atom) (child : Tree) (childSafe : CounterPreservingInitializer macros child)
    (copied : Tree) (final : Nat)
    (accepted : copyWithMacros macros fuel origin holes renames fresh
      (.list [.atom head, child]) = some (copied, final)) : final = fresh := by
  cases fuel with
  | zero => simp [copyWithMacros, operations] at accepted
  | succ fuel =>
      cases copied with
      | atom atom =>
          simp only [copyWithMacros, operations] at accepted
          split at accepted <;> simp_all
      | list items =>
          simp only [copyWithMacros, operations] at accepted
          split at accepted
          · generalize manyRun : (operations macros fuel).copyMany origin holes renames fresh
              [child] = manyOption at accepted
            cases manyOption with
            | none => simp [manyRun] at accepted
            | some result =>
                rcases result with ⟨manyCopies, middle⟩
                have manyAccepted : copyManyWithMacros macros fuel origin holes renames fresh
                    [child] = some (manyCopies, middle) := by
                  change (operations macros fuel).copyMany origin holes renames fresh [child] = _
                  exact manyRun
                have manySafe : CounterPreservingTrees macros [child] :=
                  .cons child childSafe [] .nil
                have middleEq := copyManyWithMacros_preserving_counter macros fuel origin holes
                  renames fresh [child] manyCopies middle manySafe manyAccepted
                simp [manyRun] at accepted
                omega
          · have ordinary := accepted
            simp only [named] at ordinary
            generalize manyRun : (operations macros fuel).copyMany origin holes renames fresh
              [.atom head, child] = manyOption at ordinary
            cases manyOption with
            | none => simp [manyRun] at ordinary
            | some result =>
                rcases result with ⟨manyCopies, middle⟩
                have allSafe : CounterPreservingTrees macros [.atom head, child] :=
                  .cons (.atom head) (atom_initializer_counter_preserving macros head)
                    [child] (.cons child childSafe [] .nil)
                have manyAccepted : copyManyWithMacros macros fuel origin holes renames fresh
                    [.atom head, child] = some (manyCopies, middle) := by
                  change (operations macros fuel).copyMany origin holes renames fresh _ = _
                  exact manyRun
                have middleEq := copyManyWithMacros_preserving_counter macros fuel origin holes
                  renames fresh [.atom head, child] manyCopies middle allSafe manyAccepted
                simp [manyRun] at ordinary
                omega

theorem copyWithMacros_triple_children_preserves_counter (macros : List String)
    (fuel origin : Nat) (holes : Holes) (renames : Renames) (fresh : Nat)
    (head first : Atom) (second : Tree)
    (headNotMatch : head.name ≠ "match")
    (secondSafe : CounterPreservingInitializer macros second)
    (copied : Tree) (final : Nat)
    (accepted : copyWithMacros macros fuel origin holes renames fresh
      (.list [.atom head, .atom first, second]) = some (copied, final)) : final = fresh := by
  cases fuel with
  | zero => simp [copyWithMacros, operations] at accepted
  | succ fuel =>
      cases copied with
      | atom atom =>
          simp only [copyWithMacros, operations] at accepted
          split at accepted <;> simp_all [named, headNotMatch]
      | list items =>
          simp only [copyWithMacros, operations] at accepted
          split at accepted
          · generalize manyRun : (operations macros fuel).copyMany origin holes renames fresh
              [.atom first, second] = manyOption at accepted
            cases manyOption with
            | none => simp [manyRun] at accepted
            | some result =>
                rcases result with ⟨manyCopies, middle⟩
                have manyAccepted : copyManyWithMacros macros fuel origin holes renames fresh
                    [.atom first, second] = some (manyCopies, middle) := by
                  change (operations macros fuel).copyMany origin holes renames fresh
                    [.atom first, second] = _
                  exact manyRun
                have manySafe : CounterPreservingTrees macros [.atom first, second] :=
                  .cons (.atom first) (atom_initializer_counter_preserving macros first)
                    [second] (.cons second secondSafe [] .nil)
                have middleEq := copyManyWithMacros_preserving_counter macros fuel origin holes
                  renames fresh [.atom first, second] manyCopies middle manySafe manyAccepted
                simp [manyRun] at accepted
                omega
          · have ordinary := accepted
            simp [named, headNotMatch] at ordinary
            generalize manyRun : (operations macros fuel).copyMany origin holes renames fresh
              [.atom head, .atom first, second] = manyOption at ordinary
            cases manyOption with
            | none => simp [manyRun] at ordinary
            | some result =>
                rcases result with ⟨manyCopies, middle⟩
                have allSafe : CounterPreservingTrees macros [.atom head, .atom first, second] :=
                  .cons (.atom head) (atom_initializer_counter_preserving macros head)
                    [.atom first, second]
                    (.cons (.atom first) (atom_initializer_counter_preserving macros first)
                      [second] (.cons second secondSafe [] .nil))
                have manyAccepted : copyManyWithMacros macros fuel origin holes renames fresh
                    [.atom head, .atom first, second] = some (manyCopies, middle) := by
                  change (operations macros fuel).copyMany origin holes renames fresh _ = _
                  exact manyRun
                have middleEq := copyManyWithMacros_preserving_counter macros fuel origin holes
                  renames fresh [.atom head, .atom first, second] manyCopies middle allSafe manyAccepted
                simp [manyRun] at ordinary
                omega

theorem copyWithMacros_quadruple_children_preserves_counter (macros : List String)
    (fuel origin : Nat) (holes : Holes) (renames : Renames) (fresh : Nat)
    (head first second : Atom) (third : Tree)
    (headNotMatch : head.name ≠ "match")
    (thirdSafe : CounterPreservingInitializer macros third)
    (copied : Tree) (final : Nat)
    (accepted : copyWithMacros macros fuel origin holes renames fresh
      (.list [.atom head, .atom first, .atom second, third]) = some (copied, final)) :
    final = fresh := by
  cases fuel with
  | zero => simp [copyWithMacros, operations] at accepted
  | succ fuel =>
      cases copied with
      | atom atom =>
          simp only [copyWithMacros, operations] at accepted
          split at accepted <;> simp_all [named, headNotMatch]
      | list items =>
          simp only [copyWithMacros, operations] at accepted
          split at accepted
          · generalize manyRun : (operations macros fuel).copyMany origin holes renames fresh
              [.atom first, .atom second, third] = manyOption at accepted
            cases manyOption with
            | none => simp [manyRun] at accepted
            | some result =>
                rcases result with ⟨manyCopies, middle⟩
                have manyAccepted : copyManyWithMacros macros fuel origin holes renames fresh
                    [.atom first, .atom second, third] = some (manyCopies, middle) := by
                  change (operations macros fuel).copyMany origin holes renames fresh
                    [.atom first, .atom second, third] = _
                  exact manyRun
                have manySafe : CounterPreservingTrees macros
                    [.atom first, .atom second, third] :=
                  .cons (.atom first) (atom_initializer_counter_preserving macros first)
                    [.atom second, third]
                    (.cons (.atom second) (atom_initializer_counter_preserving macros second)
                      [third] (.cons third thirdSafe [] .nil))
                have middleEq := copyManyWithMacros_preserving_counter macros fuel origin holes
                  renames fresh [.atom first, .atom second, third] manyCopies middle
                  manySafe manyAccepted
                simp [manyRun] at accepted
                omega
          · have ordinary := accepted
            simp [named, headNotMatch] at ordinary
            generalize manyRun : (operations macros fuel).copyMany origin holes renames fresh
              [.atom head, .atom first, .atom second, third] = manyOption at ordinary
            cases manyOption with
            | none => simp [manyRun] at ordinary
            | some result =>
                rcases result with ⟨manyCopies, middle⟩
                have manyAccepted : copyManyWithMacros macros fuel origin holes renames fresh
                    [.atom head, .atom first, .atom second, third] = some (manyCopies, middle) := by
                  change (operations macros fuel).copyMany origin holes renames fresh _ = _
                  exact manyRun
                have allSafe : CounterPreservingTrees macros
                    [.atom head, .atom first, .atom second, third] :=
                  .cons (.atom head) (atom_initializer_counter_preserving macros head)
                    [.atom first, .atom second, third]
                    (.cons (.atom first) (atom_initializer_counter_preserving macros first)
                      [.atom second, third]
                      (.cons (.atom second) (atom_initializer_counter_preserving macros second)
                        [third] (.cons third thirdSafe [] .nil)))
                have middleEq := copyManyWithMacros_preserving_counter macros fuel origin holes
                  renames fresh [.atom head, .atom first, .atom second, third] manyCopies middle
                  allSafe manyAccepted
                simp [manyRun] at ordinary
                omega

inductive MacroCounterSafeInitializer (macros : List String) : Tree → Prop where
  | atom (value : Atom) : MacroCounterSafeInitializer macros (.atom value)
  | neutralTree (value : Tree) (safe : CounterNeutralTree macros value) :
      MacroCounterSafeInitializer macros value
  | singletonList (value : Atom) : MacroCounterSafeInitializer macros (.list [.atom value])
  | singletonWrapped (child : Tree) (childSafe : MacroCounterSafeInitializer macros child) :
      MacroCounterSafeInitializer macros (.list [child])
  | pairChild (head : Atom) (child : Tree)
      (childSafe : MacroCounterSafeInitializer macros child) :
      MacroCounterSafeInitializer macros (.list [.atom head, child])
  | tripleChildren (head first : Atom) (second : Tree)
      (headNotMatch : head.name ≠ "match")
      (secondSafe : MacroCounterSafeInitializer macros second) :
      MacroCounterSafeInitializer macros (.list [.atom head, .atom first, second])
  | quadrupleChildren (head first second : Atom) (third : Tree)
      (headNotMatch : head.name ≠ "match")
      (thirdSafe : MacroCounterSafeInitializer macros third) :
      MacroCounterSafeInitializer macros
        (.list [.atom head, .atom first, .atom second, third])
  | pairList (head argument : Atom) :
      MacroCounterSafeInitializer macros (.list [.atom head, .atom argument])
  | tripleList (head first second : Atom) (headNotMatch : head.name ≠ "match") :
      MacroCounterSafeInitializer macros (.list [.atom head, .atom first, .atom second])
  | quadrupleList (head first second third : Atom) (headNotMatch : head.name ≠ "match") :
      MacroCounterSafeInitializer macros
        (.list [.atom head, .atom first, .atom second, .atom third])
  | atomList (atoms : List Atom) (headNotMatch : atomTreesHeadNotMatch atoms) :
      MacroCounterSafeInitializer macros (.list (atomTrees atoms))

theorem macroCounterSafeInitializer_preserving (macros : List String) (value : Tree)
    (safe : MacroCounterSafeInitializer macros value) : CounterPreservingInitializer macros value := by
  cases safe with
  | atom atom => exact atom_initializer_counter_preserving macros atom
  | neutralTree value neutral => exact counterNeutralTree_preserving macros value neutral
  | singletonList atom => exact singleton_atom_list_counter_preserving macros atom
  | singletonWrapped child childSafe =>
      intro fuel origin holes renames fresh copied final accepted
      exact copyWithMacros_singleton_child_preserves_counter macros fuel origin holes renames
        fresh child (macroCounterSafeInitializer_preserving macros child childSafe) copied final
        accepted
  | pairChild head child childSafe =>
      intro fuel origin holes renames fresh copied final accepted
      exact copyWithMacros_pair_child_preserves_counter macros fuel origin holes renames fresh
        head child (macroCounterSafeInitializer_preserving macros child childSafe) copied final
        accepted
  | tripleChildren head first second headNotMatch secondSafe =>
      intro fuel origin holes renames fresh copied final accepted
      exact copyWithMacros_triple_children_preserves_counter macros fuel origin holes renames fresh
        head first second headNotMatch
        (macroCounterSafeInitializer_preserving macros second secondSafe)
        copied final accepted
  | quadrupleChildren head first second third headNotMatch thirdSafe =>
      intro fuel origin holes renames fresh copied final accepted
      exact copyWithMacros_quadruple_children_preserves_counter macros fuel origin holes renames
        fresh head first second third headNotMatch
        (macroCounterSafeInitializer_preserving macros third thirdSafe)
        copied final accepted
  | pairList head argument => exact pair_atom_list_counter_preserving macros head argument
  | tripleList head first second headNotMatch =>
      exact triple_atom_list_counter_preserving macros head first second headNotMatch
  | quadrupleList head first second third headNotMatch =>
      exact quadruple_atom_list_counter_preserving macros head first second third headNotMatch
  | atomList atoms headNotMatch =>
      intro fuel origin holes renames fresh copied final accepted
      exact copyWithMacros_atomTrees_keeps_counter macros fuel origin holes renames fresh
        atoms headNotMatch copied final accepted

inductive MacroCounterSafeBindingInputs (macros : List String) : List Tree → Prop where
  | nil : MacroCounterSafeBindingInputs macros []
  | cons (name type value : Tree) (safe : MacroCounterSafeInitializer macros value)
      (tail : List Tree) (tailSafe : MacroCounterSafeBindingInputs macros tail) :
      MacroCounterSafeBindingInputs macros (.list [.list [name, type], value] :: tail)

theorem macroCounterSafeBindingInputs_preserving (macros : List String) (bindings : List Tree)
    (safe : MacroCounterSafeBindingInputs macros bindings) :
    CounterPreservingBindings macros bindings := by
  induction safe with
  | nil => exact .nil
  | @cons name type value valueSafe tail _tailSafe ih =>
      exact .cons name type value (macroCounterSafeInitializer_preserving macros value valueSafe)
        tail ih

inductive MacroCounterSafeCases (macros : List String) : List Tree → Prop where
  | nil : MacroCounterSafeCases macros []
  | emptyPattern (body : Tree) (bodySafe : MacroCounterSafeInitializer macros body)
      (tail : List Tree) (tailSafe : MacroCounterSafeCases macros tail) :
      MacroCounterSafeCases macros (.list [.list [], body] :: tail)
  | boundPattern (constructor : Tree) (parameters : List Tree) (body : Tree)
      (bodySafe : MacroCounterSafeInitializer macros body) (tail : List Tree)
      (tailSafe : MacroCounterSafeCases macros tail) :
      MacroCounterSafeCases macros (.list [.list (constructor :: parameters), body] :: tail)

theorem macroCounterSafeCases_preserving (macros : List String) (cases : List Tree)
    (safe : MacroCounterSafeCases macros cases) : CounterPreservingCases macros cases := by
  induction safe with
  | nil => exact .nil
  | emptyPattern body bodySafe tail _tailSafe ih =>
      exact .emptyPattern body (macroCounterSafeInitializer_preserving macros body bodySafe)
        tail ih
  | boundPattern constructor parameters body bodySafe tail _tailSafe ih =>
      exact .boundPattern constructor parameters body
        (macroCounterSafeInitializer_preserving macros body bodySafe) tail ih

theorem copyBindingsWithMacros_atoms_counter (macros : List String) (fuel origin : Nat)
    (holes : Holes) (outside : Renames) (names : Renames) (fresh : Nat)
    (bindings outputs : List Tree) (finalNames : Renames) (final : Nat)
    (atomic : AtomBindingInputs bindings)
    (accepted : copyBindingsWithMacros macros fuel origin holes outside names fresh bindings =
      some (outputs, finalNames, final)) :
    final = fresh + bindings.length := by
  induction atomic generalizing fuel origin holes outside names fresh outputs finalNames final with
  | nil =>
      cases fuel with
      | zero => simp [copyBindingsWithMacros, operations] at accepted
      | succ fuel =>
          simp only [copyBindingsWithMacros, operations] at accepted
          have tupleEq := Option.some.inj accepted
          have finalEq := congrArg (fun result : List Tree × Renames × Nat => result.2.2) tupleEq
          simpa using finalEq.symm
  | @cons name type value tail _tailAtomic ih =>
      cases fuel with
      | zero => simp [copyBindingsWithMacros, operations] at accepted
      | succ fuel =>
          simp only [copyBindingsWithMacros, operations] at accepted
          generalize binderResult : binder holes names fresh (.atom name) = binderOption at accepted
          cases binderOption with
          | none => simp [binderResult] at accepted
          | some result =>
              rcases result with ⟨nameCopy, names', next⟩
              generalize valueResult : (operations macros fuel).copy origin holes outside next
                (.atom value) = valueOption at accepted
              cases valueOption with
              | none => simp [binderResult, valueResult] at accepted
              | some result =>
                  rcases result with ⟨valueCopy, afterValue⟩
                  generalize tailResult : (operations macros fuel).copyBindings origin holes
                    outside names' afterValue tail = tailOption at accepted
                  cases tailOption with
                  | none => simp [binderResult, valueResult, tailResult] at accepted
                  | some result =>
                      rcases result with ⟨tailCopies, endNames, endCounter⟩
                      have acceptedParts := accepted
                      simp [binderResult, valueResult, tailResult] at acceptedParts
                      have finalEq : endCounter = final := acceptedParts.2.2
                      have binderFacts := binder_success_counter holes names fresh (.atom name)
                        nameCopy names' next (by simp [binderResult])
                      rcases binderFacts with ⟨freshAtom, _shape, nextEq, _tokenEq⟩
                      have valueCounter := copyWithMacros_atom_keeps_counter macros fuel origin
                        holes outside next value valueCopy afterValue valueResult
                      have tailCounter := ih fuel origin holes outside names' afterValue tailCopies
                        endNames endCounter (by
                          change (operations macros fuel).copyBindings origin holes outside names'
                            afterValue tail = some (tailCopies, endNames, endCounter)
                          exact tailResult)
                      rw [← finalEq, tailCounter, valueCounter, nextEq]
                      simp only [List.length_cons]
                      omega

theorem copyBindings_atomic_counter (fuel origin : Nat) (holes : Holes) (outside : Renames)
    (names : Renames) (fresh : Nat) (bindings outputs : List Tree)
    (finalNames : Renames) (final : Nat) (atomic : AtomicBindingInputs bindings)
    (accepted : copyBindings fuel origin holes outside names fresh bindings =
      some (outputs, finalNames, final)) :
    final = fresh + bindings.length := by
  induction atomic generalizing fuel origin holes outside names fresh outputs finalNames final with
  | nil =>
      cases fuel with
      | zero => simp [copyBindings, operations] at accepted
      | succ fuel =>
          simp only [copyBindings, operations] at accepted
          have tupleEq := Option.some.inj accepted
          have finalEq := congrArg (fun result : List Tree × Renames × Nat => result.2.2) tupleEq
          simpa using finalEq.symm
  | @cons name type value safe tail _tailAtomic ih =>
      cases fuel with
      | zero => simp [copyBindings, operations] at accepted
      | succ fuel =>
          simp only [copyBindings, operations] at accepted
          generalize binderResult : binder holes names fresh name = binderOption at accepted
          cases binderOption with
          | none => simp [binderResult] at accepted
          | some result =>
              rcases result with ⟨nameCopy, names', next⟩
              generalize valueResult : (operations [] fuel).copy origin holes outside next
                  value = valueOption at accepted
              cases valueOption with
              | none => simp [binderResult, valueResult] at accepted
              | some result =>
                  rcases result with ⟨valueCopy, afterValue⟩
                  generalize tailResult : (operations [] fuel).copyBindings origin holes outside
                      names' afterValue tail = tailOption at accepted
                  cases tailOption with
                  | none => simp [binderResult, valueResult, tailResult] at accepted
                  | some result =>
                      rcases result with ⟨tailCopies, endNames, endCounter⟩
                      have acceptedParts := accepted
                      simp [binderResult, valueResult, tailResult] at acceptedParts
                      have finalEq : endCounter = final := acceptedParts.2.2
                      have binderFacts := binder_success_counter holes names fresh name
                        nameCopy names' next (by simp [binderResult])
                      rcases binderFacts with ⟨freshAtom, _shape, nextEq, _tokenEq⟩
                      have valueCounter : afterValue = next := by
                        cases safe with
                        | atom atom =>
                            exact copy_atom_keeps_counter fuel origin holes outside
                              next atom valueCopy afterValue valueResult
                        | singletonList atom =>
                            exact copy_single_atom_list_keeps_counter fuel origin holes outside
                              next atom valueCopy afterValue valueResult
                        | pairList head argument =>
                            exact copy_two_atom_list_keeps_counter fuel origin holes outside
                              next head argument valueCopy afterValue valueResult
                        | tripleList head first second headNotMatch =>
                            exact copy_three_atom_list_keeps_counter fuel origin holes outside
                              next head first second valueCopy afterValue valueResult headNotMatch
                        | quadrupleList head first second third headNotMatch =>
                            exact copy_four_atom_list_keeps_counter fuel origin holes outside
                              next head first second third valueCopy afterValue valueResult headNotMatch
                      have tailCounter := ih fuel origin holes outside names' afterValue tailCopies
                        endNames endCounter (by
                          change (operations [] fuel).copyBindings origin holes outside names'
                            afterValue tail = some (tailCopies, endNames, endCounter)
                          exact tailResult)
                      rw [← finalEq, tailCounter, valueCounter, nextEq]
                      simp only [List.length_cons]
                      omega

def bindingTokens : List Tree → List Nat
  | [] => []
  | .list [.list [.atom atom, _], _] :: tail => atom.token :: bindingTokens tail
  | _ => []

theorem copyBindingsWithMacros_atoms_token_sequence (macros : List String) (fuel origin : Nat)
    (holes : Holes) (outside names : Renames) (fresh : Nat) (bindings outputs : List Tree)
    (finalNames : Renames) (final : Nat) (atomic : AtomBindingInputs bindings)
    (accepted : copyBindingsWithMacros macros fuel origin holes outside names fresh bindings =
      some (outputs, finalNames, final)) :
    bindingTokens outputs = counterTokens fresh bindings.length := by
  induction atomic generalizing fuel origin holes outside names fresh outputs finalNames final with
  | nil =>
      cases fuel with
      | zero => simp [copyBindingsWithMacros, operations] at accepted
      | succ fuel =>
          simp only [copyBindingsWithMacros, operations] at accepted
          have tupleEq := Option.some.inj accepted
          have copiedEmpty : outputs = [] := by
            simpa using (congrArg Prod.fst tupleEq).symm
          subst outputs
          rfl
  | @cons name type value tail _tailAtomic ih =>
      cases fuel with
      | zero => simp [copyBindingsWithMacros, operations] at accepted
      | succ fuel =>
          simp only [copyBindingsWithMacros, operations] at accepted
          generalize binderResult : binder holes names fresh (.atom name) = binderOption at accepted
          cases binderOption with
          | none => simp [binderResult] at accepted
          | some binderOutput =>
              rcases binderOutput with ⟨nameCopy, names', next⟩
              generalize valueResult : (operations macros fuel).copy origin holes outside next
                (.atom value) = valueOption at accepted
              cases valueOption with
              | none => simp [binderResult, valueResult] at accepted
              | some valueOutput =>
                  rcases valueOutput with ⟨valueCopy, afterValue⟩
                  generalize tailResult : (operations macros fuel).copyBindings origin holes
                    outside names' afterValue tail = tailOption at accepted
                  cases tailOption with
                  | none => simp [binderResult, valueResult, tailResult] at accepted
                  | some tailOutput =>
                      rcases tailOutput with ⟨tailCopies, endNames, endCounter⟩
                      have acceptedParts := accepted
                      simp [binderResult, valueResult, tailResult] at acceptedParts
                      have copiedShape : outputs =
                        .list [.list [nameCopy, .atom type], valueCopy] :: tailCopies :=
                        acceptedParts.1.symm
                      have binderFacts := binder_success_counter holes names fresh (.atom name)
                        nameCopy names' next (by simp [binderResult])
                      rcases binderFacts with ⟨freshAtom, atomShape, nextEq, tokenEq⟩
                      have valueCounter := copyWithMacros_atom_keeps_counter macros fuel origin
                        holes outside next value valueCopy afterValue valueResult
                      have tailSequence := ih fuel origin holes outside names' afterValue tailCopies
                        endNames endCounter (by
                          change (operations macros fuel).copyBindings origin holes outside names'
                            afterValue tail = some (tailCopies, endNames, endCounter)
                          exact tailResult)
                      subst outputs
                      simp [bindingTokens, atomShape, tokenEq, counterTokens, valueCounter,
                        nextEq, tailSequence]

theorem copyBindingsWithMacros_preserving_token_sequence (macros : List String)
    (fuel origin : Nat) (holes : Holes) (outside names : Renames) (fresh : Nat)
    (bindings outputs : List Tree) (finalNames : Renames) (final : Nat)
    (safe : CounterPreservingBindings macros bindings)
    (accepted : copyBindingsWithMacros macros fuel origin holes outside names fresh bindings =
      some (outputs, finalNames, final)) :
    bindingTokens outputs = counterTokens fresh bindings.length := by
  induction safe generalizing fuel origin holes outside names fresh outputs finalNames final with
  | nil =>
      cases fuel with
      | zero => simp [copyBindingsWithMacros, operations] at accepted
      | succ fuel =>
          simp only [copyBindingsWithMacros, operations] at accepted
          have tupleEq := Option.some.inj accepted
          have copiedEmpty : outputs = [] := by
            simpa using (congrArg Prod.fst tupleEq).symm
          subst outputs
          rfl
  | @cons name type value preserves tail _tailSafe ih =>
      cases fuel with
      | zero => simp [copyBindingsWithMacros, operations] at accepted
      | succ fuel =>
          simp only [copyBindingsWithMacros, operations] at accepted
          generalize binderResult : binder holes names fresh name = binderOption at accepted
          cases binderOption with
          | none => simp [binderResult] at accepted
          | some binderOutput =>
              rcases binderOutput with ⟨nameCopy, names', next⟩
              generalize valueResult : (operations macros fuel).copy origin holes outside next
                value = valueOption at accepted
              cases valueOption with
              | none => simp [binderResult, valueResult] at accepted
              | some valueOutput =>
                  rcases valueOutput with ⟨valueCopy, afterValue⟩
                  generalize tailResult : (operations macros fuel).copyBindings origin holes
                    outside names' afterValue tail = tailOption at accepted
                  cases tailOption with
                  | none => simp [binderResult, valueResult, tailResult] at accepted
                  | some tailOutput =>
                      rcases tailOutput with ⟨tailCopies, endNames, endCounter⟩
                      have acceptedParts := accepted
                      simp [binderResult, valueResult, tailResult] at acceptedParts
                      have copiedShape : outputs =
                        .list [.list [nameCopy, type], valueCopy] :: tailCopies :=
                        acceptedParts.1.symm
                      have binderFacts := binder_success_counter holes names fresh name
                        nameCopy names' next (by simp [binderResult])
                      rcases binderFacts with ⟨freshAtom, atomShape, nextEq, tokenEq⟩
                      have valueCounter := preserves fuel origin holes outside next valueCopy
                        afterValue valueResult
                      have tailSequence := ih fuel origin holes outside names' afterValue tailCopies
                        endNames endCounter (by
                          change (operations macros fuel).copyBindings origin holes outside names'
                            afterValue tail = some (tailCopies, endNames, endCounter)
                          exact tailResult)
                      subst outputs
                      simp [bindingTokens, atomShape, tokenEq, counterTokens, valueCounter,
                        nextEq, tailSequence]

theorem copyBindings_atomic_token_sequence (fuel origin : Nat) (holes : Holes)
    (outside names : Renames) (fresh : Nat) (bindings outputs : List Tree)
    (finalNames : Renames) (final : Nat) (atomic : AtomicBindingInputs bindings)
    (accepted : copyBindings fuel origin holes outside names fresh bindings =
      some (outputs, finalNames, final)) :
    bindingTokens outputs = counterTokens fresh bindings.length := by
  induction atomic generalizing fuel origin holes outside names fresh outputs finalNames final with
  | nil =>
      cases fuel with
      | zero => simp [copyBindings, operations] at accepted
      | succ fuel =>
          simp only [copyBindings, operations] at accepted
          have tupleEq := Option.some.inj accepted
          have copiedEmpty : outputs = [] := by
            simpa using (congrArg Prod.fst tupleEq).symm
          subst outputs
          rfl
  | @cons name type value safe tail _tailAtomic ih =>
      cases fuel with
      | zero => simp [copyBindings, operations] at accepted
      | succ fuel =>
          simp only [copyBindings, operations] at accepted
          generalize binderResult : binder holes names fresh name = binderOption at accepted
          cases binderOption with
          | none => simp [binderResult] at accepted
          | some binderOutput =>
              rcases binderOutput with ⟨nameCopy, names', next⟩
              generalize valueResult : (operations [] fuel).copy origin holes outside next
                  value = valueOption at accepted
              cases valueOption with
              | none => simp [binderResult, valueResult] at accepted
              | some valueOutput =>
                  rcases valueOutput with ⟨valueCopy, afterValue⟩
                  generalize tailResult : (operations [] fuel).copyBindings origin holes outside
                      names' afterValue tail = tailOption at accepted
                  cases tailOption with
                  | none => simp [binderResult, valueResult, tailResult] at accepted
                  | some tailOutput =>
                      rcases tailOutput with ⟨tailCopies, endNames, endCounter⟩
                      have acceptedParts := accepted
                      simp [binderResult, valueResult, tailResult] at acceptedParts
                      have copiedShape : outputs =
                        .list [.list [nameCopy, type], valueCopy] :: tailCopies := acceptedParts.1.symm
                      have binderFacts := binder_success_counter holes names fresh name
                        nameCopy names' next (by simp [binderResult])
                      rcases binderFacts with ⟨freshAtom, atomShape, nextEq, tokenEq⟩
                      have valueCounter : afterValue = next := by
                        cases safe with
                        | atom atom =>
                            exact copy_atom_keeps_counter fuel origin holes outside
                              next atom valueCopy afterValue valueResult
                        | singletonList atom =>
                            exact copy_single_atom_list_keeps_counter fuel origin holes outside
                              next atom valueCopy afterValue valueResult
                        | pairList head argument =>
                            exact copy_two_atom_list_keeps_counter fuel origin holes outside
                              next head argument valueCopy afterValue valueResult
                        | tripleList head first second headNotMatch =>
                            exact copy_three_atom_list_keeps_counter fuel origin holes outside
                              next head first second valueCopy afterValue valueResult headNotMatch
                        | quadrupleList head first second third headNotMatch =>
                            exact copy_four_atom_list_keeps_counter fuel origin holes outside
                              next head first second third valueCopy afterValue valueResult headNotMatch
                      have tailSequence := ih fuel origin holes outside names' afterValue tailCopies
                        endNames endCounter (by
                          change (operations [] fuel).copyBindings origin holes outside names'
                            afterValue tail = some (tailCopies, endNames, endCounter)
                          exact tailResult)
                      subst outputs
                      simp [bindingTokens, atomShape, tokenEq, counterTokens, valueCounter,
                        nextEq, tailSequence]

noncomputable def checkCopyWithMacros (macros : List String) (fuel origin : Nat) (holes : Holes)
    (fresh : Nat) (template actual : Tree) (final : Nat) : Bool :=
  decide (copyWithMacros macros fuel origin holes [] fresh template = some (actual, final))

theorem checkCopyWithMacros_sound
    (accepted : checkCopyWithMacros macros fuel origin holes fresh template actual final = true) :
    copyWithMacros macros fuel origin holes [] fresh template = some (actual, final) :=
  of_decide_eq_true accepted

noncomputable def checkCopy (fuel origin : Nat) (holes : Holes) (fresh : Nat) (template actual : Tree)
    (final : Nat) : Bool := decide (copy fuel origin holes [] fresh template = some (actual, final))

theorem checkCopy_sound (accepted : checkCopy fuel origin holes fresh template actual final = true) :
    copy fuel origin holes [] fresh template = some (actual, final) :=
  of_decide_eq_true accepted

theorem copyParameters_counter (fuel : Nat) (holes : Holes) (renames : Renames)
    (fresh : Nat) (parameters : List Tree) (copied : List Tree)
    (finalRenames : Renames) (final : Nat)
    (accepted : copyParameters fuel holes renames fresh parameters =
      some (copied, finalRenames, final)) :
    final = fresh + parameters.length := by
  induction fuel generalizing holes renames fresh parameters copied finalRenames final with
  | zero => simp [copyParameters, operations] at accepted
  | succ fuel ih =>
      cases parameters with
      | nil =>
          simp only [copyParameters, operations] at accepted
          simp only [List.length_nil, Nat.add_zero]
          simpa using (congrArg (fun result : List Tree × Renames × Nat => result.2.2)
            (Option.some.inj accepted)).symm
      | cons parameter tail =>
          cases parameter with
          | atom atom => simp [copyParameters, operations] at accepted
          | list fields =>
              cases fields with
              | nil => simp [copyParameters, operations] at accepted
              | cons name rest =>
                  cases rest with
                  | nil => simp [copyParameters, operations] at accepted
                  | cons type rest =>
                      cases rest with
                      | cons extra _ => simp [copyParameters, operations] at accepted
                      | nil =>
                          simp only [copyParameters, operations] at accepted
                          simp only [List.length_cons]
                          generalize binderResult : binder holes renames fresh name = binderOption at accepted
                          cases binderOption with
                          | none => simp [binderResult] at accepted
                          | some result =>
                              rcases result with ⟨nameCopy, names, next⟩
                              generalize tailResult : (operations [] fuel).copyParameters
                                  holes names next tail = tailOption at accepted
                              cases tailOption with
                              | none => simp [binderResult, tailResult] at accepted
                              | some tailCopy =>
                                  rcases tailCopy with ⟨outputs, endNames, endCounter⟩
                                  simp [binderResult, tailResult] at accepted
                                  have binderFacts := binder_success_counter holes renames fresh name
                                    nameCopy names next (by simp [binderResult])
                                  rcases binderFacts with ⟨freshAtom, _shape, counterStep, _tokenStep⟩
                                  have tailFacts := ih holes names next tail outputs endNames endCounter
                                    (by
                                      change (operations [] fuel).copyParameters holes names next tail =
                                        some (outputs, endNames, endCounter)
                                      exact tailResult)
                                  omega

theorem copyParameters_counter_with_macros (macros : List String) (fuel : Nat)
    (holes : Holes) (renames : Renames) (fresh : Nat) (parameters : List Tree)
    (copied : List Tree) (finalRenames : Renames) (final : Nat)
    (accepted : (operations macros fuel).copyParameters holes renames fresh parameters =
      some (copied, finalRenames, final)) :
    final = fresh + parameters.length := by
  induction fuel generalizing holes renames fresh parameters copied finalRenames final with
  | zero => simp [operations] at accepted
  | succ fuel ih =>
      cases parameters with
      | nil =>
          simp only [operations] at accepted
          simp only [List.length_nil, Nat.add_zero]
          simpa using (congrArg (fun result : List Tree × Renames × Nat => result.2.2)
            (Option.some.inj accepted)).symm
      | cons parameter tail =>
          cases parameter with
          | atom atom => simp [operations] at accepted
          | list fields =>
              cases fields with
              | nil => simp [operations] at accepted
              | cons name rest =>
                  cases rest with
                  | nil => simp [operations] at accepted
                  | cons type rest =>
                      cases rest with
                      | cons extra _ => simp [operations] at accepted
                      | nil =>
                          simp only [operations] at accepted
                          simp only [List.length_cons]
                          generalize binderResult : binder holes renames fresh name = binderOption at accepted
                          cases binderOption with
                          | none => simp [binderResult] at accepted
                          | some result =>
                              rcases result with ⟨nameCopy, names, next⟩
                              generalize tailResult : (operations macros fuel).copyParameters
                                  holes names next tail = tailOption at accepted
                              cases tailOption with
                              | none => simp [binderResult, tailResult] at accepted
                              | some tailCopy =>
                                  rcases tailCopy with ⟨outputs, endNames, endCounter⟩
                                  simp [binderResult, tailResult] at accepted
                                  have binderFacts := binder_success_counter holes renames fresh name
                                    nameCopy names next (by simp [binderResult])
                                  rcases binderFacts with ⟨freshAtom, _shape, counterStep, _tokenStep⟩
                                  have tailFacts := ih holes names next tail outputs endNames endCounter
                                    (by
                                      change (operations macros fuel).copyParameters holes names next tail =
                                        some (outputs, endNames, endCounter)
                                      exact tailResult)
                                  omega

def parameterTokens : List Tree → List Nat
  | [] => []
  | .list [.atom atom, _] :: tail => atom.token :: parameterTokens tail
  | _ => []

theorem counterTokens_add (fresh left right : Nat) :
    counterTokens fresh (left + right) =
      counterTokens fresh left ++ counterTokens (fresh + left) right := by
  induction left generalizing fresh with
  | zero => simp [counterTokens]
  | succ left ih =>
      rw [Nat.succ_add]
      simp only [counterTokens]
      rw [ih (fresh + 1)]
      simp only [List.cons_append]
      congr 1
      congr 1
      have startEq : fresh + 1 + left = fresh + (left + 1) := by omega
      rw [startEq]

private theorem counterTokens_lower_bound (fresh count token : Nat)
    (member : token ∈ counterTokens fresh count) :
    3 * (fresh + 1) + 2 ≤ token := by
  induction count generalizing fresh with
  | zero => simp [counterTokens] at member
  | succ count ih =>
      simp only [counterTokens, List.mem_cons] at member
      rcases member with same | later
      · subst token
        omega
      · have lower := ih (fresh + 1) later
        omega

def Unique (values : List Nat) : Prop :=
  match values with
  | [] => True
  | head :: tail => head ∉ tail ∧ Unique tail

theorem counterTokens_distinct (fresh count : Nat) :
    Unique (counterTokens fresh count) := by
  induction count generalizing fresh with
  | zero => simp [Unique, counterTokens]
  | succ count ih =>
      simp only [counterTokens, Unique]
      constructor
      · intro member
        have lower := counterTokens_lower_bound (fresh + 1) count
          (3 * (fresh + 1) + 2) member
        omega
      · exact ih (fresh + 1)

theorem copyBindingsWithMacros_atoms_tokens_unique (macros : List String) (fuel origin : Nat)
    (holes : Holes) (outside names : Renames) (fresh : Nat) (bindings outputs : List Tree)
    (finalNames : Renames) (final : Nat) (atomic : AtomBindingInputs bindings)
    (accepted : copyBindingsWithMacros macros fuel origin holes outside names fresh bindings =
      some (outputs, finalNames, final)) : Unique (bindingTokens outputs) := by
  rw [copyBindingsWithMacros_atoms_token_sequence macros fuel origin holes outside names fresh
    bindings outputs finalNames final atomic accepted]
  exact counterTokens_distinct fresh bindings.length

theorem counterTokens_reserved_class (fresh count token : Nat)
    (member : token ∈ counterTokens fresh count) : token % 3 = 2 := by
  induction count generalizing fresh with
  | zero => simp [counterTokens] at member
  | succ count ih =>
      simp only [counterTokens, List.mem_cons] at member
      rcases member with same | later
      · subst token
        omega
      · exact ih (fresh + 1) later

theorem counterTokens_within_interval (fresh count token : Nat)
    (member : token ∈ counterTokens fresh count) :
    ∃ counter, fresh < counter ∧ counter ≤ fresh + count ∧ token = 3 * counter + 2 := by
  induction count generalizing fresh token with
  | zero => simp [counterTokens] at member
  | succ count ih =>
      simp only [counterTokens, List.mem_cons] at member
      rcases member with same | later
      · subst token
        exact ⟨fresh + 1, by omega, by omega, by omega⟩
      · obtain ⟨counter, lower, upper, tokenEq⟩ := ih (fresh + 1) token later
        exact ⟨counter, by omega, by omega, tokenEq⟩

theorem copyBindingsWithMacros_preserving_tokens_unique (macros : List String)
    (fuel origin : Nat) (holes : Holes) (outside names : Renames) (fresh : Nat)
    (bindings outputs : List Tree) (finalNames : Renames) (final : Nat)
    (safe : CounterPreservingBindings macros bindings)
    (accepted : copyBindingsWithMacros macros fuel origin holes outside names fresh bindings =
      some (outputs, finalNames, final)) : Unique (bindingTokens outputs) := by
  rw [copyBindingsWithMacros_preserving_token_sequence macros fuel origin holes outside names fresh
    bindings outputs finalNames final safe accepted]
  exact counterTokens_distinct fresh bindings.length

theorem copyBindingsWithMacros_preserving_tokens_avoid_source (macros : List String)
    (fuel origin : Nat) (holes : Holes) (outside names : Renames) (fresh : Nat)
    (bindings outputs : List Tree) (finalNames : Renames) (final sourceToken : Nat)
    (safe : CounterPreservingBindings macros bindings)
    (accepted : copyBindingsWithMacros macros fuel origin holes outside names fresh bindings =
      some (outputs, finalNames, final)) (sourceClass : sourceToken % 3 = 1) :
    sourceToken ∉ bindingTokens outputs := by
  rw [copyBindingsWithMacros_preserving_token_sequence macros fuel origin holes outside names fresh
    bindings outputs finalNames final safe accepted]
  intro member
  have generatedClass := counterTokens_reserved_class fresh bindings.length sourceToken member
  omega

theorem copyBindingsWithMacros_preserving_tokens_within_interval (macros : List String)
    (fuel origin : Nat) (holes : Holes) (outside names : Renames) (fresh : Nat)
    (bindings outputs : List Tree) (finalNames : Renames) (final : Nat)
    (safe : CounterPreservingBindings macros bindings)
    (accepted : copyBindingsWithMacros macros fuel origin holes outside names fresh bindings =
      some (outputs, finalNames, final)) (token : Nat) (member : token ∈ bindingTokens outputs) :
    ∃ counter, fresh < counter ∧ counter ≤ final ∧ token = 3 * counter + 2 := by
  have sequence := copyBindingsWithMacros_preserving_token_sequence macros fuel origin holes
    outside names fresh bindings outputs finalNames final safe accepted
  rw [sequence] at member
  obtain ⟨counter, lower, upper, tokenEq⟩ :=
    counterTokens_within_interval fresh bindings.length token member
  have finalEq := copyBindingsWithMacros_preserving_counter macros fuel origin holes outside names
    fresh bindings outputs finalNames final safe accepted
  exact ⟨counter, lower, by omega, tokenEq⟩

theorem copyBindingsWithMacros_macro_safe_token_sequence (macros : List String)
    (fuel origin : Nat) (holes : Holes) (outside names : Renames) (fresh : Nat)
    (bindings outputs : List Tree) (finalNames : Renames) (final : Nat)
    (safe : MacroCounterSafeBindingInputs macros bindings)
    (accepted : copyBindingsWithMacros macros fuel origin holes outside names fresh bindings =
      some (outputs, finalNames, final)) :
    bindingTokens outputs = counterTokens fresh bindings.length :=
  copyBindingsWithMacros_preserving_token_sequence macros fuel origin holes outside names fresh
    bindings outputs finalNames final (macroCounterSafeBindingInputs_preserving macros bindings safe)
    accepted

theorem copyBindingsWithMacros_macro_safe_tokens_unique (macros : List String)
    (fuel origin : Nat) (holes : Holes) (outside names : Renames) (fresh : Nat)
    (bindings outputs : List Tree) (finalNames : Renames) (final : Nat)
    (safe : MacroCounterSafeBindingInputs macros bindings)
    (accepted : copyBindingsWithMacros macros fuel origin holes outside names fresh bindings =
      some (outputs, finalNames, final)) : Unique (bindingTokens outputs) :=
  copyBindingsWithMacros_preserving_tokens_unique macros fuel origin holes outside names fresh
    bindings outputs finalNames final (macroCounterSafeBindingInputs_preserving macros bindings safe)
    accepted

theorem copyBindingsWithMacros_macro_safe_tokens_avoid_source (macros : List String)
    (fuel origin : Nat) (holes : Holes) (outside names : Renames) (fresh : Nat)
    (bindings outputs : List Tree) (finalNames : Renames) (final sourceToken : Nat)
    (safe : MacroCounterSafeBindingInputs macros bindings)
    (accepted : copyBindingsWithMacros macros fuel origin holes outside names fresh bindings =
      some (outputs, finalNames, final)) (sourceClass : sourceToken % 3 = 1) :
    sourceToken ∉ bindingTokens outputs :=
  copyBindingsWithMacros_preserving_tokens_avoid_source macros fuel origin holes outside names fresh
    bindings outputs finalNames final sourceToken
    (macroCounterSafeBindingInputs_preserving macros bindings safe) accepted sourceClass

theorem copyBindingsWithMacros_macro_safe_tokens_within_interval (macros : List String)
    (fuel origin : Nat) (holes : Holes) (outside names : Renames) (fresh : Nat)
    (bindings outputs : List Tree) (finalNames : Renames) (final : Nat)
    (safe : MacroCounterSafeBindingInputs macros bindings)
    (accepted : copyBindingsWithMacros macros fuel origin holes outside names fresh bindings =
      some (outputs, finalNames, final)) (token : Nat) (member : token ∈ bindingTokens outputs) :
    ∃ counter, fresh < counter ∧ counter ≤ final ∧ token = 3 * counter + 2 :=
  copyBindingsWithMacros_preserving_tokens_within_interval macros fuel origin holes outside names
    fresh bindings outputs finalNames final (macroCounterSafeBindingInputs_preserving macros bindings safe)
    accepted token member

theorem copyBindingsWithMacros_atoms_tokens_avoid_source (macros : List String)
    (fuel origin : Nat) (holes : Holes) (outside names : Renames) (fresh : Nat)
    (bindings outputs : List Tree) (finalNames : Renames) (final sourceToken : Nat)
    (atomic : AtomBindingInputs bindings)
    (accepted : copyBindingsWithMacros macros fuel origin holes outside names fresh bindings =
      some (outputs, finalNames, final)) (sourceClass : sourceToken % 3 = 1) :
    sourceToken ∉ bindingTokens outputs := by
  rw [copyBindingsWithMacros_atoms_token_sequence macros fuel origin holes outside names fresh
    bindings outputs finalNames final atomic accepted]
  intro member
  have generatedClass := counterTokens_reserved_class fresh bindings.length sourceToken member
  omega

theorem copyBindingsWithMacros_atoms_tokens_within_interval (macros : List String)
    (fuel origin : Nat) (holes : Holes) (outside names : Renames) (fresh : Nat)
    (bindings outputs : List Tree) (finalNames : Renames) (final : Nat)
    (atomic : AtomBindingInputs bindings)
    (accepted : copyBindingsWithMacros macros fuel origin holes outside names fresh bindings =
      some (outputs, finalNames, final)) (token : Nat) (member : token ∈ bindingTokens outputs) :
    ∃ counter, fresh < counter ∧ counter ≤ final ∧ token = 3 * counter + 2 := by
  have sequence := copyBindingsWithMacros_atoms_token_sequence macros fuel origin holes outside
    names fresh bindings outputs finalNames final atomic accepted
  rw [sequence] at member
  obtain ⟨counter, lower, upper, tokenEq⟩ :=
    counterTokens_within_interval fresh bindings.length token member
  have finalEq := copyBindingsWithMacros_atoms_counter macros fuel origin holes outside names
    fresh bindings outputs finalNames final atomic accepted
  exact ⟨counter, lower, by omega, tokenEq⟩

theorem copyBindings_atomic_tokens_unique (fuel origin : Nat) (holes : Holes)
    (outside names : Renames) (fresh : Nat) (bindings outputs : List Tree)
    (finalNames : Renames) (final : Nat) (atomic : AtomicBindingInputs bindings)
    (accepted : copyBindings fuel origin holes outside names fresh bindings =
      some (outputs, finalNames, final)) : Unique (bindingTokens outputs) := by
  rw [copyBindings_atomic_token_sequence fuel origin holes outside names fresh bindings
    outputs finalNames final atomic accepted]
  exact counterTokens_distinct fresh bindings.length

theorem copyBindings_atomic_tokens_avoid_source (fuel origin : Nat) (holes : Holes)
    (outside names : Renames) (fresh : Nat) (bindings outputs : List Tree)
    (finalNames : Renames) (final sourceToken : Nat) (atomic : AtomicBindingInputs bindings)
    (accepted : copyBindings fuel origin holes outside names fresh bindings =
      some (outputs, finalNames, final)) (sourceClass : sourceToken % 3 = 1) :
    sourceToken ∉ bindingTokens outputs := by
  rw [copyBindings_atomic_token_sequence fuel origin holes outside names fresh bindings
    outputs finalNames final atomic accepted]
  intro member
  have generatedClass := counterTokens_reserved_class fresh bindings.length sourceToken member
  omega

theorem copyBindings_atomic_tokens_within_interval (fuel origin : Nat) (holes : Holes)
    (outside names : Renames) (fresh : Nat) (bindings outputs : List Tree)
    (finalNames : Renames) (final : Nat) (atomic : AtomicBindingInputs bindings)
    (accepted : copyBindings fuel origin holes outside names fresh bindings =
      some (outputs, finalNames, final)) (token : Nat)
    (member : token ∈ bindingTokens outputs) :
    ∃ counter, fresh < counter ∧ counter ≤ final ∧ token = 3 * counter + 2 := by
  have sequence := copyBindings_atomic_token_sequence fuel origin holes outside names fresh
    bindings outputs finalNames final atomic accepted
  rw [sequence] at member
  obtain ⟨counter, lower, upper, tokenEq⟩ :=
    counterTokens_within_interval fresh bindings.length token member
  have finalEq := copyBindings_atomic_counter fuel origin holes outside names fresh
    bindings outputs finalNames final atomic accepted
  exact ⟨counter, lower, by omega, tokenEq⟩

theorem copyParameters_token_sequence (fuel : Nat) (holes : Holes) (renames : Renames)
    (fresh : Nat) (parameters : List Tree) (copied : List Tree)
    (finalRenames : Renames) (final : Nat)
    (accepted : copyParameters fuel holes renames fresh parameters =
      some (copied, finalRenames, final)) :
    parameterTokens copied = counterTokens fresh parameters.length := by
  induction fuel generalizing holes renames fresh parameters copied finalRenames final with
  | zero => simp [copyParameters, operations] at accepted
  | succ fuel ih =>
      cases parameters with
      | nil =>
          simp only [copyParameters, operations] at accepted
          have tupleEq := Option.some.inj accepted
          have copiedEmpty : copied = [] := by
            simpa using (congrArg Prod.fst tupleEq).symm
          subst copied
          rfl
      | cons parameter tail =>
          cases parameter with
          | atom atom => simp [copyParameters, operations] at accepted
          | list fields =>
              cases fields with
              | nil => simp [copyParameters, operations] at accepted
              | cons name rest =>
                  cases rest with
                  | nil => simp [copyParameters, operations] at accepted
                  | cons type rest =>
                      cases rest with
                      | cons extra _ => simp [copyParameters, operations] at accepted
                      | nil =>
                          simp only [copyParameters, operations] at accepted
                          generalize binderResult : binder holes renames fresh name = binderOption at accepted
                          cases binderOption with
                          | none => simp [binderResult] at accepted
                          | some result =>
                              rcases result with ⟨nameCopy, names, next⟩
                              generalize tailResult : (operations [] fuel).copyParameters
                                  holes names next tail = tailOption at accepted
                              cases tailOption with
                              | none => simp [binderResult, tailResult] at accepted
                              | some tailCopy =>
                                  rcases tailCopy with ⟨outputs, endNames, endCounter⟩
                                  have acceptedCopy := accepted
                                  simp [binderResult, tailResult] at acceptedCopy
                                  have copiedShape : copied = .list [nameCopy, type] :: outputs :=
                                    acceptedCopy.1.symm
                                  have binderFacts := binder_success_counter holes renames fresh name
                                    nameCopy names next (by simp [binderResult])
                                  rcases binderFacts with ⟨freshAtom, atomShape, counterStep, tokenStep⟩
                                  have tailFacts := ih holes names next tail outputs endNames endCounter
                                    (by simpa [copyParameters] using tailResult)
                                  subst copied
                                  simp [parameterTokens, atomShape, tokenStep, counterTokens,
                                    counterStep, tailFacts]

theorem copyParameters_tokens_unique (fuel : Nat) (holes : Holes) (renames : Renames)
    (fresh : Nat) (parameters : List Tree) (copied : List Tree)
    (finalRenames : Renames) (final : Nat)
    (accepted : copyParameters fuel holes renames fresh parameters =
      some (copied, finalRenames, final)) :
    Unique (parameterTokens copied) := by
  rw [copyParameters_token_sequence fuel holes renames fresh parameters copied
    finalRenames final accepted]
  exact counterTokens_distinct fresh parameters.length

theorem copyParameters_tokens_avoid_source (fuel : Nat) (holes : Holes) (renames : Renames)
    (fresh : Nat) (parameters : List Tree) (copied : List Tree)
    (finalRenames : Renames) (final sourceToken : Nat)
    (accepted : copyParameters fuel holes renames fresh parameters =
      some (copied, finalRenames, final)) (sourceClass : sourceToken % 3 = 1) :
    sourceToken ∉ parameterTokens copied := by
  rw [copyParameters_token_sequence fuel holes renames fresh parameters copied
    finalRenames final accepted]
  intro member
  have generatedClass := counterTokens_reserved_class fresh parameters.length sourceToken member
  omega

theorem copyParameters_tokens_within_interval (fuel : Nat) (holes : Holes) (renames : Renames)
    (fresh : Nat) (parameters : List Tree) (copied : List Tree)
    (finalRenames : Renames) (final : Nat)
    (accepted : copyParameters fuel holes renames fresh parameters =
      some (copied, finalRenames, final)) (token : Nat)
    (member : token ∈ parameterTokens copied) :
    ∃ counter, fresh < counter ∧ counter ≤ final ∧ token = 3 * counter + 2 := by
  have sequence := copyParameters_token_sequence fuel holes renames fresh parameters
    copied finalRenames final accepted
  rw [sequence] at member
  obtain ⟨counter, lower, upper, tokenEq⟩ :=
    counterTokens_within_interval fresh parameters.length token member
  have finalEq := copyParameters_counter fuel holes renames fresh parameters
    copied finalRenames final accepted
  exact ⟨counter, lower, by omega, tokenEq⟩

def patternTokens : List Tree → List Nat
  | [] => []
  | .atom atom :: tail => atom.token :: patternTokens tail
  | _ => []

def counterPreservingCaseTokens : List Tree → List Nat
  | [] => []
  | .list [.list [], _] :: tail => counterPreservingCaseTokens tail
  | .list [.list (_ :: parameters), _] :: tail =>
      patternTokens parameters ++ counterPreservingCaseTokens tail
  | _ => []

theorem copyPattern_token_sequence (fuel : Nat) (holes : Holes) (renames : Renames)
    (fresh : Nat) (pattern : List Tree) (copied : List Tree)
    (finalRenames : Renames) (final : Nat)
    (accepted : copyPattern fuel holes renames fresh pattern =
      some (copied, finalRenames, final)) :
    patternTokens copied = counterTokens fresh pattern.length := by
  induction fuel generalizing holes renames fresh pattern copied finalRenames final with
  | zero => simp [copyPattern, operations] at accepted
  | succ fuel ih =>
      cases pattern with
      | nil =>
          simp only [copyPattern, operations] at accepted
          have tupleEq := Option.some.inj accepted
          have copiedEmpty : copied = [] := by
            simpa using (congrArg Prod.fst tupleEq).symm
          subst copied
          rfl
      | cons name tail =>
          simp only [List.length_cons]
          simp only [copyPattern, operations] at accepted
          generalize binderResult : binder holes renames fresh name = binderOption at accepted
          cases binderOption with
          | none => simp [binderResult] at accepted
          | some result =>
              rcases result with ⟨nameCopy, names, next⟩
              generalize tailResult : (operations [] fuel).copyPattern holes names next tail = tailOption at accepted
              cases tailOption with
              | none => simp [binderResult, tailResult] at accepted
              | some tailCopy =>
                  rcases tailCopy with ⟨outputs, endNames, endCounter⟩
                  have acceptedCopy := accepted
                  simp [binderResult, tailResult] at acceptedCopy
                  have copiedShape : copied = nameCopy :: outputs := acceptedCopy.1.symm
                  have binderFacts := binder_success_counter holes renames fresh name
                    nameCopy names next (by simp [binderResult])
                  rcases binderFacts with ⟨freshAtom, atomShape, counterStep, tokenStep⟩
                  have tailFacts := ih holes names next tail outputs endNames endCounter
                    (by simpa [copyPattern] using tailResult)
                  subst copied
                  simp [patternTokens, atomShape, tokenStep, counterTokens, counterStep, tailFacts]

theorem copyPattern_counter (fuel : Nat) (holes : Holes) (renames : Renames)
    (fresh : Nat) (pattern copied : List Tree)
    (finalRenames : Renames) (final : Nat)
    (accepted : copyPattern fuel holes renames fresh pattern =
      some (copied, finalRenames, final)) :
    final = fresh + pattern.length := by
  induction fuel generalizing holes renames fresh pattern copied finalRenames final with
  | zero => simp [copyPattern, operations] at accepted
  | succ fuel ih =>
      cases pattern with
      | nil =>
          simp only [copyPattern, operations] at accepted
          have tupleEq := Option.some.inj accepted
          have finalEq := congrArg (fun result : List Tree × Renames × Nat => result.2.2) tupleEq
          simpa using finalEq.symm
      | cons name tail =>
          simp only [List.length_cons]
          simp only [copyPattern, operations] at accepted
          generalize binderResult : binder holes renames fresh name = binderOption at accepted
          cases binderOption with
          | none => simp [binderResult] at accepted
          | some result =>
              rcases result with ⟨nameCopy, names, next⟩
              generalize tailResult : (operations [] fuel).copyPattern holes names next tail = tailOption at accepted
              cases tailOption with
              | none => simp [binderResult, tailResult] at accepted
              | some tailCopy =>
                  rcases tailCopy with ⟨outputs, endNames, endCounter⟩
                  simp [binderResult, tailResult] at accepted
                  have binderFacts := binder_success_counter holes renames fresh name
                    nameCopy names next (by simp [binderResult])
                  rcases binderFacts with ⟨freshAtom, _atomShape, counterStep, _tokenStep⟩
                  have tailFacts := ih holes names next tail outputs endNames endCounter
                    (by simpa [copyPattern] using tailResult)
                  omega

theorem copyPatternWithMacros_counter (macros : List String) (fuel : Nat) (holes : Holes)
    (renames : Renames) (fresh : Nat) (pattern copied : List Tree)
    (finalRenames : Renames) (final : Nat)
    (accepted : copyPatternWithMacros macros fuel holes renames fresh pattern =
      some (copied, finalRenames, final)) : final = fresh + pattern.length := by
  induction fuel generalizing holes renames fresh pattern copied finalRenames final with
  | zero => simp [copyPatternWithMacros, operations] at accepted
  | succ fuel ih =>
      cases pattern with
      | nil =>
          simp only [copyPatternWithMacros, operations] at accepted
          have tupleEq := Option.some.inj accepted
          have finalEq := congrArg (fun result : List Tree × Renames × Nat => result.2.2) tupleEq
          simpa using finalEq.symm
      | cons name tail =>
          simp only [List.length_cons]
          simp only [copyPatternWithMacros, operations] at accepted
          generalize binderResult : binder holes renames fresh name = binderOption at accepted
          cases binderOption with
          | none => simp [binderResult] at accepted
          | some result =>
              rcases result with ⟨nameCopy, names, next⟩
              generalize tailResult : (operations macros fuel).copyPattern holes names next tail =
                tailOption at accepted
              cases tailOption with
              | none => simp [binderResult, tailResult] at accepted
              | some tailCopy =>
                  rcases tailCopy with ⟨outputs, endNames, endCounter⟩
                  simp [binderResult, tailResult] at accepted
                  have binderFacts := binder_success_counter holes renames fresh name
                    nameCopy names next (by simp [binderResult])
                  rcases binderFacts with ⟨freshAtom, _atomShape, counterStep, _tokenStep⟩
                  have tailFacts := ih holes names next tail outputs endNames endCounter
                    (by simpa [copyPatternWithMacros] using tailResult)
                  omega

theorem copyPatternWithMacros_token_sequence (macros : List String) (fuel : Nat)
    (holes : Holes) (renames : Renames) (fresh : Nat) (pattern copied : List Tree)
    (finalRenames : Renames) (final : Nat)
    (accepted : copyPatternWithMacros macros fuel holes renames fresh pattern =
      some (copied, finalRenames, final)) :
    patternTokens copied = counterTokens fresh pattern.length := by
  induction fuel generalizing holes renames fresh pattern copied finalRenames final with
  | zero => simp [copyPatternWithMacros, operations] at accepted
  | succ fuel ih =>
      cases pattern with
      | nil =>
          simp only [copyPatternWithMacros, operations] at accepted
          have tupleEq := Option.some.inj accepted
          have copiedEmpty : copied = [] := by
            simpa using (congrArg Prod.fst tupleEq).symm
          subst copied
          rfl
      | cons name tail =>
          simp only [List.length_cons]
          simp only [copyPatternWithMacros, operations] at accepted
          generalize binderResult : binder holes renames fresh name = binderOption at accepted
          cases binderOption with
          | none => simp [binderResult] at accepted
          | some result =>
              rcases result with ⟨nameCopy, names, next⟩
              generalize tailResult : (operations macros fuel).copyPattern holes names next tail =
                tailOption at accepted
              cases tailOption with
              | none => simp [binderResult, tailResult] at accepted
              | some tailCopy =>
                  rcases tailCopy with ⟨outputs, endNames, endCounter⟩
                  have acceptedCopy := accepted
                  simp [binderResult, tailResult] at acceptedCopy
                  have copiedShape : copied = nameCopy :: outputs := acceptedCopy.1.symm
                  have binderFacts := binder_success_counter holes renames fresh name
                    nameCopy names next (by simp [binderResult])
                  rcases binderFacts with ⟨freshAtom, atomShape, counterStep, tokenStep⟩
                  have tailFacts := ih holes names next tail outputs endNames endCounter
                    (by simpa [copyPatternWithMacros] using tailResult)
                  subst copied
                  simp [patternTokens, atomShape, tokenStep, counterTokens, counterStep, tailFacts]

theorem copyCasesWithMacros_preserving_counter (macros : List String) (fuel origin : Nat)
    (holes : Holes) (names : Renames) (fresh : Nat) (cases outputs : List Tree)
    (final : Nat) (safe : CounterPreservingCases macros cases)
    (accepted : copyCasesWithMacros macros fuel origin holes names fresh cases =
      some (outputs, final)) : final = fresh + counterPreservingCaseCount cases := by
  induction safe generalizing fuel origin holes names fresh outputs final with
  | nil =>
      cases fuel with
      | zero => simp [copyCasesWithMacros, operations] at accepted
      | succ fuel =>
          simp only [copyCasesWithMacros, operations] at accepted
          have tupleEq := Option.some.inj accepted
          have finalEq := congrArg (fun result : List Tree × Nat => result.2) tupleEq
          simpa [counterPreservingCaseCount] using finalEq.symm
  | @emptyPattern body bodySafe tail _tailSafe ih =>
      cases fuel with
      | zero => simp [copyCasesWithMacros, operations] at accepted
      | succ fuel =>
          simp only [copyCasesWithMacros, operations] at accepted
          generalize bodyResult : (operations macros fuel).copy origin holes names fresh body =
            bodyOption at accepted
          cases bodyOption with
          | none => simp [bodyResult] at accepted
          | some bodyOutput =>
              rcases bodyOutput with ⟨bodyCopy, afterBody⟩
              generalize tailResult : (operations macros fuel).copyCases origin holes names
                afterBody tail = tailOption at accepted
              cases tailOption with
              | none => simp [bodyResult, tailResult] at accepted
              | some tailOutput =>
                  rcases tailOutput with ⟨tailCopies, endCounter⟩
                  have acceptedParts := accepted
                  simp [bodyResult, tailResult] at acceptedParts
                  have finalEq : endCounter = final := acceptedParts.2
                  have bodyCounter := bodySafe fuel origin holes names fresh bodyCopy afterBody bodyResult
                  have tailCounter := ih fuel origin holes names afterBody tailCopies endCounter
                    (by
                      change (operations macros fuel).copyCases origin holes names afterBody tail =
                        some (tailCopies, endCounter)
                      exact tailResult)
                  rw [← finalEq, tailCounter, bodyCounter]
                  simp [counterPreservingCaseCount]
  | @boundPattern constructor parameters body bodySafe tail _tailSafe ih =>
      cases fuel with
      | zero => simp [copyCasesWithMacros, operations] at accepted
      | succ fuel =>
          simp only [copyCasesWithMacros, operations] at accepted
          generalize namesResult : patternNames parameters = namesOption at accepted
          cases namesOption with
          | none => simp [namesResult] at accepted
          | some originals =>
              generalize distinctResult : Lexical.distinctNames originals = distinct at accepted
              cases distinct <;> simp [namesResult, distinctResult] at accepted
              generalize patternResult : (operations macros fuel).copyPattern holes names fresh
                parameters = patternOption at accepted
              cases patternOption with
              | none => simp [namesResult, distinctResult, patternResult] at accepted
              | some patternOutput =>
                  rcases patternOutput with ⟨parameterCopies, localNames, afterPattern⟩
                  generalize bodyResult : (operations macros fuel).copy origin holes localNames
                    afterPattern body = bodyOption at accepted
                  cases bodyOption with
                  | none => simp [namesResult, distinctResult, patternResult, bodyResult] at accepted
                  | some bodyOutput =>
                      rcases bodyOutput with ⟨bodyCopy, afterBody⟩
                      generalize tailResult : (operations macros fuel).copyCases origin holes names
                        afterBody tail = tailOption at accepted
                      cases tailOption with
                      | none => simp [namesResult, distinctResult, patternResult, bodyResult,
                          tailResult] at accepted
                      | some tailOutput =>
                          rcases tailOutput with ⟨tailCopies, endCounter⟩
                          have acceptedParts := accepted
                          simp [namesResult, distinctResult, patternResult, bodyResult, tailResult]
                            at acceptedParts
                          have finalEq : endCounter = final := acceptedParts.2
                          have patternCounter := copyPatternWithMacros_counter macros fuel holes names
                            fresh parameters parameterCopies localNames afterPattern (by
                              change (operations macros fuel).copyPattern holes names fresh parameters =
                                some (parameterCopies, localNames, afterPattern)
                              exact patternResult)
                          have bodyCounter := bodySafe fuel origin holes localNames afterPattern
                            bodyCopy afterBody bodyResult
                          have tailCounter := ih fuel origin holes names afterBody tailCopies
                            endCounter (by
                              change (operations macros fuel).copyCases origin holes names afterBody tail =
                                some (tailCopies, endCounter)
                              exact tailResult)
                          rw [← finalEq, tailCounter, bodyCounter, patternCounter]
                          simp [counterPreservingCaseCount]
                          omega

theorem copyCasesWithMacros_preserving_token_sequence (macros : List String)
    (fuel origin : Nat) (holes : Holes) (names : Renames) (fresh : Nat)
    (cases outputs : List Tree) (final : Nat) (safe : CounterPreservingCases macros cases)
    (accepted : copyCasesWithMacros macros fuel origin holes names fresh cases =
      some (outputs, final)) :
    counterPreservingCaseTokens outputs =
      counterTokens fresh (counterPreservingCaseCount cases) := by
  induction safe generalizing fuel origin holes names fresh outputs final with
  | nil =>
      cases fuel with
      | zero => simp [copyCasesWithMacros, operations] at accepted
      | succ fuel =>
          simp only [copyCasesWithMacros, operations] at accepted
          have tupleEq := Option.some.inj accepted
          have copiedEmpty : outputs = [] := by
            simpa using (congrArg Prod.fst tupleEq).symm
          subst outputs
          rfl
  | @emptyPattern body bodySafe tail _tailSafe ih =>
      cases fuel with
      | zero => simp [copyCasesWithMacros, operations] at accepted
      | succ fuel =>
          simp only [copyCasesWithMacros, operations] at accepted
          generalize bodyResult : (operations macros fuel).copy origin holes names fresh body =
            bodyOption at accepted
          cases bodyOption with
          | none => simp [bodyResult] at accepted
          | some bodyOutput =>
              rcases bodyOutput with ⟨bodyCopy, afterBody⟩
              generalize tailResult : (operations macros fuel).copyCases origin holes names
                afterBody tail = tailOption at accepted
              cases tailOption with
              | none => simp [bodyResult, tailResult] at accepted
              | some tailOutput =>
                  rcases tailOutput with ⟨tailCopies, endCounter⟩
                  have acceptedParts := accepted
                  simp [bodyResult, tailResult] at acceptedParts
                  have copiedShape : outputs =
                    .list [.list [], bodyCopy] :: tailCopies := acceptedParts.1.symm
                  have bodyCounter := bodySafe fuel origin holes names fresh bodyCopy afterBody bodyResult
                  have tailSequence := ih fuel origin holes names afterBody tailCopies endCounter
                    (by
                      change (operations macros fuel).copyCases origin holes names afterBody tail =
                        some (tailCopies, endCounter)
                      exact tailResult)
                  subst outputs
                  simp [counterPreservingCaseTokens, counterPreservingCaseCount, bodyCounter,
                    tailSequence]
  | @boundPattern constructor parameters body bodySafe tail _tailSafe ih =>
      cases fuel with
      | zero => simp [copyCasesWithMacros, operations] at accepted
      | succ fuel =>
          simp only [copyCasesWithMacros, operations] at accepted
          generalize namesResult : patternNames parameters = namesOption at accepted
          cases namesOption with
          | none => simp [namesResult] at accepted
          | some originals =>
              generalize distinctResult : Lexical.distinctNames originals = distinct at accepted
              cases distinct <;> simp [namesResult, distinctResult] at accepted
              generalize patternResult : (operations macros fuel).copyPattern holes names fresh
                parameters = patternOption at accepted
              cases patternOption with
              | none => simp [namesResult, distinctResult, patternResult] at accepted
              | some patternOutput =>
                  rcases patternOutput with ⟨parameterCopies, localNames, afterPattern⟩
                  generalize bodyResult : (operations macros fuel).copy origin holes localNames
                    afterPattern body = bodyOption at accepted
                  cases bodyOption with
                  | none => simp [namesResult, distinctResult, patternResult, bodyResult] at accepted
                  | some bodyOutput =>
                      rcases bodyOutput with ⟨bodyCopy, afterBody⟩
                      generalize tailResult : (operations macros fuel).copyCases origin holes names
                        afterBody tail = tailOption at accepted
                      cases tailOption with
                      | none => simp [namesResult, distinctResult, patternResult, bodyResult,
                          tailResult] at accepted
                      | some tailOutput =>
                          rcases tailOutput with ⟨tailCopies, endCounter⟩
                          have acceptedParts := accepted
                          simp [namesResult, distinctResult, patternResult, bodyResult, tailResult]
                            at acceptedParts
                          have copiedShape : outputs = .list
                            [.list (constructor :: parameterCopies), bodyCopy] :: tailCopies :=
                            acceptedParts.1.symm
                          have patternSequence := copyPatternWithMacros_token_sequence macros fuel
                            holes names fresh parameters parameterCopies localNames afterPattern (by
                              change (operations macros fuel).copyPattern holes names fresh parameters =
                                some (parameterCopies, localNames, afterPattern)
                              exact patternResult)
                          have patternCounter := copyPatternWithMacros_counter macros fuel holes names
                            fresh parameters parameterCopies localNames afterPattern (by
                              change (operations macros fuel).copyPattern holes names fresh parameters =
                                some (parameterCopies, localNames, afterPattern)
                              exact patternResult)
                          have bodyCounter := bodySafe fuel origin holes localNames afterPattern
                            bodyCopy afterBody bodyResult
                          have tailSequence := ih fuel origin holes names afterBody tailCopies
                            endCounter (by
                              change (operations macros fuel).copyCases origin holes names afterBody tail =
                                some (tailCopies, endCounter)
                              exact tailResult)
                          subst outputs
                          simp only [counterPreservingCaseTokens, patternSequence, tailSequence,
                            counterPreservingCaseCount]
                          rw [bodyCounter, patternCounter]
                          rw [← counterTokens_add]

theorem copyCasesWithMacros_preserving_tokens_unique (macros : List String)
    (fuel origin : Nat) (holes : Holes) (names : Renames) (fresh : Nat)
    (cases outputs : List Tree) (final : Nat) (safe : CounterPreservingCases macros cases)
    (accepted : copyCasesWithMacros macros fuel origin holes names fresh cases =
      some (outputs, final)) : Unique (counterPreservingCaseTokens outputs) := by
  rw [copyCasesWithMacros_preserving_token_sequence macros fuel origin holes names fresh cases
    outputs final safe accepted]
  exact counterTokens_distinct fresh (counterPreservingCaseCount cases)

theorem copyCasesWithMacros_preserving_tokens_avoid_source (macros : List String)
    (fuel origin : Nat) (holes : Holes) (names : Renames) (fresh sourceToken : Nat)
    (cases outputs : List Tree) (final : Nat) (safe : CounterPreservingCases macros cases)
    (accepted : copyCasesWithMacros macros fuel origin holes names fresh cases =
      some (outputs, final)) (sourceClass : sourceToken % 3 = 1) :
    sourceToken ∉ counterPreservingCaseTokens outputs := by
  rw [copyCasesWithMacros_preserving_token_sequence macros fuel origin holes names fresh cases
    outputs final safe accepted]
  intro member
  have generatedClass := counterTokens_reserved_class fresh (counterPreservingCaseCount cases)
    sourceToken member
  omega

theorem copyCasesWithMacros_preserving_tokens_within_interval (macros : List String)
    (fuel origin : Nat) (holes : Holes) (names : Renames) (fresh : Nat)
    (cases outputs : List Tree) (final : Nat) (safe : CounterPreservingCases macros cases)
    (accepted : copyCasesWithMacros macros fuel origin holes names fresh cases =
      some (outputs, final)) (token : Nat) (member : token ∈ counterPreservingCaseTokens outputs) :
    ∃ counter, fresh < counter ∧ counter ≤ final ∧ token = 3 * counter + 2 := by
  rw [copyCasesWithMacros_preserving_token_sequence macros fuel origin holes names fresh cases
    outputs final safe accepted] at member
  obtain ⟨counter, lower, upper, tokenEq⟩ :=
    counterTokens_within_interval fresh (counterPreservingCaseCount cases) token member
  have finalEq := copyCasesWithMacros_preserving_counter macros fuel origin holes names fresh
    cases outputs final safe accepted
  exact ⟨counter, lower, by rw [finalEq]; exact upper, tokenEq⟩

theorem copyPattern_tokens_unique (fuel : Nat) (holes : Holes) (renames : Renames)
    (fresh : Nat) (pattern : List Tree) (copied : List Tree)
    (finalRenames : Renames) (final : Nat)
    (accepted : copyPattern fuel holes renames fresh pattern =
      some (copied, finalRenames, final)) :
    Unique (patternTokens copied) := by
  rw [copyPattern_token_sequence fuel holes renames fresh pattern copied
    finalRenames final accepted]
  exact counterTokens_distinct fresh pattern.length

theorem copyPattern_tokens_avoid_source (fuel : Nat) (holes : Holes) (renames : Renames)
    (fresh : Nat) (pattern : List Tree) (copied : List Tree)
    (finalRenames : Renames) (final sourceToken : Nat)
    (accepted : copyPattern fuel holes renames fresh pattern =
      some (copied, finalRenames, final)) (sourceClass : sourceToken % 3 = 1) :
    sourceToken ∉ patternTokens copied := by
  rw [copyPattern_token_sequence fuel holes renames fresh pattern copied
    finalRenames final accepted]
  intro member
  have generatedClass := counterTokens_reserved_class fresh pattern.length sourceToken member
  omega

theorem copyPattern_tokens_within_interval (fuel : Nat) (holes : Holes) (renames : Renames)
    (fresh : Nat) (pattern copied : List Tree) (finalRenames : Renames) (final : Nat)
    (accepted : copyPattern fuel holes renames fresh pattern =
      some (copied, finalRenames, final)) (token : Nat)
    (member : token ∈ patternTokens copied) :
    ∃ counter, fresh < counter ∧ counter ≤ final ∧ token = 3 * counter + 2 := by
  have sequence := copyPattern_token_sequence fuel holes renames fresh pattern
    copied finalRenames final accepted
  rw [sequence] at member
  obtain ⟨counter, lower, upper, tokenEq⟩ :=
    counterTokens_within_interval fresh pattern.length token member
  have finalEq := copyPattern_counter fuel holes renames fresh pattern copied finalRenames final accepted
  exact ⟨counter, lower, by omega, tokenEq⟩

theorem parameter_then_pattern_tokens_unique (fuel : Nat) (holes : Holes)
    (renames : Renames) (fresh : Nat)
    (parameters parameterCopies : List Tree) (middleRenames : Renames) (middle : Nat)
    (pattern patternCopies : List Tree) (finalRenames : Renames) (final : Nat)
    (parameterCopy : copyParameters fuel holes renames fresh parameters =
      some (parameterCopies, middleRenames, middle))
    (patternCopy : copyPattern fuel holes middleRenames middle pattern =
      some (patternCopies, finalRenames, final)) :
    Unique (parameterTokens parameterCopies ++ patternTokens patternCopies) := by
  have middleCounter := copyParameters_counter fuel holes renames fresh parameters
    parameterCopies middleRenames middle parameterCopy
  have firstSequence := copyParameters_token_sequence fuel holes renames fresh parameters
    parameterCopies middleRenames middle parameterCopy
  have secondSequence := copyPattern_token_sequence fuel holes middleRenames middle pattern
    patternCopies finalRenames final patternCopy
  rw [firstSequence, secondSequence, middleCounter, ← counterTokens_add]
  exact counterTokens_distinct fresh (parameters.length + pattern.length)

/-- Compose the binder token guarantees across parameter, let-binding,
pattern, and match-case copy phases. Each phase starts at the previous phase's
final counter, so the complete generated binder sequence occupies one
contiguous interval and is pairwise distinct. -/
theorem macro_head_retains_namespace (macros : List String) (head replacement : Atom)
    (known : macros.contains head.name = true) :
    copyWithMacros macros 3 origin [] [(head.name, replacement)] fresh (.list [.atom head]) =
      some (.list [.atom {head with origin := some origin}], fresh) := by
  simp [copyWithMacros, operations, lookup, known]

/-- A zero-argument macro call that is written literally in a template keeps
its macro head when the template is copied, provided no hole substitutes that
head. This is the smallest call-site preservation fact needed to connect a
template call to a call in the copied output. -/
theorem copyWithMacros_preserves_zero_arg_macro_call (macros : List String)
    (origin fresh : Nat) (holes : Holes) (head : Atom)
    (known : macros.contains head.name = true)
    (notHole : (lookup head.name holes).isNone = true) :
    copyWithMacros macros 2 origin holes [] fresh (.list [.atom head]) =
      some (.list [.atom {head with origin := some origin}], fresh) := by
  simp [copyWithMacros, operations, lookup, known, notHole]

theorem copyManyWithMacros_preserves_length (macros : List String) (fuel origin : Nat)
    (holes : Holes) (renames : Renames) (fresh : Nat) (trees copied : List Tree)
    (final : Nat)
    (accepted : copyManyWithMacros macros fuel origin holes renames fresh trees =
      some (copied, final)) :
    copied.length = trees.length := by
  induction fuel generalizing trees copied final fresh with
  | zero => simp [copyManyWithMacros, operations] at accepted
  | succ fuel ih =>
      cases trees with
      | nil =>
          simp [copyManyWithMacros, operations] at accepted
          rcases accepted with ⟨rfl, rfl⟩
          simp
      | cons head tail =>
          simp only [copyManyWithMacros, operations] at accepted
          generalize headResult : (operations macros fuel).copy origin holes renames fresh head =
            headOption at accepted
          cases headOption with
          | none => simp [headResult] at accepted
          | some headPair =>
              rcases headPair with ⟨headCopy, next⟩
              generalize tailResult : (operations macros fuel).copyMany origin holes renames
                next tail = tailOption at accepted
              cases tailOption with
              | none => simp [headResult, tailResult] at accepted
              | some tailPair =>
                  rcases tailPair with ⟨tailCopies, last⟩
                  simp [headResult, tailResult] at accepted
                  rcases accepted with ⟨copiedEq, _⟩
                  have tailLength := ih next tail tailCopies last tailResult
                  rw [← copiedEq]
                  simp [tailLength]

theorem copyCasesWithMacros_preserves_length (macros : List String) (fuel origin : Nat)
    (holes : Holes) (renames : Renames) (fresh : Nat) (cases copied : List Tree)
    (final : Nat)
    (accepted : copyCasesWithMacros macros fuel origin holes renames fresh cases =
      some (copied, final)) :
    copied.length = cases.length := by
  induction fuel generalizing cases copied final fresh with
  | zero => simp [copyCasesWithMacros, operations] at accepted
  | succ fuel ih =>
      cases cases with
      | nil =>
          simp [copyCasesWithMacros, operations] at accepted
          rcases accepted with ⟨rfl, rfl⟩
          rfl
      | cons head tail =>
          cases head with
          | atom atom => simp [copyCasesWithMacros, operations] at accepted
          | list row =>
              cases row with
              | nil => simp [copyCasesWithMacros, operations] at accepted
              | cons pattern rest =>
                  cases pattern with
                  | atom atom => simp [copyCasesWithMacros, operations] at accepted
                  | list pattern =>
                      cases rest with
                      | nil => simp [copyCasesWithMacros, operations] at accepted
                      | cons body rest =>
                          cases rest with
                          | cons extra rest => simp [copyCasesWithMacros, operations] at accepted
                          | nil =>
                              simp only [copyCasesWithMacros, operations] at accepted
                              cases pattern with
                              | nil =>
                                  simp only [bind, Option.bind] at accepted
                                  generalize bodyResult : (operations macros fuel).copy origin
                                    holes renames fresh body = bodyOption at accepted
                                  cases bodyOption with
                                  | none => simp [bodyResult] at accepted
                                  | some bodyPair =>
                                      rcases bodyPair with ⟨bodyCopy, next⟩
                                      generalize tailResult : (operations macros fuel).copyCases
                                        origin holes renames next tail = tailOption at accepted
                                      cases tailOption with
                                      | none => simp [bodyResult, tailResult] at accepted
                                      | some tailPair =>
                                          rcases tailPair with ⟨tailCopy, last⟩
                                          simp [bodyResult, tailResult] at accepted
                                          rcases accepted with ⟨outputEq, _⟩
                                          have tailLength := ih next tail tailCopy last tailResult
                                          rw [← outputEq]
                                          simp [tailLength]
                              | cons constructor parameters =>
                                  simp only [bind, Option.bind] at accepted
                                  generalize namesResult : patternNames parameters = namesOption at accepted
                                  cases namesOption with
                                  | none => simp [namesResult] at accepted
                                  | some names =>
                                      simp only [namesResult] at accepted
                                      split at accepted
                                      · simp at accepted
                                      ·
                                        generalize patternResult : (operations macros fuel).copyPattern
                                          holes renames fresh parameters = patternOption at accepted
                                        cases patternOption with
                                        | none => simp [patternResult] at accepted
                                        | some patternPair =>
                                            rcases patternPair with ⟨patternCopy, localNames, afterPattern⟩
                                            generalize bodyResult : (operations macros fuel).copy origin
                                              holes localNames afterPattern body = bodyOption at accepted
                                            cases bodyOption with
                                            | none => simp [patternResult, bodyResult] at accepted
                                            | some bodyPair =>
                                                rcases bodyPair with ⟨bodyCopy, afterBody⟩
                                                generalize tailResult : (operations macros fuel).copyCases
                                                  origin holes renames afterBody tail = tailOption at accepted
                                                cases tailOption with
                                                | none => simp [patternResult, bodyResult, tailResult] at accepted
                                                | some tailPair =>
                                                    rcases tailPair with ⟨tailCopy, last⟩
                                                    simp [patternResult, bodyResult, tailResult] at accepted
                                                    rcases accepted with ⟨outputEq, _⟩
                                                    have tailLength := ih afterBody tail tailCopy last tailResult
                                                    rw [← outputEq]
                                                    simp [tailLength]

theorem copyManyWithMacros_cons_parts (macros : List String) (fuel origin : Nat)
    (holes : Holes) (renames : Renames) (fresh : Nat) (head : Tree) (tail : List Tree)
    (copied : List Tree) (final : Nat)
    (accepted : copyManyWithMacros macros fuel origin holes renames fresh (head :: tail) =
      some (copied, final)) :
    ∃ copiedHead copiedTail middle,
      (operations macros (fuel - 1)).copy origin holes renames fresh head =
        some (copiedHead, middle) ∧
      copyManyWithMacros macros (fuel - 1) origin holes renames middle tail =
        some (copiedTail, final) ∧ copied = copiedHead :: copiedTail := by
  cases fuel with
  | zero => simp [copyManyWithMacros, operations] at accepted
  | succ fuel =>
      simp only [copyManyWithMacros, operations] at accepted
      generalize headResult : (operations macros fuel).copy origin holes renames fresh head =
        headOption at accepted
      cases headOption with
      | none => simp [headResult] at accepted
      | some headPair =>
          rcases headPair with ⟨copiedHead, middle⟩
          generalize tailResult : (operations macros fuel).copyMany origin holes renames
            middle tail = tailOption at accepted
          cases tailOption with
          | none => simp [headResult, tailResult] at accepted
          | some tailPair =>
              rcases tailPair with ⟨copiedTail, final'⟩
              simp [headResult, tailResult] at accepted
              rcases accepted with ⟨copiedEq, finalEq⟩
              subst copied
              subst final'
              refine ⟨copiedHead, copiedTail, middle, headResult, ?_, rfl⟩
              simpa [copyManyWithMacros] using tailResult

/-- Split a successful list copy around an element at any position. The fuel
available to that element decreases once for each preceding sibling. -/
theorem copyManyWithMacros_extract_element (macros : List String)
    (childFuel origin fresh : Nat) (holes : Holes) (renames : Renames)
    (beforeItems : List Tree) (item : Tree) (suffix copied : List Tree) (final : Nat)
    (accepted : copyManyWithMacros macros (childFuel + beforeItems.length + 1) origin
      holes renames fresh (beforeItems ++ item :: suffix) = some (copied, final)) :
    ∃ copiedPrefix copiedItem copiedSuffix before middle,
      (operations macros childFuel).copy origin holes renames before item =
        some (copiedItem, middle) ∧
      copyManyWithMacros macros childFuel origin holes renames middle suffix =
        some (copiedSuffix, final) ∧
      copied = copiedPrefix ++ copiedItem :: copiedSuffix := by
  induction beforeItems generalizing childFuel fresh copied final with
  | nil =>
      have parts := copyManyWithMacros_cons_parts macros (childFuel + 1) origin holes
        renames fresh item suffix copied final (by simpa using accepted)
      obtain ⟨copiedItem, copiedSuffix, middle, itemCopy, suffixCopy, outputEq⟩ := parts
      refine ⟨[], copiedItem, copiedSuffix, fresh, middle, itemCopy, suffixCopy, ?_⟩
      simpa using outputEq
  | cons head beforeItems ih =>
      have accepted' : copyManyWithMacros macros (childFuel + beforeItems.length + 2)
          origin holes renames fresh (head :: (beforeItems ++ item :: suffix)) =
          some (copied, final) := by
        simpa [List.length, Nat.add_assoc] using accepted
      have headAndTail := copyManyWithMacros_cons_parts macros
        (childFuel + beforeItems.length + 2) origin holes renames fresh head
        (beforeItems ++ item :: suffix) copied final accepted'
      obtain ⟨copiedHead, copiedRest, afterHead, _headCopy, restCopy, outputEq⟩ :=
        headAndTail
      have restAccepted : copyManyWithMacros macros
          (childFuel + beforeItems.length + 1) origin holes renames afterHead
          (beforeItems ++ item :: suffix) = some (copiedRest, final) := by
        have fuelDecrease : childFuel + beforeItems.length + 2 - 1 =
            childFuel + beforeItems.length + 1 := by omega
        simpa [fuelDecrease, copyManyWithMacros] using restCopy
      obtain ⟨copiedPrefix, copiedItem, copiedSuffix, before, middle,
        itemCopy, suffixCopy, restShape⟩ :=
        ih (childFuel := childFuel) (fresh := afterHead) (copied := copiedRest)
          (final := final) restAccepted
      refine ⟨copiedHead :: copiedPrefix, copiedItem, copiedSuffix, before, middle,
        itemCopy, suffixCopy, ?_⟩
      rw [outputEq, restShape]
      simp [List.append_assoc]

theorem copyWithMacros_preserves_root_macro_call (macros : List String)
    (fuel origin : Nat) (holes : Holes) (renames : Renames) (fresh final : Nat)
    (head : Atom) (arguments copiedArguments : List Tree)
    (known : macros.contains head.name = true)
    (headNotSubstituted : (lookup head.name holes).isNone = true)
    (argumentsCopied : copyManyWithMacros macros fuel origin holes renames fresh arguments =
      some (copiedArguments, final)) :
    copyWithMacros macros (fuel + 1) origin holes renames fresh
      (.list (.atom head :: arguments)) =
        some (.list (.atom {head with origin := some origin} :: copiedArguments), final) := by
  simp [copyWithMacros, operations, known, headNotSubstituted]
  refine ⟨(copiedArguments, final), ?_, rfl, rfl⟩
  simpa [copyManyWithMacros] using argumentsCopied

theorem copyWithMacros_root_macro_call_parts (macros : List String)
    (fuel origin : Nat) (holes : Holes) (renames : Renames) (fresh final : Nat)
    (head : Atom) (arguments : List Tree) (output : Tree)
    (known : macros.contains head.name = true)
    (headNotSubstituted : (lookup head.name holes).isNone = true)
    (accepted : copyWithMacros macros (fuel + 1) origin holes renames fresh
      (.list (.atom head :: arguments)) = some (output, final)) :
    ∃ copiedArguments,
      copyManyWithMacros macros fuel origin holes renames fresh arguments =
        some (copiedArguments, final) ∧
      output = .list (.atom {head with origin := some origin} :: copiedArguments) := by
  have raw := accepted
  simp [copyWithMacros, operations, known, headNotSubstituted] at raw
  obtain ⟨pair, argumentsAccepted, outputEq, finalEq⟩ := raw
  rcases pair with ⟨copiedArguments, middle⟩
  have middleEq : middle = final := by simpa using finalEq
  have argumentsAccepted' : copyManyWithMacros macros fuel origin holes renames fresh arguments =
      some (copiedArguments, final) := by
    rw [middleEq] at argumentsAccepted
    simpa [copyManyWithMacros] using argumentsAccepted
  have outputEq' : output =
      .list (.atom {head with origin := some origin} :: copiedArguments) := by
    simpa using outputEq.symm
  exact ⟨copiedArguments, argumentsAccepted', outputEq'⟩

theorem copyManyWithMacros_preserves_literal_call_child (macros : List String)
    (fuel origin : Nat) (holes : Holes) (renames : Renames) (fresh final : Nat)
    (head : Atom) (arguments tail copied : List Tree)
    (known : macros.contains head.name = true)
    (headNotSubstituted : (lookup head.name holes).isNone = true)
    (accepted : copyManyWithMacros macros (fuel + 2) origin holes renames fresh
      (.list (.atom head :: arguments) :: tail) = some (copied, final)) :
    ∃ copiedArguments copiedTail middle,
      copyManyWithMacros macros fuel origin holes renames fresh arguments =
        some (copiedArguments, middle) ∧
      copyManyWithMacros macros (fuel + 1) origin holes renames middle tail =
        some (copiedTail, final) ∧
      copied = .list (.atom {head with origin := some origin} :: copiedArguments) :: copiedTail := by
  obtain ⟨copiedCall, copiedTail, middle, callCopy, tailCopy, outputEq⟩ :=
    copyManyWithMacros_cons_parts macros (fuel + 2) origin holes renames fresh
      (.list (.atom head :: arguments)) tail copied final accepted
  have callCopy' : copyWithMacros macros (fuel + 1) origin holes renames fresh
      (.list (.atom head :: arguments)) = some (copiedCall, middle) := by
    change (operations macros (fuel + 1)).copy origin holes renames fresh
      (.list (.atom head :: arguments)) = some (copiedCall, middle)
    exact callCopy
  obtain ⟨copiedArguments, argumentsCopy, callShape⟩ :=
    copyWithMacros_root_macro_call_parts macros fuel origin holes renames fresh middle
      head arguments copiedCall known headNotSubstituted callCopy'
  refine ⟨copiedArguments, copiedTail, middle, argumentsCopy, tailCopy, ?_⟩
  rw [outputEq, callShape]

private theorem option_pair_components {α : Type} {result : Option (List α × Nat)}
    {values : List α} {final : Nat}
    (accepted : ∃ pair, result = some pair ∧ pair.1 = values ∧ pair.2 = final) :
    result = some (values, final) := by
  obtain ⟨pair, resultEq, valuesEq, finalEq⟩ := accepted
  cases pair with
  | mk actualValues actualFinal =>
      simp only [Prod.fst, Prod.snd] at valuesEq finalEq
      subst actualValues
      subst actualFinal
      exact resultEq

theorem copyWithMacros_substituted_head_uses_copyMany (macros : List String)
    (fuel origin : Nat) (holes : Holes) (renames : Renames) (fresh : Nat)
    (head : Atom) (arguments : List Tree) (copiedItems : List Tree) (final : Nat)
    (headSubstituted : (lookup head.name holes).isSome = true)
    (ordinaryHead : head.name ≠ "lambda" ∧ head.name ≠ "let" ∧ head.name ≠ "match")
    (copied : copyWithMacros macros (fuel + 1) origin holes renames fresh
      (.list (.atom head :: arguments)) = some (.list copiedItems, final)) :
    (operations macros fuel).copyMany origin holes renames fresh (.atom head :: arguments) =
      some (copiedItems, final) := by
  cases lookupResult : lookup head.name holes with
  | none => simp [lookupResult] at headSubstituted
  | some replacement =>
      cases arguments with
      | nil =>
          simp [copyWithMacros, operations, lookupResult, named] at copied
          exact option_pair_components copied
      | cons first tail =>
          cases tail with
          | nil =>
              simp [copyWithMacros, operations, lookupResult, named] at copied
              exact option_pair_components copied
          | cons second tail =>
              cases tail with
              | nil =>
                  cases first <;>
                    simp [copyWithMacros, operations, lookupResult, named, ordinaryHead] at copied
                  all_goals exact option_pair_components copied
              | cons third tail =>
                  cases tail with
                  | nil =>
                      cases first <;>
                        simp [copyWithMacros, operations, lookupResult, named, ordinaryHead] at copied
                      all_goals exact option_pair_components copied
                  | cons fourth rest =>
                      simp [copyWithMacros, operations, lookupResult, named, ordinaryHead] at copied
                      exact option_pair_components copied

theorem capture_uses_definition_origin (a : Atom) (origin fresh : Nat) :
    copy 1 origin [] [] fresh (.atom a) =
      some (.atom {a with origin := some origin}, fresh) := rfl

theorem hole_keeps_argument (name : String) (argument : Tree) (a : Atom)
    (same : a.name = name) :
    copy 1 origin [(name, argument)] [] fresh (.atom a) = some (argument, fresh) := by
  simp [copy, operations, lookup, same]

end NLisp.CMacroCopy
