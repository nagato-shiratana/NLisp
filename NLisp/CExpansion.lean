import NLisp.CMacroCopy

namespace NLisp.CExpansion
open CMacroCopy

/- Source rules retain their declaration-position environment index. -/
def rulesAt (index : Nat) (form : Tree) : List (Nat × Tree) :=
  match form with
  | .list [head, _, .list (_ :: rules)] =>
      if named head "define-macro" then rules.map (fun rule => (index, rule)) else []
  | _ => []

def isMacro (form : Tree) : Bool :=
  match form with
  | .list (head :: _) => named head "define-macro"
  | _ => false

def sourceRules : Nat → List Tree → List (Nat × Tree)
  | _, [] => []
  | index, form :: tail =>
      rulesAt index form ++ sourceRules (if isMacro form then index else index + 1) tail

def programForms (forms : List Tree) : List Tree := forms.filter (fun form => !isMacro form)

def holeEntries : List Tree → List Tree → Option Holes
  | [], [] => some []
  | .atom parameter :: parameters, argument :: arguments => do
      return (parameter.name, argument) :: (← holeEntries parameters arguments)
  | _, _ => none

def matchRule (rule input : Tree) : Option (Holes × Tree) :=
  match rule, input with
  | .list [.list (.atom pattern :: parameters), _, _, template], .list (.atom called :: arguments) =>
      if pattern.name = called.name then
        (holeEntries parameters arguments).map (fun holes => (holes, template))
      else none
  | _, _ => none

/- The reflexive, transitive, context closure of hygienic rule substitution.
A certificate supplies a finite derivation, without claiming all macros stop. -/
inductive Expands (rules : List (Nat × Tree)) : Tree → Tree → Prop where
  | refl (tree : Tree) : Expands rules tree tree
  | cons : Expands rules head head' → Expands rules (.list tail) (.list tail') →
      Expands rules (.list (head :: tail)) (.list (head' :: tail'))
  | macroStep (origin fuel fresh final : Nat) (rule input template output : Tree) (holes : Holes) :
      (origin, rule) ∈ rules →
      matchRule rule input = some (holes, template) →
      copy fuel origin holes [] fresh template = some (output, final) →
      Expands rules input output
  | trans : Expands rules first second → Expands rules second third → Expands rules first third

noncomputable def sourceAtomsValid : Tree → Bool :=
  Tree.rec (motive_1 := fun _ => Bool) (motive_2 := fun _ => Bool)
    (fun atom => atom.origin.isNone && atom.token % 3 == 1 && !atom.name.startsWith "#%nlisp")
    (fun _ children => children) true (fun _ _ head tail => head && tail)

theorem source_and_generated_ids_differ (source : identity % 3 = 1) (counter : Nat) :
    identity ≠ 3 * counter + 2 := by omega

def separated (first second : Nat × Nat) : Bool :=
  decide (first.2 ≤ second.1 ∨ second.2 ≤ first.1)

def disjointIntervals : List (Nat × Nat) → Bool
  | [] => true
  | interval :: tail => decide (interval.1 ≤ interval.2) &&
      tail.all (separated interval) && disjointIntervals tail

theorem separated_fresh_values_differ (accepted : separated first second = true)
    (aLower : first.1 < a) (aUpper : a ≤ first.2)
    (bLower : second.1 < b) (bUpper : b ≤ second.2) : a ≠ b := by
  have split : first.2 ≤ second.1 ∨ second.2 ≤ first.1 := of_decide_eq_true accepted
  omega


theorem expansion_keeps_argument (a : Atom) (argument : Tree) (origin fresh : Nat) :
    copy 1 origin [(a.name, argument)] [] fresh (.atom a) = some (argument, fresh) :=
  hole_keeps_argument a.name argument a rfl

end NLisp.CExpansion
