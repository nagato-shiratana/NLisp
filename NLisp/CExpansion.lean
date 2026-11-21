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

/- Structural cost model for the parameter/argument walk after a macro head
has matched. Each paired parameter consumes one unit; reaching the end or a
shape/arity mismatch consumes one terminal unit. String comparison and list
allocation costs are outside this model. -/
def holeEntriesWithCost : List Tree → List Tree → Option Holes × Nat
  | [], [] => (some [], 1)
  | .atom parameter :: parameters, argument :: arguments =>
      let (entries, cost) := holeEntriesWithCost parameters arguments
      (entries.map (fun holes => (parameter.name, argument) :: holes), cost + 1)
  | _, _ => (none, 1)

theorem holeEntriesWithCost_result (parameters arguments : List Tree) :
    (holeEntriesWithCost parameters arguments).1 = holeEntries parameters arguments := by
  induction parameters generalizing arguments with
  | nil => cases arguments <;> rfl
  | cons parameter tail ih =>
      cases parameter with
      | atom atom =>
          cases arguments with
          | nil => rfl
          | cons argument arguments =>
              have recursiveResult := ih arguments
              cases costed : holeEntriesWithCost tail arguments with
              | mk entries cost =>
                  have entriesEq : entries = holeEntries tail arguments := by
                    simpa [costed] using recursiveResult
                  simp only [holeEntriesWithCost, costed]
                  rw [entriesEq]
                  simpa only [holeEntries] using
                    (CMacroCopy.option_map_eq_bind_some (holeEntries tail arguments)
                      (fun holes => (atom.name, argument) :: holes))
      | list children => cases arguments <;> rfl

theorem holeEntriesWithCost_cost_le_parameters_add_one
    (parameters arguments : List Tree) :
    (holeEntriesWithCost parameters arguments).2 ≤ parameters.length + 1 := by
  induction parameters generalizing arguments with
  | nil => cases arguments <;> simp [holeEntriesWithCost]
  | cons parameter tail ih =>
      cases parameter with
      | atom atom =>
          cases arguments with
          | nil => simp [holeEntriesWithCost, List.length_cons]
          | cons argument arguments =>
              simp only [holeEntriesWithCost, List.length_cons]
              have tailBound := ih arguments
              omega
      | list children => cases arguments <;> simp [holeEntriesWithCost, List.length_cons]

def matchRule (rule input : Tree) : Option (Holes × Tree) :=
  match rule, input with
  | .list [.list (.atom pattern :: parameters), _, _, template], .list (.atom called :: arguments) =>
      if pattern.name = called.name then
        (holeEntries parameters arguments).map (fun holes => (holes, template))
      else none
  | _, _ => none

def matchRuleParameterCount : Tree → Nat
  | .list [.list (.atom _ :: parameters), _, _, _] => parameters.length
  | _ => 0

def matchRulePayloadWithCost (pattern : Atom) (parameters : List Tree)
    (template : Tree) (called : Atom) (arguments : List Tree) :
    Option (Holes × Tree) × Nat :=
  if pattern.name = called.name then
    let (entries, cost) := holeEntriesWithCost parameters arguments
    (entries.map (fun holes => (holes, template)), cost + 1)
  else (none, 1)

theorem matchRulePayloadWithCost_result (pattern : Atom) (parameters : List Tree)
    (template : Tree) (called : Atom) (arguments : List Tree) :
    (matchRulePayloadWithCost pattern parameters template called arguments).1 =
      (if pattern.name = called.name then
        (holeEntries parameters arguments).map (fun holes => (holes, template)) else none) := by
  by_cases same : pattern.name = called.name
  · cases entries : holeEntries parameters arguments with
    | none => simp [matchRulePayloadWithCost, same, holeEntriesWithCost_result, entries]
    | some holes => simp [matchRulePayloadWithCost, same, holeEntriesWithCost_result, entries]
  · simp [matchRulePayloadWithCost, same]

theorem matchRulePayloadWithCost_cost_le (pattern : Atom) (parameters : List Tree)
    (template : Tree) (called : Atom) (arguments : List Tree) :
    (matchRulePayloadWithCost pattern parameters template called arguments).2 ≤
      parameters.length + 2 := by
  by_cases same : pattern.name = called.name
  · have holesBound := holeEntriesWithCost_cost_le_parameters_add_one parameters arguments
    simp only [matchRulePayloadWithCost, if_pos same, Prod.snd]
    omega
  · simp only [matchRulePayloadWithCost, if_neg same, Prod.snd]
    omega

/- Costed version of the shallow rule-shape/head check plus the instrumented
parameter walk. One unit covers the top-level dispatch and head-name check;
the parameter/argument traversal uses `holeEntriesWithCost`. -/
def matchRuleWithCost (rule input : Tree) : Option (Holes × Tree) × Nat :=
  match rule, input with
  | .list [.list (.atom pattern :: parameters), _, _, template],
      .list (.atom called :: arguments) =>
      matchRulePayloadWithCost pattern parameters template called arguments
  | _, _ => (none, 1)

theorem matchRuleWithCost_result (rule input : Tree) :
    (matchRuleWithCost rule input).1 = matchRule rule input := by
  unfold matchRuleWithCost matchRule
  split
  · exact matchRulePayloadWithCost_result _ _ _ _ _
  · rfl

theorem matchRuleWithCost_cost_le_parameters_add_two (rule input : Tree) :
    (matchRuleWithCost rule input).2 ≤ matchRuleParameterCount rule + 2 := by
  unfold matchRuleWithCost matchRuleParameterCount
  split
  · simp [matchRulePayloadWithCost_cost_le]
  · omega

/- The reflexive, transitive, context closure of hygienic rule substitution.
A certificate supplies a finite derivation, without claiming all macros stop. -/
inductive Expands (rules : List (Nat × Tree)) : Tree → Tree → Prop where
  | refl (tree : Tree) : Expands rules tree tree
  | cons : Expands rules head head' → Expands rules (.list tail) (.list tail') →
      Expands rules (.list (head :: tail)) (.list (head' :: tail'))
  | macroStep (origin fuel fresh final : Nat) (rule input template output : Tree) (holes : Holes) :
      (origin, rule) ∈ rules →
      matchRule rule input = some (holes, template) →
      copyWithMacros (macroNames rules) fuel origin holes [] fresh template = some (output, final) →
      Expands rules input output
  | trans : Expands rules first second → Expands rules second third → Expands rules first third

noncomputable def sourceAtomsValid : Tree → Bool :=
  Tree.rec (motive_1 := fun _ => Bool) (motive_2 := fun _ => Bool)
    (fun atom => atom.origin.isNone && atom.token % 3 == 1 && !atom.name.startsWith "#%nlisp")
    (fun _ children => children) true (fun _ _ head tail => head && tail)

theorem source_and_generated_ids_differ (source : identity % 3 = 1) (counter : Nat) :
    identity ≠ 3 * counter + 2 := by omega

theorem successful_binder_avoids_source_identity (holes : Holes) (renames : Renames)
    (fresh : Nat) (tree copied : Tree) (names : Renames) (final : Nat)
    (sourceAtom : Atom) (sourceClass : sourceAtom.token % 3 = 1)
    (accepted : binder holes renames fresh tree = some (copied, names, final))
    (copiedAtom : copied = .atom generated) : sourceAtom.token ≠ generated.token := by
  obtain ⟨atom, shape, counter, token⟩ :=
    binder_success_counter holes renames fresh tree copied names final accepted
  rw [copiedAtom] at shape
  have same : atom = generated := Tree.atom.inj shape.symm
  subst generated
  rw [token]
  exact source_and_generated_ids_differ sourceClass final

def separated (first second : Nat × Nat) : Bool :=
  decide (first.2 ≤ second.1 ∨ second.2 ≤ first.1)

def disjointIntervals : List (Nat × Nat) → Bool
  | [] => true
  | interval :: tail => decide (interval.1 ≤ interval.2) &&
      tail.all (separated interval) && disjointIntervals tail

theorem separated_symmetric (first second : Nat × Nat)
    (accepted : separated first second = true) : separated second first = true := by
  unfold separated at accepted ⊢
  simp only [decide_eq_true_eq] at accepted ⊢
  rcases accepted with h | h
  · exact Or.inr h
  · exact Or.inl h

theorem disjoint_head_separated (head : Nat × Nat) (tail : List (Nat × Nat))
    (accepted : disjointIntervals (head :: tail) = true) (item : Nat × Nat)
    (member : item ∈ tail) : separated head item = true := by
  simp [disjointIntervals, Bool.and_eq_true] at accepted
  exact accepted.1.2 item member

theorem disjoint_members_separated (intervals : List (Nat × Nat))
    (accepted : disjointIntervals intervals = true)
    (first second : Nat × Nat) (firstMember : first ∈ intervals)
    (secondMember : second ∈ intervals) (different : first ≠ second) :
    separated first second = true := by
  induction intervals generalizing first second with
  | nil => simp at firstMember
  | cons head tail ih =>
      rcases List.mem_cons.mp firstMember with firstHead | firstTail
      · rcases List.mem_cons.mp secondMember with secondHead | secondTail
        · subst first
          subst second
          exact False.elim (different rfl)
        · subst first
          exact disjoint_head_separated head tail accepted second secondTail
      · rcases List.mem_cons.mp secondMember with secondHead | secondTail
        · subst second
          exact separated_symmetric head first
            (disjoint_head_separated head tail accepted first firstTail)
        · exact ih (by
            simp [disjointIntervals, Bool.and_eq_true] at accepted
            exact accepted.2) first second firstTail secondTail different

theorem separated_fresh_values_differ (accepted : separated first second = true)
    (aLower : first.1 < a) (aUpper : a ≤ first.2)
    (bLower : second.1 < b) (bUpper : b ≤ second.2) : a ≠ b := by
  have split : first.2 ≤ second.1 ∨ second.2 ≤ first.1 := of_decide_eq_true accepted
  omega

theorem disjoint_interval_counters_differ (accepted : disjointIntervals intervals = true)
    (first second : Nat × Nat) (firstMember : first ∈ intervals)
    (secondMember : second ∈ intervals) (different : first ≠ second)
    (aLower : first.1 < a) (aUpper : a ≤ first.2)
    (bLower : second.1 < b) (bUpper : b ≤ second.2) : a ≠ b := by
  exact separated_fresh_values_differ
    (disjoint_members_separated intervals accepted first second firstMember secondMember different)
    aLower aUpper bLower bUpper

theorem disjoint_interval_generated_ids_differ (accepted : disjointIntervals intervals = true)
    (first second : Nat × Nat) (firstMember : first ∈ intervals)
    (secondMember : second ∈ intervals) (different : first ≠ second)
    (aLower : first.1 < a) (aUpper : a ≤ first.2)
    (bLower : second.1 < b) (bUpper : b ≤ second.2) :
    3 * a + 2 ≠ 3 * b + 2 := by
  have counters := disjoint_interval_counters_differ accepted first second
    firstMember secondMember different aLower aUpper bLower bUpper
  intro equal
  have same : a = b := by omega
  exact counters same


theorem expansion_keeps_argument (a : Atom) (argument : Tree) (origin fresh : Nat) :
    copy 1 origin [(a.name, argument)] [] fresh (.atom a) = some (argument, fresh) :=
  hole_keeps_argument a.name argument a rfl

end NLisp.CExpansion
