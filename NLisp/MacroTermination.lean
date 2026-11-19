import NLisp.CExpansion

namespace NLisp.MacroTermination
open CMacroCopy CExpansion

private theorem option_bind_some {α β : Type} {source : Option α}
    {continuation : α → Option β} {value : β}
    (accepted : source.bind continuation = some value) :
    ∃ intermediate, source = some intermediate ∧ continuation intermediate = some value := by
  cases source with
  | none => simp at accepted
  | some intermediate => exact ⟨intermediate, rfl, accepted⟩

private theorem mem_append_left {α : Type} (left right : List α) {item : α}
    (member : item ∈ left) : item ∈ left ++ right := by
  induction left with
  | nil => simp at member
  | cons head tail ih =>
      simp only [List.cons_append, List.mem_cons] at member ⊢
      rcases member with same | member
      · subst item
        exact Or.inl rfl
      · exact Or.inr (ih member)

private theorem mem_append_right {α : Type} (left right : List α) {item : α}
    (member : item ∈ right) : item ∈ left ++ right := by
  have each (pre : List α) : item ∈ right → item ∈ pre ++ right := by
    induction pre with
    | nil => simp
    | cons head tail ih =>
        intro member
        simp only [List.cons_append, List.mem_cons]
        exact Or.inr (ih member)
  exact each left member

private theorem mem_map_counter (values : List Nat) (target index : Nat)
    (member : target ∈ values) :
    (target, index) ∈ values.map (fun child => (child, index)) := by
  induction values with
  | nil => simp at member
  | cons child tail ih =>
      rcases List.mem_cons.mp member with same | rest
      · subst target
        simp [List.map_cons]
      · exact List.mem_cons_of_mem _ (ih rest)

abbrev Edge := Nat × Nat -- child, parent

def signature : Tree → Option (String × Nat)
  | .list [.list (.atom head :: parameters), _, _, _] => some (head.name, parameters.length)
  | _ => none

def findRule (name : String) (arity : Nat) : Nat → List (Nat × Tree) → Option Nat
  | _, [] => none
  | index, (_, rule) :: tail =>
      if signature rule = some (name, arity) then some index else findRule name arity (index + 1) tail

def targetsOfSignature (name : String) (arity : Nat) : Nat → List (Nat × Tree) → List Nat
  | _, [] => []
  | index, (_, rule) :: tail =>
      if signature rule = some (name, arity) then
        index :: targetsOfSignature name arity (index + 1) tail
      else targetsOfSignature name arity (index + 1) tail

theorem findRule_mem_targetsOfSignature (name : String) (arity start : Nat)
    (rules : List (Nat × Tree)) (target : Nat)
    (found : findRule name arity start rules = some target) :
    target ∈ targetsOfSignature name arity start rules := by
  induction rules generalizing start with
  | nil => simp [findRule] at found
  | cons entry tail ih =>
      rcases entry with ⟨owner, rule⟩
      change (if signature rule = some (name, arity) then some start
        else findRule name arity (start + 1) tail) = some target at found
      change target ∈ (if signature rule = some (name, arity) then
        start :: targetsOfSignature name arity (start + 1) tail
        else targetsOfSignature name arity (start + 1) tail)
      by_cases signatureMatches : signature rule = some (name, arity)
      · simp [signatureMatches] at found
        subst target
        simp [signatureMatches]
      · simp [signatureMatches] at found
        have rest := ih (start + 1) found
        simp [signatureMatches]
        exact rest

def parameters : Tree → Option (List String × Tree)
  | .list [.list (_ :: names), _, _, template] => do
      let holes ← names.mapM (fun tree => match tree with
        | .atom a => some a.name
        | _ => none)
      pure (holes, template)
  | _ => none

/- A syntax hole in call-head position can be substituted by any macro name.
Include every rule of the same arity as a conservative target candidate. -/
def targetsOfArity (arity : Nat) : Nat → List (Nat × Tree) → List Nat
  | _, [] => []
  | index, (_, rule) :: tail =>
      if (signature rule).map Prod.snd = some arity then
        index :: targetsOfArity arity (index + 1) tail
      else targetsOfArity arity (index + 1) tail

theorem findRule_mem_targetsOfArity (name : String) (arity start : Nat)
    (rules : List (Nat × Tree)) (target : Nat)
    (found : findRule name arity start rules = some target) :
    target ∈ targetsOfArity arity start rules := by
  induction rules generalizing start with
  | nil => simp [findRule] at found
  | cons entry tail ih =>
      rcases entry with ⟨owner, rule⟩
      change (if signature rule = some (name, arity) then some start
        else findRule name arity (start + 1) tail) = some target at found
      change target ∈ (if (signature rule).map Prod.snd = some arity then
        start :: targetsOfArity arity (start + 1) tail
        else targetsOfArity arity (start + 1) tail)
      by_cases signatureMatches : signature rule = some (name, arity)
      · simp [signatureMatches] at found
        subst target
        simp [signatureMatches]
      · simp [signatureMatches] at found
        have rest := ih (start + 1) found
        by_cases sameArity : (signature rule).map Prod.snd = some arity
        · simp [sameArity]
          exact Or.inr rest
        · simp [sameArity]
          exact rest

/- Conservative call extraction. A hole in head position can manufacture a
new call, so every rule of the same arity is a possible target. A named call
includes every rule with that exact signature. Scanning annotations too only
adds edges and may reduce completeness. -/
structure CallOperations where
  calls : List (Nat × Tree) → List String → Tree → Option (List Nat)
  callsMany : List (Nat × Tree) → List String → List Tree → Option (List Nat)

def callOperations : Nat → CallOperations
  | 0 => ⟨fun _ _ _ => none, fun _ _ _ => none⟩
  | fuel + 1 =>
      let previous := callOperations fuel
      { calls := fun rules holes tree =>
          match tree with
          | .atom _ => some []
          | .list items =>
              match previous.callsMany rules holes items with
              | none => none
              | some nested =>
                match items with
                | .atom head :: arguments =>
                    if head.name ∈ holes then
                      some (targetsOfArity arguments.length 0 rules ++ nested)
                    else
                      some (targetsOfSignature head.name arguments.length 0 rules ++ nested)
                | _ => some nested
        callsMany := fun rules holes trees =>
          match trees with
          | [] => some []
          | head :: tail =>
              match previous.calls rules holes head with
              | none => none
              | some headCalls =>
                match previous.callsMany rules holes tail with
                | none => none
                | some tailCalls => some (headCalls ++ tailCalls) }

def calls (fuel : Nat) := (callOperations fuel).calls
def callsMany (fuel : Nat) := (callOperations fuel).callsMany

theorem calls_direct_macro_complete (fuel : Nat) (rules : List (Nat × Tree))
    (holes : List String) (head : Atom) (arguments : List Tree) (target : Nat)
    (targets : List Nat) (notHole : head.name ∉ holes)
    (found : findRule head.name arguments.length 0 rules = some target)
    (checked : calls (fuel + 1) rules holes (.list (.atom head :: arguments)) = some targets) :
    target ∈ targets := by
  simp only [calls, callOperations, notHole] at checked
  generalize nestedResult : (callOperations fuel).callsMany rules holes
      (.atom head :: arguments) = nestedOption at checked
  cases nestedOption with
  | none => simp [nestedResult] at checked
  | some nested =>
      simp [nestedResult] at checked
      subst targets
      exact mem_append_left _ _
        (findRule_mem_targetsOfSignature head.name arguments.length 0 rules target found)

inductive StaticCall (rules : List (Nat × Tree)) (holes : List String) : Tree → Nat → Prop where
  | direct {head : Atom} {arguments : List Tree} {target : Nat} :
      head.name ∉ holes → target ∈ targetsOfSignature head.name arguments.length 0 rules →
      StaticCall rules holes (.list (.atom head :: arguments)) target
  | substitutedHead {head : Atom} {arguments : List Tree} {target : Nat} :
      head.name ∈ holes → target ∈ targetsOfArity arguments.length 0 rules →
      StaticCall rules holes (.list (.atom head :: arguments)) target
  | nested {items : List Tree} {child : Tree} {target : Nat} :
      child ∈ items → StaticCall rules holes child target →
      StaticCall rules holes (.list items) target

def HasStaticCall (rules : List (Nat × Tree)) (holes : List String)
    (trees : List Tree) (target : Nat) : Prop :=
  ∃ tree, tree ∈ trees ∧ StaticCall rules holes tree target

theorem call_extraction_complete (fuel : Nat) :
    (∀ rules holes tree targets, calls fuel rules holes tree = some targets →
      ∀ target, StaticCall rules holes tree target → target ∈ targets) ∧
    (∀ rules holes trees targets, callsMany fuel rules holes trees = some targets →
      ∀ target, HasStaticCall rules holes trees target → target ∈ targets) := by
  induction fuel with
  | zero =>
      constructor
      · intro rules holes tree targets checked target _call
        simp [calls, callOperations] at checked
      · intro rules holes trees targets checked target _call
        simp [callsMany, callOperations] at checked
  | succ fuel ih =>
      constructor
      · intro rules holes tree targets checked target call
        cases tree with
        | atom atom => cases call
        | list items =>
            simp only [calls, callOperations] at checked
            generalize nestedResult : (callOperations fuel).callsMany rules holes items = nestedOption at checked
            cases nestedOption with
            | none => simp [nestedResult] at checked
            | some nested =>
                cases call with
                | direct notHole found =>
                    simp [nestedResult, notHole] at checked
                    subst targets
                    exact mem_append_left _ _ found
                | substitutedHead isHole member =>
                    simp [nestedResult, isHole] at checked
                    subst targets
                    exact mem_append_left _ _ member
                | nested member inside =>
                    have nestedMember := ih.2 rules holes items nested nestedResult target
                      ⟨_, member, inside⟩
                    cases items with
                    | nil => simp at member
                    | cons first rest =>
                        cases first with
                        | atom head =>
                            by_cases isHole : head.name ∈ holes
                            · simp [nestedResult, isHole] at checked
                              subst targets
                              exact mem_append_right _ _ nestedMember
                            · simp [nestedResult, isHole] at checked
                              subst targets
                              exact mem_append_right _ _ nestedMember
                        | list nestedHead =>
                            simp [nestedResult] at checked
                            subst targets
                            exact nestedMember
      · intro rules holes trees targets checked target call
        cases trees with
        | nil => rcases call with ⟨tree, member, _⟩; simp at member
        | cons head tail =>
            simp only [callsMany, callOperations] at checked
            generalize headResult : (callOperations fuel).calls rules holes head = headOption at checked
            cases headOption with
            | none => simp [headResult] at checked
            | some headCalls =>
                generalize tailResult : (callOperations fuel).callsMany rules holes tail = tailOption at checked
                cases tailOption with
                | none => simp [headResult, tailResult] at checked
                | some tailCalls =>
                    simp [headResult, tailResult] at checked
                    have resultEq : headCalls ++ tailCalls = targets := checked
                    subst targets
                    rcases call with ⟨tree, member, inside⟩
                    rcases List.mem_cons.mp member with same | inTail
                    · subst tree
                      exact mem_append_left _ _
                        (ih.1 rules holes head headCalls headResult target inside)
                    · exact mem_append_right _ _
                        (ih.2 rules holes tail tailCalls tailResult target ⟨tree, inTail, inside⟩)

def graphRows (fuel : Nat) (rules : List (Nat × Tree)) : Nat → List (Nat × Tree) → Option (List Edge)
  | _, [] => some []
  | index, (_, rule) :: tail => do
      let (holes, template) ← parameters rule
      let dependencies ← calls fuel rules holes template
      let remaining ← graphRows fuel rules (index + 1) tail
      pure (dependencies.map (fun child => (child, index)) ++ remaining)

theorem graphRows_dependency_edge (fuel : Nat) (rules : List (Nat × Tree))
    (index owner : Nat) (rule : Tree) (tail : List (Nat × Tree))
    (holes : List String) (template : Tree) (dependency : Nat) (edges : List Edge)
    (parsed : parameters rule = some (holes, template))
    (dependencyCheck : calls fuel rules holes template = some dependencies)
    (member : dependency ∈ dependencies)
    (checked : graphRows fuel rules index ((owner, rule) :: tail) = some edges) :
    (dependency, index) ∈ edges := by
  simp only [graphRows, parsed, bind, Option.bind] at checked
  obtain ⟨actualDependencies, actualCheck, restCheck⟩ := option_bind_some checked
  obtain ⟨remaining, _remainingCheck, resultEq⟩ := option_bind_some restCheck
  have sameDependencies : actualDependencies = dependencies :=
    Option.some.inj (actualCheck.symm.trans dependencyCheck)
  subst actualDependencies
  have edgesEq : dependencies.map (fun child => (child, index)) ++ remaining = edges := by
    simpa using resultEq
  rw [← edgesEq]
  exact mem_append_left _ _ (mem_map_counter dependencies dependency index member)

theorem graphRows_root_call_edge (fuel : Nat) (rules : List (Nat × Tree))
    (index owner : Nat) (rule : Tree) (tail : List (Nat × Tree))
    (holes : List String) (template : Tree) (head : Atom) (arguments : List Tree)
    (target : Nat) (edges : List Edge)
    (parsed : parameters rule = some (holes, template))
    (templateShape : template = .list (.atom head :: arguments))
    (notHole : head.name ∉ holes)
    (found : findRule head.name arguments.length 0 rules = some target)
    (checked : graphRows (fuel + 1) rules index ((owner, rule) :: tail) = some edges) :
    (target, index) ∈ edges := by
  have checkedCopy := checked
  simp only [graphRows, parsed, bind, Option.bind] at checkedCopy
  obtain ⟨dependencies, dependencyCheck, _restCheck⟩ := option_bind_some checkedCopy
  have included := calls_direct_macro_complete fuel rules holes head arguments target
    dependencies notHole found (by simpa [templateShape] using dependencyCheck)
  exact graphRows_dependency_edge (fuel + 1) rules index owner rule tail holes template
    target edges parsed dependencyCheck included checked

theorem graphRows_static_call_edge (fuel : Nat) (rules : List (Nat × Tree))
    (index owner : Nat) (rule : Tree) (tail : List (Nat × Tree))
    (holes : List String) (template : Tree) (target : Nat) (edges : List Edge)
    (parsed : parameters rule = some (holes, template))
    (dependencyCheck : calls fuel rules holes template = some dependencies)
    (staticCall : StaticCall rules holes template target)
    (checked : graphRows fuel rules index ((owner, rule) :: tail) = some edges) :
    (target, index) ∈ edges := by
  have included := (call_extraction_complete fuel).1 rules holes template dependencies
    dependencyCheck target staticCall
  exact graphRows_dependency_edge fuel rules index owner rule tail holes template target
    edges parsed dependencyCheck included checked

private theorem graphRows_cons_parts (fuel : Nat) (rules : List (Nat × Tree))
    (index owner : Nat) (rule : Tree) (tail : List (Nat × Tree)) (edges : List Edge)
    (accepted : graphRows fuel rules index ((owner, rule) :: tail) = some edges) :
    ∃ holes template dependencies remaining,
      parameters rule = some (holes, template) ∧
      calls fuel rules holes template = some dependencies ∧
      graphRows fuel rules (index + 1) tail = some remaining ∧
      dependencies.map (fun child => (child, index)) ++ remaining = edges := by
  simp only [graphRows, bind, Option.bind] at accepted
  obtain ⟨parsed, parsedResult, restCheck⟩ := option_bind_some accepted
  rcases parsed with ⟨holes, template⟩
  have parsedRule : parameters rule = some (holes, template) := parsedResult
  obtain ⟨dependencies, dependencyCheck, restCheck⟩ := option_bind_some restCheck
  obtain ⟨remaining, remainingCheck, resultEq⟩ := option_bind_some restCheck
  have edgesEq : dependencies.map (fun child => (child, index)) ++ remaining = edges := by
    simpa using resultEq
  exact ⟨holes, template, dependencies, remaining, parsedRule, dependencyCheck,
    remainingCheck, edgesEq⟩

inductive GraphCall (rules : List (Nat × Tree)) : Nat → List (Nat × Tree) → Edge → Prop where
  | here {index owner : Nat} {rule : Tree} {tail : List (Nat × Tree)}
      {holes : List String} {template : Tree} {child : Nat} :
      parameters rule = some (holes, template) → StaticCall rules holes template child →
      GraphCall rules index ((owner, rule) :: tail) (child, index)
  | later {index owner : Nat} {head : Tree} {tail : List (Nat × Tree)} {edge : Edge} :
      GraphCall rules (index + 1) tail edge →
      GraphCall rules index ((owner, head) :: tail) edge

theorem graphRows_contains_static_calls (fuel : Nat) (rules : List (Nat × Tree))
    (index : Nat) (rows : List (Nat × Tree)) (edges : List Edge)
    (checked : graphRows fuel rules index rows = some edges)
    (call : GraphCall rules index rows edge) : edge ∈ edges := by
  induction call generalizing edges with
  | @here index owner rule tail holes template child parsed staticCall =>
      simp only [graphRows, parsed, bind, Option.bind] at checked
      obtain ⟨dependencies, dependencyCheck, restCheck⟩ := option_bind_some checked
      obtain ⟨remaining, _remainingCheck, resultEq⟩ := option_bind_some restCheck
      have included := (call_extraction_complete fuel).1 rules holes template dependencies
        dependencyCheck child staticCall
      have mapped := mem_append_left (dependencies.map (fun target => (target, index)))
        remaining (mem_map_counter dependencies child index included)
      have edgesEq : dependencies.map (fun target => (target, index)) ++ remaining = edges := by
        simpa using resultEq
      rw [← edgesEq]
      exact mapped
  | @later index owner head tail edge _inner ih =>
      obtain ⟨_holes, _template, _dependencies, remaining, _parsed, _dependencyCheck,
        remainingCheck, edgesEq⟩ := graphRows_cons_parts fuel rules index owner head tail edges checked
      have edgeInTail := ih remaining remainingCheck
      rw [← edgesEq]
      exact mem_append_right _ _ edgeInTail

def graph (fuel : Nat) (rules : List (Nat × Tree)) : Option (List Edge) := graphRows fuel rules 0 rules

def rank (ranks : List Nat) (node : Nat) : Nat := (ranks[node]?).getD 0

def checkRanks (edges : List Edge) (ranks : List Nat) : Bool :=
  edges.all (fun edge => decide (rank ranks edge.1 < rank ranks edge.2))

def Calls (edges : List Edge) (child parent : Nat) : Prop := (child, parent) ∈ edges

theorem checkRanks_decreases (accepted : checkRanks edges ranks = true)
    (edge : Calls edges child parent) : rank ranks child < rank ranks parent := by
  have all := List.all_eq_true.mp accepted
  exact of_decide_eq_true (all (child, parent) edge)

/- This is Lean's ordinary well-founded recursion mechanism, with the
certificate's rule rank as termination_by measure. It constructs accessibility
for every node rather than merely testing a recursion-depth threshold. -/
def accessible (edges : List Edge) (ranks : List Nat)
    (accepted : checkRanks edges ranks = true) (node : Nat) : Acc (Calls edges) node :=
  Acc.intro node (fun child _edge => accessible edges ranks accepted child)
termination_by rank ranks node
decreasing_by exact checkRanks_decreases accepted _edge

theorem ranked_graph_wellFounded (accepted : checkRanks edges ranks = true) :
    WellFounded (Calls edges) := ⟨accessible edges ranks accepted⟩

/- A path is a finite prefix of nested recursive invocations. -/
inductive Path (edges : List Edge) : Nat → Nat → Nat → Prop where
  | zero (node : Nat) : Path edges node node 0
  | step : Calls edges next first → Path edges next last count →
      Path edges first last (count + 1)

theorem path_length_bounded (accepted : checkRanks edges ranks = true)
    (path : Path edges first last count) : count + rank ranks last ≤ rank ranks first := by
  induction path with
  | zero _ => omega
  | step edge _ ih =>
      have decrease := checkRanks_decreases accepted edge
      omega

end NLisp.MacroTermination
