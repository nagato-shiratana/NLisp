import NLisp.ExpansionLowering

namespace NLisp.Surface
open ExpansionLowering

private theorem range_loop_member (n index : Nat) (acc : List Nat)
    (h : index < n ∨ index ∈ acc) : index ∈ List.range.loop n acc := by
  induction n generalizing acc with
  | zero => simpa [List.range.loop, Nat.not_lt_zero] using h
  | succ n ih =>
    apply ih
    rcases h with bound | member
    · by_cases same : index = n
      · exact Or.inr (by simp [same])
      · exact Or.inl (by omega)
    · exact Or.inr (List.mem_cons_of_mem n member)

theorem below_member_range {index count : Nat} (bound : index < count) :
    index ∈ List.range count := range_loop_member count index [] (Or.inl bound)

/- Every occurrence of a quantified variable determines the corresponding
argument. Candidates are compared as syntax, with caller variables rigid. -/
theorem occurrence_determines (fuel : Nat) (typeIndex : Nat) (left right : List Ty)
    (bound : typeIndex < left.length) (sameLength : left.length = right.length) :
    (∀ type, occurs fuel typeIndex type = true →
      Ty.instantiate left type = Ty.instantiate right type → left[typeIndex]? = right[typeIndex]?) ∧
    (∀ types, occursMany fuel typeIndex types = true →
      instantiateTypes left types = instantiateTypes right types → left[typeIndex]? = right[typeIndex]?) := by
  induction fuel with
  | zero => simp [occurs, occursMany]
  | succ fuel ih =>
    refine ⟨?_, ?_⟩
    · intro type occurrence same
      cases type with
      | boolean | integer | unit => simp [occurs] at occurrence
      | var i =>
        have eq : i = typeIndex := by simpa [occurs] using occurrence
        subst i
        have otherBound : typeIndex < right.length := by omega
        simpa [Ty.instantiate, getElem?_def, bound, otherBound] using same
      | fn parameters result =>
        simp only [occurs, Bool.or_eq_true] at occurrence
        simp only [Ty.instantiate] at same
        have parts := Ty.fn.inj same
        rcases occurrence with fromParameters | fromResult
        · exact ih.2 parameters fromParameters parts.1
        · exact ih.1 result fromResult parts.2
      | list element =>
        simp only [occurs] at occurrence
        simp only [Ty.instantiate] at same
        exact ih.1 element occurrence (Ty.list.inj same)
      | option element =>
        simp only [occurs] at occurrence
        simp only [Ty.instantiate] at same
        exact ih.1 element occurrence (Ty.option.inj same)
    · intro types occurrence same
      cases types with
      | nil => simp [occursMany] at occurrence
      | cons head tail =>
        simp only [occursMany, Bool.or_eq_true] at occurrence
        simp only [instantiateTypes] at same
        have parts := List.cons.inj same
        rcases occurrence with fromHead | fromTail
        · exact ih.1 head fromHead parts.1
        · exact ih.2 tail fromTail parts.2

theorem inferred_arguments_unique (fuel : Nat) (header : Header)
    (accepted : inferrable fuel header = true) (left right : List Ty)
    (leftArity : left.length = header.variables.length)
    (rightArity : right.length = header.variables.length)
    (same : instantiateTypes left (header.parameters.map Prod.snd) =
      instantiateTypes right (header.parameters.map Prod.snd)) : left = right := by
  apply List.ext_get (by omega)
  intro index leftBound rightBound
  have bound : index < header.variables.length := by omega
  have occurrence : occursMany fuel index (header.parameters.map Prod.snd) = true :=
    List.all_eq_true.mp accepted index (below_member_range bound)
  have sameLookup := (occurrence_determines fuel index left right leftBound (by omega)).2 _ occurrence same
  simpa [getElem?_def, leftBound, rightBound] using sameLookup

mutual
def collectArgument : Nat → Ty → Ty → List (Option Ty) → Option (List (Option Ty))
  | 0, _, _, _ => none
  | fuel + 1, pattern, actual, assignments =>
    match pattern with
    | .var index =>
      match assignments[index]? with
      | none => none
      | some none => some (assignments.set index (some actual))
      | some (some previous) => if previous = actual then some assignments else none
    | .boolean => if actual = .boolean then some assignments else none
    | .integer => if actual = .integer then some assignments else none
    | .unit => if actual = .unit then some assignments else none
    | .fn parameters result =>
      match actual with
      | .fn inputs output => do
        let next ← collectArguments fuel parameters inputs assignments
        collectArgument fuel result output next
      | _ => none
    | .list element =>
      match actual with
      | .list input => collectArgument fuel element input assignments
      | _ => none
    | .option element =>
      match actual with
      | .option input => collectArgument fuel element input assignments
      | _ => none

def collectArguments : Nat → List Ty → List Ty → List (Option Ty) → Option (List (Option Ty))
  | 0, _, _, _ => none
  | fuel + 1, patterns, actuals, assignments =>
    match patterns, actuals with
    | [], [] => some assignments
    | pattern :: patterns, actual :: actuals => do
      let next ← collectArgument fuel pattern actual assignments
      collectArguments fuel patterns actuals next
    | _, _ => none
end

/- Structural resource bound for the collector. Function-parameter traversal and
the result-type traversal both start with the same remaining fuel, so the
function case adds their recursive costs. -/
mutual
def collectorTypeFuel (type : Ty) : Nat :=
  match type with
  | .boolean | .integer | .unit | .var _ => 1
  | .fn parameters result => collectorTypesFuel parameters + collectorTypeFuel result + 1
  | .list element | .option element => collectorTypeFuel element + 1
termination_by sizeOf type
decreasing_by all_goals simp_wf; omega

def collectorTypesFuel (types : List Ty) : Nat :=
  match types with
  | [] => 1
  | type :: tail => collectorTypeFuel type + collectorTypesFuel tail + 1
termination_by sizeOf types
decreasing_by all_goals simp_wf; omega
end

private theorem indexed_lookup_eq_get? {α : Type} (values : List α) (index : Nat) :
    values[index]? = values.get? index := by
  induction values generalizing index with
  | nil => cases index <;> simp [getElem?_def]
  | cons head tail ih => cases index with
      | zero => simp [getElem?_def]
      | succ index => simpa [getElem?_def, Nat.succ_lt_succ_iff] using ih index

private theorem indexed_set_preserves_other {α : Type} (values : List α)
    (index queried : Nat) (replacement original : α)
    (different : index ≠ queried)
    (old : values[queried]? = some original) :
    (values.set index replacement)[queried]? = some original := by
  have old' : values.get? queried = some original := by
    rw [← indexed_lookup_eq_get?]
    exact old
  obtain ⟨bound, entry⟩ := List.get?_eq_some.mp old'
  have newBound : queried < (values.set index replacement).length := by
    simpa [List.length_set] using bound
  have indicesNe : index ≠ queried := different
  have unchanged := List.get_set_ne values indicesNe replacement newBound
  have new' : (values.set index replacement).get? queried = some original :=
    List.get?_eq_some.mpr ⟨newBound, unchanged.trans entry⟩
  rw [indexed_lookup_eq_get?]
  exact new'

mutual
theorem collectArgument_preserves_assigned (fuel : Nat) (pattern actual : Ty)
    (assignments updated : List (Option Ty))
    (collected : collectArgument fuel pattern actual assignments = some updated)
    (index : Nat) (value : Ty)
    (assigned : assignments[index]? = some (some value)) :
    updated[index]? = some (some value) := by
  cases fuel with
  | zero => simp [collectArgument] at collected
  | succ fuel =>
      cases pattern with
      | boolean =>
          cases actual with
          | boolean =>
              have resultEq : assignments = updated := by simpa [collectArgument] using collected
              simpa [resultEq] using assigned
          | integer | unit | var _ | fn _ _ | list _ | option _ =>
              simp [collectArgument] at collected
      | integer =>
          cases actual with
          | integer =>
              have resultEq : assignments = updated := by simpa [collectArgument] using collected
              simpa [resultEq] using assigned
          | boolean | unit | var _ | fn _ _ | list _ | option _ =>
              simp [collectArgument] at collected
      | unit =>
          cases actual with
          | unit =>
              have resultEq : assignments = updated := by simpa [collectArgument] using collected
              simpa [resultEq] using assigned
          | boolean | integer | var _ | fn _ _ | list _ | option _ =>
              simp [collectArgument] at collected
      | var patternIndex =>
          cases slot : assignments[patternIndex]? with
          | none => simp [collectArgument, slot] at collected
          | some entry =>
              cases entry with
              | none =>
                  have resultEq : assignments.set patternIndex (some actual) = updated := by
                    simpa [collectArgument, slot] using collected
                  subst updated
                  by_cases same : patternIndex = index
                  · subst index
                    simp [slot] at assigned
                  · exact indexed_set_preserves_other assignments patternIndex index
                      (some actual) (some value) same assigned
              | some previous =>
                  have resultEq : assignments = updated := by
                    simp [collectArgument, slot] at collected
                    exact collected.2
                  simpa [resultEq] using assigned
      | list element =>
          cases actual with
          | list input =>
              exact collectArgument_preserves_assigned fuel element input assignments updated
                (by simpa [collectArgument] using collected) index value assigned
          | boolean | integer | unit | var _ | fn _ _ | option _ =>
              simp [collectArgument] at collected
      | option element =>
          cases actual with
          | option input =>
              exact collectArgument_preserves_assigned fuel element input assignments updated
                (by simpa [collectArgument] using collected) index value assigned
          | boolean | integer | unit | var _ | fn _ _ | list _ =>
              simp [collectArgument] at collected
      | fn parameters result =>
          cases actual with
          | fn inputs output =>
              simp only [collectArgument] at collected
              cases first : collectArguments fuel parameters inputs assignments with
              | none => simp [first] at collected
              | some intermediate =>
                  have second : collectArgument fuel result output intermediate = some updated := by
                    simpa [first] using collected
                  have firstPreserves := collectArguments_preserves_assigned fuel parameters inputs
                    assignments intermediate first index value assigned
                  exact collectArgument_preserves_assigned fuel result output intermediate updated
                    second index value firstPreserves
          | boolean | integer | unit | var _ | list _ | option _ =>
              simp [collectArgument] at collected
termination_by fuel
decreasing_by all_goals simp_wf; omega

theorem collectArguments_preserves_assigned (fuel : Nat) (patterns actuals : List Ty)
    (assignments updated : List (Option Ty))
    (collected : collectArguments fuel patterns actuals assignments = some updated)
    (index : Nat) (value : Ty)
    (assigned : assignments[index]? = some (some value)) :
    updated[index]? = some (some value) := by
  cases fuel with
  | zero => simp [collectArguments] at collected
  | succ fuel =>
      cases patterns with
      | nil =>
          cases actuals with
          | nil =>
              have resultEq : assignments = updated := by simpa [collectArguments] using collected
              simpa [resultEq] using assigned
          | cons actual rest => simp [collectArguments] at collected
      | cons pattern rest =>
          cases actuals with
          | nil => simp [collectArguments] at collected
          | cons actual actualRest =>
              simp only [collectArguments] at collected
              cases first : collectArgument fuel pattern actual assignments with
              | none => simp [first] at collected
              | some intermediate =>
                  have second : collectArguments fuel rest actualRest intermediate = some updated := by
                    simpa [first] using collected
                  have firstPreserves := collectArgument_preserves_assigned fuel pattern actual
                    assignments intermediate first index value assigned
                  exact collectArguments_preserves_assigned fuel rest actualRest intermediate
                    updated second index value firstPreserves
termination_by fuel
decreasing_by all_goals simp_wf; omega
end

/- These equations expose the same constraint update used by C's
`match_type`: the first occurrence stores the actual type verbatim; later
occurrences compare that stored type with the new actual. In particular, a
caller-side `Ty.var` is retained as rigid syntax and is never recursively
solved by this matcher. -/
theorem collectArgument_first_variable_capture (fuel index : Nat) (actual : Ty)
    (assignments : List (Option Ty))
    (emptySlot : assignments[index]? = some none) :
    collectArgument (fuel + 1) (.var index) actual assignments =
      some (assignments.set index (some actual)) := by
  simp [collectArgument, emptySlot]

theorem collectArgument_repeated_variable_same (fuel index : Nat) (patternType actual : Ty)
    (assignments : List (Option Ty))
    (assigned : assignments[index]? = some (some patternType))
    (consistent : patternType = actual) :
    collectArgument (fuel + 1) (.var index) actual assignments = some assignments := by
  simp [collectArgument, assigned, consistent]

theorem collectArgument_repeated_variable_conflict (fuel index : Nat) (previous actual : Ty)
    (assignments : List (Option Ty))
    (assigned : assignments[index]? = some (some previous))
    (inconsistent : previous ≠ actual) :
    collectArgument (fuel + 1) (.var index) actual assignments = none := by
  simp [collectArgument, assigned, inconsistent]

def AssignmentsAgree (candidate : List Ty) (assignments : List (Option Ty)) : Prop :=
  ∀ (index : Nat) (value : Ty), assignments[index]? = some (some value) →
    candidate[index]? = some value

theorem AssignmentsAgree.set {candidate : List Ty} {assignments : List (Option Ty)}
    (agree : AssignmentsAgree candidate assignments) {index : Nat} {actual : Ty}
    (candidateAtIndex : candidate[index]? = some actual) :
    AssignmentsAgree candidate (assignments.set index (some actual)) := by
  intro queried value found
  have found' : (assignments.set index (some actual)).get? queried = some (some value) := by
    rw [← indexed_lookup_eq_get?]
    exact found
  obtain ⟨bound, entry⟩ := List.get?_eq_some.mp found'
  by_cases same : queried = index
  · subst queried
    have inserted := List.get_set_eq assignments index (some actual) bound
    have valueEq : some actual = some value := inserted.symm.trans entry
    have valueEq := Option.some.inj valueEq
    subst value
    exact candidateAtIndex
  · have queriedBound : queried < assignments.length := by
      simpa only [List.length_set] using bound
    have indicesNe : index ≠ queried := by
      intro eq
      exact same eq.symm
    have unchanged := List.get_set_ne assignments indicesNe (some actual) bound
    have oldEntry : assignments.get? queried = some (some value) :=
      List.get?_eq_some.mpr ⟨queriedBound, unchanged.symm.trans entry⟩
    have oldEntry' : assignments[queried]? = some (some value) := by
      rw [indexed_lookup_eq_get?]
      exact oldEntry
    exact agree queried value oldEntry'

theorem collectArgument_first_variable_agrees (fuel index : Nat) (actual : Ty)
    (candidate : List Ty) (assignments : List (Option Ty))
    (agree : AssignmentsAgree candidate assignments)
    (emptySlot : assignments[index]? = some none)
    (candidateAtIndex : candidate[index]? = some actual) :
    ∃ updated, collectArgument (fuel + 1) (.var index) actual assignments = some updated ∧
      AssignmentsAgree candidate updated := by
  refine ⟨assignments.set index (some actual), collectArgument_first_variable_capture
    fuel index actual assignments emptySlot, AssignmentsAgree.set agree candidateAtIndex⟩

theorem collectArgument_repeated_variable_agrees (fuel index : Nat) (previous actual : Ty)
    (candidate : List Ty) (assignments : List (Option Ty))
    (agree : AssignmentsAgree candidate assignments)
    (assigned : assignments[index]? = some (some previous))
    (candidateAtIndex : candidate[index]? = some actual) :
    ∃ updated, collectArgument (fuel + 1) (.var index) actual assignments = some updated ∧
      AssignmentsAgree candidate updated := by
  have previousMatches : previous = actual := by
    have candidatePrevious := agree index previous assigned
    exact Option.some.inj (candidatePrevious.symm.trans candidateAtIndex)
  exact ⟨assignments,
    collectArgument_repeated_variable_same fuel index previous actual assignments assigned
      previousMatches,
    agree⟩

theorem collectArgument_variable_complete (fuel index : Nat) (actual : Ty)
    (candidate : List Ty) (assignments : List (Option Ty))
    (sameLength : assignments.length = candidate.length)
    (agree : AssignmentsAgree candidate assignments)
    (indexBound : index < candidate.length)
    (candidateAtIndex : candidate[index]? = some actual) :
    ∃ updated, collectArgument (fuel + 1) (.var index) actual assignments = some updated ∧
      AssignmentsAgree candidate updated ∧ updated.length = assignments.length ∧
      updated[index]? = some (some actual) := by
  cases slot : assignments[index]? with
  | none =>
      have slot' : assignments.get? index = none := by
        rw [← indexed_lookup_eq_get?]
        exact slot
      have impossible : assignments.length ≤ index := List.get?_eq_none.mp slot'
      omega
  | some value =>
      cases value with
      | none =>
          refine ⟨assignments.set index (some actual),
            collectArgument_first_variable_capture fuel index actual assignments slot,
            AssignmentsAgree.set agree candidateAtIndex, ?_, ?_⟩
          · simp
          · have assignmentsBound : index < assignments.length := by omega
            have setBound : index < (assignments.set index (some actual)).length := by
              simpa [List.length_set] using assignmentsBound
            have atIndex := List.get_set_eq assignments index (some actual) setBound
            have found : (assignments.set index (some actual)).get? index = some (some actual) :=
              List.get?_eq_some.mpr ⟨setBound, atIndex⟩
            rw [indexed_lookup_eq_get?]
            exact found
      | some previous =>
          have previousMatches : previous = actual := by
            have candidatePrevious := agree index previous slot
            exact Option.some.inj (candidatePrevious.symm.trans candidateAtIndex)
          refine ⟨assignments,
            collectArgument_repeated_variable_same fuel index previous actual assignments slot
              previousMatches,
            agree, rfl, ?_⟩
          simpa [previousMatches] using slot

mutual
theorem collectArgument_complete (fuel : Nat) (pattern actual : Ty)
    (candidate : List Ty) (assignments : List (Option Ty))
    (sameLength : assignments.length = candidate.length)
    (agree : AssignmentsAgree candidate assignments)
    (patternWellFormed : pattern.wellFormed candidate.length)
    (instantiates : pattern.instantiate candidate = actual)
    (fuelBound : collectorTypeFuel pattern ≤ fuel) :
    ∃ updated, collectArgument fuel pattern actual assignments = some updated ∧
      AssignmentsAgree candidate updated ∧ updated.length = assignments.length ∧
      (∀ index, occurs fuel index pattern = true → ∀ value,
        candidate[index]? = some value → updated[index]? = some (some value)) := by
  cases fuel with
  | zero => cases pattern <;> simp [collectorTypeFuel, collectorTypesFuel] at fuelBound
  | succ fuel =>
    cases pattern with
    | boolean =>
        cases actual with
        | boolean =>
            exact ⟨assignments, by simp [Ty.instantiate, collectArgument], agree, rfl, by
              intro index occurrence value _
              simp [occurs] at occurrence⟩
        | integer | unit | var _ | fn _ _ | list _ | option _ =>
            simp [Ty.instantiate] at instantiates
    | integer =>
        cases actual with
        | integer =>
            exact ⟨assignments, by simp [Ty.instantiate, collectArgument], agree, rfl, by
              intro index occurrence value _
              simp [occurs] at occurrence⟩
        | boolean | unit | var _ | fn _ _ | list _ | option _ =>
            simp [Ty.instantiate] at instantiates
    | unit =>
        cases actual with
        | unit =>
            exact ⟨assignments, by simp [Ty.instantiate, collectArgument], agree, rfl, by
              intro index occurrence value _
              simp [occurs] at occurrence⟩
        | boolean | integer | var _ | fn _ _ | list _ | option _ =>
            simp [Ty.instantiate] at instantiates
    | var index =>
        have indexBound : index < candidate.length := by
          simpa [Ty.wellFormed] using patternWellFormed
        have candidateAtIndex : candidate[index]? = some actual := by
          simpa [Ty.instantiate, getElem?_def, indexBound] using instantiates
        obtain ⟨updated, collected, updatedAgree, updatedLength, slotCaptured⟩ :=
          collectArgument_variable_complete fuel index actual candidate assignments
            sameLength agree indexBound candidateAtIndex
        refine ⟨updated, collected, updatedAgree, updatedLength, ?_⟩
        intro queried occurrence value candidateAt
        have same : index = queried := by simpa [occurs] using occurrence
        subst queried
        have valueEq : actual = value := Option.some.inj (candidateAtIndex.symm.trans candidateAt)
        subst value
        exact slotCaptured
    | list element =>
        have elementWellFormed : element.wellFormed candidate.length := by
          simpa [Ty.wellFormed] using patternWellFormed
        cases actual with
        | list input =>
            have elementInstantiates : element.instantiate candidate = input := by
              simpa [Ty.instantiate] using instantiates
            have elementBound : collectorTypeFuel element ≤ fuel := by
              simp only [collectorTypeFuel] at fuelBound ⊢
              omega
            obtain ⟨updated, collected, updatedAgree, updatedLength, childCaptures⟩ :=
              collectArgument_complete fuel element input candidate assignments sameLength agree
                elementWellFormed elementInstantiates elementBound
            exact ⟨updated, by simpa [collectArgument] using collected,
              updatedAgree, updatedLength, by
                intro index occurrence value candidateAt
                apply childCaptures index (by simpa [occurs] using occurrence) value candidateAt⟩
        | boolean | integer | unit | var _ | fn _ _ | option _ =>
            simp [Ty.instantiate] at instantiates
    | option element =>
        have elementWellFormed : element.wellFormed candidate.length := by
          simpa [Ty.wellFormed] using patternWellFormed
        cases actual with
        | option input =>
            have elementInstantiates : element.instantiate candidate = input := by
              simpa [Ty.instantiate] using instantiates
            have elementBound : collectorTypeFuel element ≤ fuel := by
              simp only [collectorTypeFuel] at fuelBound ⊢
              omega
            obtain ⟨updated, collected, updatedAgree, updatedLength, childCaptures⟩ :=
              collectArgument_complete fuel element input candidate assignments sameLength agree
                elementWellFormed elementInstantiates elementBound
            exact ⟨updated, by simpa [collectArgument] using collected,
              updatedAgree, updatedLength, by
                intro index occurrence value candidateAt
                apply childCaptures index (by simpa [occurs] using occurrence) value candidateAt⟩
        | boolean | integer | unit | var _ | fn _ _ | list _ =>
            simp [Ty.instantiate] at instantiates
    | fn parameters result =>
        cases actual with
        | fn inputs output =>
            have instantiatedFn :
                Ty.fn (instantiateTypes candidate parameters) (result.instantiate candidate) =
                  Ty.fn inputs output := by
              simpa [Ty.instantiate] using instantiates
            have parts := Ty.fn.inj instantiatedFn
            have wfParts := patternWellFormed
            simp only [Ty.wellFormed] at wfParts
            have parametersWellFormed : ∀ t ∈ parameters, t.wellFormed candidate.length := by
              exact wfParts.1
            have resultWellFormed : result.wellFormed candidate.length := wfParts.2
            have parametersBound : collectorTypesFuel parameters ≤ fuel := by
              simp only [collectorTypeFuel, collectorTypesFuel] at fuelBound ⊢
              omega
            have resultBound : collectorTypeFuel result ≤ fuel := by
              simp only [collectorTypeFuel, collectorTypesFuel] at fuelBound ⊢
              omega
            obtain ⟨afterParameters, parametersCollected, parametersAgree,
                parametersLength, parametersCapture⟩ := collectArguments_complete fuel parameters inputs candidate
                  assignments sameLength agree parametersWellFormed parts.1 parametersBound
            have parametersCandidateLength : afterParameters.length = candidate.length :=
              parametersLength.trans sameLength
            obtain ⟨updated, resultCollected, updatedAgree, updatedLength, resultCapture⟩ :=
              collectArgument_complete fuel result output candidate afterParameters
                parametersCandidateLength parametersAgree resultWellFormed parts.2 resultBound
            exact ⟨updated, by simp [collectArgument, parametersCollected, resultCollected],
              updatedAgree, updatedLength.trans parametersLength, by
                intro index occurrence value candidateAt
                simp only [occurs, Bool.or_eq_true] at occurrence
                rcases occurrence with fromParameters | fromResult
                · have assignedAfterParameters := parametersCapture index fromParameters value candidateAt
                  exact collectArgument_preserves_assigned fuel result output afterParameters updated
                    resultCollected index value assignedAfterParameters
                · exact resultCapture index fromResult value candidateAt⟩
        | boolean | integer | unit | var _ | list _ | option _ =>
            simp [Ty.instantiate] at instantiates
termination_by fuel
decreasing_by all_goals simp_wf; omega

theorem collectArguments_complete (fuel : Nat) (patterns actuals : List Ty)
    (candidate : List Ty) (assignments : List (Option Ty))
    (sameLength : assignments.length = candidate.length)
    (agree : AssignmentsAgree candidate assignments)
    (patternsWellFormed : ∀ t ∈ patterns, t.wellFormed candidate.length)
    (instantiates : instantiateTypes candidate patterns = actuals)
    (fuelBound : collectorTypesFuel patterns ≤ fuel) :
    ∃ updated, collectArguments fuel patterns actuals assignments = some updated ∧
      AssignmentsAgree candidate updated ∧ updated.length = assignments.length ∧
      (∀ index, occursMany fuel index patterns = true → ∀ value,
        candidate[index]? = some value → updated[index]? = some (some value)) := by
  cases fuel with
  | zero => cases patterns <;> simp [collectorTypeFuel, collectorTypesFuel] at fuelBound
  | succ fuel =>
    cases patterns with
    | nil =>
        cases actuals with
        | nil =>
            exact ⟨assignments, by simp [collectArguments], agree, rfl, by
              intro index occurrence value _
              simp [occursMany] at occurrence⟩
        | cons actual rest => simp [instantiateTypes] at instantiates
    | cons pattern rest =>
        cases actuals with
        | nil => simp [instantiateTypes] at instantiates
        | cons actual actualRest =>
            have parts := List.cons.inj (by simpa [instantiateTypes] using instantiates)
            have patternWellFormed : pattern.wellFormed candidate.length :=
              patternsWellFormed pattern (by simp)
            have restWellFormed : ∀ t ∈ rest, t.wellFormed candidate.length := by
              intro t mem
              exact patternsWellFormed t (by simp [mem])
            have patternBound : collectorTypeFuel pattern ≤ fuel := by
              simp only [collectorTypeFuel, collectorTypesFuel] at fuelBound ⊢
              omega
            have restBound : collectorTypesFuel rest ≤ fuel := by
              simp only [collectorTypeFuel, collectorTypesFuel] at fuelBound ⊢
              omega
            obtain ⟨afterPattern, patternCollected, patternAgree, patternLength, patternCaptures⟩ :=
              collectArgument_complete fuel pattern actual candidate assignments sameLength agree
                patternWellFormed parts.1 patternBound
            have patternCandidateLength : afterPattern.length = candidate.length :=
              patternLength.trans sameLength
            obtain ⟨updated, restCollected, updatedAgree, updatedLength, restCaptures⟩ :=
              collectArguments_complete fuel rest actualRest candidate afterPattern
                patternCandidateLength patternAgree restWellFormed parts.2 restBound
            exact ⟨updated, by simp [collectArguments, patternCollected, restCollected],
              updatedAgree, updatedLength.trans patternLength, by
                intro index occurrence value candidateAt
                simp only [occursMany, Bool.or_eq_true] at occurrence
                rcases occurrence with fromPattern | fromRest
                · have assignedAfterPattern := patternCaptures index fromPattern value candidateAt
                  exact collectArguments_preserves_assigned fuel rest actualRest afterPattern updated
                    restCollected index value assignedAfterPattern
                · exact restCaptures index fromRest value candidateAt⟩
termination_by fuel
decreasing_by all_goals simp_wf; omega
end

structure TypeArgumentSolution (callerCount : Nat) (header : Header) (actuals : List Ty) where
  arguments : List Ty
  arity : arguments.length = header.variables.length
  valid : ∀ t ∈ arguments, t.wellFormed callerCount
  instantiates : instantiateTypes arguments (header.parameters.map Prod.snd) = actuals
  unique : ∀ other, other.length = header.variables.length →
    instantiateTypes other (header.parameters.map Prod.snd) = actuals → other = arguments

/- No expected return type is an input. Caller type variables appearing in
actuals are rigid syntax; they are never recursively solved or unified. -/
def inferTypeArguments (fuel callerCount : Nat) (header : Header) (actuals : List Ty) :
    Option (TypeArgumentSolution callerCount header actuals) := do
  if covered : inferrable fuel header = true then
    let assignments ← collectArguments fuel (header.parameters.map Prod.snd) actuals
      (List.replicate header.variables.length none)
    let arguments ← assignments.mapM (fun value => value)
    let valid ← checkTypesWF fuel callerCount arguments
    if arity : arguments.length = header.variables.length then
      if matched : instantiateTypes arguments (header.parameters.map Prod.snd) = actuals then
        pure ⟨arguments, arity, valid.down, matched, fun other otherArity otherMatches =>
          inferred_arguments_unique fuel header covered other arguments otherArity arity
            (otherMatches.trans matched.symm)⟩
      else none
    else none
  else none

theorem type_argument_solution_unique (first second : TypeArgumentSolution callerCount header actuals) :
    first.arguments = second.arguments := first.unique second.arguments second.arity second.instantiates |>.symm

end NLisp.Surface
