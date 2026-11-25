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

private theorem type_mem_of_indexed_lookup {types : List Ty} {index : Nat} {type : Ty}
    (found : types[index]? = some type) : type ∈ types := by
  induction types generalizing index with
  | nil =>
      have impossible : False := by simp [getElem?_def, Nat.not_lt_zero] at found
      exact impossible.elim
  | cons head tail ih =>
      cases index with
      | zero =>
          have same : head = type := by simpa [getElem?_def] using found
          subst type
          simp
      | succ index =>
          have tailFound : tail[index]? = some type := by
            simpa [getElem?_def, Nat.succ_lt_succ_iff] using found
          exact List.mem_cons_of_mem _ (ih tailFound)

theorem Ty.instantiate_rigidCallerVariable_wellFormed (arguments : List Ty)
    (callerCount index : Nat)
    (argumentsWellFormed : ∀ argument ∈ arguments, argument.wellFormed callerCount)
    (sourceWellFormed : index < arguments.length + callerCount) :
    (Ty.var index).instantiate arguments |>.wellFormed callerCount := by
  cases found : arguments[index]? with
  | some argument =>
      have member := type_mem_of_indexed_lookup found
      simpa [Ty.instantiate, found] using argumentsWellFormed argument member
  | none =>
      have beyond : arguments.length ≤ index := by
        by_cases bound : index < arguments.length
        · simp [getElem?_def, bound] at found
        · omega
      have remainingBound : index - arguments.length < callerCount := by omega
      simpa [Ty.instantiate, found, Ty.wellFormed] using remainingBound

theorem Ty.instantiate_wellFormed (arguments : List Ty) (type : Ty)
    (callerCount : Nat)
    (argumentsWellFormed : ∀ argument ∈ arguments, argument.wellFormed callerCount)
    (typeWellFormed : type.wellFormed (arguments.length + callerCount)) :
    (type.instantiate arguments).wellFormed callerCount := by
  refine Ty.rec
    (motive_1 := fun current =>
      current.wellFormed (arguments.length + callerCount) →
        (current.instantiate arguments).wellFormed callerCount)
    (motive_2 := fun types =>
      (∀ current ∈ types, current.wellFormed (arguments.length + callerCount)) →
        ∀ current ∈ instantiateTypes arguments types, current.wellFormed callerCount)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ type typeWellFormed
  · intro _
    simp [Ty.instantiate, Ty.wellFormed]
  · intro _
    simp [Ty.instantiate, Ty.wellFormed]
  · intro _
    simp [Ty.instantiate, Ty.wellFormed]
  · intro _
    simp [Ty.instantiate, Ty.wellFormed]
  · intro _
    simp [Ty.instantiate, Ty.wellFormed]
  · intro _
    simp [Ty.instantiate, Ty.wellFormed]
  · intro index sourceWellFormed
    exact Ty.instantiate_rigidCallerVariable_wellFormed arguments callerCount index
      argumentsWellFormed (by simpa [Ty.wellFormed] using sourceWellFormed)
  · intro parameters result parametersIH resultIH sourceWellFormed
    simp only [Ty.wellFormed] at sourceWellFormed
    rcases sourceWellFormed with ⟨parametersWellFormed, resultWellFormed⟩
    have parametersResult := parametersIH parametersWellFormed
    have resultResult := resultIH resultWellFormed
    simpa [Ty.instantiate, Ty.wellFormed] using And.intro parametersResult resultResult
  · intro element elementIH sourceWellFormed
    have elementWellFormed : element.wellFormed (arguments.length + callerCount) := by
      simpa [Ty.wellFormed] using sourceWellFormed
    simpa [Ty.instantiate, Ty.wellFormed] using elementIH elementWellFormed
  · intro element elementIH sourceWellFormed
    have elementWellFormed : element.wellFormed (arguments.length + callerCount) := by
      simpa [Ty.wellFormed] using sourceWellFormed
    simpa [Ty.instantiate, Ty.wellFormed] using elementIH elementWellFormed
  · intro _sourceWellFormed current member
    simp [instantiateTypes] at member
  · intro head tail headIH tailIH sourceWellFormed current member
    simp only [instantiateTypes, List.mem_cons] at member
    rcases member with same | tailMember
    · cases same
      exact headIH (sourceWellFormed head (by simp))
    · exact tailIH (by
        intro item itemMember
        exact sourceWellFormed item (by simp [itemMember])) current tailMember


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
      | boolean | integer | float | string | character | unit => simp [occurs] at occurrence
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
    | .float => if actual = .float then some assignments else none
    | .string => if actual = .string then some assignments else none
    | .character => if actual = .character then some assignments else none
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

private theorem indexed_lookup_eq_get? {α : Type} (values : List α) (index : Nat) :
    values[index]? = values.get? index := by
  induction values generalizing index with
  | nil => cases index <;> simp [getElem?_def]
  | cons head tail ih => cases index with
      | zero => simp [getElem?_def]
      | succ index => simpa [getElem?_def, Nat.succ_lt_succ_iff] using ih index

/-- A successful C-style constraint match leaves the matched quantified slot
assigned to the actual type, whether it filled an empty slot or agreed with a
previous argument. This is the local soundness fact used by the structural
`match_type` simulation. -/
theorem collectArgument_variable_success_captures (fuel index : Nat) (actual : Ty)
    (assignments updated : List (Option Ty))
    (collected : collectArgument (fuel + 1) (.var index) actual assignments = some updated) :
    updated[index]? = some (some actual) := by
  cases slot : assignments[index]? with
  | none => simp [collectArgument, slot] at collected
  | some entry =>
      cases entry with
      | none =>
          have resultEq : assignments.set index (some actual) = updated := by
            simpa [collectArgument, slot] using collected
          subst updated
          have bound : index < assignments.length := by
            have entry' : assignments.get? index = some none := by
              rw [← indexed_lookup_eq_get?]
              exact slot
            exact (List.get?_eq_some.mp entry').1
          have updatedBound : index < (assignments.set index (some actual)).length := by
            simpa [List.length_set] using bound
          have atIndex := List.get_set_eq assignments index (some actual) updatedBound
          have getEntry : (assignments.set index (some actual)).get? index = some (some actual) :=
            List.get?_eq_some.mpr ⟨updatedBound, atIndex⟩
          rw [indexed_lookup_eq_get?]
          exact getEntry
      | some previous =>
          have resultEq : assignments = updated := by
            simp [collectArgument, slot] at collected
            exact collected.2
          have sameActual : previous = actual := by
            simp [collectArgument, slot] at collected
            exact collected.1
          rw [← resultEq, ← sameActual]
          exact slot

/-- The C `match_type` function rejects a function type with a different
parameter count before checking its parameters. `collectArguments` expresses
the same arity guard by synchronously consuming both parameter lists; no
successful collection is possible when their lengths differ. -/
theorem collectArguments_arity_mismatch (fuel : Nat) (patterns actuals : List Ty)
    (assignments : List (Option Ty)) (different : patterns.length ≠ actuals.length) :
    collectArguments fuel patterns actuals assignments = none := by
  induction fuel generalizing patterns actuals assignments with
  | zero => rfl
  | succ fuel ihFuel =>
      induction patterns generalizing actuals assignments with
      | nil =>
          cases actuals with
          | nil => exact False.elim (different rfl)
          | cons actual tail => rfl
      | cons pattern tail _ihPatterns =>
          cases actuals with
          | nil => rfl
          | cons actual actualTail =>
              have tailDifferent : tail.length ≠ actualTail.length := by
                intro same
                apply different
                simp [same]
              simp only [collectArguments]
              cases collected : collectArgument fuel pattern actual assignments with
              | none => simp [collected]
              | some updated =>
                  simp [collected, ihFuel tail actualTail updated tailDifferent]

/-- Function-pattern specialization of the arity argument: after matching
function constructors, a parameter-count mismatch is rejected before the
result type is traversed, matching C's `pattern->arity != actual->arity`
guard in `match_type`. -/
theorem collectArgument_function_arity_mismatch (fuel : Nat)
    (patterns actuals : List Ty) (patternResult actualResult : Ty)
    (assignments : List (Option Ty)) (different : patterns.length ≠ actuals.length) :
    collectArgument (fuel + 1) (.fn patterns patternResult)
      (.fn actuals actualResult) assignments = none := by
  simp only [collectArgument]
  rw [collectArguments_arity_mismatch fuel patterns actuals assignments different]
  simp

/-- The converse direction of the C `match_type` function-arity guard: a
successful Lean constraint collection for function types certifies that the
parameter arrays had equal lengths. This records both rejection and
successful-branch behavior of C's `pattern->arity != actual->arity` check. -/
theorem collectArgument_function_success_same_arity (fuel : Nat)
    (patterns actuals : List Ty) (patternResult actualResult : Ty)
    (assignments : List (Option Ty))
    (accepted : (collectArgument (fuel + 1) (.fn patterns patternResult)
      (.fn actuals actualResult) assignments).isSome = true) :
    patterns.length = actuals.length := by
  by_cases same : patterns.length = actuals.length
  · exact same
  · have rejected := collectArgument_function_arity_mismatch fuel patterns actuals
      patternResult actualResult assignments same
    rw [rejected] at accepted
    simp at accepted

/- Structural resource bound for the collector. Function-parameter traversal and
the result-type traversal both start with the same remaining fuel, so the
function case adds their recursive costs. -/
mutual
def collectorTypeFuel (type : Ty) : Nat :=
  match type with
  | .boolean | .integer | .float | .string | .character | .unit | .var _ => 1
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
          | integer | float | string | character | unit | var _ | fn _ _ | list _ | option _ =>
              simp [collectArgument] at collected
      | integer =>
          cases actual with
          | integer =>
              have resultEq : assignments = updated := by simpa [collectArgument] using collected
              simpa [resultEq] using assigned
          | boolean | float | string | character | unit | var _ | fn _ _ | list _ | option _ =>
              simp [collectArgument] at collected
      | float =>
          cases actual with
          | float =>
              have resultEq : assignments = updated := by simpa [collectArgument] using collected
              simpa [resultEq] using assigned
          | boolean | integer | string | character | unit | var _ | fn _ _ | list _ | option _ =>
              simp [collectArgument] at collected
      | string =>
          cases actual with
          | string =>
              have resultEq : assignments = updated := by simpa [collectArgument] using collected
              simpa [resultEq] using assigned
          | boolean | integer | float | character | unit | var _ | fn _ _ | list _ | option _ =>
              simp [collectArgument] at collected
      | character =>
          cases actual with
          | character =>
              have resultEq : assignments = updated := by simpa [collectArgument] using collected
              simpa [resultEq] using assigned
          | boolean | integer | float | string | unit | var _ | fn _ _ | list _ | option _ =>
              simp [collectArgument] at collected
      | unit =>
          cases actual with
          | unit =>
              have resultEq : assignments = updated := by simpa [collectArgument] using collected
              simpa [resultEq] using assigned
          | boolean | float | integer | string | character | var _ | fn _ _ | list _ | option _ =>
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
          | boolean | integer | float | string | character | unit | var _ | fn _ _ | option _ =>
              simp [collectArgument] at collected
      | option element =>
          cases actual with
          | option input =>
              exact collectArgument_preserves_assigned fuel element input assignments updated
                (by simpa [collectArgument] using collected) index value assigned
          | boolean | integer | float | string | character | unit | var _ | fn _ _ | list _ =>
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
          | boolean | integer | float | string | character | unit | var _ | list _ | option _ =>
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

/- Absence of a quantified variable from a constraint guarantees that the
constraint cannot fill its assignment slot. This is the converse companion
to `collectArgument_preserves_assigned` and is used to derive the coverage
guard from complete C matcher assignments. -/
mutual
theorem collectArgument_preserves_empty_of_absent (fuel : Nat) (pattern actual : Ty)
    (assignments updated : List (Option Ty))
    (collected : collectArgument fuel pattern actual assignments = some updated)
    (index : Nat) (absent : occurs fuel index pattern = false)
    (empty : assignments[index]? = some none) :
    updated[index]? = some none := by
  cases fuel with
  | zero => simp [collectArgument] at collected
  | succ fuel =>
      cases pattern with
      | boolean =>
          cases actual with
          | boolean =>
              have same : assignments = updated := by simpa [collectArgument] using collected
              simpa [same] using empty
          | integer | float | string | character | unit | var _ | fn _ _ | list _ | option _ =>
              simp [collectArgument] at collected
      | integer =>
          cases actual with
          | integer =>
              have same : assignments = updated := by simpa [collectArgument] using collected
              simpa [same] using empty
          | boolean | float | string | character | unit | var _ | fn _ _ | list _ | option _ =>
              simp [collectArgument] at collected
      | float =>
          cases actual with
          | float =>
              have same : assignments = updated := by simpa [collectArgument] using collected
              simpa [same] using empty
          | boolean | integer | string | character | unit | var _ | fn _ _ | list _ | option _ =>
              simp [collectArgument] at collected
      | string =>
          cases actual with
          | string =>
              have same : assignments = updated := by simpa [collectArgument] using collected
              simpa [same] using empty
          | boolean | integer | float | character | unit | var _ | fn _ _ | list _ | option _ =>
              simp [collectArgument] at collected
      | character =>
          cases actual with
          | character =>
              have same : assignments = updated := by simpa [collectArgument] using collected
              simpa [same] using empty
          | boolean | integer | float | string | unit | var _ | fn _ _ | list _ | option _ =>
              simp [collectArgument] at collected
      | unit =>
          cases actual with
          | unit =>
              have same : assignments = updated := by simpa [collectArgument] using collected
              simpa [same] using empty
          | boolean | integer | float | string | character | var _ | fn _ _ | list _ | option _ =>
              simp [collectArgument] at collected
      | var patternIndex =>
          have different : patternIndex ≠ index := by
            intro same
            subst patternIndex
            simp [occurs] at absent
          cases slot : assignments[patternIndex]? with
          | none => simp [collectArgument, slot] at collected
          | some entry =>
              cases entry with
              | none =>
                  have resultEq : assignments.set patternIndex (some actual) = updated := by
                    simpa [collectArgument, slot] using collected
                  subst updated
                  exact indexed_set_preserves_other assignments patternIndex index
                    (some actual) none different empty
              | some previous =>
                  have resultEq : assignments = updated := by
                    simp [collectArgument, slot] at collected
                    exact collected.2
                  simpa [resultEq] using empty
      | list element =>
          cases actual with
          | list input =>
              exact collectArgument_preserves_empty_of_absent fuel element input assignments
                updated (by simpa [collectArgument] using collected) index
                (by simpa [occurs] using absent) empty
          | boolean | integer | float | string | character | unit | var _ | fn _ _ | option _ =>
              simp [collectArgument] at collected
      | option element =>
          cases actual with
          | option input =>
              exact collectArgument_preserves_empty_of_absent fuel element input assignments
                updated (by simpa [collectArgument] using collected) index
                (by simpa [occurs] using absent) empty
          | boolean | integer | float | string | character | unit | var _ | fn _ _ | list _ =>
              simp [collectArgument] at collected
      | fn parameters result =>
          cases actual with
          | fn inputs output =>
              have noPart : occursMany fuel index parameters = false ∧
                  occurs fuel index result = false := by
                cases hParameters : occursMany fuel index parameters <;>
                  cases hResult : occurs fuel index result <;>
                  simp [occurs, hParameters, hResult] at absent ⊢
              simp only [collectArgument] at collected
              cases first : collectArguments fuel parameters inputs assignments with
              | none => simp [first] at collected
              | some intermediate =>
                  have second : collectArgument fuel result output intermediate = some updated := by
                    simpa [first] using collected
                  have middleEmpty := collectArguments_preserves_empty_of_absent fuel
                    parameters inputs assignments intermediate first index noPart.1 empty
                  exact collectArgument_preserves_empty_of_absent fuel result output
                    intermediate updated second index noPart.2 middleEmpty
          | boolean | integer | float | string | character | unit | var _ | list _ | option _ =>
              simp [collectArgument] at collected
termination_by fuel
decreasing_by all_goals simp_wf; omega

theorem collectArguments_preserves_empty_of_absent (fuel : Nat)
    (patterns actuals : List Ty) (assignments updated : List (Option Ty))
    (collected : collectArguments fuel patterns actuals assignments = some updated)
    (index : Nat) (absent : occursMany fuel index patterns = false)
    (empty : assignments[index]? = some none) :
    updated[index]? = some none := by
  cases fuel with
  | zero => simp [collectArguments] at collected
  | succ fuel =>
      cases patterns with
      | nil =>
          cases actuals with
          | nil =>
              have same : assignments = updated := by simpa [collectArguments] using collected
              simpa [same] using empty
          | cons actual rest => simp [collectArguments] at collected
      | cons pattern rest =>
          cases actuals with
          | nil => simp [collectArguments] at collected
          | cons actual actualRest =>
              have noParts : occurs fuel index pattern = false ∧
                  occursMany fuel index rest = false := by
                cases hHead : occurs fuel index pattern <;>
                  cases hTail : occursMany fuel index rest <;>
                  simp [occursMany, hHead, hTail] at absent ⊢
              simp only [collectArguments] at collected
              cases first : collectArgument fuel pattern actual assignments with
              | none => simp [first] at collected
              | some intermediate =>
                  have second : collectArguments fuel rest actualRest intermediate = some updated := by
                    simpa [first] using collected
                  have middleEmpty := collectArgument_preserves_empty_of_absent fuel
                    pattern actual assignments intermediate first index noParts.1 empty
                  exact collectArguments_preserves_empty_of_absent fuel rest actualRest
                    intermediate updated second index noParts.2 middleEmpty
termination_by fuel
decreasing_by all_goals simp_wf; omega
end

/-- If left-to-right type collection starts with an empty slot and ends with
that slot assigned, some parameter constraint must have mentioned the
quantified variable. -/
theorem collectArguments_assigned_implies_occurs (fuel : Nat)
    (patterns actuals : List Ty) (assignments updated : List (Option Ty))
    (collected : collectArguments fuel patterns actuals assignments = some updated)
    (index : Nat) (value : Ty)
    (initiallyEmpty : assignments[index]? = some none)
    (finallyAssigned : updated[index]? = some (some value)) :
    occursMany fuel index patterns = true := by
  cases occurrence : occursMany fuel index patterns with
  | true => rfl
  | false =>
      have remainedEmpty := collectArguments_preserves_empty_of_absent fuel patterns actuals
        assignments updated collected index occurrence initiallyEmpty
      have contradiction : (some none : Option (Option Ty)) = some (some value) :=
        remainedEmpty.symm.trans finallyAssigned
      cases contradiction

/- These equations expose the same constraint update used by C's
`match_type`: the first occurrence stores the actual type verbatim; later
occurrences compare that stored type with the new actual. In particular, a
caller-side `Ty.var` is retained as rigid syntax and is never recursively
solved by this matcher. -/
theorem Ty.instantiate_rigidCallerVariable (arguments : List Ty) (index callerIndex : Nat)
    (captured : arguments[index]? = some (.var callerIndex)) :
    Ty.instantiate arguments (.var index) = .var callerIndex := by
  simp [Ty.instantiate, captured]

theorem collectArgument_first_variable_capture (fuel index : Nat) (actual : Ty)
    (assignments : List (Option Ty))
    (emptySlot : assignments[index]? = some none) :
    collectArgument (fuel + 1) (.var index) actual assignments =
      some (assignments.set index (some actual)) := by
  simp [collectArgument, emptySlot]

/-- The C `sub[index] = actual` branch changes only the matched quantified
variable's slot. This exposes the array-update behavior of `match_type` in
the list-based Lean assignment representation. -/
theorem collectArgument_first_variable_capture_effect (fuel index : Nat) (actual : Ty)
    (assignments : List (Option Ty))
    (emptySlot : assignments[index]? = some none) :
    collectArgument (fuel + 1) (.var index) actual assignments =
        some (assignments.set index (some actual)) ∧
      (assignments.set index (some actual))[index]? = some (some actual) ∧
      (∀ other value, other ≠ index → assignments[other]? = some value →
        (assignments.set index (some actual))[other]? = some value) := by
  refine ⟨collectArgument_first_variable_capture fuel index actual assignments emptySlot,
    ?_, ?_⟩
  · have bound : index < assignments.length := by
      have entry : assignments.get? index = some none := by
        rw [← indexed_lookup_eq_get?]
        exact emptySlot
      exact (List.get?_eq_some.mp entry).1
    have setBound : index < (assignments.set index (some actual)).length := by
      simpa [List.length_set] using bound
    have atIndex := List.get_set_eq assignments index (some actual) setBound
    have entry : (assignments.set index (some actual)).get? index = some (some actual) :=
      List.get?_eq_some.mpr ⟨by simpa using bound, atIndex⟩
    rw [indexed_lookup_eq_get?]
    exact entry
  · intro other value different original
    have original' : assignments.get? other = some value := by
      rw [← indexed_lookup_eq_get?]
      exact original
    obtain ⟨bound, atOther⟩ := List.get?_eq_some.mp original'
    have indicesNe : index ≠ other := Ne.symm different
    have setBound : other < (assignments.set index (some actual)).length := by
      simpa [List.length_set] using bound
    have unchanged := List.get_set_ne assignments indicesNe (some actual) setBound
    have result : (assignments.set index (some actual)).get? other = some value :=
      List.get?_eq_some.mpr ⟨setBound, unchanged.trans atOther⟩
    rw [indexed_lookup_eq_get?]
    exact result

/-- Across the C-style left-to-right call-argument loop, a caller-side type
variable captured by the first quantified occurrence remains stored verbatim
after every later argument has been checked. This composes the `sub[index] =
actual` branch with the no-overwrite property of subsequent constraints. -/
theorem collectArguments_keeps_first_caller_variable_capture
    (fuel index callerIndex : Nat) (patterns actuals : List Ty)
    (assignments final : List (Option Ty))
    (emptySlot : assignments[index]? = some none)
    (collected : collectArguments (fuel + 2)
      (.var index :: patterns) (.var callerIndex :: actuals) assignments = some final) :
    final[index]? = some (some (.var callerIndex)) := by
  have firstCollected :
      collectArgument (fuel + 1) (.var index) (.var callerIndex) assignments =
        some (assignments.set index (some (.var callerIndex))) :=
    collectArgument_first_variable_capture fuel index (.var callerIndex) assignments emptySlot
  have tailCollected :
      collectArguments (fuel + 1) patterns actuals
        (assignments.set index (some (.var callerIndex))) = some final := by
    simp only [collectArguments] at collected
    rw [firstCollected] at collected
    simpa using collected
  have captured :
      (assignments.set index (some (.var callerIndex)))[index]? =
        some (some (.var callerIndex)) :=
    (collectArgument_first_variable_capture_effect fuel index (.var callerIndex)
      assignments emptySlot).2.1
  exact collectArguments_preserves_assigned (fuel + 1) patterns actuals
    (assignments.set index (some (.var callerIndex))) final tailCollected index
    (.var callerIndex) captured

/-- A caller-side type variable remains rigid when the callee's quantified
variable occurs under a function constructor, matching the recursive
`TY_FUN`/parameter-array path in C's `match_type` and `check_call`. -/
theorem collectArgument_function_parameter_captures_caller_variable
    (fuel callerIndex : Nat) (assignments : List (Option Ty))
    (emptySlot : assignments[0]? = some none) :
    collectArgument (fuel + 3)
      (.fn [.var 0] .unit) (.fn [.var callerIndex] .unit) assignments =
      some (assignments.set 0 (some (.var callerIndex))) := by
  simp [collectArgument, collectArguments, collectArgument_first_variable_capture,
    emptySlot]

/-- C rejects a call when repeated appearances of one quantified type
variable constrain it to different actual argument types. This lifts the
single-slot conflict equation through the left-to-right function-parameter
array traversal. -/
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

/-- C rejects a call when repeated appearances of one quantified type
variable constrain it to different actual argument types. This lifts the
single-slot conflict equation through the left-to-right function-parameter
array traversal. -/
theorem collectArguments_repeated_variable_conflict (fuel : Nat) :
    collectArguments (fuel + 3) [.var 0, .var 0] [.integer, .boolean] [none] = none := by
  simp [collectArguments, collectArgument, getElem?_def,
    collectArgument_repeated_variable_conflict]

def AssignmentsAgree (candidate : List Ty) (assignments : List (Option Ty)) : Prop :=
  ∀ (index : Nat) (value : Ty), assignments[index]? = some (some value) →
    candidate[index]? = some value

/- A successful collection is sound as a substitution: applying the
candidate substitution to the pattern reproduces the actual type. The list
case composes left-to-right updates; preservation of assigned slots lets the
final assignment agreement be used at each earlier recursive step. -/
mutual
theorem collectArgument_sound (fuel : Nat) (pattern actual : Ty)
    (candidate : List Ty) (assignments updated : List (Option Ty))
    (patternWellFormed : pattern.wellFormed candidate.length)
    (collected : collectArgument fuel pattern actual assignments = some updated)
    (updatedAgree : AssignmentsAgree candidate updated) :
    pattern.instantiate candidate = actual := by
  cases fuel with
  | zero => simp [collectArgument] at collected
  | succ fuel =>
      cases pattern with
      | boolean => cases actual <;> simp [collectArgument, Ty.instantiate] at collected ⊢
      | integer => cases actual <;> simp [collectArgument, Ty.instantiate] at collected ⊢
      | float => cases actual <;> simp [collectArgument, Ty.instantiate] at collected ⊢
      | string => cases actual <;> simp [collectArgument, Ty.instantiate] at collected ⊢
      | character => cases actual <;> simp [collectArgument, Ty.instantiate] at collected ⊢
      | unit => cases actual <;> simp [collectArgument, Ty.instantiate] at collected ⊢
      | var index =>
          have indexBound : index < candidate.length := by
            simpa [Ty.wellFormed] using patternWellFormed
          have captured := collectArgument_variable_success_captures fuel index actual
            assignments updated collected
          have candidateAtIndex := updatedAgree index actual captured
          simpa [Ty.instantiate, getElem?_def, indexBound] using candidateAtIndex
      | list element =>
          have elementWellFormed : element.wellFormed candidate.length := by
            simpa [Ty.wellFormed] using patternWellFormed
          cases actual with
          | list input =>
              have childCollected : collectArgument fuel element input assignments = some updated := by
                simpa [collectArgument] using collected
              have childSound := collectArgument_sound fuel element input candidate assignments
                updated elementWellFormed childCollected updatedAgree
              simpa [Ty.instantiate] using congrArg Ty.list childSound
          | boolean | integer | float | string | character | unit | var _ | fn _ _ | option _ =>
              simp [collectArgument] at collected
      | option element =>
          have elementWellFormed : element.wellFormed candidate.length := by
            simpa [Ty.wellFormed] using patternWellFormed
          cases actual with
          | option input =>
              have childCollected : collectArgument fuel element input assignments = some updated := by
                simpa [collectArgument] using collected
              have childSound := collectArgument_sound fuel element input candidate assignments
                updated elementWellFormed childCollected updatedAgree
              simpa [Ty.instantiate] using congrArg Ty.option childSound
          | boolean | integer | float | string | character | unit | var _ | fn _ _ | list _ =>
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
                  have intermediateAgree : AssignmentsAgree candidate intermediate := by
                    intro index value assigned
                    have survives := collectArgument_preserves_assigned fuel result output
                      intermediate updated second index value assigned
                    exact updatedAgree index value survives
                  have fnWellFormed : (∀ type ∈ parameters,
                      type.wellFormed candidate.length) ∧ result.wellFormed candidate.length := by
                    simpa [Ty.wellFormed] using patternWellFormed
                  have parameterWellFormed : ∀ type ∈ parameters,
                      type.wellFormed candidate.length := by
                    exact fnWellFormed.1
                  have resultWellFormed : result.wellFormed candidate.length := by
                    exact fnWellFormed.2
                  have parametersSound := collectArguments_sound fuel parameters inputs candidate
                    assignments intermediate parameterWellFormed first intermediateAgree
                  have resultSound := collectArgument_sound fuel result output candidate
                    intermediate updated resultWellFormed second updatedAgree
                  simp only [Ty.instantiate]
                  rw [parametersSound, resultSound]
          | boolean | integer | float | string | character | unit | var _ | list _ | option _ =>
              simp [collectArgument] at collected
termination_by fuel
decreasing_by all_goals simp_wf; omega

theorem collectArguments_sound (fuel : Nat) (patterns actuals : List Ty)
    (candidate : List Ty) (assignments updated : List (Option Ty))
    (patternsWellFormed : ∀ type ∈ patterns, type.wellFormed candidate.length)
    (collected : collectArguments fuel patterns actuals assignments = some updated)
    (updatedAgree : AssignmentsAgree candidate updated) :
    instantiateTypes candidate patterns = actuals := by
  cases fuel with
  | zero => simp [collectArguments] at collected
  | succ fuel =>
      cases patterns with
      | nil =>
          cases actuals with
          | nil => rfl
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
                  have intermediateAgree : AssignmentsAgree candidate intermediate := by
                    intro index value assigned
                    have survives := collectArguments_preserves_assigned fuel rest actualRest
                      intermediate updated second index value assigned
                    exact updatedAgree index value survives
                  have headWellFormed := patternsWellFormed pattern (by simp)
                  have tailWellFormed : ∀ type ∈ rest, type.wellFormed candidate.length := by
                    intro type member
                    exact patternsWellFormed type (by simp [member])
                  have headSound := collectArgument_sound fuel pattern actual candidate
                    assignments intermediate headWellFormed first intermediateAgree
                  have tailSound := collectArguments_sound fuel rest actualRest candidate
                    intermediate updated tailWellFormed second updatedAgree
                  simp only [instantiateTypes]
                  rw [headSound, tailSound]
termination_by fuel
decreasing_by all_goals simp_wf; omega
end

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
        | integer | float | string | character | unit | var _ | fn _ _ | list _ | option _ =>
            simp [Ty.instantiate] at instantiates
    | integer =>
        cases actual with
        | integer =>
            exact ⟨assignments, by simp [Ty.instantiate, collectArgument], agree, rfl, by
              intro index occurrence value _
              simp [occurs] at occurrence⟩
        | boolean | float | string | character | unit | var _ | fn _ _ | list _ | option _ =>
            simp [Ty.instantiate] at instantiates
    | float =>
        cases actual with
        | float =>
            exact ⟨assignments, by simp [Ty.instantiate, collectArgument], agree, rfl, by
              intro index occurrence value _
              simp [occurs] at occurrence⟩
        | boolean | integer | string | character | unit | var _ | fn _ _ | list _ | option _ =>
            simp [Ty.instantiate] at instantiates
    | string =>
        cases actual with
        | string =>
            exact ⟨assignments, by simp [Ty.instantiate, collectArgument], agree, rfl, by
              intro index occurrence value _
              simp [occurs] at occurrence⟩
        | boolean | integer | float | character | unit | var _ | fn _ _ | list _ | option _ =>
            simp [Ty.instantiate] at instantiates
    | character =>
        cases actual with
        | character =>
            exact ⟨assignments, by simp [Ty.instantiate, collectArgument], agree, rfl, by
              intro index occurrence value _
              simp [occurs] at occurrence⟩
        | boolean | integer | float | string | unit | var _ | fn _ _ | list _ | option _ =>
            simp [Ty.instantiate] at instantiates
    | unit =>
        cases actual with
        | unit =>
            exact ⟨assignments, by simp [Ty.instantiate, collectArgument], agree, rfl, by
              intro index occurrence value _
              simp [occurs] at occurrence⟩
        | boolean | float | integer | string | character | var _ | fn _ _ | list _ | option _ =>
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
        | boolean | integer | float | string | character | unit | var _ | fn _ _ | option _ =>
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
        | boolean | integer | float | string | character | unit | var _ | fn _ _ | list _ =>
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
        | boolean | integer | float | string | character | unit | var _ | list _ | option _ =>
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

/-- If every quantified candidate occurs in the parameter patterns, a
successful candidate-directed collection fills every slot.  This is the
assignment-vector fact used by inference after it rejects unresolved type
variables. -/
theorem collectArguments_complete_assignments_eq_candidate
    (fuel : Nat) (patterns actuals candidate : List Ty)
    (assignments : List (Option Ty))
    (sameLength : assignments.length = candidate.length)
    (agree : AssignmentsAgree candidate assignments)
    (patternsWellFormed : ∀ t ∈ patterns, t.wellFormed candidate.length)
    (instantiates : instantiateTypes candidate patterns = actuals)
    (fuelBound : collectorTypesFuel patterns ≤ fuel)
    (everyCandidateOccurs : ∀ index, index < candidate.length →
      occursMany fuel index patterns = true) :
    ∃ updated, collectArguments fuel patterns actuals assignments = some updated ∧
      updated = candidate.map some := by
  obtain ⟨updated, collected, _updatedAgree, updatedLength, captures⟩ :=
    collectArguments_complete fuel patterns actuals candidate assignments sameLength agree
      patternsWellFormed instantiates fuelBound
  have assignmentsEq : updated = candidate.map some := by
    apply List.ext_get (by simp [updatedLength, sameLength])
    intro index updatedBound candidateBound
    have indexBound : index < candidate.length := by
      simpa using candidateBound
    have candidateAtIndex : candidate[index]? = some (candidate[index]'indexBound) := by
      simp [getElem?_def, indexBound]
    have captured := captures index (everyCandidateOccurs index indexBound)
      (candidate[index]'indexBound) candidateAtIndex
    simpa [getElem?_def, updatedBound, candidateBound] using captured
  exact ⟨updated, collected, assignmentsEq⟩

structure TypeArgumentSolution (callerCount : Nat) (header : Header) (actuals : List Ty) where
  arguments : List Ty
  arity : arguments.length = header.variables.length
  valid : ∀ t ∈ arguments, t.wellFormed callerCount
  instantiates : instantiateTypes arguments (header.parameters.map Prod.snd) = actuals
  unique : ∀ other, other.length = header.variables.length →
    instantiateTypes other (header.parameters.map Prod.snd) = actuals → other = arguments

theorem TypeArgumentSolution.instantiated_result_wellFormed
    (solution : TypeArgumentSolution callerCount header actuals)
    (resultWellFormed : header.result.wellFormed
      (header.variables.length + callerCount)) :
    header.result.instantiate solution.arguments |>.wellFormed callerCount := by
  have resultTypeWellFormed :
      header.result.wellFormed (solution.arguments.length + callerCount) := by
    rw [solution.arity]
    exact resultWellFormed
  exact Ty.instantiate_wellFormed solution.arguments header.result callerCount
    solution.valid resultTypeWellFormed

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

/-- Boundary theorem for C `check_call`: successful left-to-right argument
constraint collection yields the unique substitution, and only then is that
substitution applied to the declared result type. No expected result type is
consulted. -/
theorem inferTypeArguments_success_result
    (fuel callerCount : Nat) (header : Header) (actuals : List Ty)
    (accepted : (inferTypeArguments fuel callerCount header actuals).isSome = true)
    (resultWellFormed : header.result.wellFormed
      (header.variables.length + callerCount)) :
    ∃ solution : TypeArgumentSolution callerCount header actuals,
      inferTypeArguments fuel callerCount header actuals = some solution ∧
      (header.result.instantiate solution.arguments).wellFormed callerCount ∧
      (header.result.instantiate solution.arguments : Ty) =
        Ty.instantiate solution.arguments header.result := by
  cases inferred : inferTypeArguments fuel callerCount header actuals with
  | none => simp [inferred] at accepted
  | some solution =>
      exact ⟨solution, by simpa [inferred],
        solution.instantiated_result_wellFormed resultWellFormed, rfl⟩

/-- For two successful C-style call-argument inferences, the inferred
substitution is determined by the quantified-variable list and parameter
types alone. Different declared result types and function bodies cannot
change the substitution selected before C calls `substitute_type` on the
result. -/
theorem inferTypeArguments_success_arguments_determined_by_parameters
    (fuel callerCount : Nat) (firstHeader secondHeader : Header) (actuals : List Ty)
    (sameVariables : firstHeader.variables = secondHeader.variables)
    (sameParameters : firstHeader.parameters.map Prod.snd =
      secondHeader.parameters.map Prod.snd)
    (first : TypeArgumentSolution callerCount firstHeader actuals)
    (firstAccepted : inferTypeArguments fuel callerCount firstHeader actuals = some first)
    (second : TypeArgumentSolution callerCount secondHeader actuals) :
    (secondAccepted : inferTypeArguments fuel callerCount secondHeader actuals = some second) →
    first.arguments = second.arguments := by
  intro _secondAccepted
  have covered : inferrable fuel firstHeader = true := by
    cases check : inferrable fuel firstHeader with
    | false =>
        simp [inferTypeArguments, check] at firstAccepted
    | true => rfl
  have secondArity : second.arguments.length = firstHeader.variables.length := by
    rw [sameVariables]
    exact second.arity
  have secondInstantiates :
      instantiateTypes second.arguments (firstHeader.parameters.map Prod.snd) = actuals := by
    rw [sameParameters]
    exact second.instantiates
  exact inferred_arguments_unique fuel firstHeader covered first.arguments second.arguments
    first.arity secondArity (first.instantiates.trans secondInstantiates.symm)

theorem type_argument_solution_unique (first second : TypeArgumentSolution callerCount header actuals) :
    first.arguments = second.arguments := first.unique second.arguments second.arity second.instantiates |>.symm

end NLisp.Surface
