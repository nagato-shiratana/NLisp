import NLisp.CTypeArguments
import NLisp.CheckerCompleteness

namespace NLisp.Surface
open ExpansionLowering

private theorem range_loop_member_bound (count index : Nat) (acc : List Nat)
    (member : index ∈ List.range.loop count acc) : index < count ∨ index ∈ acc := by
  induction count generalizing acc with
  | zero => simp [List.range.loop] at member; exact Or.inr member
  | succ count ih =>
      have smaller := ih (count :: acc) (by simpa [List.range.loop] using member)
      rcases smaller with bound | inAcc
      · by_cases same : index = count
        · omega
        · exact Or.inl (by omega)
      · simp only [List.mem_cons] at inAcc
        rcases inAcc with same | inAcc
        · subst index
          exact Or.inl (Nat.lt_succ_self count)
        · exact Or.inr inAcc

private theorem range_member_lt (count index : Nat)
    (member : index ∈ List.range count) : index < count := by
  simp only [List.range] at member
  rcases range_loop_member_bound count index [] member with bound | impossible
  · exact bound
  · simp at impossible

private theorem replicate_getElem_eq {α : Type} (count index : Nat) (value : α)
    (bound : index < count) : (List.replicate count value)[index]'(by simp; omega) = value := by
  induction count generalizing index with
  | zero => omega
  | succ count ih =>
      cases index with
      | zero => simp [List.replicate]
      | succ index => simpa [List.replicate] using ih index (by omega)

/-- Under the same parameter types and quantified arity, C's successful
matcher plus its unresolved-slot rejection produces exactly the argument
vector accepted by Lean's executable one-way inference. The parameter,
caller-scope and checker-fuel conditions make the C/Lean representation
boundary explicit. -/
theorem cMatchTypes_success_agrees_with_inferTypeArguments
    (callerPointers scheme : List Nat) (fuel : Nat)
    (patterns actuals : List CTypeNode) (patternTypes actualTypes : List Ty)
    (header : Header) (result : CTypeNode)
    (patternsDecoded : decodeCTypes scheme patterns = some patternTypes)
    (actualsDecoded : decodeCTypes callerPointers actuals = some actualTypes)
    (actualsMonotype : cMonotypes actuals = true)
    (headerArity : header.variables.length = scheme.length)
    (headerParameters : header.parameters.map Prod.snd = patternTypes)
    (inferrable : inferrable fuel header = true)
    (collectorEnough : collectorTypesFuel patternTypes ≤ fuel)
    (checkerEnough : ∀ candidate, candidate.length = scheme.length →
      checkerTypesFuel candidate ≤ fuel)
    (cFinal : List (Option CTypeNode))
    (matched : cMatchTypes fuel scheme patterns actuals
      (List.replicate scheme.length (none : Option CTypeNode)) = some cFinal)
    (allAssigned : cFinal.length = scheme.length ∧
      ∀ index, index < scheme.length →
        ∃ ctype, cFinal[index]? = some (some ctype))
    (resultDecoded : decodeCType scheme result = some header.result) :
    ∃ solution output,
      inferTypeArguments fuel callerPointers.length header actualTypes = some solution ∧
      cSubstituteType scheme (cFinal.map (Option.getD · .unit)) result = some output ∧
      decodeCType callerPointers output =
        some (header.result.instantiate solution.arguments) := by
  obtain ⟨candidate, output, candidateArity, candidateValid, candidateMatches,
      substituted, resultAgreement⟩ :=
    cMatchTypes_success_infers_arguments_and_substitutes_result callerPointers scheme fuel
      patterns actuals patternTypes actualTypes patternsDecoded actualsDecoded actualsMonotype
      cFinal matched allAssigned result header.result resultDecoded
  have arity : candidate.length = header.variables.length := by
    rw [headerArity]
    exact candidateArity
  have parametersWellFormed : ∀ type ∈ header.parameters.map Prod.snd,
      type.wellFormed header.variables.length := by
    intro type member
    have decodedWellFormed : type.wellFormed scheme.length :=
      decodeCTypes_wellFormed scheme patterns patternTypes patternsDecoded type
        (by simpa [headerParameters] using member)
    simpa [headerArity] using decodedWellFormed
  have headerCandidateMatches :
      instantiateTypes candidate (header.parameters.map Prod.snd) = actualTypes := by
    rw [headerParameters]
    exact candidateMatches
  have headerCollectorEnough :
      collectorTypesFuel (header.parameters.map Prod.snd) ≤ fuel := by
    rw [headerParameters]
    exact collectorEnough
  obtain ⟨solution, inferred⟩ := inferTypeArguments_complete_from_candidate fuel
    callerPointers.length header actualTypes candidate inferrable arity candidateValid
    parametersWellFormed headerCandidateMatches headerCollectorEnough
    (checkerEnough candidate candidateArity)
  have candidateIsSolution : candidate = solution.arguments :=
    solution.unique candidate arity headerCandidateMatches
  exact ⟨solution, output, inferred, substituted,
    by simpa [candidateIsSolution] using resultAgreement⟩

/-- A complete successful C matcher assignment implies that every quantified
variable occurred in the decoded parameter constraints. Consequently Lean's
`inferrable` guard follows from C's unresolved-slot check rather than being an
independent premise. -/
theorem cMatchTypes_success_agrees_with_inferTypeArguments_of_all_slots
    (callerPointers scheme : List Nat) (fuel : Nat)
    (patterns actuals : List CTypeNode) (patternTypes actualTypes : List Ty)
    (header : Header) (result : CTypeNode)
    (patternsDecoded : decodeCTypes scheme patterns = some patternTypes)
    (actualsDecoded : decodeCTypes callerPointers actuals = some actualTypes)
    (actualsMonotype : cMonotypes actuals = true)
    (headerArity : header.variables.length = scheme.length)
    (headerParameters : header.parameters.map Prod.snd = patternTypes)
    (collectorEnough : collectorTypesFuel patternTypes ≤ fuel)
    (checkerEnough : ∀ candidate, candidate.length = scheme.length →
      checkerTypesFuel candidate ≤ fuel)
    (cFinal : List (Option CTypeNode))
    (matched : cMatchTypes fuel scheme patterns actuals
      (List.replicate scheme.length (none : Option CTypeNode)) = some cFinal)
    (allAssigned : cFinal.length = scheme.length ∧
      ∀ index, index < scheme.length →
        ∃ ctype, cFinal[index]? = some (some ctype))
    (resultDecoded : decodeCType scheme result = some header.result) :
    ∃ solution output,
      inferTypeArguments fuel callerPointers.length header actualTypes = some solution ∧
      cSubstituteType scheme (cFinal.map (Option.getD · .unit)) result = some output ∧
      decodeCType callerPointers output =
        some (header.result.instantiate solution.arguments) := by
  obtain ⟨leanFinal, collected, stateAgree⟩ :=
    (cMatchType_and_types_state_simulation fuel).2 scheme callerPointers patterns actuals
      patternTypes actualTypes (List.replicate scheme.length none)
      (List.replicate scheme.length none) cFinal actualsMonotype patternsDecoded actualsDecoded
      (cSubstitutionStateAgree_initial_empty callerPointers scheme) matched
  have everyLeanSlotAssigned : ∀ index, index < scheme.length →
      ∃ type, leanFinal[index]? = some (some type) := by
    intro index bound
    obtain ⟨ctype, cAssigned⟩ := allAssigned.2 index bound
    rcases stateAgree.2.2 index bound with empty | assigned
    · have contradiction : (some none : Option (Option CTypeNode)) = some (some ctype) :=
        empty.1.symm.trans cAssigned
      cases contradiction
    · obtain ⟨_ctype, type, _cFound, leanFound, _decoded⟩ := assigned
      exact ⟨type, leanFound⟩
  have inferrableCondition : inferrable fuel header = true := by
    unfold inferrable
    apply List.all_eq_true.mpr
    intro index member
    have headerBound : index < header.variables.length :=
      range_member_lt header.variables.length index member
    have slotBound : index < scheme.length := by omega
    obtain ⟨type, assigned⟩ := everyLeanSlotAssigned index slotBound
    have initiallyEmpty :
        (List.replicate scheme.length (none : Option Ty))[index]? = some none := by
      have replicateBound : index <
          (List.replicate scheme.length (none : Option Ty)).length := by simp; exact slotBound
      have entry : (List.replicate scheme.length (none : Option Ty))[index]'replicateBound = none :=
        replicate_getElem_eq scheme.length index none slotBound
      simp only [getElem?_def, dif_pos replicateBound, entry]
    have occurs := collectArguments_assigned_implies_occurs fuel patternTypes actualTypes
      (List.replicate scheme.length (none : Option Ty)) leanFinal collected index type
      initiallyEmpty assigned
    simpa [headerParameters] using occurs
  exact cMatchTypes_success_agrees_with_inferTypeArguments callerPointers scheme fuel
    patterns actuals patternTypes actualTypes header result patternsDecoded actualsDecoded
    actualsMonotype headerArity headerParameters inferrableCondition collectorEnough
    checkerEnough cFinal matched allAssigned resultDecoded

/-- The monomorphic `check_call` case needs no separate inference-coverage or
unassigned-slot premise: with an empty quantified pointer array, there are no
slots for C to leave unresolved, and Lean's `inferrable` guard is immediate. -/
theorem cMatchTypes_monomorphic_success_agrees_with_inferTypeArguments
    (callerPointers scheme : List Nat) (fuel : Nat)
    (patterns actuals : List CTypeNode) (patternTypes actualTypes : List Ty)
    (header : Header) (result : CTypeNode)
    (schemeEmpty : scheme = [])
    (patternsDecoded : decodeCTypes scheme patterns = some patternTypes)
    (actualsDecoded : decodeCTypes callerPointers actuals = some actualTypes)
    (actualsMonotype : cMonotypes actuals = true)
    (headerArity : header.variables.length = scheme.length)
    (headerParameters : header.parameters.map Prod.snd = patternTypes)
    (collectorEnough : collectorTypesFuel patternTypes ≤ fuel)
    (checkerEnough : ∀ candidate, candidate.length = scheme.length →
      checkerTypesFuel candidate ≤ fuel)
    (cFinal : List (Option CTypeNode))
    (matched : cMatchTypes fuel scheme patterns actuals
      (List.replicate scheme.length (none : Option CTypeNode)) = some cFinal)
    (resultDecoded : decodeCType scheme result = some header.result) :
    ∃ solution output,
      inferTypeArguments fuel callerPointers.length header actualTypes = some solution ∧
      cSubstituteType scheme
        (cFinal.map (Option.getD · .unit)) result = some output ∧
      decodeCType callerPointers output =
        some (header.result.instantiate solution.arguments) := by
  have variablesEmpty : header.variables = [] := by
    apply List.eq_nil_of_length_eq_zero
    simpa [schemeEmpty] using headerArity
  have coverage : inferrable fuel header = true := by
    unfold ExpansionLowering.inferrable
    change (List.range header.variables.length).all
      (fun i => occursMany fuel i (header.parameters.map Prod.snd)) = true
    rw [variablesEmpty]
    rfl
  have allAssigned : cFinal.length = scheme.length ∧
      ∀ index, index < scheme.length →
        ∃ ctype, cFinal[index]? = some (some ctype) := by
    have initialState := cSubstitutionStateAgree_initial_empty callerPointers scheme
    obtain ⟨leanFinal, _collected, finalState⟩ :=
      (cMatchType_and_types_state_simulation fuel).2 scheme callerPointers patterns actuals
        patternTypes actualTypes (List.replicate scheme.length none)
        (List.replicate scheme.length none) cFinal actualsMonotype patternsDecoded actualsDecoded
        initialState matched
    constructor
    · simpa [schemeEmpty] using finalState.1
    · intro index bound
      have indexBound : index < 0 := by simpa [schemeEmpty] using bound
      omega
  exact cMatchTypes_success_agrees_with_inferTypeArguments callerPointers scheme fuel
    patterns actuals patternTypes actualTypes header result patternsDecoded actualsDecoded
    actualsMonotype (by simpa [schemeEmpty] using headerArity) headerParameters coverage
    collectorEnough checkerEnough cFinal matched allAssigned resultDecoded

end NLisp.Surface
