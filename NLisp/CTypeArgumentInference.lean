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
    cMatchTypes_success_infers_arguments_and_substitutes_result_of_decoded_actuals
      callerPointers scheme fuel patterns actuals patternTypes actualTypes
      patternsDecoded actualsDecoded
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
  have actualsMonotype := decodeCTypes_success_are_monotypes callerPointers actuals
    actualTypes actualsDecoded
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
    headerArity headerParameters inferrableCondition collectorEnough
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
    have actualsMonotype := decodeCTypes_success_are_monotypes callerPointers actuals
      actualTypes actualsDecoded
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
    (by simpa [schemeEmpty] using headerArity) headerParameters coverage
    collectorEnough checkerEnough cFinal matched allAssigned resultDecoded

/-- The successful polymorphic `check_call` path includes both C's explicit
arity guard and its left-to-right matcher. This records the arity fact that
is implicit in matcher success alongside Lean's inferred arguments and the
substituted result type. -/
theorem cCheckCall_success_agrees_with_inferTypeArguments
    (callerPointers scheme : List Nat) (fuel : Nat)
    (patterns actuals : List CTypeNode) (patternTypes actualTypes : List Ty)
    (header : Header) (result : CTypeNode)
    (patternsDecoded : decodeCTypes scheme patterns = some patternTypes)
    (actualsDecoded : decodeCTypes callerPointers actuals = some actualTypes)
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
    patterns.length = actuals.length ∧
    ∃ solution output,
      inferTypeArguments fuel callerPointers.length header actualTypes = some solution ∧
      cSubstituteType scheme (cFinal.map (Option.getD · .unit)) result = some output ∧
      decodeCType callerPointers output =
        some (header.result.instantiate solution.arguments) := by
  have matchedArity : patterns.length = actuals.length := by
    by_cases arity : patterns.length = actuals.length
    · exact arity
    · have rejected := cMatchTypes_arity_mismatch fuel scheme patterns actuals
        (List.replicate scheme.length (none : Option CTypeNode)) arity
      rw [matched] at rejected
      contradiction
  refine ⟨matchedArity, ?_⟩
  exact cMatchTypes_success_agrees_with_inferTypeArguments_of_all_slots
    callerPointers scheme fuel patterns actuals patternTypes actualTypes header result
    patternsDecoded actualsDecoded headerArity headerParameters
    collectorEnough checkerEnough cFinal matched allAssigned resultDecoded

/-- The same successful C call check also establishes caller-scope safety of
the substituted result type. This records the postcondition of C's
`substitute_type` step alongside argument inference and result decoding. -/
theorem cCheckCall_success_resultWellFormed
    (callerPointers scheme : List Nat) (fuel : Nat)
    (patterns actuals : List CTypeNode) (patternTypes actualTypes : List Ty)
    (header : Header) (result : CTypeNode)
    (patternsDecoded : decodeCTypes scheme patterns = some patternTypes)
    (actualsDecoded : decodeCTypes callerPointers actuals = some actualTypes)
    (headerArity : header.variables.length = scheme.length)
    (headerParameters : header.parameters.map Prod.snd = patternTypes)
    (resultWellFormed : header.result.wellFormed
      (header.variables.length + callerPointers.length))
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
    patterns.length = actuals.length ∧
    ∃ solution output,
      inferTypeArguments fuel callerPointers.length header actualTypes = some solution ∧
      cSubstituteType scheme (cFinal.map (Option.getD · .unit)) result = some output ∧
      decodeCType callerPointers output =
        some (header.result.instantiate solution.arguments) ∧
      (header.result.instantiate solution.arguments).wellFormed callerPointers.length := by
  obtain ⟨arity, solution, output, inferred, substituted, decoded⟩ :=
    cCheckCall_success_agrees_with_inferTypeArguments callerPointers scheme fuel
      patterns actuals patternTypes actualTypes header result patternsDecoded actualsDecoded
      headerArity headerParameters collectorEnough checkerEnough cFinal
      matched allAssigned resultDecoded
  exact ⟨arity, solution, output, inferred, substituted, decoded,
    solution.instantiated_result_wellFormed resultWellFormed⟩

/-- Reverse the decoded C matcher on certified atomic parameter rows from a
successful Lean inference. The inference theorem exposes its actual collector
result, which is then simulated in C while preserving the shared slot state. -/
theorem typeArgumentSolution_cMatchTypes_atomicRows
    {fuel : Nat} (callerPointers scheme : List Nat)
    {patterns actuals : List CTypeNode} (rows : CAtomicMonotypeRows fuel patterns actuals)
    {patternTypes actualTypes : List Ty} (header : Header)
    (patternsDecoded : decodeCTypes scheme patterns = some patternTypes)
    (actualsDecoded : decodeCTypes callerPointers actuals = some actualTypes)
    (headerArity : header.variables.length = scheme.length)
    (headerParameters : header.parameters.map Prod.snd = patternTypes)
    (solution : TypeArgumentSolution callerPointers.length header actualTypes)
    (inferred : inferTypeArguments fuel callerPointers.length header actualTypes =
      some solution) :
    ∃ cFinal, cMatchTypes fuel scheme patterns actuals
      (List.replicate scheme.length (none : Option CTypeNode)) = some cFinal ∧
      ∃ leanFinal, collectArguments fuel patternTypes actualTypes
          (List.replicate scheme.length none) = some leanFinal ∧
        CSubstitutionStateAgree callerPointers scheme cFinal leanFinal ∧
        leanFinal.mapM (fun value => value) = some solution.arguments := by
  obtain ⟨leanFinal, collected, finalAssignments⟩ :=
    inferTypeArguments_success_collectArguments fuel callerPointers.length header actualTypes
      solution inferred
  have collectedPatterns : collectArguments fuel patternTypes actualTypes
      (List.replicate scheme.length none) = some leanFinal := by
    simpa [headerParameters, headerArity] using collected
  have initialState := cSubstitutionStateAgree_initial_empty callerPointers scheme
  obtain ⟨cFinal, matched, finalState⟩ :=
    cMatchTypes_atomicMonotypeRows_state_simulation_reverse rows patternsDecoded actualsDecoded
      (List.replicate scheme.length none) (List.replicate scheme.length none) leanFinal
      initialState collectedPatterns
  exact ⟨cFinal, matched, leanFinal, collectedPatterns, finalState, finalAssignments⟩

/-- The same inference-to-C reverse simulation for the broader certificate
whose rows may wrap an atomic constraint in arbitrarily many List/Option
constructors. -/
theorem typeArgumentSolution_cMatchTypes_wrappedAtomicRows
    {scheme callerPointers : List Nat} {fuel : Nat}
    {rows : List (CWrappedAtomicMonotypeRow scheme callerPointers)}
    (rowProof : CWrappedAtomicMonotypeRows scheme callerPointers fuel rows)
    (header : Header)
    (headerArity : header.variables.length = scheme.length)
    (headerParameters : header.parameters.map Prod.snd =
      rows.map CWrappedAtomicMonotypeRow.patternIRType)
    (solution : TypeArgumentSolution callerPointers.length header
      (rows.map CWrappedAtomicMonotypeRow.actualIRType))
    (inferred : inferTypeArguments fuel callerPointers.length header
      (rows.map CWrappedAtomicMonotypeRow.actualIRType) = some solution) :
    ∃ cFinal, cMatchTypes fuel scheme
      (rows.map CWrappedAtomicMonotypeRow.patternNode)
      (rows.map CWrappedAtomicMonotypeRow.actualNode)
      (List.replicate scheme.length (none : Option CTypeNode)) = some cFinal ∧
      ∃ leanFinal, collectArguments fuel
          (rows.map CWrappedAtomicMonotypeRow.patternIRType)
          (rows.map CWrappedAtomicMonotypeRow.actualIRType)
          (List.replicate scheme.length none) = some leanFinal ∧
        CSubstitutionStateAgree callerPointers scheme cFinal leanFinal ∧
        leanFinal.mapM (fun value => value) = some solution.arguments := by
  obtain ⟨leanFinal, collected, finalAssignments⟩ :=
    inferTypeArguments_success_collectArguments fuel callerPointers.length header
      (rows.map CWrappedAtomicMonotypeRow.actualIRType) solution inferred
  have collectedRows : collectArguments fuel
      (rows.map CWrappedAtomicMonotypeRow.patternIRType)
      (rows.map CWrappedAtomicMonotypeRow.actualIRType)
      (List.replicate scheme.length none) = some leanFinal := by
    simpa [headerParameters, headerArity] using collected
  have initialState := cSubstitutionStateAgree_initial_empty callerPointers scheme
  obtain ⟨cFinal, matched, finalState⟩ :=
    cMatchTypes_wrappedAtomicMonotypeRows_state_simulation_reverse rowProof
      (List.replicate scheme.length none) (List.replicate scheme.length none) leanFinal
      initialState collectedRows
  exact ⟨cFinal, matched, leanFinal, collectedRows, finalState, finalAssignments⟩

/-- Lift successful inference through a single Function-type argument. Its
parameter list may have any length of List/Option-wrapped atomic constraints,
and its result may also be wrapped; the C matcher follows the same
parameter-then-result assignment order as Lean's collector. -/
theorem typeArgumentSolution_cMatchTypes_function_wrappedAtomic
    {scheme callerPointers : List Nat} {fuel : Nat}
    {rows : List (CWrappedAtomicMonotypeRow scheme callerPointers)}
    (rowProof : CWrappedAtomicMonotypeRows scheme callerPointers fuel rows)
    (resultRow : CWrappedAtomicMonotypeRow scheme callerPointers)
    (resultFuel : resultRow.baseFuel + resultRow.wrappers.length + 1 = fuel)
    (resultCost : cTypeCost resultRow.actualNode < fuel)
    (header : Header)
    (headerArity : header.variables.length = scheme.length)
    (headerParameters : header.parameters.map Prod.snd =
      [.fn (rows.map CWrappedAtomicMonotypeRow.patternIRType) resultRow.patternIRType])
    (solution : TypeArgumentSolution callerPointers.length header
      [.fn (rows.map CWrappedAtomicMonotypeRow.actualIRType) resultRow.actualIRType])
    (inferred : inferTypeArguments (fuel + 2) callerPointers.length header
      [.fn (rows.map CWrappedAtomicMonotypeRow.actualIRType) resultRow.actualIRType] =
        some solution) :
    ∃ cFinal, cMatchTypes (fuel + 2) scheme
      [.function (rows.map CWrappedAtomicMonotypeRow.patternNode) resultRow.patternNode]
      [.function (rows.map CWrappedAtomicMonotypeRow.actualNode) resultRow.actualNode]
      (List.replicate scheme.length (none : Option CTypeNode)) = some cFinal ∧
      ∃ leanFinal,
        CSubstitutionStateAgree callerPointers scheme cFinal leanFinal ∧
        leanFinal.mapM (fun value => value) = some solution.arguments := by
  obtain ⟨leanFinal, collected, finalAssignments⟩ :=
    inferTypeArguments_success_collectArguments (fuel + 2) callerPointers.length header
      [.fn (rows.map CWrappedAtomicMonotypeRow.actualIRType) resultRow.actualIRType]
      solution inferred
  have functionCollected : collectArgument (fuel + 1)
      (.fn (rows.map CWrappedAtomicMonotypeRow.patternIRType) resultRow.patternIRType)
      (.fn (rows.map CWrappedAtomicMonotypeRow.actualIRType) resultRow.actualIRType)
      (List.replicate scheme.length none) = some leanFinal := by
    have listCollected : collectArguments (fuel + 2)
        [.fn (rows.map CWrappedAtomicMonotypeRow.patternIRType) resultRow.patternIRType]
        [.fn (rows.map CWrappedAtomicMonotypeRow.actualIRType) resultRow.actualIRType]
        (List.replicate scheme.length none) = some leanFinal := by
      simpa [headerParameters, headerArity] using collected
    simpa [collectArguments] using listCollected
  have initialState := cSubstitutionStateAgree_initial_empty callerPointers scheme
  obtain ⟨cNext, functionMatched, finalState⟩ :=
    cMatchType_function_wrappedAtomicMonotypeRowsResult_state_simulation_reverse fuel
      (rows := rows) rowProof resultRow resultFuel resultCost
      (List.replicate scheme.length none) (List.replicate scheme.length none) leanFinal
      initialState functionCollected
  refine ⟨cNext, ?_, leanFinal, finalState, finalAssignments⟩
  simpa [cMatchTypes, functionMatched]

/-- A certified Function-type constraint whose parameter rows and result are
each List/Option-wrapped atomic constraints. -/
structure CFunctionWrappedAtomicMonotypeRow (scheme callerPointers : List Nat) where
  functionFuel : Nat
  parameters : List (CWrappedAtomicMonotypeRow scheme callerPointers)
  parametersProof : CWrappedAtomicMonotypeRows scheme callerPointers functionFuel parameters
  result : CWrappedAtomicMonotypeRow scheme callerPointers
  resultFuel : result.baseFuel + result.wrappers.length + 1 = functionFuel
  resultCost : cTypeCost result.actualNode < functionFuel

def CFunctionWrappedAtomicMonotypeRow.patternNode
    {scheme callerPointers : List Nat}
    (row : CFunctionWrappedAtomicMonotypeRow scheme callerPointers) : CTypeNode :=
  .function (row.parameters.map CWrappedAtomicMonotypeRow.patternNode)
    row.result.patternNode

def CFunctionWrappedAtomicMonotypeRow.actualNode
    {scheme callerPointers : List Nat}
    (row : CFunctionWrappedAtomicMonotypeRow scheme callerPointers) : CTypeNode :=
  .function (row.parameters.map CWrappedAtomicMonotypeRow.actualNode)
    row.result.actualNode

def CFunctionWrappedAtomicMonotypeRow.patternIRType
    {scheme callerPointers : List Nat}
    (row : CFunctionWrappedAtomicMonotypeRow scheme callerPointers) : Ty :=
  .fn (row.parameters.map CWrappedAtomicMonotypeRow.patternIRType) row.result.patternIRType

def CFunctionWrappedAtomicMonotypeRow.actualIRType
    {scheme callerPointers : List Nat}
    (row : CFunctionWrappedAtomicMonotypeRow scheme callerPointers) : Ty :=
  .fn (row.parameters.map CWrappedAtomicMonotypeRow.actualIRType) row.result.actualIRType

/-- A left-to-right list of certified Function constraints. One outer matcher
step is reserved for each argument row, while each row carries the fuel for
its own parameter/result traversal. -/
inductive CFunctionWrappedAtomicMonotypeRows (scheme callerPointers : List Nat) :
    Nat → List (CFunctionWrappedAtomicMonotypeRow scheme callerPointers) → Prop where
  | nil (fuel : Nat) : CFunctionWrappedAtomicMonotypeRows scheme callerPointers (fuel + 1) []
  | cons (fuel : Nat) (row : CFunctionWrappedAtomicMonotypeRow scheme callerPointers)
      (rest : List (CFunctionWrappedAtomicMonotypeRow scheme callerPointers)) :
      row.functionFuel = fuel →
      CFunctionWrappedAtomicMonotypeRows scheme callerPointers (fuel + 1) rest →
      CFunctionWrappedAtomicMonotypeRows scheme callerPointers (fuel + 2) (row :: rest)

/-- Reverse simulation for an arbitrary list of Function-type arguments built
from wrapper-aware atomic parameter and result constraints. The shared
substitution state flows from one argument, through its parameters and result,
then into the next argument. -/
theorem cMatchTypes_function_wrappedAtomicMonotypeRows_state_simulation_reverse
    {scheme callerPointers : List Nat} {fuel : Nat}
    {rows : List (CFunctionWrappedAtomicMonotypeRow scheme callerPointers)}
    (rowProof : CFunctionWrappedAtomicMonotypeRows scheme callerPointers fuel rows)
    (cAssignments : List (Option CTypeNode)) (leanAssignments leanFinal : List (Option Ty))
    (stateAgree : CSubstitutionStateAgree callerPointers scheme cAssignments leanAssignments)
    (collected : collectArguments fuel
      (rows.map CFunctionWrappedAtomicMonotypeRow.patternIRType)
      (rows.map CFunctionWrappedAtomicMonotypeRow.actualIRType) leanAssignments = some leanFinal) :
    ∃ cFinal, cMatchTypes fuel scheme
      (rows.map CFunctionWrappedAtomicMonotypeRow.patternNode)
      (rows.map CFunctionWrappedAtomicMonotypeRow.actualNode) cAssignments = some cFinal ∧
      CSubstitutionStateAgree callerPointers scheme cFinal leanFinal := by
  induction rowProof generalizing cAssignments leanAssignments leanFinal with
  | nil fuel =>
      have finalEq : leanFinal = leanAssignments := by
        simpa [collectArguments] using collected.symm
      subst leanFinal
      exact ⟨cAssignments, by simp [cMatchTypes], stateAgree⟩
  | cons fuel row rest rowFuelEq tailProof ih =>
      simp only [List.map, collectArguments] at collected
      obtain ⟨leanNext, headCollected, tailCollected⟩ := Option.bind_eq_some.mp collected
      have headCollected' : collectArgument (fuel + 1) row.patternIRType row.actualIRType
          leanAssignments = some leanNext := by
        simpa [CFunctionWrappedAtomicMonotypeRow.patternIRType,
          CFunctionWrappedAtomicMonotypeRow.actualIRType] using headCollected
      obtain ⟨cNext, headMatched, nextAgree⟩ :=
        cMatchType_function_wrappedAtomicMonotypeRowsResult_state_simulation_reverse fuel
          row.parameters (by simpa [rowFuelEq] using row.parametersProof)
          row.result (by simpa [rowFuelEq] using row.resultFuel)
          (by simpa [rowFuelEq] using row.resultCost)
          cAssignments leanAssignments leanNext stateAgree headCollected'
      obtain ⟨cFinal, tailMatched, finalAgree⟩ :=
        ih cNext leanNext leanFinal nextAgree tailCollected
      refine ⟨cFinal, ?_, finalAgree⟩
      simp [CFunctionWrappedAtomicMonotypeRow.patternNode,
        CFunctionWrappedAtomicMonotypeRow.actualNode, rowFuelEq, cMatchTypes,
        headMatched, tailMatched]

/-- End-to-end inference-to-C reverse simulation for lists of certified
Function-type arguments. It extracts the real collector result from successful
inference and feeds it to the ordered function-row matcher simulation. -/
theorem typeArgumentSolution_cMatchTypes_functionRows
    {scheme callerPointers : List Nat} {fuel : Nat}
    {rows : List (CFunctionWrappedAtomicMonotypeRow scheme callerPointers)}
    (rowProof : CFunctionWrappedAtomicMonotypeRows scheme callerPointers fuel rows)
    (header : Header)
    (headerArity : header.variables.length = scheme.length)
    (headerParameters : header.parameters.map Prod.snd =
      rows.map CFunctionWrappedAtomicMonotypeRow.patternIRType)
    (solution : TypeArgumentSolution callerPointers.length header
      (rows.map CFunctionWrappedAtomicMonotypeRow.actualIRType))
    (inferred : inferTypeArguments fuel callerPointers.length header
      (rows.map CFunctionWrappedAtomicMonotypeRow.actualIRType) = some solution) :
    ∃ cFinal, cMatchTypes fuel scheme
      (rows.map CFunctionWrappedAtomicMonotypeRow.patternNode)
      (rows.map CFunctionWrappedAtomicMonotypeRow.actualNode)
      (List.replicate scheme.length (none : Option CTypeNode)) = some cFinal ∧
      ∃ leanFinal, collectArguments fuel
          (rows.map CFunctionWrappedAtomicMonotypeRow.patternIRType)
          (rows.map CFunctionWrappedAtomicMonotypeRow.actualIRType)
          (List.replicate scheme.length none) = some leanFinal ∧
        CSubstitutionStateAgree callerPointers scheme cFinal leanFinal ∧
        leanFinal.mapM (fun value => value) = some solution.arguments := by
  obtain ⟨leanFinal, collected, finalAssignments⟩ :=
    inferTypeArguments_success_collectArguments fuel callerPointers.length header
      (rows.map CFunctionWrappedAtomicMonotypeRow.actualIRType) solution inferred
  have collectedRows : collectArguments fuel
      (rows.map CFunctionWrappedAtomicMonotypeRow.patternIRType)
      (rows.map CFunctionWrappedAtomicMonotypeRow.actualIRType)
      (List.replicate scheme.length none) = some leanFinal := by
    simpa [headerParameters, headerArity] using collected
  have initialState := cSubstitutionStateAgree_initial_empty callerPointers scheme
  obtain ⟨cFinal, matched, finalState⟩ :=
    cMatchTypes_function_wrappedAtomicMonotypeRows_state_simulation_reverse rowProof
      (List.replicate scheme.length none) (List.replicate scheme.length none) leanFinal
      initialState collectedRows
  exact ⟨cFinal, matched, leanFinal, collectedRows, finalState, finalAssignments⟩

end NLisp.Surface
