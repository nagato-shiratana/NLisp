import NLisp.CMacroCopy

namespace NLisp.CMacroCopy

/-- Tokens emitted by an arbitrary finite sequence of copy phases, where
each phase starts at the previous phase's counter. -/
def counterTokenChunks (fresh : Nat) : List Nat → List Nat
  | [] => []
  | count :: rest =>
      counterTokens fresh count ++ counterTokenChunks (fresh + count) rest

def copyPhaseTokenCount : List Nat → Nat
  | [] => 0
  | count :: rest => count + copyPhaseTokenCount rest

/-- Sequential counter chunks are exactly one contiguous counter interval,
regardless of how many independently implemented copy phases are composed. -/
theorem counterTokenChunks_eq_counterTokens (fresh : Nat) (counts : List Nat) :
    counterTokenChunks fresh counts = counterTokens fresh (copyPhaseTokenCount counts) := by
  induction counts generalizing fresh with
  | nil => simp [counterTokenChunks, copyPhaseTokenCount, counterTokens]
  | cons count rest ih =>
      simp only [counterTokenChunks, copyPhaseTokenCount]
      rw [ih]
      rw [← counterTokens_add fresh count (copyPhaseTokenCount rest)]

/-- Pairwise freshness follows for any finite sequential phase list, rather
than only a fixed number of binder-copy phases. -/
theorem counterTokenChunks_unique (fresh : Nat) (counts : List Nat) :
    Unique (counterTokenChunks fresh counts) := by
  rw [counterTokenChunks_eq_counterTokens]
  exact counterTokens_distinct fresh (copyPhaseTokenCount counts)

/-- Every token emitted by any finite sequential phase list avoids source
identifiers in the reserved source-token residue class. -/
theorem counterTokenChunks_avoid_source (fresh : Nat) (counts : List Nat)
    (sourceToken : Nat) (sourceClass : sourceToken % 3 = 1) :
    sourceToken ∉ counterTokenChunks fresh counts := by
  rw [counterTokenChunks_eq_counterTokens]
  intro member
  have generated := counterTokens_reserved_class fresh (copyPhaseTokenCount counts)
    sourceToken member
  omega

/-- Every token emitted by an arbitrary finite sequence of contiguous copy
phases lies strictly after its initial counter and no later than the final
counter obtained by summing all phase counts. -/
theorem counterTokenChunks_within_interval (fresh : Nat) (counts : List Nat)
    (token : Nat) (member : token ∈ counterTokenChunks fresh counts) :
    ∃ counter, fresh < counter ∧
      counter ≤ fresh + copyPhaseTokenCount counts ∧ token = 3 * counter + 2 := by
  rw [counterTokenChunks_eq_counterTokens] at member
  obtain ⟨counter, lower, upper, tokenEq⟩ :=
    counterTokens_within_interval fresh (copyPhaseTokenCount counts) token member
  exact ⟨counter, lower, by omega, tokenEq⟩

/-- Compose the binder token guarantees across parameter, let-binding,
pattern, and match-case copy phases. Each phase starts at the previous phase's
final counter, so the complete generated binder sequence occupies one
contiguous interval and is pairwise distinct. -/
theorem copyBinderPhases_freshness (fuel origin : Nat) (holes : Holes)
    (macros : List String) (outside : Renames) (fresh : Nat)
    (parameters parameterCopies : List Tree) (parameterNames : Renames) (afterParameters : Nat)
    (bindings bindingCopies : List Tree) (bindingNames : Renames) (afterBindings : Nat)
    (pattern patternCopies : List Tree) (patternNames : Renames) (afterPattern : Nat)
    (cases caseCopies : List Tree) (afterCases : Nat)
    (bindingSyntaxSafe : MacroCounterSafeBindingInputs macros bindings)
    (casesSyntaxSafe : MacroCounterSafeCases macros cases)
    (parameterCopy : copyParameters fuel holes outside fresh parameters =
      some (parameterCopies, parameterNames, afterParameters))
    (bindingCopy : copyBindingsWithMacros macros fuel origin holes outside parameterNames
      afterParameters bindings = some (bindingCopies, bindingNames, afterBindings))
    (patternCopy : copyPatternWithMacros macros fuel holes bindingNames afterBindings pattern =
      some (patternCopies, patternNames, afterPattern))
    (caseCopy : copyCasesWithMacros macros fuel origin holes patternNames afterPattern cases =
      some (caseCopies, afterCases)) :
    Unique (parameterTokens parameterCopies ++ bindingTokens bindingCopies ++
      patternTokens patternCopies ++ counterPreservingCaseTokens caseCopies) ∧
      (∀ sourceToken, sourceToken % 3 = 1 →
        sourceToken ∉ (parameterTokens parameterCopies ++ bindingTokens bindingCopies ++
          patternTokens patternCopies ++ counterPreservingCaseTokens caseCopies)) ∧
      (∀ token, token ∈ (parameterTokens parameterCopies ++ bindingTokens bindingCopies ++
          patternTokens patternCopies ++ counterPreservingCaseTokens caseCopies) →
        ∃ counter, fresh < counter ∧ counter ≤ afterCases ∧ token = 3 * counter + 2) := by
  have bindingSafe := macroCounterSafeBindingInputs_preserving macros bindings bindingSyntaxSafe
  have casesSafe := macroCounterSafeCases_preserving macros cases casesSyntaxSafe
  have parameterCounter := copyParameters_counter fuel holes outside fresh parameters
    parameterCopies parameterNames afterParameters parameterCopy
  have bindingCounter := copyBindingsWithMacros_preserving_counter macros fuel origin holes outside
    parameterNames afterParameters bindings bindingCopies bindingNames afterBindings bindingSafe
    bindingCopy
  have patternCounter := copyPatternWithMacros_counter macros fuel holes bindingNames afterBindings
    pattern patternCopies patternNames afterPattern patternCopy
  have casesCounter := copyCasesWithMacros_preserving_counter macros fuel origin holes
    patternNames afterPattern cases caseCopies afterCases casesSafe caseCopy
  have parameterSequence := copyParameters_token_sequence fuel holes outside fresh parameters
    parameterCopies parameterNames afterParameters parameterCopy
  have bindingSequence := copyBindingsWithMacros_preserving_token_sequence macros fuel origin holes
    outside parameterNames afterParameters bindings bindingCopies bindingNames afterBindings
    bindingSafe bindingCopy
  have patternSequence := copyPatternWithMacros_token_sequence macros fuel holes bindingNames
    afterBindings pattern patternCopies patternNames afterPattern patternCopy
  have casesSequence := copyCasesWithMacros_preserving_token_sequence macros fuel origin holes
    patternNames afterPattern cases caseCopies afterCases casesSafe caseCopy
  have tokenSequence :
      parameterTokens parameterCopies ++ bindingTokens bindingCopies ++
        patternTokens patternCopies ++ counterPreservingCaseTokens caseCopies =
      counterTokens fresh (parameters.length +
        (bindings.length + (pattern.length + counterPreservingCaseCount cases))) := by
    calc
      _ = counterTokens fresh parameters.length ++
          counterTokens (fresh + parameters.length) bindings.length ++
          counterTokens (fresh + parameters.length + bindings.length) pattern.length ++
          counterTokens (fresh + parameters.length + bindings.length + pattern.length)
            (counterPreservingCaseCount cases) := by
        rw [parameterSequence, bindingSequence, patternSequence, casesSequence,
          parameterCounter, bindingCounter, patternCounter]
        simp [parameterCounter, bindingCounter, patternCounter, Nat.add_assoc]
      _ = counterTokens fresh (parameters.length +
          (bindings.length + (pattern.length + counterPreservingCaseCount cases))) := by
        have casesGrouped := (counterTokens_add
          (fresh + parameters.length + bindings.length) pattern.length
          (counterPreservingCaseCount cases)).symm
        have bindingsGrouped := (counterTokens_add (fresh + parameters.length) bindings.length
          (pattern.length + counterPreservingCaseCount cases)).symm
        have parametersGrouped := (counterTokens_add fresh parameters.length
          (bindings.length + (pattern.length + counterPreservingCaseCount cases))).symm
        calc
          _ = counterTokens fresh parameters.length ++
              (counterTokens (fresh + parameters.length) bindings.length ++
                (counterTokens (fresh + parameters.length + bindings.length) pattern.length ++
                  counterTokens (fresh + parameters.length + bindings.length + pattern.length)
                    (counterPreservingCaseCount cases))) := by
            simp only [List.append_assoc]
          _ = counterTokens fresh parameters.length ++
              (counterTokens (fresh + parameters.length) bindings.length ++
                counterTokens (fresh + parameters.length + bindings.length)
                  (pattern.length + counterPreservingCaseCount cases)) :=
            congrArg (fun tail => counterTokens fresh parameters.length ++
              (counterTokens (fresh + parameters.length) bindings.length ++ tail)) casesGrouped
          _ = counterTokens fresh parameters.length ++ counterTokens (fresh + parameters.length)
                (bindings.length + (pattern.length + counterPreservingCaseCount cases)) :=
            congrArg (fun tail => counterTokens fresh parameters.length ++ tail) bindingsGrouped
          _ = counterTokens fresh (parameters.length +
              (bindings.length + (pattern.length + counterPreservingCaseCount cases))) :=
            parametersGrouped
  let phaseCounts := [parameters.length, bindings.length, pattern.length,
    counterPreservingCaseCount cases]
  have tokenChunks :
      parameterTokens parameterCopies ++ bindingTokens bindingCopies ++
        patternTokens patternCopies ++ counterPreservingCaseTokens caseCopies =
      counterTokenChunks fresh phaseCounts := by
    rw [tokenSequence]
    change counterTokens fresh
        (parameters.length + (bindings.length +
          (pattern.length + counterPreservingCaseCount cases))) =
      counterTokenChunks fresh
        [parameters.length, bindings.length, pattern.length, counterPreservingCaseCount cases]
    have countEq : copyPhaseTokenCount
        [parameters.length, bindings.length, pattern.length, counterPreservingCaseCount cases] =
        parameters.length + (bindings.length +
          (pattern.length + counterPreservingCaseCount cases)) := by
      simp [copyPhaseTokenCount]
    rw [← countEq]
    exact (counterTokenChunks_eq_counterTokens fresh
      [parameters.length, bindings.length, pattern.length, counterPreservingCaseCount cases]).symm
  have finalCounter : afterCases = fresh +
      (parameters.length + (bindings.length + (pattern.length + counterPreservingCaseCount cases))) := by
    rw [casesCounter, patternCounter, bindingCounter, parameterCounter]
    omega
  constructor
  · rw [tokenChunks]
    exact counterTokenChunks_unique fresh phaseCounts
  constructor
  · intro sourceToken sourceClass member
    rw [tokenChunks] at member
    exact counterTokenChunks_avoid_source fresh phaseCounts sourceToken sourceClass member
  · intro token member
    rw [tokenChunks] at member
    obtain ⟨counter, lower, upper, tokenEq⟩ :=
      counterTokenChunks_within_interval fresh phaseCounts token member
    have phaseCount : copyPhaseTokenCount phaseCounts =
        parameters.length + (bindings.length +
          (pattern.length + counterPreservingCaseCount cases)) := by
      simp [phaseCounts, copyPhaseTokenCount]
    have upperFinal : counter ≤ afterCases := by
      rw [finalCounter]
      rw [phaseCount] at upper
      exact upper
    exact ⟨counter, lower, upperFinal, tokenEq⟩

/-- The final counter of the composed binder-copy phases is exactly the
initial counter plus all generated parameter, binding, pattern, and
counter-preserving case binders. -/
theorem copyBinderPhases_final_counter (fuel origin : Nat) (holes : Holes)
    (macros : List String) (outside : Renames) (fresh : Nat)
    (parameters parameterCopies : List Tree) (parameterNames : Renames) (afterParameters : Nat)
    (bindings bindingCopies : List Tree) (bindingNames : Renames) (afterBindings : Nat)
    (pattern patternCopies : List Tree) (patternNames : Renames) (afterPattern : Nat)
    (cases caseCopies : List Tree) (afterCases : Nat)
    (bindingSyntaxSafe : MacroCounterSafeBindingInputs macros bindings)
    (casesSyntaxSafe : MacroCounterSafeCases macros cases)
    (parameterCopy : copyParameters fuel holes outside fresh parameters =
      some (parameterCopies, parameterNames, afterParameters))
    (bindingCopy : copyBindingsWithMacros macros fuel origin holes outside parameterNames
      afterParameters bindings = some (bindingCopies, bindingNames, afterBindings))
    (patternCopy : copyPatternWithMacros macros fuel holes bindingNames afterBindings pattern =
      some (patternCopies, patternNames, afterPattern))
    (caseCopy : copyCasesWithMacros macros fuel origin holes patternNames afterPattern cases =
      some (caseCopies, afterCases)) :
    afterCases = fresh + (parameters.length +
      (bindings.length + (pattern.length + counterPreservingCaseCount cases))) := by
  have bindingSafe := macroCounterSafeBindingInputs_preserving macros bindings bindingSyntaxSafe
  have casesSafe := macroCounterSafeCases_preserving macros cases casesSyntaxSafe
  have parameterCounter := copyParameters_counter fuel holes outside fresh parameters
    parameterCopies parameterNames afterParameters parameterCopy
  have bindingCounter := copyBindingsWithMacros_preserving_counter macros fuel origin holes outside
    parameterNames afterParameters bindings bindingCopies bindingNames afterBindings bindingSafe
    bindingCopy
  have patternCounter := copyPatternWithMacros_counter macros fuel holes bindingNames afterBindings
    pattern patternCopies patternNames afterPattern patternCopy
  have casesCounter := copyCasesWithMacros_preserving_counter macros fuel origin holes
    patternNames afterPattern cases caseCopies afterCases casesSafe caseCopy
  omega

/-- The reserved-class result composes with any source binder inventory whose
identifiers use the source class. -/
theorem copyBinderPhases_disjoint_source (fuel origin : Nat) (holes : Holes)
    (macros : List String) (outside : Renames) (fresh : Nat)
    (parameters parameterCopies : List Tree) (parameterNames : Renames) (afterParameters : Nat)
    (bindings bindingCopies : List Tree) (bindingNames : Renames) (afterBindings : Nat)
    (pattern patternCopies : List Tree) (patternNames : Renames) (afterPattern : Nat)
    (cases caseCopies : List Tree) (afterCases : Nat)
    (bindingSyntaxSafe : MacroCounterSafeBindingInputs macros bindings)
    (casesSyntaxSafe : MacroCounterSafeCases macros cases)
    (parameterCopy : copyParameters fuel holes outside fresh parameters =
      some (parameterCopies, parameterNames, afterParameters))
    (bindingCopy : copyBindingsWithMacros macros fuel origin holes outside parameterNames
      afterParameters bindings = some (bindingCopies, bindingNames, afterBindings))
    (patternCopy : copyPatternWithMacros macros fuel holes bindingNames afterBindings pattern =
      some (patternCopies, patternNames, afterPattern))
    (caseCopy : copyCasesWithMacros macros fuel origin holes patternNames afterPattern cases =
      some (caseCopies, afterCases))
    (sourceTokens : List Nat) (sourceClass : ∀ token ∈ sourceTokens, token % 3 = 1) :
    (∀ token ∈ sourceTokens, token ∉ (parameterTokens parameterCopies ++
      bindingTokens bindingCopies ++ patternTokens patternCopies ++
      counterPreservingCaseTokens caseCopies)) := by
  intro token inSource inGenerated
  have sourceResidue := sourceClass token inSource
  have reserved := (copyBinderPhases_freshness fuel origin holes macros outside fresh
    parameters parameterCopies parameterNames afterParameters bindings bindingCopies bindingNames
    afterBindings pattern patternCopies patternNames afterPattern cases caseCopies afterCases
    bindingSyntaxSafe casesSyntaxSafe parameterCopy bindingCopy patternCopy caseCopy).2.1 token sourceResidue
  exact reserved inGenerated

end NLisp.CMacroCopy
