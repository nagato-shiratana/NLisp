import NLisp.CMacroCopy

namespace NLisp.CMacroCopy

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
    (bindingSafe : CounterPreservingBindings macros bindings)
    (casesSafe : CounterPreservingCases macros cases)
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
  have binderCount : parameters.length +
      (bindings.length + (pattern.length + counterPreservingCaseCount cases)) =
      parameters.length + bindings.length + pattern.length + counterPreservingCaseCount cases := by
    omega
  have finalCounter : afterCases = fresh +
      (parameters.length + (bindings.length + (pattern.length + counterPreservingCaseCount cases))) := by
    rw [casesCounter, patternCounter, bindingCounter, parameterCounter]
    omega
  constructor
  · rw [tokenSequence]
    exact counterTokens_distinct fresh
      (parameters.length + (bindings.length + (pattern.length + counterPreservingCaseCount cases)))
  constructor
  · intro sourceToken sourceClass member
    rw [tokenSequence] at member
    have generatedClass := counterTokens_reserved_class fresh
      (parameters.length + (bindings.length + (pattern.length + counterPreservingCaseCount cases)))
      sourceToken member
    omega
  · intro token member
    rw [tokenSequence] at member
    obtain ⟨counter, lower, upper, tokenEq⟩ := counterTokens_within_interval fresh
      (parameters.length + (bindings.length + (pattern.length + counterPreservingCaseCount cases)))
      token member
    exact ⟨counter, lower, by rw [finalCounter, binderCount]; omega, tokenEq⟩

/-- The reserved-class result composes with any source binder inventory whose
identifiers use the source class. -/
theorem copyBinderPhases_disjoint_source (fuel origin : Nat) (holes : Holes)
    (macros : List String) (outside : Renames) (fresh : Nat)
    (parameters parameterCopies : List Tree) (parameterNames : Renames) (afterParameters : Nat)
    (bindings bindingCopies : List Tree) (bindingNames : Renames) (afterBindings : Nat)
    (pattern patternCopies : List Tree) (patternNames : Renames) (afterPattern : Nat)
    (cases caseCopies : List Tree) (afterCases : Nat)
    (bindingSafe : CounterPreservingBindings macros bindings)
    (casesSafe : CounterPreservingCases macros cases)
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
    bindingSafe casesSafe parameterCopy bindingCopy patternCopy caseCopy).2.1 token sourceResidue
  exact reserved inGenerated

end NLisp.CMacroCopy
