import NLisp.CMacroCopyBinderComposition
import NLisp.ExpansionCertificate

namespace NLisp.CMacroCopy

/-- Successful outputs of the four binder-producing copy phases that share a
single counter. The input syntax is a structure parameter so the safety
evidence is indexed by exactly the syntax copied by the phases. -/
structure BinderPhaseCopy (fuel origin : Nat) (holes : Holes) (macros : List String)
    (outside : Renames) (fresh : Nat) (parameters bindings pattern cases : List Tree) where
  parameterCopies : List Tree
  parameterNames : Renames
  afterParameters : Nat
  bindingCopies : List Tree
  bindingNames : Renames
  afterBindings : Nat
  patternCopies : List Tree
  patternNames : Renames
  afterPattern : Nat
  caseCopies : List Tree
  afterCases : Nat
  bindingSafe : CounterPreservingBindings macros bindings
  casesSafe : CounterPreservingCases macros cases
  parameterCopy : copyParameters fuel holes outside fresh parameters =
    some (parameterCopies, parameterNames, afterParameters)
  bindingCopy : copyBindingsWithMacros macros fuel origin holes outside parameterNames
    afterParameters bindings = some (bindingCopies, bindingNames, afterBindings)
  patternCopy : copyPatternWithMacros macros fuel holes bindingNames afterBindings pattern =
    some (patternCopies, patternNames, afterPattern)
  caseCopy : copyCasesWithMacros macros fuel origin holes patternNames afterPattern cases =
    some (caseCopies, afterCases)

def BinderPhaseCopy.tokens {fuel origin holes macros outside fresh parameters bindings pattern cases}
    (copy : BinderPhaseCopy fuel origin holes macros outside fresh parameters bindings pattern cases)
    : List Nat :=
  parameterTokens copy.parameterCopies ++ bindingTokens copy.bindingCopies ++
    patternTokens copy.patternCopies ++ counterPreservingCaseTokens copy.caseCopies

theorem BinderPhaseCopy.tokens_unique {fuel origin holes macros outside fresh
    parameters bindings pattern cases}
    (copy : BinderPhaseCopy fuel origin holes macros outside fresh parameters bindings pattern cases)
    : Unique copy.tokens := by
  have phaseFresh := copyBinderPhases_freshness fuel origin holes macros outside fresh
    parameters copy.parameterCopies copy.parameterNames copy.afterParameters
    bindings copy.bindingCopies copy.bindingNames copy.afterBindings
    pattern copy.patternCopies copy.patternNames copy.afterPattern
    cases copy.caseCopies copy.afterCases copy.bindingSafe copy.casesSafe
    copy.parameterCopy copy.bindingCopy copy.patternCopy copy.caseCopy
  exact phaseFresh.1

theorem BinderPhaseCopy.tokens_avoid_source_class {fuel origin holes macros outside fresh
    parameters bindings pattern cases}
    (copy : BinderPhaseCopy fuel origin holes macros outside fresh parameters bindings pattern cases)
    (token : Nat) (sourceClass : token % 3 = 1) : token ∉ copy.tokens := by
  have phaseFresh := copyBinderPhases_freshness fuel origin holes macros outside fresh
    parameters copy.parameterCopies copy.parameterNames copy.afterParameters
    bindings copy.bindingCopies copy.bindingNames copy.afterBindings
    pattern copy.patternCopies copy.patternNames copy.afterPattern
    cases copy.caseCopies copy.afterCases copy.bindingSafe copy.casesSafe
    copy.parameterCopy copy.bindingCopy copy.patternCopy copy.caseCopy
  exact phaseFresh.2.1 token sourceClass

theorem BinderPhaseCopy.tokens_within_interval {fuel origin holes macros outside fresh
    parameters bindings pattern cases}
    (copy : BinderPhaseCopy fuel origin holes macros outside fresh parameters bindings pattern cases)
    (token : Nat) (member : token ∈ copy.tokens) :
    ∃ counter, fresh < counter ∧ counter ≤ copy.afterCases ∧
      token = 3 * counter + 2 := by
  have phaseFresh := copyBinderPhases_freshness fuel origin holes macros outside fresh
    parameters copy.parameterCopies copy.parameterNames copy.afterParameters
    bindings copy.bindingCopies copy.bindingNames copy.afterBindings
    pattern copy.patternCopies copy.patternNames copy.afterPattern
    cases copy.caseCopies copy.afterCases copy.bindingSafe copy.casesSafe
    copy.parameterCopy copy.bindingCopy copy.patternCopy copy.caseCopy
  exact phaseFresh.2.2 token (by simpa [BinderPhaseCopy.tokens] using member)

/-- Binder tokens from two phase-composed copy results cannot collide when
their counter intervals belong to different macro steps in one accepted
freshness certificate. -/
theorem certifiedBinderPhaseCopies_disjoint
    (rules : List (Nat × Tree)) (certificate : ExpansionCertificate.Certificate)
    (accepted : ExpansionCertificate.checkFresh rules certificate = true)
    (firstInterval secondInterval : Nat × Nat)
    (firstMember : firstInterval ∈ ExpansionCertificate.freshIntervals certificate)
    (secondMember : secondInterval ∈ ExpansionCertificate.freshIntervals certificate)
    (different : firstInterval ≠ secondInterval)
    {fuelA originA : Nat} {holesA : Holes} {macrosA : List String}
    {outsideA : Renames} {freshA : Nat} {parametersA bindingsA patternA casesA : List Tree}
    (firstCopy : BinderPhaseCopy fuelA originA holesA macrosA outsideA freshA
      parametersA bindingsA patternA casesA)
    (firstIntervalEq : firstInterval = (freshA, firstCopy.afterCases))
    {fuelB originB : Nat} {holesB : Holes} {macrosB : List String}
    {outsideB : Renames} {freshB : Nat} {parametersB bindingsB patternB casesB : List Tree}
    (secondCopy : BinderPhaseCopy fuelB originB holesB macrosB outsideB freshB
      parametersB bindingsB patternB casesB)
    (secondIntervalEq : secondInterval = (freshB, secondCopy.afterCases)) :
    ∀ tokenA, tokenA ∈ firstCopy.tokens → ∀ tokenB, tokenB ∈ secondCopy.tokens →
      tokenA ≠ tokenB := by
  apply ExpansionCertificate.checkFresh_separates_token_collections (rules := rules)
    certificate accepted firstInterval secondInterval firstMember secondMember different
    firstCopy.tokens secondCopy.tokens
  · intro token member
    obtain ⟨counter, lower, upper, generated⟩ := firstCopy.tokens_within_interval token member
    exact ⟨counter, by simpa [firstIntervalEq] using lower,
      by simpa [firstIntervalEq] using upper, generated⟩
  · intro token member
    obtain ⟨counter, lower, upper, generated⟩ := secondCopy.tokens_within_interval token member
    exact ⟨counter, by simpa [secondIntervalEq] using lower,
      by simpa [secondIntervalEq] using upper, generated⟩

/-- Combined freshness for two certified phase-composed copies: uniqueness
inside each copy, noncollision across the two certificate intervals, and
separation from source identifiers in the reserved source-token class. -/
theorem certifiedBinderPhaseCopies_freshness
    (rules : List (Nat × Tree)) (certificate : ExpansionCertificate.Certificate)
    (accepted : ExpansionCertificate.checkFresh rules certificate = true)
    (firstInterval secondInterval : Nat × Nat)
    (firstMember : firstInterval ∈ ExpansionCertificate.freshIntervals certificate)
    (secondMember : secondInterval ∈ ExpansionCertificate.freshIntervals certificate)
    (different : firstInterval ≠ secondInterval)
    {fuelA originA : Nat} {holesA : Holes} {macrosA : List String}
    {outsideA : Renames} {freshA : Nat} {parametersA bindingsA patternA casesA : List Tree}
    (firstCopy : BinderPhaseCopy fuelA originA holesA macrosA outsideA freshA
      parametersA bindingsA patternA casesA)
    (firstIntervalEq : firstInterval = (freshA, firstCopy.afterCases))
    {fuelB originB : Nat} {holesB : Holes} {macrosB : List String}
    {outsideB : Renames} {freshB : Nat} {parametersB bindingsB patternB casesB : List Tree}
    (secondCopy : BinderPhaseCopy fuelB originB holesB macrosB outsideB freshB
      parametersB bindingsB patternB casesB)
    (secondIntervalEq : secondInterval = (freshB, secondCopy.afterCases))
    (sourceTokens : List Nat)
    (sourceClass : ∀ token, token ∈ sourceTokens → token % 3 = 1) :
    Unique firstCopy.tokens ∧ Unique secondCopy.tokens ∧
      (∀ tokenA, tokenA ∈ firstCopy.tokens → ∀ tokenB, tokenB ∈ secondCopy.tokens →
        tokenA ≠ tokenB) ∧
      (∀ token, token ∈ sourceTokens → token ∉ firstCopy.tokens) ∧
      (∀ token, token ∈ sourceTokens → token ∉ secondCopy.tokens) := by
  refine ⟨firstCopy.tokens_unique, secondCopy.tokens_unique,
    certifiedBinderPhaseCopies_disjoint rules certificate accepted firstInterval secondInterval
      firstMember secondMember different firstCopy firstIntervalEq secondCopy secondIntervalEq,
    ?_, ?_⟩
  · intro token member
    exact firstCopy.tokens_avoid_source_class token (sourceClass token member)
  · intro token member
    exact secondCopy.tokens_avoid_source_class token (sourceClass token member)

end NLisp.CMacroCopy
