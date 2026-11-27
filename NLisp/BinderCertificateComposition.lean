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
  bindingSafe : MacroCounterSafeBindingInputs macros bindings
  casesSafe : MacroCounterSafeCases macros cases
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

/-- A binder-token collection paired with the accepted expansion interval
that bounds every token in it. -/
structure CertifiedBinderTokenChunk (certificate : ExpansionCertificate.Certificate) where
  tokens : List Nat
  interval : Nat × Nat
  intervalMember : interval ∈ ExpansionCertificate.freshIntervals certificate
  internallyUnique : Unique tokens
  avoidsSourceClass : ∀ token, token % 3 = 1 → token ∉ tokens
  withinInterval : ∀ token, token ∈ tokens →
    ∃ counter, interval.1 < counter ∧ counter ≤ interval.2 ∧ token = 3 * counter + 2

def BinderPhaseCopy.certifiedTokenChunk
    {certificate : ExpansionCertificate.Certificate}
    {fuel origin holes macros outside fresh parameters bindings pattern cases}
    (copy : BinderPhaseCopy fuel origin holes macros outside fresh
      parameters bindings pattern cases)
    (interval : Nat × Nat)
    (intervalEq : interval = (fresh, copy.afterCases))
    (intervalMember : interval ∈ ExpansionCertificate.freshIntervals certificate) :
    CertifiedBinderTokenChunk certificate :=
  { tokens := copy.tokens
    interval := interval
    intervalMember := intervalMember
    internallyUnique := copy.tokens_unique
    avoidsSourceClass := fun token sourceClass =>
      copy.tokens_avoid_source_class token sourceClass
    withinInterval := by
      intro token member
      obtain ⟨counter, lower, upper, tokenEq⟩ := copy.tokens_within_interval token member
      exact ⟨counter, by simpa [intervalEq] using lower,
        by simpa [intervalEq] using upper, tokenEq⟩ }

/-- Pairwise token disjointness for an arbitrary finite family of binder
copy chunks accepted by one freshness certificate. Each chunk may summarize
all four phases of a copy; distinct certified intervals imply that no fresh
identifier is shared across any two chunks. -/
def PairwiseTokenDisjoint {certificate : ExpansionCertificate.Certificate} :
    List (CertifiedBinderTokenChunk certificate) → Prop
  | [] => True
  | first :: rest =>
      (∀ second, second ∈ rest → ∀ tokenA, tokenA ∈ first.tokens →
        ∀ tokenB, tokenB ∈ second.tokens → tokenA ≠ tokenB) ∧
      PairwiseTokenDisjoint rest

def binderTokenSequence {certificate : ExpansionCertificate.Certificate} :
    List (CertifiedBinderTokenChunk certificate) → List Nat
  | [] => []
  | chunk :: rest => chunk.tokens ++ binderTokenSequence rest

private theorem mem_append_iff {α : Type} (left right : List α) (value : α) :
    value ∈ left ++ right ↔ value ∈ left ∨ value ∈ right := by
  induction left with
  | nil => simp
  | cons head tail ih => simp [ih, or_assoc]

private theorem mem_binderTokenSequence_iff
    {certificate : ExpansionCertificate.Certificate}
    (chunks : List (CertifiedBinderTokenChunk certificate)) (token : Nat) :
    token ∈ binderTokenSequence chunks ↔
      ∃ chunk, chunk ∈ chunks ∧ token ∈ chunk.tokens := by
  induction chunks with
  | nil => simp [binderTokenSequence]
  | cons head tail ih =>
      simp [binderTokenSequence, mem_append_iff, ih]

/-- The reserved source-token class is disjoint from the complete sequence
whenever every certified chunk avoids that class. -/
theorem binderTokenSequence_avoids_source_class
    {certificate : ExpansionCertificate.Certificate}
    (chunks : List (CertifiedBinderTokenChunk certificate)) (token : Nat)
    (sourceClass : token % 3 = 1) :
    token ∉ binderTokenSequence chunks := by
  intro member
  obtain ⟨chunk, _chunkMember, tokenMember⟩ :=
    mem_binderTokenSequence_iff chunks token |>.mp member
  exact chunk.avoidsSourceClass token sourceClass tokenMember

/-- Every token in the combined sequence remains bounded by the certified
fresh interval of the chunk that produced it. -/
theorem binderTokenSequence_within_interval
    {certificate : ExpansionCertificate.Certificate}
    (chunks : List (CertifiedBinderTokenChunk certificate)) (token : Nat)
    (member : token ∈ binderTokenSequence chunks) :
    ∃ chunk, chunk ∈ chunks ∧ chunk.interval ∈ ExpansionCertificate.freshIntervals certificate ∧
      ∃ counter, chunk.interval.1 < counter ∧ chunk.interval.2 ≥ counter ∧
        token = 3 * counter + 2 := by
  obtain ⟨chunk, chunkMember, tokenMember⟩ :=
    mem_binderTokenSequence_iff chunks token |>.mp member
  obtain ⟨counter, lower, upper, generated⟩ := chunk.withinInterval token tokenMember
  exact ⟨chunk, chunkMember, chunk.intervalMember, counter, lower, upper, generated⟩

private theorem unique_append_of_disjoint (left right : List Nat)
    (leftUnique : Unique left) (rightUnique : Unique right)
    (disjoint : ∀ leftToken, leftToken ∈ left → ∀ rightToken,
      rightToken ∈ right → leftToken ≠ rightToken) :
    Unique (left ++ right) := by
  induction left with
  | nil => simpa using rightUnique
  | cons head tail ih =>
      simp only [List.cons_append, Unique] at leftUnique ⊢
      rcases leftUnique with ⟨headFresh, tailUnique⟩
      refine ⟨?_, ?_⟩
      · intro member
        have member' : head ∈ tail ∨ head ∈ right := (mem_append_iff tail right head).mp member
        rcases member' with inTail | inRight
        · exact headFresh inTail
        · exact disjoint head (by simp) head inRight rfl
      · exact ih tailUnique (by
          intro leftToken leftMember rightToken rightMember
          exact disjoint leftToken (List.mem_cons_of_mem _ leftMember) rightToken rightMember)

/-- Internal uniqueness for each binder chunk plus pairwise chunk separation
implies uniqueness of the complete token sequence across any finite family. -/
theorem pairwiseTokenDisjoint_flatMap_unique
    {certificate : ExpansionCertificate.Certificate}
    (chunks : List (CertifiedBinderTokenChunk certificate))
    (pairwise : PairwiseTokenDisjoint chunks) :
    Unique (binderTokenSequence chunks) := by
  induction chunks with
  | nil => trivial
  | cons first rest ih =>
      rcases pairwise with ⟨firstSeparated, restPairwise⟩
      have restUnique := ih restPairwise
      apply unique_append_of_disjoint first.tokens
        (binderTokenSequence rest) first.internallyUnique restUnique
      intro tokenA memberA tokenB memberB
      obtain ⟨second, secondMember, tokenMember⟩ :=
        mem_binderTokenSequence_iff rest tokenB |>.mp memberB
      exact firstSeparated second secondMember tokenA memberA tokenB tokenMember

theorem certifiedBinderTokenChunks_pairwise_disjoint
    (rules : List (Nat × Tree)) (certificate : ExpansionCertificate.Certificate)
    (accepted : ExpansionCertificate.checkFresh rules certificate = true)
    (chunks : List (CertifiedBinderTokenChunk certificate))
    (intervalsDistinct : ∀ first, first ∈ chunks → ∀ second, second ∈ chunks →
      first.interval ≠ second.interval) :
    PairwiseTokenDisjoint chunks := by
  induction chunks with
  | nil => trivial
  | cons first rest ih =>
      constructor
      · intro second secondMember tokenA memberA tokenB memberB
        have firstMember : first ∈ first :: rest := by simp
        have secondInAll : second ∈ first :: rest := by simp [secondMember]
        exact ExpansionCertificate.checkFresh_separates_token_collections
          certificate accepted first.interval second.interval first.intervalMember
          second.intervalMember (intervalsDistinct first firstMember second secondInAll)
          first.tokens second.tokens first.withinInterval second.withinInterval
          tokenA memberA tokenB memberB
      · apply ih
        intro earlier earlierMember later laterMember
        exact intervalsDistinct earlier (by simp [earlierMember]) later (by simp [laterMember])

/-- One aggregate freshness result for any finite set of binder chunks:
acceptance of the independent certificate and distinct chunk intervals imply
pairwise uniqueness of every generated token and separation from all source
tokens in the reserved source class. -/
theorem certifiedBinderTokenChunks_freshness
    (rules : List (Nat × Tree)) (certificate : ExpansionCertificate.Certificate)
    (accepted : ExpansionCertificate.checkFresh rules certificate = true)
    (chunks : List (CertifiedBinderTokenChunk certificate))
    (intervalsDistinct : ∀ first, first ∈ chunks → ∀ second, second ∈ chunks →
      first.interval ≠ second.interval)
    (sourceTokens : List Nat)
    (sourceClass : ∀ token, token ∈ sourceTokens → token % 3 = 1) :
    Unique (binderTokenSequence chunks) ∧
      (∀ token, token ∈ sourceTokens → token ∉ binderTokenSequence chunks) ∧
      (∀ token, token ∈ binderTokenSequence chunks →
        ∃ chunk, chunk ∈ chunks ∧
          chunk.interval ∈ ExpansionCertificate.freshIntervals certificate ∧
          ∃ counter, chunk.interval.1 < counter ∧ chunk.interval.2 ≥ counter ∧
            token = 3 * counter + 2) := by
  have pairwise := certifiedBinderTokenChunks_pairwise_disjoint rules certificate accepted
    chunks intervalsDistinct
  refine ⟨pairwiseTokenDisjoint_flatMap_unique chunks pairwise, ?_,
    binderTokenSequence_within_interval chunks⟩
  intro token inSource
  apply binderTokenSequence_avoids_source_class chunks token (sourceClass token inSource)

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
