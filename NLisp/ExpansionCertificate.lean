import NLisp.CExpansion

namespace NLisp.ExpansionCertificate

open CMacroCopy CExpansion

/- A proof-free, local certificate. A list-context step changes one child,
while trans composes adjacent steps. Macro rule membership, matching, and
bounded hygienic copying are recomputed from the original rule set. -/
inductive Certificate where
  | refl (tree : Tree)
  | congList (pre suffix : List Tree) (child : Certificate)
  | macroStep (origin fuel fresh final : Nat) (rule input output : Tree)
  | trans (first second : Certificate)

def source : Certificate → Tree
  | .refl tree => tree
  | .congList pre suffix child => .list (pre ++ source child :: suffix)
  | .macroStep _ _ _ _ _ input _ => input
  | .trans first _ => source first

def target : Certificate → Tree
  | .refl tree => tree
  | .congList pre suffix child => .list (pre ++ target child :: suffix)
  | .macroStep _ _ _ _ _ _ output => output
  | .trans _ second => target second

def freshIntervals : Certificate → List (Nat × Nat)
  | .refl _ => []
  | .congList _ _ child => freshIntervals child
  | .macroStep _ _ fresh final _ _ _ => [(fresh, final)]
  | .trans first second => freshIntervals first ++ freshIntervals second

noncomputable def checkStep (rules : List (Nat × Tree)) (origin fuel fresh final : Nat)
    (rule input output : Tree) : Bool :=
  match matchRule rule input with
  | none => false
  | some (holes, template) =>
      decide ((origin, rule) ∈ rules) &&
      decide (copyWithMacros (macroNames rules) fuel origin holes [] fresh template =
        some (output, final))

noncomputable def check (rules : List (Nat × Tree)) : Certificate → Bool
  | .refl _ => true
  | .congList _ _ child => check rules child
  | .macroStep origin fuel fresh final rule input output =>
      checkStep rules origin fuel fresh final rule input output
  | .trans first second =>
      check rules first && check rules second && decide (target first = source second)

noncomputable def checkFresh (rules : List (Nat × Tree)) (certificate : Certificate) : Bool :=
  disjointIntervals (freshIntervals certificate) && check rules certificate

theorem checkFresh_intro (intervals : disjointIntervals (freshIntervals certificate) = true)
    (accepted : check rules certificate = true) : checkFresh rules certificate = true := by
  simp [checkFresh, intervals, accepted]

theorem checkFresh_intervals (accepted : checkFresh rules certificate = true) :
    disjointIntervals (freshIntervals certificate) = true := by
  simp [checkFresh] at accepted
  exact accepted.1

theorem checkStep_intro (member : (origin, rule) ∈ rules)
    (matched : matchRule rule input = some (holes, template))
    (copied : copyWithMacros (macroNames rules) fuel origin holes [] fresh template =
      some (output, final)) :
    checkStep rules origin fuel fresh final rule input output = true := by
  simp [checkStep, matched, member, copied]

theorem check_congList (accepted : check rules child = true) :
    check rules (.congList pre suffix child) = true := by
  simpa [check] using accepted

theorem check_trans (firstAccepted : check rules first = true)
    (secondAccepted : check rules second = true)
    (joined : target first = source second) :
    check rules (.trans first second) = true := by
  simp [check, firstAccepted, secondAccepted, joined]

theorem checkStep_sound (accepted : checkStep rules origin fuel fresh final rule input output = true) :
    ∃ holes template, (origin, rule) ∈ rules ∧
      matchRule rule input = some (holes, template) ∧
      copyWithMacros (macroNames rules) fuel origin holes [] fresh template = some (output, final) := by
  unfold checkStep at accepted
  cases matched : matchRule rule input with
  | none => simp [matched] at accepted
  | some result =>
      simp [matched, Bool.and_eq_true] at accepted
      obtain ⟨member, copied⟩ := accepted
      cases result with
      | mk holes template =>
          exact ⟨holes, template, member, rfl, copied⟩

theorem list_context (child : Expands rules before after) (pre suffix : List Tree) :
    Expands rules (.list (pre ++ before :: suffix)) (.list (pre ++ after :: suffix)) := by
  induction pre with
  | nil =>
      simpa using (Expands.cons child (.refl (.list suffix)))
  | cons head tail ih =>
      simpa [List.cons_append] using (Expands.cons (.refl head) ih)

theorem check_sound (certificate : Certificate) (accepted : check rules certificate = true) :
    Expands rules (source certificate) (target certificate) := by
  induction certificate with
  | refl tree =>
      simpa [source, target] using (Expands.refl tree)
  | congList pre suffix child ih =>
      have childProof := ih accepted
      simpa [source, target] using (list_context childProof pre suffix)
  | macroStep origin fuel fresh final rule input output =>
      obtain ⟨holes, template, member, matched, copied⟩ := checkStep_sound accepted
      simpa [source, target] using
        (Expands.macroStep origin fuel fresh final rule input template output holes
          member matched copied)
  | trans first second ihFirst ihSecond =>
      simp [check, Bool.and_eq_true, decide_eq_true_eq] at accepted
      obtain ⟨⟨firstAccepted, secondAccepted⟩, joined⟩ := accepted
      have firstProof := ihFirst firstAccepted
      have secondProof := ihSecond secondAccepted
      simpa [source, target] using (Expands.trans firstProof (by rw [joined]; exact secondProof))

theorem checkFresh_sound (certificate : Certificate)
    (accepted : checkFresh rules certificate = true) :
    Expands rules (source certificate) (target certificate) := by
  simp [checkFresh] at accepted
  exact check_sound certificate accepted.2

theorem checkFresh_separates_interval_counters (certificate : Certificate)
    (accepted : checkFresh rules certificate = true)
    (first second : Nat × Nat)
    (firstMember : first ∈ freshIntervals certificate)
    (secondMember : second ∈ freshIntervals certificate)
    (different : first ≠ second)
    (aLower : first.1 < a) (aUpper : a ≤ first.2)
    (bLower : second.1 < b) (bUpper : b ≤ second.2) : a ≠ b := by
  exact CExpansion.disjoint_interval_counters_differ (checkFresh_intervals accepted)
    first second firstMember secondMember different aLower aUpper bLower bUpper

theorem checkFresh_generated_tokens_differ (certificate : Certificate)
    (accepted : checkFresh rules certificate = true)
    (first second : Nat × Nat)
    (firstMember : first ∈ freshIntervals certificate)
    (secondMember : second ∈ freshIntervals certificate)
    (different : first ≠ second)
    (aLower : first.1 < a) (aUpper : a ≤ first.2)
    (bLower : second.1 < b) (bUpper : b ≤ second.2) :
    3 * a + 2 ≠ 3 * b + 2 := by
  exact CExpansion.disjoint_interval_generated_ids_differ (checkFresh_intervals accepted)
    first second firstMember secondMember different aLower aUpper bLower bUpper

theorem checkFresh_separates_parameter_copy_tokens (certificate : Certificate)
    (certificateAccepted : checkFresh rules certificate = true)
    (first second : Nat × Nat)
    (firstMember : first ∈ freshIntervals certificate)
    (secondMember : second ∈ freshIntervals certificate)
    (different : first ≠ second)
    (fuel : Nat) (holesA : Holes) (renamesA : Renames) (parametersA copiedA : List Tree)
    (namesA : Renames) (firstCopy : copyParameters fuel holesA renamesA first.1 parametersA =
      some (copiedA, namesA, first.2))
    (holesB : Holes) (renamesB : Renames) (parametersB copiedB : List Tree)
    (namesB : Renames) (secondCopy : copyParameters fuel holesB renamesB second.1 parametersB =
      some (copiedB, namesB, second.2))
    (tokenA tokenB : Nat) (memberA : tokenA ∈ parameterTokens copiedA)
    (memberB : tokenB ∈ parameterTokens copiedB) : tokenA ≠ tokenB := by
  obtain ⟨counterA, lowerA, upperA, tokenEqA⟩ :=
    copyParameters_tokens_within_interval fuel holesA renamesA first.1 parametersA
      copiedA namesA first.2 firstCopy tokenA memberA
  obtain ⟨counterB, lowerB, upperB, tokenEqB⟩ :=
    copyParameters_tokens_within_interval fuel holesB renamesB second.1 parametersB
      copiedB namesB second.2 secondCopy tokenB memberB
  have generated := checkFresh_generated_tokens_differ certificate certificateAccepted
    first second firstMember secondMember different (a := counterA) (b := counterB)
    lowerA upperA lowerB upperB
  intro same
  apply generated
  rw [← tokenEqA, ← tokenEqB]
  exact same

theorem checkFresh_separates_pattern_copy_tokens (certificate : Certificate)
    (certificateAccepted : checkFresh rules certificate = true)
    (first second : Nat × Nat)
    (firstMember : first ∈ freshIntervals certificate)
    (secondMember : second ∈ freshIntervals certificate)
    (different : first ≠ second)
    (fuel : Nat) (holesA : Holes) (renamesA : Renames) (patternA copiedA : List Tree)
    (namesA : Renames) (firstCopy : copyPattern fuel holesA renamesA first.1 patternA =
      some (copiedA, namesA, first.2))
    (holesB : Holes) (renamesB : Renames) (patternB copiedB : List Tree)
    (namesB : Renames) (secondCopy : copyPattern fuel holesB renamesB second.1 patternB =
      some (copiedB, namesB, second.2))
    (tokenA tokenB : Nat) (memberA : tokenA ∈ patternTokens copiedA)
    (memberB : tokenB ∈ patternTokens copiedB) : tokenA ≠ tokenB := by
  obtain ⟨counterA, lowerA, upperA, tokenEqA⟩ :=
    copyPattern_tokens_within_interval fuel holesA renamesA first.1 patternA
      copiedA namesA first.2 firstCopy tokenA memberA
  obtain ⟨counterB, lowerB, upperB, tokenEqB⟩ :=
    copyPattern_tokens_within_interval fuel holesB renamesB second.1 patternB
      copiedB namesB second.2 secondCopy tokenB memberB
  have generated := checkFresh_generated_tokens_differ certificate certificateAccepted
    first second firstMember secondMember different (a := counterA) (b := counterB)
    lowerA upperA lowerB upperB
  intro same
  apply generated
  rw [← tokenEqA, ← tokenEqB]
  exact same

theorem checkFresh_separates_atomic_binding_tokens (certificate : Certificate)
    (certificateAccepted : checkFresh rules certificate = true)
    (first second : Nat × Nat)
    (firstMember : first ∈ freshIntervals certificate)
    (secondMember : second ∈ freshIntervals certificate)
    (different : first ≠ second)
    (fuel origin : Nat) (holesA : Holes) (outsideA namesA : Renames)
    (bindingsA copiedA : List Tree) (finalNamesA : Renames)
    (atomicA : AtomicBindingInputs bindingsA)
    (firstCopy : copyBindings fuel origin holesA outsideA namesA first.1 bindingsA =
      some (copiedA, finalNamesA, first.2))
    (holesB : Holes) (outsideB namesB : Renames) (bindingsB copiedB : List Tree)
    (finalNamesB : Renames) (atomicB : AtomicBindingInputs bindingsB)
    (secondCopy : copyBindings fuel origin holesB outsideB namesB second.1 bindingsB =
      some (copiedB, finalNamesB, second.2))
    (tokenA tokenB : Nat) (memberA : tokenA ∈ bindingTokens copiedA)
    (memberB : tokenB ∈ bindingTokens copiedB) : tokenA ≠ tokenB := by
  obtain ⟨counterA, lowerA, upperA, tokenEqA⟩ :=
    copyBindings_atomic_tokens_within_interval fuel origin holesA outsideA namesA first.1
      bindingsA copiedA finalNamesA first.2 atomicA firstCopy tokenA memberA
  obtain ⟨counterB, lowerB, upperB, tokenEqB⟩ :=
    copyBindings_atomic_tokens_within_interval fuel origin holesB outsideB namesB second.1
      bindingsB copiedB finalNamesB second.2 atomicB secondCopy tokenB memberB
  have generated := checkFresh_generated_tokens_differ certificate certificateAccepted
    first second firstMember secondMember different (a := counterA) (b := counterB)
    lowerA upperA lowerB upperB
  intro same
  apply generated
  rw [← tokenEqA, ← tokenEqB]
  exact same

theorem checkFresh_separates_macro_aware_atom_binding_tokens (certificate : Certificate)
    (certificateAccepted : checkFresh rules certificate = true)
    (first second : Nat × Nat)
    (firstMember : first ∈ freshIntervals certificate)
    (secondMember : second ∈ freshIntervals certificate)
    (different : first ≠ second)
    (fuel origin : Nat) (macrosA : List String) (holesA : Holes) (outsideA namesA : Renames)
    (bindingsA copiedA : List Tree) (finalNamesA : Renames)
    (atomicA : AtomBindingInputs bindingsA)
    (firstCopy : copyBindingsWithMacros macrosA fuel origin holesA outsideA namesA first.1
      bindingsA = some (copiedA, finalNamesA, first.2))
    (macrosB : List String) (holesB : Holes) (outsideB namesB : Renames)
    (bindingsB copiedB : List Tree) (finalNamesB : Renames)
    (atomicB : AtomBindingInputs bindingsB)
    (secondCopy : copyBindingsWithMacros macrosB fuel origin holesB outsideB namesB second.1
      bindingsB = some (copiedB, finalNamesB, second.2))
    (tokenA tokenB : Nat) (memberA : tokenA ∈ bindingTokens copiedA)
    (memberB : tokenB ∈ bindingTokens copiedB) : tokenA ≠ tokenB := by
  obtain ⟨counterA, lowerA, upperA, tokenEqA⟩ :=
    copyBindingsWithMacros_atoms_tokens_within_interval macrosA fuel origin holesA outsideA namesA
      first.1 bindingsA copiedA finalNamesA first.2 atomicA firstCopy tokenA memberA
  obtain ⟨counterB, lowerB, upperB, tokenEqB⟩ :=
    copyBindingsWithMacros_atoms_tokens_within_interval macrosB fuel origin holesB outsideB namesB
      second.1 bindingsB copiedB finalNamesB second.2 atomicB secondCopy tokenB memberB
  have generated := checkFresh_generated_tokens_differ certificate certificateAccepted
    first second firstMember secondMember different (a := counterA) (b := counterB)
    lowerA upperA lowerB upperB
  intro same
  apply generated
  rw [← tokenEqA, ← tokenEqB]
  exact same

theorem checkFresh_separates_counter_preserving_binding_tokens (certificate : Certificate)
    (certificateAccepted : checkFresh rules certificate = true)
    (first second : Nat × Nat)
    (firstMember : first ∈ freshIntervals certificate)
    (secondMember : second ∈ freshIntervals certificate)
    (different : first ≠ second)
    (fuel origin : Nat) (macrosA : List String) (holesA : Holes)
    (outsideA namesA : Renames) (bindingsA copiedA : List Tree)
    (finalNamesA : Renames) (safeA : CounterPreservingBindings macrosA bindingsA)
    (firstCopy : copyBindingsWithMacros macrosA fuel origin holesA outsideA namesA first.1
      bindingsA = some (copiedA, finalNamesA, first.2))
    (macrosB : List String) (holesB : Holes) (outsideB namesB : Renames)
    (bindingsB copiedB : List Tree) (finalNamesB : Renames)
    (safeB : CounterPreservingBindings macrosB bindingsB)
    (secondCopy : copyBindingsWithMacros macrosB fuel origin holesB outsideB namesB second.1
      bindingsB = some (copiedB, finalNamesB, second.2))
    (tokenA tokenB : Nat) (memberA : tokenA ∈ bindingTokens copiedA)
    (memberB : tokenB ∈ bindingTokens copiedB) : tokenA ≠ tokenB := by
  obtain ⟨counterA, lowerA, upperA, tokenEqA⟩ :=
    copyBindingsWithMacros_preserving_tokens_within_interval macrosA fuel origin holesA outsideA
      namesA first.1 bindingsA copiedA finalNamesA first.2 safeA firstCopy tokenA memberA
  obtain ⟨counterB, lowerB, upperB, tokenEqB⟩ :=
    copyBindingsWithMacros_preserving_tokens_within_interval macrosB fuel origin holesB outsideB
      namesB second.1 bindingsB copiedB finalNamesB second.2 safeB secondCopy tokenB memberB
  have generated := checkFresh_generated_tokens_differ certificate certificateAccepted
    first second firstMember secondMember different (a := counterA) (b := counterB)
    lowerA upperA lowerB upperB
  intro same
  apply generated
  rw [← tokenEqA, ← tokenEqB]
  exact same

theorem checkFresh_separates_macro_counter_safe_binding_tokens (certificate : Certificate)
    (certificateAccepted : checkFresh rules certificate = true)
    (first second : Nat × Nat)
    (firstMember : first ∈ freshIntervals certificate)
    (secondMember : second ∈ freshIntervals certificate)
    (different : first ≠ second)
    (fuel origin : Nat) (macrosA : List String) (holesA : Holes)
    (outsideA namesA : Renames) (bindingsA copiedA : List Tree)
    (finalNamesA : Renames) (safeA : MacroCounterSafeBindingInputs macrosA bindingsA)
    (firstCopy : copyBindingsWithMacros macrosA fuel origin holesA outsideA namesA first.1
      bindingsA = some (copiedA, finalNamesA, first.2))
    (macrosB : List String) (holesB : Holes) (outsideB namesB : Renames)
    (bindingsB copiedB : List Tree) (finalNamesB : Renames)
    (safeB : MacroCounterSafeBindingInputs macrosB bindingsB)
    (secondCopy : copyBindingsWithMacros macrosB fuel origin holesB outsideB namesB second.1
      bindingsB = some (copiedB, finalNamesB, second.2))
    (tokenA tokenB : Nat) (memberA : tokenA ∈ bindingTokens copiedA)
    (memberB : tokenB ∈ bindingTokens copiedB) : tokenA ≠ tokenB := by
  exact checkFresh_separates_counter_preserving_binding_tokens certificate certificateAccepted
    first second firstMember secondMember different fuel origin macrosA holesA outsideA namesA
    bindingsA copiedA finalNamesA (macroCounterSafeBindingInputs_preserving macrosA bindingsA safeA)
    firstCopy macrosB holesB outsideB namesB bindingsB copiedB finalNamesB
    (macroCounterSafeBindingInputs_preserving macrosB bindingsB safeB) secondCopy
    tokenA tokenB memberA memberB

theorem checkFresh_separates_case_copy_tokens (certificate : Certificate)
    (certificateAccepted : checkFresh rules certificate = true)
    (first second : Nat × Nat)
    (firstMember : first ∈ freshIntervals certificate)
    (secondMember : second ∈ freshIntervals certificate)
    (different : first ≠ second)
    (fuel origin : Nat) (macrosA : List String) (holesA : Holes) (namesA : Renames)
    (casesA copiedA : List Tree) (safeA : CounterPreservingCases macrosA casesA)
    (firstCopy : copyCasesWithMacros macrosA fuel origin holesA namesA first.1 casesA =
      some (copiedA, first.2))
    (macrosB : List String) (holesB : Holes) (namesB : Renames)
    (casesB copiedB : List Tree) (safeB : CounterPreservingCases macrosB casesB)
    (secondCopy : copyCasesWithMacros macrosB fuel origin holesB namesB second.1 casesB =
      some (copiedB, second.2))
    (tokenA tokenB : Nat) (memberA : tokenA ∈ counterPreservingCaseTokens copiedA)
    (memberB : tokenB ∈ counterPreservingCaseTokens copiedB) : tokenA ≠ tokenB := by
  obtain ⟨counterA, lowerA, upperA, tokenEqA⟩ :=
    copyCasesWithMacros_preserving_tokens_within_interval macrosA fuel origin holesA namesA
      first.1 casesA copiedA first.2 safeA firstCopy tokenA memberA
  obtain ⟨counterB, lowerB, upperB, tokenEqB⟩ :=
    copyCasesWithMacros_preserving_tokens_within_interval macrosB fuel origin holesB namesB
      second.1 casesB copiedB second.2 safeB secondCopy tokenB memberB
  have generated := checkFresh_generated_tokens_differ certificate certificateAccepted
    first second firstMember secondMember different (a := counterA) (b := counterB)
    lowerA upperA lowerB upperB
  intro same
  apply generated
  rw [← tokenEqA, ← tokenEqB]
  exact same

theorem checkFresh_separates_macro_counter_safe_case_tokens (certificate : Certificate)
    (certificateAccepted : checkFresh rules certificate = true)
    (first second : Nat × Nat)
    (firstMember : first ∈ freshIntervals certificate)
    (secondMember : second ∈ freshIntervals certificate)
    (different : first ≠ second)
    (fuel origin : Nat) (macrosA : List String) (holesA : Holes) (namesA : Renames)
    (casesA copiedA : List Tree) (safeA : MacroCounterSafeCases macrosA casesA)
    (firstCopy : copyCasesWithMacros macrosA fuel origin holesA namesA first.1 casesA =
      some (copiedA, first.2))
    (macrosB : List String) (holesB : Holes) (namesB : Renames)
    (casesB copiedB : List Tree) (safeB : MacroCounterSafeCases macrosB casesB)
    (secondCopy : copyCasesWithMacros macrosB fuel origin holesB namesB second.1 casesB =
      some (copiedB, second.2))
    (tokenA tokenB : Nat) (memberA : tokenA ∈ counterPreservingCaseTokens copiedA)
    (memberB : tokenB ∈ counterPreservingCaseTokens copiedB) : tokenA ≠ tokenB :=
  checkFresh_separates_case_copy_tokens certificate certificateAccepted first second firstMember
    secondMember different fuel origin macrosA holesA namesA casesA copiedA
    (macroCounterSafeCases_preserving macrosA casesA safeA) firstCopy macrosB holesB namesB
    casesB copiedB (macroCounterSafeCases_preserving macrosB casesB safeB) secondCopy tokenA tokenB
    memberA memberB

end NLisp.ExpansionCertificate
