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

/- Count the entries inspected while searching a list. A successful comparison
and each unsuccessful comparison both cost one unit. -/
def membershipWithCost {α : Type} [DecidableEq α] : List α → α → Bool × Nat
  | [], _ => (false, 0)
  | head :: tail, needle =>
      if head = needle then (true, 1)
      else
        let (found, cost) := membershipWithCost tail needle
        (found, cost + 1)

theorem membershipWithCost_result {α : Type} [DecidableEq α]
    (values : List α) (needle : α) :
    (membershipWithCost values needle).1 = decide (needle ∈ values) := by
  induction values with
  | nil => simp [membershipWithCost]
  | cons head tail ih =>
      by_cases same : head = needle
      · simp [membershipWithCost, same]
      · have notReversed : needle ≠ head := fun reversed => same reversed.symm
        simp [membershipWithCost, same, notReversed, ih]

theorem membershipWithCost_cost_le {α : Type} [DecidableEq α]
    (values : List α) (needle : α) :
    (membershipWithCost values needle).2 ≤ values.length := by
  induction values with
  | nil => simp [membershipWithCost]
  | cons head tail ih =>
      by_cases same : head = needle
      · simp [membershipWithCost, same]
      · simp only [membershipWithCost, same, if_neg same, List.length_cons]
        have tailBound := ih
        omega

/- The cost model covers rule dispatch, the parameter/argument walk, and the
actual number of entries inspected for rule membership after a successful
match. The `copyWithMacros` decision is still performed but its internal work
is not included in this partial cost. -/
noncomputable def checkStepWithMatchCost (rules : List (Nat × Tree))
    (origin fuel fresh final : Nat) (rule input output : Tree) : Bool × Nat :=
  let (matched, cost) := matchRuleWithCost rule input
  match matched with
  | none => (false, cost)
  | some (holes, template) =>
      let (member, memberCost) := membershipWithCost rules (origin, rule)
      (member &&
        decide (copyWithMacros (macroNames rules) fuel origin holes [] fresh template =
          some (output, final)), cost + memberCost)

theorem checkStepWithMatchCost_result (rules : List (Nat × Tree))
    (origin fuel fresh final : Nat) (rule input output : Tree) :
    (checkStepWithMatchCost rules origin fuel fresh final rule input output).1 =
      checkStep rules origin fuel fresh final rule input output := by
  simp only [checkStepWithMatchCost, matchRuleWithCost_result]
  cases matched : matchRule rule input with
  | none => simp [checkStep, matched]
  | some payload => simp [checkStep, matched, membershipWithCost_result]

theorem checkStepWithMatchCost_cost_le (rules : List (Nat × Tree))
    (origin fuel fresh final : Nat) (rule input output : Tree) :
    (checkStepWithMatchCost rules origin fuel fresh final rule input output).2 ≤
      matchRuleParameterCount rule + rules.length + 2 := by
  have matchedCost := matchRuleWithCost_cost_le_parameters_add_two rule input
  have memberCost := membershipWithCost_cost_le rules (origin, rule)
  unfold checkStepWithMatchCost
  cases matched : matchRuleWithCost rule input with
  | mk result cost =>
      have localBound : cost ≤ matchRuleParameterCount rule + 2 := by
        simpa [matched] using matchedCost
      cases result with
      | none => simp [matched]; omega
      | some payload =>
          simp only [matched]
          omega

noncomputable def check (rules : List (Nat × Tree)) : Certificate → Bool
  | .refl _ => true
  | .congList _ _ child => check rules child
  | .macroStep origin fuel fresh final rule input output =>
      checkStep rules origin fuel fresh final rule input output
  | .trans first second =>
      check rules first && check rules second && decide (target first = source second)

/- Explicit cost model for certificate constructor traversal. One unit is
charged per visited constructor. `macroStep` charges one unit for dispatch
only; the work inside `checkStep`/`copyWithMacros` and endpoint equality are
outside this basic measure. The bound charges both children of a trans node
even if Boolean short-circuiting skips the second. -/
noncomputable def checkWithTraversalCost (rules : List (Nat × Tree)) :
    Certificate → Bool × Nat
  | .refl _ => (true, 1)
  | .congList _ _ child =>
      let (accepted, cost) := checkWithTraversalCost rules child
      (accepted, cost + 1)
  | .macroStep origin fuel fresh final rule input output =>
      (checkStep rules origin fuel fresh final rule input output, 1)
  | .trans first second =>
      let (firstAccepted, firstCost) := checkWithTraversalCost rules first
      let (secondAccepted, secondCost) := checkWithTraversalCost rules second
      (firstAccepted && secondAccepted && decide (target first = source second),
        firstCost + secondCost + 1)

def certificateNodeCount : Certificate → Nat
  | .refl _ => 1
  | .congList _ _ child => certificateNodeCount child + 1
  | .macroStep _ _ _ _ _ _ _ => 1
  | .trans first second => certificateNodeCount first + certificateNodeCount second + 1

def freshIntervalCount (certificate : Certificate) : Nat :=
  (freshIntervals certificate).length

def certificateTransCount : Certificate → Nat
  | .refl _ => 0
  | .congList _ _ child => certificateTransCount child
  | .macroStep _ _ _ _ _ _ _ => 0
  | .trans first second => certificateTransCount first + certificateTransCount second + 1

noncomputable def certificateTransComparisonCost : Certificate → Nat
  | .refl _ => 0
  | .congList _ _ child => certificateTransComparisonCost child
  | .macroStep _ _ _ _ _ _ _ => 0
  | .trans first second =>
      certificateTransComparisonCost first + certificateTransComparisonCost second +
        treeNodeCount (target first)

noncomputable def certificateMaxEndpointNodes : Certificate → Nat
  | .refl tree => treeNodeCount tree
  | .congList pre suffix child =>
      max (treeNodeCount (source (.congList pre suffix child)))
        (max (treeNodeCount (target (.congList pre suffix child)))
          (certificateMaxEndpointNodes child))
  | .macroStep _ _ _ _ _ input output =>
      max (treeNodeCount input) (treeNodeCount output)
  | .trans first second =>
      max (treeNodeCount (target first))
        (max (certificateMaxEndpointNodes first) (certificateMaxEndpointNodes second))

/- Aggregate the syntax-node payload exposed by certificate endpoints. For a
trans node, also count the left endpoint that its composition check compares.
This is a structural-size measure, not a serialized-byte measure. -/
noncomputable def certificateEndpointPayloadNodes : Certificate → Nat
  | .refl tree => treeNodeCount tree
  | .congList pre suffix child =>
      treeNodeCount (source (.congList pre suffix child)) +
        (treeNodeCount (target (.congList pre suffix child)) +
          certificateEndpointPayloadNodes child)
  | .macroStep _ _ _ _ _ input output => treeNodeCount input + treeNodeCount output
  | .trans first second =>
      treeNodeCount (target first) +
        (certificateEndpointPayloadNodes first + certificateEndpointPayloadNodes second)

theorem certificateMaxEndpointNodes_le_payload (certificate : Certificate) :
    certificateMaxEndpointNodes certificate ≤ certificateEndpointPayloadNodes certificate := by
  induction certificate with
  | refl tree => simp [certificateMaxEndpointNodes, certificateEndpointPayloadNodes]
  | congList pre suffix child ih =>
      simp only [certificateMaxEndpointNodes, certificateEndpointPayloadNodes]
      apply Nat.max_le.mpr
      constructor
      · omega
      · apply Nat.max_le.mpr
        constructor <;> omega
  | macroStep origin fuel fresh final rule input output =>
      simp only [certificateMaxEndpointNodes, certificateEndpointPayloadNodes]
      apply Nat.max_le.mpr
      constructor <;> omega
  | trans first second ihFirst ihSecond =>
      simp only [certificateMaxEndpointNodes, certificateEndpointPayloadNodes]
      apply Nat.max_le.mpr
      constructor
      · omega
      · apply Nat.max_le.mpr
        constructor <;> omega

theorem certificateTransComparisonCost_le_count_mul_max (certificate : Certificate) :
    certificateTransComparisonCost certificate ≤
      certificateTransCount certificate * certificateMaxEndpointNodes certificate := by
  induction certificate with
  | refl tree => simp [certificateTransComparisonCost, certificateTransCount]
  | congList pre suffix child ih =>
      have maxBound : certificateMaxEndpointNodes child ≤
          certificateMaxEndpointNodes (.congList pre suffix child) := by
        change certificateMaxEndpointNodes child ≤
          max (treeNodeCount (source (.congList pre suffix child)))
            (max (treeNodeCount (target (.congList pre suffix child)))
              (certificateMaxEndpointNodes child))
        exact Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)
      have scaled := Nat.mul_le_mul_left (certificateTransCount child) maxBound
      simpa [certificateTransComparisonCost, certificateTransCount] using
        Nat.le_trans ih scaled
  | macroStep origin fuel fresh final rule input output =>
      simp [certificateTransComparisonCost, certificateTransCount]
  | trans first second ihFirst ihSecond =>
      have firstMax : certificateMaxEndpointNodes first ≤
          certificateMaxEndpointNodes (.trans first second) := by
        simp only [certificateMaxEndpointNodes]
        exact Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)
      have secondMax : certificateMaxEndpointNodes second ≤
          certificateMaxEndpointNodes (.trans first second) := by
        simp only [certificateMaxEndpointNodes]
        exact Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)
      have endpointMax : treeNodeCount (target first) ≤
          certificateMaxEndpointNodes (.trans first second) := by
        simp only [certificateMaxEndpointNodes]
        exact Nat.le_max_left _ _
      have firstCost := Nat.le_trans ihFirst
        (Nat.mul_le_mul_left (certificateTransCount first) firstMax)
      have secondCost := Nat.le_trans ihSecond
        (Nat.mul_le_mul_left (certificateTransCount second) secondMax)
      have combined :
          certificateTransComparisonCost first + certificateTransComparisonCost second +
            treeNodeCount (target first) ≤
          certificateTransCount first * certificateMaxEndpointNodes (.trans first second) +
            certificateTransCount second * certificateMaxEndpointNodes (.trans first second) +
            certificateMaxEndpointNodes (.trans first second) := by
        omega
      have factor :
          certificateTransCount first * certificateMaxEndpointNodes (.trans first second) +
            certificateTransCount second * certificateMaxEndpointNodes (.trans first second) +
            certificateMaxEndpointNodes (.trans first second) =
          (certificateTransCount first + certificateTransCount second + 1) *
            certificateMaxEndpointNodes (.trans first second) := by
        simp [Nat.add_mul, Nat.mul_add, Nat.one_mul]
      simpa [certificateTransComparisonCost, certificateTransCount, factor] using combined

theorem freshIntervalCount_le_nodes (certificate : Certificate) :
    freshIntervalCount certificate ≤ certificateNodeCount certificate := by
  induction certificate with
  | refl _ => simp [freshIntervalCount, freshIntervals, certificateNodeCount]
  | congList _ _ child ih =>
      simpa [freshIntervalCount, freshIntervals, certificateNodeCount] using Nat.le_succ_of_le ih
  | macroStep _ _ _ _ _ _ _ => simp [freshIntervalCount, freshIntervals, certificateNodeCount]
  | trans first second ihFirst ihSecond =>
      have firstBound : (freshIntervals first).length ≤ certificateNodeCount first := by
        simpa [freshIntervalCount] using ihFirst
      have secondBound : (freshIntervals second).length ≤ certificateNodeCount second := by
        simpa [freshIntervalCount] using ihSecond
      simp only [freshIntervalCount, freshIntervals, certificateNodeCount, List.length_append]
      omega

/- This counts the number of interval-pair predicate calls made by the
quadratic tail scan in `disjointIntervals`; it does not count the bit cost of
the Nat comparisons themselves. -/
def intervalPairComparisonCost : List (Nat × Nat) → Nat
  | [] => 0
  | _ :: tail => tail.length + intervalPairComparisonCost tail

/- Instrument the pairwise interval scan used by `List.all`. The model counts
one unit for each call to `separated`; endpoint checks are counted separately
by `disjointIntervalsWithCost`. -/
def separatedManyWithCost (interval : Nat × Nat) : List (Nat × Nat) → Bool × Nat
  | [] => (true, 0)
  | other :: tail =>
      if separated interval other then
        let (accepted, cost) := separatedManyWithCost interval tail
        (accepted, cost + 1)
      else (false, 1)

theorem separatedManyWithCost_result (interval : Nat × Nat)
    (others : List (Nat × Nat)) :
    (separatedManyWithCost interval others).1 = others.all (separated interval) := by
  induction others with
  | nil => rfl
  | cons head tail ih =>
      cases separated interval head <;> simp [separatedManyWithCost, ih]

theorem separatedManyWithCost_cost_le (interval : Nat × Nat)
    (others : List (Nat × Nat)) :
    (separatedManyWithCost interval others).2 ≤ others.length := by
  induction others with
  | nil => simp [separatedManyWithCost]
  | cons head tail ih =>
      cases separated interval head with
      | false => simp [separatedManyWithCost, List.length_cons]
      | true =>
          simp only [separatedManyWithCost, List.length_cons]
          omega

def disjointIntervalsWithCost : List (Nat × Nat) → Bool × Nat
  | [] => (true, 0)
  | interval :: tail =>
      if decide (interval.1 ≤ interval.2) then
        let (pairwise, pairCost) := separatedManyWithCost interval tail
        if pairwise then
          let (rest, restCost) := disjointIntervalsWithCost tail
          (rest, pairCost + restCost + 1)
        else (false, pairCost + 1)
      else (false, 1)

theorem disjointIntervalsWithCost_result (intervals : List (Nat × Nat)) :
    (disjointIntervalsWithCost intervals).1 = disjointIntervals intervals := by
  induction intervals with
  | nil => rfl
  | cons interval tail ih =>
      cases bound : decide (interval.1 ≤ interval.2) with
      | false => simp [disjointIntervalsWithCost, disjointIntervals, bound]
      | true =>
          cases pairwise : (separatedManyWithCost interval tail).1 with
          | false =>
              simp [disjointIntervalsWithCost, disjointIntervals, bound, pairwise,
                separatedManyWithCost_result]
          | true =>
              simp [disjointIntervalsWithCost, disjointIntervals, bound, pairwise,
                separatedManyWithCost_result, ih]

theorem disjointIntervalsWithCost_cost_le (intervals : List (Nat × Nat)) :
    (disjointIntervalsWithCost intervals).2 ≤
      intervalPairComparisonCost intervals + intervals.length := by
  induction intervals with
  | nil => rfl
  | cons interval tail ih =>
      have pairBound := separatedManyWithCost_cost_le interval tail
      simp only [disjointIntervalsWithCost, intervalPairComparisonCost, List.length_cons]
      by_cases bound : decide (interval.1 ≤ interval.2) = true
      · cases pairwise : (separatedManyWithCost interval tail).1 with
        | false => simp [bound, pairwise]; omega
        | true => simp [bound, pairwise]; omega
      · simp [bound]
        omega

theorem intervalPairComparisonCost_le_square (intervals : List (Nat × Nat)) :
    intervalPairComparisonCost intervals ≤ intervals.length * intervals.length := by
  induction intervals with
  | nil => simp [intervalPairComparisonCost]
  | cons head tail ih =>
      simp only [intervalPairComparisonCost, List.length_cons]
      calc
        tail.length + intervalPairComparisonCost tail ≤
            tail.length + tail.length * tail.length := Nat.add_le_add_left ih _
        _ ≤ (tail.length + 1) * (tail.length + 1) := by
          rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]
          simp only [Nat.one_mul, Nat.mul_one]
          omega

def checkFreshStructuralCost (certificate : Certificate) : Nat :=
  certificateNodeCount certificate + intervalPairComparisonCost (freshIntervals certificate)

theorem checkFreshStructuralCost_polynomial (certificate : Certificate) :
    checkFreshStructuralCost certificate ≤
      certificateNodeCount certificate + certificateNodeCount certificate *
        certificateNodeCount certificate := by
  have intervalsBound := freshIntervalCount_le_nodes certificate
  have comparisonsBound := intervalPairComparisonCost_le_square (freshIntervals certificate)
  have squareBound := Nat.mul_le_mul intervalsBound intervalsBound
  unfold checkFreshStructuralCost
  calc
    certificateNodeCount certificate + intervalPairComparisonCost (freshIntervals certificate) ≤
        certificateNodeCount certificate + freshIntervalCount certificate * freshIntervalCount certificate :=
      Nat.add_le_add_left comparisonsBound _
    _ ≤ certificateNodeCount certificate + certificateNodeCount certificate *
        certificateNodeCount certificate := Nat.add_le_add_left squareBound _

theorem checkWithTraversalCost_result (rules : List (Nat × Tree)) (certificate : Certificate) :
    (checkWithTraversalCost rules certificate).1 = check rules certificate := by
  induction certificate with
  | refl tree => rfl
  | congList _ _ child ih => simp [checkWithTraversalCost, check, ih]
  | macroStep origin fuel fresh final rule input output => rfl
  | trans first second ihFirst ihSecond => simp [checkWithTraversalCost, check, ihFirst, ihSecond]

theorem checkWithTraversalCost_le_nodes (rules : List (Nat × Tree))
    (certificate : Certificate) :
    (checkWithTraversalCost rules certificate).2 ≤ certificateNodeCount certificate := by
  induction certificate with
  | refl _ => simp [checkWithTraversalCost, certificateNodeCount]
  | congList _ _ child ih => simp [checkWithTraversalCost, certificateNodeCount, ih]
  | macroStep _ _ _ _ _ _ _ => simp [checkWithTraversalCost, certificateNodeCount]
  | trans first second ihFirst ihSecond =>
      simp [checkWithTraversalCost, certificateNodeCount, ihFirst, ihSecond]
      omega

theorem certificateTransCount_le_nodes (certificate : Certificate) :
    certificateTransCount certificate ≤ certificateNodeCount certificate := by
  induction certificate with
  | refl tree => simp [certificateTransCount, certificateNodeCount]
  | congList pre suffix child ih =>
      simpa [certificateTransCount, certificateNodeCount] using Nat.le_succ_of_le ih
  | macroStep origin fuel fresh final rule input output =>
      simp [certificateTransCount, certificateNodeCount]
  | trans first second ihFirst ihSecond =>
      simp only [certificateTransCount, certificateNodeCount]
      omega

noncomputable def checkWithMatchTraversalCost (rules : List (Nat × Tree)) :
    Certificate → Bool × Nat
  | .refl _ => (true, 1)
  | .congList _ _ child =>
      let (accepted, cost) := checkWithMatchTraversalCost rules child
      (accepted, cost + 1)
  | .macroStep origin fuel fresh final rule input output =>
      checkStepWithMatchCost rules origin fuel fresh final rule input output
  | .trans first second =>
      let (firstAccepted, firstCost) := checkWithMatchTraversalCost rules first
      let (secondAccepted, secondCost) := checkWithMatchTraversalCost rules second
      let (connected, comparisonCost) :=
        treeEqWithWorstCaseCost (target first) (source second)
      (firstAccepted && secondAccepted && connected,
        firstCost + secondCost + comparisonCost + 2)

noncomputable def certificateMatchCostBound (rules : List (Nat × Tree)) : Certificate → Nat
  | .refl _ => 1
  | .congList _ _ child => certificateMatchCostBound rules child + 1
  | .macroStep _ _ _ _ rule _ _ => matchRuleParameterCount rule + rules.length + 2
  | .trans first second =>
      certificateMatchCostBound rules first + certificateMatchCostBound rules second +
        treeNodeCount (target first) + 2

def certificateMacroStepCount : Certificate → Nat
  | .refl _ => 0
  | .congList _ _ child => certificateMacroStepCount child
  | .macroStep _ _ _ _ _ _ _ => 1
  | .trans first second => certificateMacroStepCount first + certificateMacroStepCount second

def certificateMacroParameterTotal : Certificate → Nat
  | .refl _ => 0
  | .congList _ _ child => certificateMacroParameterTotal child
  | .macroStep _ _ _ _ rule _ _ => matchRuleParameterCount rule
  | .trans first second =>
      certificateMacroParameterTotal first + certificateMacroParameterTotal second

theorem certificateMatchCostBound_eq_components (rules : List (Nat × Tree))
    (certificate : Certificate) :
    certificateMatchCostBound rules certificate =
      certificateNodeCount certificate + certificateMacroParameterTotal certificate +
        certificateMacroStepCount certificate * (rules.length + 1) +
        certificateTransCount certificate + certificateTransComparisonCost certificate := by
  induction certificate with
  | refl tree => simp [certificateMatchCostBound, certificateNodeCount,
      certificateMacroParameterTotal, certificateMacroStepCount, certificateTransCount,
      certificateTransComparisonCost]
  | congList pre suffix child ih =>
      simpa [certificateMatchCostBound, certificateNodeCount,
        certificateMacroParameterTotal, certificateMacroStepCount, certificateTransCount,
        certificateTransComparisonCost] using ih
  | macroStep origin fuel fresh final rule input output =>
      simp [certificateMatchCostBound, certificateNodeCount,
        certificateMacroParameterTotal, certificateMacroStepCount, certificateTransCount,
        certificateTransComparisonCost]
      omega
  | trans first second ihFirst ihSecond =>
      simp only [certificateMatchCostBound, certificateNodeCount,
        certificateMacroParameterTotal, certificateMacroStepCount, certificateTransCount,
        certificateTransComparisonCost]
      rw [ihFirst, ihSecond]
      rw [Nat.add_mul]
      omega

theorem certificateMacroStepCount_le_nodes (certificate : Certificate) :
    certificateMacroStepCount certificate ≤ certificateNodeCount certificate := by
  induction certificate with
  | refl tree => simp [certificateMacroStepCount, certificateNodeCount]
  | congList pre suffix child ih =>
      simpa [certificateMacroStepCount, certificateNodeCount] using Nat.le_succ_of_le ih
  | macroStep origin fuel fresh final rule input output => simp [certificateMacroStepCount,
      certificateNodeCount]
  | trans first second ihFirst ihSecond =>
      simp only [certificateMacroStepCount, certificateNodeCount]
      omega

theorem certificateMatchCostBound_le_structural_bound (rules : List (Nat × Tree))
    (certificate : Certificate) :
    certificateMatchCostBound rules certificate ≤
      certificateNodeCount certificate + certificateMacroParameterTotal certificate +
        certificateNodeCount certificate * (rules.length + 1) +
        certificateTransCount certificate + certificateTransComparisonCost certificate := by
  rw [certificateMatchCostBound_eq_components]
  have stepsBound := certificateMacroStepCount_le_nodes certificate
  have scaledBound := Nat.mul_le_mul_right (rules.length + 1) stepsBound
  have baseBound := Nat.add_le_add_left scaledBound
    (certificateNodeCount certificate + certificateMacroParameterTotal certificate)
  have withTransBound := Nat.add_le_add_right baseBound (certificateTransCount certificate)
  exact Nat.add_le_add_right withTransBound (certificateTransComparisonCost certificate)

theorem certificateMatchCostBound_le_endpoint_polynomial (rules : List (Nat × Tree))
    (certificate : Certificate) :
    certificateMatchCostBound rules certificate ≤
      certificateNodeCount certificate + certificateMacroParameterTotal certificate +
        certificateNodeCount certificate * (rules.length + 1) +
        certificateNodeCount certificate +
        certificateNodeCount certificate * certificateMaxEndpointNodes certificate := by
  have structuralBound := certificateMatchCostBound_le_structural_bound rules certificate
  have comparisonsBound := certificateTransComparisonCost_le_count_mul_max certificate
  have transBound := certificateTransCount_le_nodes certificate
  have scaledTransBound := Nat.mul_le_mul_right (certificateMaxEndpointNodes certificate) transBound
  have comparisonBound := Nat.le_trans comparisonsBound scaledTransBound
  omega

theorem checkWithMatchTraversalCost_result (rules : List (Nat × Tree))
    (certificate : Certificate) :
    (checkWithMatchTraversalCost rules certificate).1 = check rules certificate := by
  induction certificate with
  | refl tree => rfl
  | congList pre suffix child ih => simp [checkWithMatchTraversalCost, check, ih]
  | macroStep origin fuel fresh final rule input output =>
      exact checkStepWithMatchCost_result rules origin fuel fresh final rule input output
  | trans first second ihFirst ihSecond =>
      simp [checkWithMatchTraversalCost, check, treeEqWithWorstCaseCost_result,
        ihFirst, ihSecond]

theorem checkWithMatchTraversalCost_le_bound (rules : List (Nat × Tree))
    (certificate : Certificate) :
    (checkWithMatchTraversalCost rules certificate).2 ≤ certificateMatchCostBound rules certificate := by
  induction certificate with
  | refl tree => simp [checkWithMatchTraversalCost, certificateMatchCostBound]
  | congList pre suffix child ih =>
      simp [checkWithMatchTraversalCost, certificateMatchCostBound, ih]
      omega
  | macroStep origin fuel fresh final rule input output =>
      simpa [checkWithMatchTraversalCost, certificateMatchCostBound] using
        checkStepWithMatchCost_cost_le rules origin fuel fresh final rule input output
  | trans first second ihFirst ihSecond =>
      simp [checkWithMatchTraversalCost, certificateMatchCostBound,
        treeEqWithWorstCaseCost_cost, ihFirst, ihSecond]
      omega

noncomputable def checkFresh (rules : List (Nat × Tree)) (certificate : Certificate) : Bool :=
  disjointIntervals (freshIntervals certificate) && check rules certificate

/- Combined partial cost for freshness checking, rule matching, and trans
endpoint tree comparison. Other syntax payload traversals, the `copyWithMacros`
predicate, and Nat bit operations remain outside this model. -/
noncomputable def checkFreshWithMatchCost (rules : List (Nat × Tree))
    (certificate : Certificate) : Bool × Nat :=
  let (intervalsAccepted, intervalCost) :=
    disjointIntervalsWithCost (freshIntervals certificate)
  let (certificateAccepted, certificateCost) :=
    checkWithMatchTraversalCost rules certificate
  (intervalsAccepted && certificateAccepted, intervalCost + certificateCost)

theorem checkFreshWithMatchCost_result (rules : List (Nat × Tree))
    (certificate : Certificate) :
    (checkFreshWithMatchCost rules certificate).1 = checkFresh rules certificate := by
  simp [checkFreshWithMatchCost, checkFresh, disjointIntervalsWithCost_result,
    checkWithMatchTraversalCost_result]

theorem checkFreshWithMatchCost_le_partial_bound (rules : List (Nat × Tree))
    (certificate : Certificate) :
    (checkFreshWithMatchCost rules certificate).2 ≤
      certificateMatchCostBound rules certificate +
        certificateNodeCount certificate * certificateNodeCount certificate +
        certificateNodeCount certificate := by
  have intervalBound := disjointIntervalsWithCost_cost_le (freshIntervals certificate)
  have matchBound := checkWithMatchTraversalCost_le_bound rules certificate
  have countBound := freshIntervalCount_le_nodes certificate
  have pairBound := intervalPairComparisonCost_le_square (freshIntervals certificate)
  have squareBound := Nat.mul_le_mul countBound countBound
  have intervalCostBound :
      (disjointIntervalsWithCost (freshIntervals certificate)).2 ≤
        certificateNodeCount certificate * certificateNodeCount certificate +
          certificateNodeCount certificate := by
    calc
      (disjointIntervalsWithCost (freshIntervals certificate)).2 ≤
          intervalPairComparisonCost (freshIntervals certificate) +
            (freshIntervals certificate).length := intervalBound
      _ ≤ freshIntervalCount certificate * freshIntervalCount certificate +
            certificateNodeCount certificate := by
          exact Nat.add_le_add pairBound (by simpa [freshIntervalCount] using countBound)
      _ ≤ certificateNodeCount certificate * certificateNodeCount certificate +
            certificateNodeCount certificate := by
          exact Nat.add_le_add_right squareBound _
  simp only [checkFreshWithMatchCost]
  omega

theorem checkFreshWithMatchCost_le_structural_bound (rules : List (Nat × Tree))
    (certificate : Certificate) :
    (checkFreshWithMatchCost rules certificate).2 ≤
      certificateNodeCount certificate + certificateMacroParameterTotal certificate +
        certificateNodeCount certificate * (rules.length + 1) +
        certificateNodeCount certificate * certificateNodeCount certificate +
        certificateNodeCount certificate + certificateNodeCount certificate +
        certificateTransComparisonCost certificate := by
  have freshBound := checkFreshWithMatchCost_le_partial_bound rules certificate
  have matchingBound := certificateMatchCostBound_le_structural_bound rules certificate
  have transBound := certificateTransCount_le_nodes certificate
  omega

theorem checkFreshWithMatchCost_le_endpoint_polynomial (rules : List (Nat × Tree))
    (certificate : Certificate) :
    (checkFreshWithMatchCost rules certificate).2 ≤
      certificateNodeCount certificate + certificateMacroParameterTotal certificate +
        certificateNodeCount certificate * (rules.length + 1) +
        certificateNodeCount certificate * certificateNodeCount certificate +
        certificateNodeCount certificate + certificateNodeCount certificate +
        certificateNodeCount certificate * certificateMaxEndpointNodes certificate := by
  have freshBound := checkFreshWithMatchCost_le_partial_bound rules certificate
  have matchingBound := certificateMatchCostBound_le_endpoint_polynomial rules certificate
  omega

theorem checkFreshWithMatchCost_le_payload_polynomial (rules : List (Nat × Tree))
    (certificate : Certificate) :
    (checkFreshWithMatchCost rules certificate).2 ≤
      certificateNodeCount certificate + certificateMacroParameterTotal certificate +
        certificateNodeCount certificate * (rules.length + 1) +
        certificateNodeCount certificate * certificateNodeCount certificate +
        certificateNodeCount certificate + certificateNodeCount certificate +
        certificateNodeCount certificate * certificateEndpointPayloadNodes certificate := by
  have endpointBound := checkFreshWithMatchCost_le_endpoint_polynomial rules certificate
  have payloadBound := certificateMaxEndpointNodes_le_payload certificate
  have scaledBound := Nat.mul_le_mul_left (certificateNodeCount certificate) payloadBound
  omega

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
