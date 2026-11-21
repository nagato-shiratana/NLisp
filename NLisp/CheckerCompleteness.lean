import NLisp.PolymorphicSafety
import NLisp.ErasureExecution

namespace NLisp.Surface
open ExpansionLowering

/- A structural upper bound for checking type annotations. Each recursive type
node and each element of a function-parameter list consumes one unit. -/
mutual
def checkerTypeFuel : Ty → Nat
  | .boolean | .integer | .unit | .var _ => 1
  | .fn parameters result => max (checkerTypesFuel parameters) (checkerTypeFuel result) + 1
  | .list element | .option element => checkerTypeFuel element + 1

def checkerTypesFuel : List Ty → Nat
  | [] => 1
  | type :: tail => max (checkerTypeFuel type) (checkerTypesFuel tail) + 1
end

mutual
theorem checkWF_sufficient (type : Ty) (count fuel : Nat)
    (valid : type.wellFormed count) (enough : checkerTypeFuel type ≤ fuel) :
    ∃ checked, checkWF fuel count type = some checked := by
  cases fuel with
  | zero => cases type <;> simp [checkerTypeFuel, checkerTypesFuel] at enough
  | succ fuel =>
    cases type with
    | boolean =>
      refine ⟨⟨True.intro⟩, ?_⟩
      simp [checkWF]
    | integer =>
      refine ⟨⟨True.intro⟩, ?_⟩
      simp [checkWF]
    | unit =>
      refine ⟨⟨True.intro⟩, ?_⟩
      simp [checkWF]
    | var index =>
      have bound : index < count := by simpa [Ty.wellFormed] using valid
      have wellFormed : (Ty.var index).wellFormed count := by
        simpa [Ty.wellFormed] using bound
      refine ⟨⟨wellFormed⟩, ?_⟩
      simp [checkWF, bound]
    | fn parameters result =>
      simp only [checkerTypeFuel] at enough
      have parametersBound : checkerTypesFuel parameters ≤ fuel := by omega
      have resultBound : checkerTypeFuel result ≤ fuel := by omega
      have validParts : (∀ t ∈ parameters, t.wellFormed count) ∧ result.wellFormed count := by
        simpa [Ty.wellFormed] using valid
      have parametersValid : ∀ t ∈ parameters, t.wellFormed count := validParts.1
      have resultValid : result.wellFormed count := validParts.2
      obtain ⟨parametersChecked, parametersOK⟩ :=
        checkTypesWF_sufficient parameters count fuel parametersValid parametersBound
      obtain ⟨resultChecked, resultOK⟩ :=
        checkWF_sufficient result count fuel resultValid resultBound
      have wholeValid : (Ty.fn parameters result).wellFormed count := by
        simpa [Ty.wellFormed] using And.intro parametersChecked.down resultChecked.down
      refine ⟨⟨wholeValid⟩, ?_⟩
      simp [checkWF, parametersOK, resultOK]
    | list element =>
      have elementBound : checkerTypeFuel element ≤ fuel := by
        simp only [checkerTypeFuel] at enough
        omega
      have elementValid : element.wellFormed count := by
        simpa [Ty.wellFormed] using valid
      obtain ⟨checked, checkedOK⟩ := checkWF_sufficient element count fuel elementValid elementBound
      have wholeValid : (Ty.list element).wellFormed count := by
        simpa [Ty.wellFormed] using checked.down
      refine ⟨⟨wholeValid⟩, ?_⟩
      simp [checkWF, checkedOK]
    | option element =>
      have elementBound : checkerTypeFuel element ≤ fuel := by
        simp only [checkerTypeFuel] at enough
        omega
      have elementValid : element.wellFormed count := by
        simpa [Ty.wellFormed] using valid
      obtain ⟨checked, checkedOK⟩ := checkWF_sufficient element count fuel elementValid elementBound
      have wholeValid : (Ty.option element).wellFormed count := by
        simpa [Ty.wellFormed] using checked.down
      refine ⟨⟨wholeValid⟩, ?_⟩
      simp [checkWF, checkedOK]

theorem checkTypesWF_sufficient (types : List Ty) (count fuel : Nat)
    (valid : ∀ t ∈ types, t.wellFormed count) (enough : checkerTypesFuel types ≤ fuel) :
    ∃ checked, checkTypesWF fuel count types = some checked := by
  cases fuel with
  | zero => cases types <;> simp [checkerTypesFuel, checkerTypeFuel] at enough
  | succ fuel =>
    cases types with
    | nil =>
      refine ⟨⟨by simp⟩, ?_⟩
      simp [checkTypesWF]
    | cons head tail =>
      have headBound : checkerTypeFuel head ≤ fuel := by
        simp only [checkerTypesFuel] at enough
        omega
      have tailBound : checkerTypesFuel tail ≤ fuel := by
        simp only [checkerTypesFuel] at enough
        omega
      have headValid := valid head (by simp)
      have tailValid : ∀ t ∈ tail, t.wellFormed count := by
        intro t member
        exact valid t (by simp [member])
      obtain ⟨headChecked, headOK⟩ := checkWF_sufficient head count fuel headValid headBound
      obtain ⟨tailChecked, tailOK⟩ := checkTypesWF_sufficient tail count fuel tailValid tailBound
      refine ⟨⟨fun t member => ?_⟩, ?_⟩
      · exact valid t (by simp [member])
      · simp [checkTypesWF, headOK, tailOK]
end

/-- A structural fuel bound for validating both parameter types and the result
type of a signature. This composes the type and type-list bounds above. -/
def checkerSignatureFuel (signature : Signature) : Nat :=
  checkerTypesFuel signature.parameters + checkerTypeFuel signature.result + 1

theorem checkSignatureWF_sufficient (signature : Signature)
    (valid : signature.wellFormed) :
    ∃ parametersChecked resultChecked,
      checkTypesWF (checkerSignatureFuel signature) signature.typeArity signature.parameters =
        some parametersChecked ∧
      checkWF (checkerSignatureFuel signature) signature.typeArity signature.result =
        some resultChecked := by
  have parts :
      (∀ type ∈ signature.parameters, type.wellFormed signature.typeArity) ∧
        signature.result.wellFormed signature.typeArity := by
    simpa [Signature.wellFormed] using valid
  obtain ⟨parametersChecked, parametersAccepted⟩ :=
    checkTypesWF_sufficient signature.parameters signature.typeArity
      (checkerSignatureFuel signature) parts.1 (by
        simp [checkerSignatureFuel]
        omega)
  obtain ⟨resultChecked, resultAccepted⟩ :=
    checkWF_sufficient signature.result signature.typeArity
      (checkerSignatureFuel signature) parts.2 (by
        simp [checkerSignatureFuel]
        omega)
  exact ⟨parametersChecked, resultChecked, parametersAccepted, resultAccepted⟩

theorem checkWF_sufficient_proof (type : Ty) (count fuel : Nat)
    (valid : type.wellFormed count) (enough : checkerTypeFuel type ≤ fuel) :
    checkWF fuel count type = some ⟨valid⟩ := by
  obtain ⟨checked, accepted⟩ := checkWF_sufficient type count fuel valid enough
  cases checked with
  | up checkedProof =>
      have proofEq : checkedProof = valid := Subsingleton.elim _ _
      subst checkedProof
      exact accepted

theorem checkTypesWF_sufficient_proof (types : List Ty) (count fuel : Nat)
    (valid : ∀ t ∈ types, t.wellFormed count) (enough : checkerTypesFuel types ≤ fuel) :
    checkTypesWF fuel count types = some ⟨valid⟩ := by
  obtain ⟨checked, accepted⟩ := checkTypesWF_sufficient types count fuel valid enough
  cases checked with
  | up checkedProof =>
      have proofEq : checkedProof = valid := Subsingleton.elim _ _
      subst checkedProof
      exact accepted

theorem checkWF_structural_bound {type : Ty} {count : Nat}
    (valid : type.wellFormed count) :
    ∃ bound, bound ≤ checkerTypeFuel type ∧
      ∀ fuel, bound ≤ fuel → checkWF fuel count type = some ⟨valid⟩ := by
  refine ⟨checkerTypeFuel type, Nat.le_refl _, ?_⟩
  intro fuel enough
  exact checkWF_sufficient_proof type count fuel valid enough

theorem checkTypesWF_structural_bound {types : List Ty} {count : Nat}
    (valid : ∀ t ∈ types, t.wellFormed count) :
    ∃ bound, bound ≤ checkerTypesFuel types ∧
      ∀ fuel, bound ≤ fuel → checkTypesWF fuel count types = some ⟨valid⟩ := by
  refine ⟨checkerTypesFuel types, Nat.le_refl _, ?_⟩
  intro fuel enough
  exact checkTypesWF_sufficient_proof types count fuel valid enough

theorem checkSignatureWF_structural_bound {signature : Signature}
    (valid : signature.wellFormed) :
    ∃ bound, bound ≤ checkerSignatureFuel signature ∧ ∀ fuel, bound ≤ fuel →
      (checkTypesWF fuel signature.typeArity signature.parameters =
          some ⟨valid.1⟩) ∧
      (checkWF fuel signature.typeArity signature.result = some ⟨valid.2⟩) := by
  refine ⟨checkerSignatureFuel signature, Nat.le_refl _, ?_⟩
  intro fuel enough
  constructor
  · exact checkTypesWF_sufficient_proof signature.parameters signature.typeArity fuel
      valid.1 (by simp [checkerSignatureFuel] at enough ⊢; omega)
  · exact checkWF_sufficient_proof signature.result signature.typeArity fuel
      valid.2 (by simp [checkerSignatureFuel] at enough ⊢; omega)

def checkerSignaturesFuel : List Signature → Nat
  | [] => 1
  | signature :: tail => max (checkerSignatureFuel signature) (checkerSignaturesFuel tail) + 1

theorem checkerSignatureFuel_le_of_mem (signature : Signature) (signatures : List Signature)
    (member : signature ∈ signatures) : checkerSignatureFuel signature ≤ checkerSignaturesFuel signatures := by
  induction signatures with
  | nil => simp at member
  | cons head tail ih =>
      simp only [List.mem_cons] at member
      rcases member with same | member
      · subst signature
        simp only [checkerSignaturesFuel]
        exact Nat.le_trans (Nat.le_max_left _ _) (Nat.le_succ _)
      · have tailBound := ih member
        simp only [checkerSignaturesFuel]
        exact Nat.le_trans tailBound
          (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_succ _))

private theorem signature_mem_of_getElem? {signatures : List Signature} {index : Nat}
    {signature : Signature} (found : signatures[index]? = some signature) :
    signature ∈ signatures := by
  induction signatures generalizing index with
  | nil =>
      have impossible : False := by
        have indexInvalid : ¬ index < 0 := by omega
        simp [getElem?_def, indexInvalid] at found
      exact False.elim impossible
  | cons head tail ih =>
      cases index with
      | zero =>
          have foundHead : some head = some signature := by
            simpa [getElem?_def] using found
          have headEq := Option.some.inj foundHead
          subst signature
          simp
      | succ index =>
          have foundTail : tail[index]? = some signature := by
            simpa [getElem?_def, List.length_cons, Nat.succ_lt_succ_iff] using found
          exact List.mem_cons_of_mem _ (ih foundTail)

theorem checkerSignatureFuel_le_of_lookup {signatures : List Signature} {index : Nat}
    {signature : Signature} (found : signatures[index]? = some signature) :
    checkerSignatureFuel signature ≤ checkerSignaturesFuel signatures :=
  checkerSignatureFuel_le_of_mem signature signatures (signature_mem_of_getElem? found)

/- A computable structural fuel bound for the expression checker. -/
mutual
def checkerExprFuel (globals : List Signature) (expression : Expr) : Nat :=
  match expression with
  | .var _ | .bool _ | .int _ | .unit => 1
  | .global _ typeArguments => checkerTypesFuel typeArguments + checkerSignaturesFuel globals + 1
  | .lam parameters result body =>
      checkerTypesFuel parameters + checkerTypeFuel result + checkerExprFuel globals body + 1
  | .app function arguments =>
      checkerExprFuel globals function + checkerExprsFuel globals arguments + 1
  | .ite condition yes no =>
      checkerExprFuel globals condition + checkerExprFuel globals yes + checkerExprFuel globals no + 1
  | .add left right | .sub left right | .mul left right | .le left right | .intEq left right =>
      checkerExprFuel globals left + checkerExprFuel globals right + 1
  | .letMany types initializers body =>
      checkerTypesFuel types + checkerExprsFuel globals initializers + checkerExprFuel globals body + 1
  | .begin first rest => checkerExprFuel globals first + checkerExprsFuel globals rest + 1
  | .nil type | .none type => checkerTypeFuel type + 1
  | .cons type head tail =>
      checkerTypeFuel type + checkerExprFuel globals head + checkerExprFuel globals tail + 1
  | .some type value => checkerTypeFuel type + checkerExprFuel globals value + 1
  | .matchList target empty full | .matchOption target empty full =>
      checkerExprFuel globals target + checkerExprFuel globals empty + checkerExprFuel globals full + 1
  termination_by sizeOf expression

def checkerExprsFuel (globals : List Signature) (expressions : List Expr) : Nat :=
  match expressions with
  | [] => 1
  | head :: tail => checkerExprFuel globals head + checkerExprsFuel globals tail + 1
  termination_by sizeOf expressions
decreasing_by all_goals simp_wf; omega
end

theorem checkerExprFuel_global_components (globals : List Signature) (index : Nat)
    (typeArguments : List Ty) :
    checkerTypesFuel typeArguments < checkerExprFuel globals (.global index typeArguments) ∧
    checkerSignaturesFuel globals < checkerExprFuel globals (.global index typeArguments) := by
  simp [checkerExprFuel]
  omega

theorem checkerExprFuel_lambda_components (globals : List Signature) (parameters : List Ty)
    (result : Ty) (body : Expr) :
    checkerTypesFuel parameters < checkerExprFuel globals (.lam parameters result body) ∧
    checkerTypeFuel result < checkerExprFuel globals (.lam parameters result body) ∧
    checkerExprFuel globals body < checkerExprFuel globals (.lam parameters result body) := by
  simp [checkerExprFuel]
  omega

theorem checkerExprFuel_app_components (globals : List Signature) (function : Expr)
    (arguments : List Expr) :
    checkerExprFuel globals function < checkerExprFuel globals (.app function arguments) ∧
    checkerExprsFuel globals arguments < checkerExprFuel globals (.app function arguments) := by
  simp [checkerExprFuel, checkerExprsFuel]
  omega

theorem checkerExprFuel_letMany_components (globals : List Signature) (types : List Ty)
    (initializers : List Expr) (body : Expr) :
    checkerTypesFuel types < checkerExprFuel globals (.letMany types initializers body) ∧
    checkerExprsFuel globals initializers < checkerExprFuel globals (.letMany types initializers body) ∧
    checkerExprFuel globals body < checkerExprFuel globals (.letMany types initializers body) := by
  simp [checkerExprFuel, checkerExprsFuel]
  omega

theorem checkerExprsFuel_cons_components (globals : List Signature) (head : Expr)
    (tail : List Expr) :
    checkerExprFuel globals head < checkerExprsFuel globals (head :: tail) ∧
    checkerExprsFuel globals tail < checkerExprsFuel globals (head :: tail) := by
  simp [checkerExprFuel, checkerExprsFuel]
  omega

mutual
theorem checkWF_complete (type : Ty) (count : Nat) (valid : type.wellFormed count) :
    ∃ bound, ∀ fuel, bound ≤ fuel → checkWF fuel count type = some ⟨valid⟩ := by
  cases type with
  | boolean | integer | unit =>
    refine ⟨1, ?_⟩
    intro fuel bound
    cases fuel with
    | zero => omega
    | succ fuel => simp [checkWF]
  | var index =>
    have hi : index < count := by simpa [Ty.wellFormed] using valid
    refine ⟨1, ?_⟩
    intro fuel bound
    cases fuel with
    | zero => omega
    | succ fuel => simp [checkWF, hi]
  | fn ps result =>
    obtain ⟨psValid, retValid⟩ := (by simpa [Ty.wellFormed] using valid :
      (∀ t ∈ ps, t.wellFormed count) ∧ result.wellFormed count)
    obtain ⟨a, ha⟩ := checkTypesWF_complete ps count psValid
    obtain ⟨b, hb⟩ := checkWF_complete result count retValid
    refine ⟨a + b + 1, ?_⟩
    intro fuel bound
    cases fuel with
    | zero => omega
    | succ fuel => simp [checkWF, ha fuel (by omega), hb fuel (by omega)]
  | list element | option element =>
    obtain ⟨a, ha⟩ := checkWF_complete element count (by simpa [Ty.wellFormed] using valid)
    refine ⟨a + 1, ?_⟩
    intro fuel bound
    cases fuel with
    | zero => omega
    | succ fuel => simp [checkWF, ha fuel (by omega)]
termination_by sizeOf type
decreasing_by all_goals simp_wf; subst_vars; simp_all; omega

theorem checkTypesWF_complete (types : List Ty) (count : Nat)
    (valid : ∀ t ∈ types, t.wellFormed count) :
    ∃ bound, ∀ fuel, bound ≤ fuel → checkTypesWF fuel count types = some ⟨valid⟩ := by
  cases types with
  | nil =>
    refine ⟨1, ?_⟩
    intro fuel bound
    cases fuel with
    | zero => omega
    | succ fuel => simp [checkTypesWF]
  | cons head tail =>
    obtain ⟨a, ha⟩ := checkWF_complete head count (valid head (by simp))
    obtain ⟨b, hb⟩ := checkTypesWF_complete tail count (by intro t ht; exact valid t (by simp [ht]))
    refine ⟨a + b + 1, ?_⟩
    intro fuel bound
    cases fuel with
    | zero => omega
    | succ fuel => simp [checkTypesWF, ha fuel (by omega), hb fuel (by omega)]
termination_by sizeOf types
decreasing_by all_goals simp_wf; subst_vars; simp_all; omega
end

private theorem replicate_none_no_assigned (count index : Nat) (value : Ty) :
    (List.replicate count (none : Option Ty))[index]? ≠ some (some value) := by
  induction count generalizing index with
  | zero => cases index <;> simp [getElem?_def, Nat.not_lt_zero]
  | succ count ih =>
      cases index with
      | zero => simp [getElem?_def]
      | succ index => simpa [getElem?_def, Nat.succ_lt_succ_iff] using ih index

private theorem mapM_some_loop {α : Type} (values accumulator : List α) :
    List.mapM.loop (m := Option) (fun value : Option α => value) (values.map some) accumulator =
      some (accumulator.reverse ++ values) := by
  induction values generalizing accumulator with
  | nil => simp [List.mapM.loop]
  | cons head tail ih =>
      simp [List.mapM.loop, ih, List.reverse_cons, List.append_assoc]

private theorem mapM_some {α : Type} (values : List α) :
    (values.map some).mapM (fun value => value) = some values := by
  simp [List.mapM, mapM_some_loop]

/-- If a candidate instantiates every parameter and every quantified variable
occurs in those parameters, the one-way collector returns the complete candidate
vector. The two structural fuel premises separately cover collection and the
subsequent well-formedness check. -/
theorem inferTypeArguments_complete_from_candidate (fuel callerCount : Nat)
    (header : Header) (actuals candidate : List Ty)
    (covered : inferrable fuel header = true)
    (candidateArity : candidate.length = header.variables.length)
    (candidateValid : ∀ t ∈ candidate, t.wellFormed callerCount)
    (parametersValid : ∀ t ∈ header.parameters.map Prod.snd,
      t.wellFormed header.variables.length)
    (candidateMatches : instantiateTypes candidate (header.parameters.map Prod.snd) = actuals)
    (collectorEnough : collectorTypesFuel (header.parameters.map Prod.snd) ≤ fuel)
    (checkerEnough : checkerTypesFuel candidate ≤ fuel) :
    ∃ solution, inferTypeArguments fuel callerCount header actuals = some solution := by
  let initial := List.replicate header.variables.length (none : Option Ty)
  have initialLength : initial.length = candidate.length := by
    simp [initial, candidateArity]
  have initialAgree : AssignmentsAgree candidate initial := by
    intro index value found
    exact False.elim ((replicate_none_no_assigned header.variables.length index value) (by
      simpa [initial] using found))
  have parametersValidCandidate : ∀ t ∈ header.parameters.map Prod.snd,
      t.wellFormed candidate.length := by
    intro t mem
    rw [candidateArity]
    exact parametersValid t mem
  obtain ⟨assignments, collected, _, assignmentsLength, captures⟩ :=
    collectArguments_complete fuel (header.parameters.map Prod.snd) actuals candidate initial
      initialLength initialAgree parametersValidCandidate candidateMatches collectorEnough
  have assignmentsCandidateLength : assignments.length = candidate.length :=
    assignmentsLength.trans initialLength
  have assignmentsEq : assignments = candidate.map some := by
    apply List.ext_get (by simp [assignmentsCandidateLength, candidateArity])
    intro index assignmentsBound candidateBound
    have indexBound : index < candidate.length := by
      simpa using candidateBound
    have occursHere : occursMany fuel index (header.parameters.map Prod.snd) = true := by
      have indexInRange : index ∈ List.range header.variables.length :=
        below_member_range (by omega)
      exact List.all_eq_true.mp (by simpa [inferrable] using covered) index indexInRange
    have candidateAtIndex : candidate[index]? = some (candidate[index]'indexBound) := by
      simp [getElem?_def, indexBound]
    have captured := captures index occursHere (candidate[index]'indexBound) candidateAtIndex
    simpa [getElem?_def, assignmentsBound, candidateBound] using captured
  have collectedCandidate :
      collectArguments fuel (header.parameters.map Prod.snd) actuals initial =
        some (candidate.map some) := by
    simpa [assignmentsEq] using collected
  have candidateChecked :
      ∃ checked, checkTypesWF fuel callerCount candidate = some checked :=
    checkTypesWF_sufficient candidate callerCount fuel candidateValid checkerEnough
  obtain ⟨checked, checkedAccepted⟩ := candidateChecked
  have mappedCandidate := mapM_some candidate
  refine ⟨⟨candidate, candidateArity, candidateValid, candidateMatches, ?_⟩, ?_⟩
  · intro other otherArity otherMatches
    exact inferred_arguments_unique fuel header covered other candidate otherArity candidateArity
      (otherMatches.trans candidateMatches.symm)
  · simp [inferTypeArguments, covered, collectedCandidate, mappedCandidate, checkedAccepted,
      candidateArity, candidateMatches]

/-- Executable structural fuel sufficient for both type-argument collection
and validation of the candidate argument vector. -/
def inferTypeArgumentsCandidateFuel (header : Header) (candidate : List Ty) : Nat :=
  max (collectorTypesFuel (header.parameters.map Prod.snd)) (checkerTypesFuel candidate)

theorem inferTypeArguments_complete_at_candidate_fuel (fuel callerCount : Nat)
    (header : Header) (actuals candidate : List Ty)
    (covered : inferrable fuel header = true)
    (candidateArity : candidate.length = header.variables.length)
    (candidateValid : ∀ t ∈ candidate, t.wellFormed callerCount)
    (parametersValid : ∀ t ∈ header.parameters.map Prod.snd,
      t.wellFormed header.variables.length)
    (candidateMatches : instantiateTypes candidate (header.parameters.map Prod.snd) = actuals)
    (fuelEnough : inferTypeArgumentsCandidateFuel header candidate ≤ fuel) :
    ∃ solution, inferTypeArguments fuel callerCount header actuals = some solution := by
  apply inferTypeArguments_complete_from_candidate fuel callerCount header actuals candidate covered
    candidateArity candidateValid parametersValid candidateMatches
  · exact Nat.le_trans (Nat.le_max_left _ _) fuelEnough
  · exact Nat.le_trans (Nat.le_max_right _ _) fuelEnough

theorem wf_bound {type : Ty} {count : Nat} (valid : type.wellFormed count) :
    ∃ bound, ∀ fuel, bound ≤ fuel → checkWF fuel count type = some ⟨valid⟩ :=
  checkWF_complete type count valid

theorem wf_types_bound {types : List Ty} {count : Nat} (valid : ∀ t ∈ types, t.wellFormed count) :
    ∃ bound, ∀ fuel, bound ≤ fuel → checkTypesWF fuel count types = some ⟨valid⟩ :=
  checkTypesWF_complete types count valid

open Lean Meta Elab Tactic in
elab "add_wf_bounds" : tactic => withMainContext do
  let mut goal ← getMainGoal
  let declarations := (← getLCtx).getFVarIds
  for id in declarations do
    let signatureWF ← goal.withContext do return (← id.getType).isAppOf ``Signature.wellFormed
    if signatureWF then
      for (projection, lemma) in [(``And.left, ``wf_types_bound), (``And.right, ``wf_bound)] do
        let next ← goal.withContext do
          let component ← mkAppM projection #[mkFVar id]
          let proof ← mkAppM lemma #[component]
          let declaration ← goal.assert (← mkFreshUserName `signatureBound) (← inferType proof) proof
          let (_, next) ← declaration.intro1
          return next
        goal := next
    for lemma in [``wf_bound, ``wf_types_bound] do
      let saved ← saveState
      try
        let next ← goal.withContext do
          let proof ← mkAppM lemma #[mkFVar id]
          let proof ← instantiateMVars proof
          if proof.hasMVar then throwError "unresolved well-formedness bound"
          let declaration ← goal.assert (← mkFreshUserName `wfBound) (← inferType proof) proof
          let (_, next) ← declaration.intro1
          return next
        goal := next
      catch _ => saved.restore
  replaceMainGoal [goal]

private theorem lookup_unique (left : value = some a) (right : value = some b) : a = b :=
  Option.some.inj (left.symm.trans right)

open Lean Meta Elab Tactic in
elab "add_structural_wf_bounds" : tactic => withMainContext do
  let mut goal ← getMainGoal
  let declarations ← goal.withContext do return (← getLCtx).getFVarIds
  for id in declarations do
    let savedLookup ← saveState
    try
      let next ← goal.withContext do
        let proof ← mkAppM ``checkerSignatureFuel_le_of_lookup #[mkFVar id]
        let proof ← instantiateMVars proof
        if proof.hasMVar then throwError "not a signature lookup"
        let declaration ← goal.assert (← mkFreshUserName `signatureFuelBound)
          (← inferType proof) proof
        let (_, next) ← declaration.intro1
        return next
      goal := next
    catch _ => savedLookup.restore
    let signatureWF ← goal.withContext do
      return (← inferType (mkFVar id)).isAppOf ``Signature.wellFormed
    if signatureWF then
      let next ← goal.withContext do
        let proof ← mkAppM ``checkSignatureWF_structural_bound #[mkFVar id]
        let declaration ← goal.assert (← mkFreshUserName `signatureStructuralBound)
          (← inferType proof) proof
        let (_, next) ← declaration.intro1
        return next
      goal := next
    for lemma in [``checkWF_structural_bound, ``checkTypesWF_structural_bound] do
      let saved ← saveState
      try
        let next ← goal.withContext do
          let proof ← mkAppM lemma #[mkFVar id]
          let proof ← instantiateMVars proof
          if proof.hasMVar then throwError "unresolved structural well-formedness bound"
          let proofType ← whnf (← inferType proof)
          if !proofType.isAppOf ``Exists then throwError "not a structural bound"
          let declaration ← goal.assert (← mkFreshUserName `structuralWFBound) proofType proof
          let (_, next) ← declaration.intro1
          return next
        goal := next
      catch _ => saved.restore
  replaceMainGoal [goal]

open Lean Meta Elab Tactic in
elab "unpack_conjunctions" : tactic => withMainContext do
  let mut goal ← getMainGoal
  let mut changed := true
  while changed do
    changed := false
    let ids ← goal.withContext do return (← getLCtx).getFVarIds
    for id in ids do
      let isAnd ← goal.withContext do
        return (← whnf (← inferType (mkFVar id))).isAppOf ``And
      if isAnd then
        let branches ← goal.cases id
        if hsize : branches.size = 1 then
          goal := (branches[0]'(by omega)).mvarId
          changed := true
          break
  replaceMainGoal [goal]

theorem inference_eventually (typing : HasType globals count context expression type) :
    ∃ bound, ∀ fuel, bound ≤ fuel → infer fuel globals count context expression = some ⟨type, typing⟩ := by
  apply HasType.rec
    (motive_1 := fun context expression type typing => ∃ bound, ∀ fuel, bound ≤ fuel →
      infer fuel globals count context expression = some ⟨type, typing⟩)
    (motive_2 := fun context expressions types typing => ∃ bound, ∀ fuel, bound ≤ fuel →
      inferArgs fuel globals count context expressions = some ⟨types, typing⟩)
    (motive_3 := fun context expressions previous result typing => ∃ bound, ∀ fuel, bound ≤ fuel →
      inferSequence fuel globals count context expressions previous = some ⟨result, typing⟩)
    (t := typing)
  all_goals intros
  case global =>
    rename_i index signature arguments localContext found arity argumentsValid signatureValid
    obtain ⟨a, ha⟩ := wf_types_bound argumentsValid
    obtain ⟨b, hb⟩ := wf_types_bound signatureValid.1
    obtain ⟨c, hc⟩ := wf_bound signatureValid.2
    refine ⟨a + b + c + 1, ?_⟩
    intro fuel bound
    cases fuel with
    | zero => omega
    | succ fuel =>
      simp [infer, found, arity, ha fuel (by omega), hb fuel (by omega), hc fuel (by omega),
        bind, Option.bind, pure]
      split
      · rename_i missing
        have impossible := missing.symm.trans found
        cases impossible
      · rename_i actual lookup
        have same := lookup_unique lookup found
        subst actual
        simp [arity, hb fuel (by omega), hc fuel (by omega), bind, Option.bind, pure]
  all_goals add_wf_bounds
  all_goals convergence_bound
  all_goals intro fuel bound
  all_goals cases fuel with
  | zero => omega
  | succ fuel =>
    use_bounds_at fuel
    simp_all [infer, inferArgs, inferSequence, Inferred.expect, bind, Option.bind, pure]
    all_goals repeat' split
    all_goals simp_all
    all_goals subst_vars
    all_goals try simp_all
    all_goals solve_by_elim [lookup_unique]

/-- The computable expression bound is sufficient fuel for accepted typing
derivations. -/
theorem inference_structural_fuel (typing : HasType globals count context expression type) :
    ∃ bound, bound ≤ checkerExprFuel globals expression ∧
      ∀ fuel, bound ≤ fuel → infer fuel globals count context expression =
        some ⟨type, typing⟩ := by
  apply HasType.rec
    (motive_1 := fun context expression type typing =>
      ∃ bound, bound ≤ checkerExprFuel globals expression ∧ ∀ fuel, bound ≤ fuel →
        infer fuel globals count context expression = some ⟨type, typing⟩)
    (motive_2 := fun context expressions types typing =>
      ∃ bound, bound ≤ checkerExprsFuel globals expressions ∧ ∀ fuel, bound ≤ fuel →
        inferArgs fuel globals count context expressions = some ⟨types, typing⟩)
    (motive_3 := fun context expressions previous result typing =>
      ∃ bound, bound ≤ checkerExprsFuel globals expressions ∧ ∀ fuel, bound ≤ fuel →
        inferSequence fuel globals count context expressions previous = some ⟨result, typing⟩)
    (t := typing)
  all_goals intros
  case global =>
    rename_i index signature arguments localContext found arity argumentsValid signatureValid
    refine ⟨checkerExprFuel globals (.global index arguments), Nat.le_refl _, ?_⟩
    intro fuel enough
    cases fuel with
    | zero => simp [checkerExprFuel] at enough
    | succ fuel =>
      have signatureMember : signature ∈ globals := signature_mem_of_getElem? found
      have signatureBound : checkerSignatureFuel signature ≤ checkerSignaturesFuel globals :=
        checkerSignatureFuel_le_of_mem signature globals signatureMember
      have parametersMeasure : checkerTypesFuel signature.parameters ≤ checkerSignatureFuel signature := by
        simp [checkerSignatureFuel]
        omega
      have resultMeasure : checkerTypeFuel signature.result ≤ checkerSignatureFuel signature := by
        simp [checkerSignatureFuel]
        omega
      have argumentsOK := checkTypesWF_sufficient_proof arguments count fuel argumentsValid (by
        simp [checkerExprFuel] at enough
        omega)
      have parametersOK := checkTypesWF_sufficient_proof signature.parameters signature.typeArity
        fuel signatureValid.1 (by
          simp [checkerExprFuel] at enough
          omega)
      have resultOK := checkWF_sufficient_proof signature.result signature.typeArity fuel
        signatureValid.2 (by
          simp [checkerExprFuel] at enough
          omega)
      simp [infer, found, arity, argumentsOK, parametersOK, resultOK, bind, Option.bind, pure]
      split
      · rename_i missing
        have impossible := missing.symm.trans found
        cases impossible
      · rename_i actual lookup
        have same := lookup_unique lookup found
        subst actual
        simp [arity, argumentsOK, parametersOK, resultOK, bind, Option.bind, pure]
  all_goals add_structural_wf_bounds
  all_goals convergence_bound
  all_goals unpack_conjunctions
  all_goals constructor
  all_goals try simp [checkerExprFuel, checkerExprsFuel, checkerSignatureFuel,
    checkerSignaturesFuel]
  all_goals try omega
  all_goals intro fuel bound
  all_goals cases fuel with
  | zero => omega
  | succ fuel =>
    use_bounds_at fuel
    unpack_conjunctions
    simp_all [infer, inferArgs, inferSequence, Inferred.expect, bind, Option.bind, pure]
    all_goals repeat' split
    all_goals simp_all
    all_goals subst_vars
    all_goals try simp_all
    all_goals solve_by_elim [lookup_unique]

theorem type_unique (first : HasType globals count context expression a)
    (second : HasType globals count context expression b) : a = b := by
  obtain ⟨n, hn⟩ := inference_eventually first
  obtain ⟨m, hm⟩ := inference_eventually second
  have same := (hn (n + m) (by omega)).symm.trans (hm (n + m) (by omega))
  exact congrArg Inferred.type (Option.some.inj same)

end NLisp.Surface
