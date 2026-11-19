import NLisp.PolymorphicSafety
import NLisp.ErasureExecution

namespace NLisp.Surface

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

theorem type_unique (first : HasType globals count context expression a)
    (second : HasType globals count context expression b) : a = b := by
  obtain ⟨n, hn⟩ := inference_eventually first
  obtain ⟨m, hm⟩ := inference_eventually second
  have same := (hn (n + m) (by omega)).symm.trans (hm (n + m) (by omega))
  exact congrArg Inferred.type (Option.some.inj same)

end NLisp.Surface
