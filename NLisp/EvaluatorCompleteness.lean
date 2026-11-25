import NLisp.EvaluatorCorrectness

namespace NLisp.PolyIR

/- Proof automation only: it constructs ordinary proof terms checked by the
kernel. A common upper bound is the sum of child bounds plus one. -/
open Lean Meta Elab Tactic in
elab "convergence_bound" : tactic => withMainContext do
  let mut goal ← getMainGoal
  let mut total := mkNatLit 1
  let declarations := (← getLCtx).getFVarIds
  for id in declarations do
    let result ← goal.withContext do
      let declaration ← id.getDecl
      let type ← whnf declaration.type
      if type.isAppOf ``Exists then
        let branches ← goal.cases id
        if hsize : branches.size = 1 then
          let branch := branches[0]'(by omega)
          return some (branch.mvarId, branch.fields[0]!)
        else throwError "expected a single existential constructor"
      return none
    if let some (next, bound) := result then
      goal := next
      total ← goal.withContext do mkAppM ``HAdd.hAdd #[total, bound]
  goal.withContext do
    let target ← whnf (← goal.getType)
    unless target.isAppOf ``Exists do throwError "expected convergence goal"
    let predicate := target.getAppArgs[1]!
    let rest ← mkFreshExprMVar ((mkApp predicate total).headBeta)
    let proof := mkAppN (mkConst ``Exists.intro [Level.succ Level.zero])
      #[mkConst ``Nat, predicate, total, rest]
    goal.assign proof
    replaceMainGoal [rest.mvarId!]

open Lean Meta Elab Tactic in
elab "use_bounds_at" fuel:ident : tactic => withMainContext do
  let value ← elabTerm fuel none
  let mut goal ← getMainGoal
  let declarations := (← getLCtx).getFVarIds
  for id in declarations do
    let next ← goal.withContext do
      let declaration ← id.getDecl
      let type ← whnf declaration.type
      if let .forallE _ domain _ _ := type then
        if domain.isConstOf ``Nat then
          let applied := mkApp (mkFVar id) value
          let appliedType ← whnf (← inferType applied)
          if let .forallE _ condition _ _ := appliedType then
            if condition.isAppOf ``LE.le then
              let obligation ← mkFreshExprMVar condition
              let saved ← getGoals
              setGoals [obligation.mvarId!]
              evalTactic (← `(tactic| omega))
              setGoals saved
              let proof := mkApp applied obligation
              let asserted ← goal.assert (← mkFreshUserName `childResult) (← inferType proof) proof
              let (_, next) ← asserted.intro1
              return next
      return goal
    goal := next
  replaceMainGoal [goal]

/- Every finite derivation has a depth budget sufficient for that result,
and the result is obtained at every larger budget as well. -/
theorem evaluation_eventually (h : Evaluates program env term value) :
    ∃ bound, ∀ fuel, bound ≤ fuel → evaluate program fuel env term = .ok value := by
  apply Evaluates.rec
    (motive_1 := fun env term value _ =>
      ∃ bound, ∀ fuel, bound ≤ fuel → evaluate program fuel env term = .ok value)
    (motive_2 := fun env terms values _ =>
      ∃ bound, ∀ fuel, bound ≤ fuel → evaluateArgs program fuel env terms = .ok values)
    (motive_3 := fun env terms previous value _ =>
      ∃ bound, ∀ fuel, bound ≤ fuel → evaluateSequence program fuel env previous terms = .ok value)
    (t := h)
  all_goals intros
  all_goals convergence_bound
  all_goals intro fuel bound
  all_goals cases fuel with
  | zero => omega
  | succ fuel =>
    use_bounds_at fuel
    simp_all [evaluate, evaluateArgs, evaluateSequence, bind, Except.bind, pure, Except.pure]
    all_goals rfl

theorem evaluate_complete (h : Evaluates program env term value) :
    ∃ fuel, evaluate program fuel env term = .ok value := by
  obtain ⟨bound, proof⟩ := evaluation_eventually h
  exact ⟨bound, proof bound (Nat.le_refl bound)⟩

theorem evaluates_iff_success : Evaluates program env term value ↔
    ∃ fuel, evaluate program fuel env term = .ok value :=
  ⟨evaluate_complete, fun ⟨_, proof⟩ => evaluate_sound proof⟩

end NLisp.PolyIR
