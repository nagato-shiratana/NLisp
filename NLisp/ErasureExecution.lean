import NLisp.Erasure
import NLisp.SurfaceEvaluator
import NLisp.EvaluatorCompleteness
import NLisp.SurfaceEvaluatorCorrectness

namespace NLisp.PolyIR

set_option maxHeartbeats 800000

open Lean Meta Elab Tactic in
elab "split_conjunction" : tactic => withMainContext do
  let goal ← getMainGoal
  for declaration in (← getLCtx) do
    if declaration.type.isAppOf ``And then
      let branches ← goal.cases declaration.fvarId
      replaceMainGoal (branches.toList.map (fun b => b.mvarId))
      return
  throwError "no conjunction"

open Lean Meta Elab Tactic in
elab "split_source_result" : tactic => withMainContext do
  let goal ← getMainGoal
  let target ← goal.getType
  let call := target.find? (fun e => e.isAppOfArity ``Surface.evaluate 4 ||
    e.isAppOfArity ``Surface.evaluateArgs 4 || e.isAppOfArity ``Surface.evaluateSequence 5)
  let some call := call | throwError "no source evaluation to split"
  let (ids, next) ← goal.generalize #[{expr := call, hName? := some (← mkFreshUserName `sourceResult)}]
  let branches ← next.cases ids[0]!
  replaceMainGoal (branches.toList.map (fun b => b.mvarId))

open Lean Meta Elab Tactic in
elab "split_source_value" : tactic => withMainContext do
  let goal ← getMainGoal
  let target ← goal.getType
  let mut call := target.find? (fun e => e.isAppOfArity ``eraseValue 1 && e.getAppArgs[0]!.isFVar)
  if call.isNone then
    for declaration in (← getLCtx) do
      if declaration.type.isAppOf ``Eq then
        if let some found := declaration.type.find? (fun e =>
            e.isAppOfArity ``eraseValue 1 && e.getAppArgs[0]!.isFVar) then
          call := some found
          break
  let some selected := call | throwError "no source value to split"
  let branches ← goal.cases selected.getAppArgs[0]!.fvarId!
  replaceMainGoal (branches.toList.map (fun b => b.mvarId))

def eraseResult : Except Fault Surface.Value → Except Fault Value
  | .error error => .error error
  | .ok value => .ok (eraseValue value)

def eraseArgumentsResult : Except Fault (List Surface.Value) → Except Fault (List Value)
  | .error error => .error error
  | .ok values => .ok (eraseValues values)

theorem eraseValues_lookup_eq (env : List Surface.Value) (index : Nat) :
    (eraseValues env)[index]? = (env[index]?).map eraseValue := by
  induction env generalizing index with
  | nil => simp [eraseValues, getElem?_def, Nat.not_lt_zero]
  | cons head tail ih =>
    cases index with
    | zero => simp [eraseValues, getElem?_def]
    | succ i => simpa [eraseValues, getElem?_def, Nat.succ_lt_succ_iff] using ih i

theorem eraseDefinitions_lookup_eq (program : Surface.Definitions) (index : Nat) :
    (eraseDefinitions program)[index]? = (program[index]?).map
      (fun definition => RuntimeDefinition.mk definition.1.parameters.length (erase definition.2)) := by
  induction program generalizing index with
  | nil => simp [eraseDefinitions, getElem?_def, Nat.not_lt_zero]
  | cons head tail ih =>
    cases index with
    | zero => simp [eraseDefinitions, getElem?_def]
    | succ i => simpa [eraseDefinitions, getElem?_def, Nat.succ_lt_succ_iff] using ih i

/- A commuting diagram for the actual executable interpreters, including
their errors and fuel exhaustion, not merely their successful results. -/
theorem execution_commutes (program : Surface.Definitions) (fuel : Nat) :
    (∀ env expression,
      eraseResult (Surface.evaluate program fuel env expression) =
        evaluate (eraseDefinitions program) fuel (eraseValues env) (erase expression)) ∧
    (∀ env expressions,
      eraseArgumentsResult (Surface.evaluateArgs program fuel env expressions) =
        evaluateArgs (eraseDefinitions program) fuel (eraseValues env) (eraseList expressions)) ∧
    (∀ env previous expressions,
      eraseResult (Surface.evaluateSequence program fuel env previous expressions) =
        evaluateSequence (eraseDefinitions program) fuel (eraseValues env)
          (eraseValue previous) (eraseList expressions)) := by
  induction fuel with
  | zero => simp [Surface.evaluate, Surface.evaluateArgs, Surface.evaluateSequence,
      evaluate, evaluateArgs, evaluateSequence, eraseResult, eraseArgumentsResult]
  | succ fuel ih =>
    obtain ⟨exprCommutes, argsCommutes, sequenceCommutes⟩ := ih
    refine ⟨?_, ?_, ?_⟩
    · intro env expression
      cases expression <;> simp only [Surface.evaluate, erase, evaluate,
        eraseValues_lookup_eq, eraseDefinitions_lookup_eq,
        ← exprCommutes, ← argsCommutes, bind, Except.bind, pure, Except.pure]
      all_goals repeat' split
      all_goals try simp_all [eraseResult, eraseArgumentsResult, eraseValue, eraseValues,
        eraseValues_append, eraseValues_length]
      all_goals repeat' split_conjunction
      all_goals subst_vars
      all_goals repeat' (first
        | solve | simp_all [eraseResult, eraseArgumentsResult, eraseValue, eraseValues,
            eraseValues_append, eraseValues_length, ← exprCommutes, ← argsCommutes, ← sequenceCommutes]
        | split_source_value)
      all_goals exfalso
      all_goals solve_by_elim (config := { maxDepth := 6 }) [Eq.refl]
    · intro env expressions
      cases expressions <;> simp only [Surface.evaluateArgs, eraseList, evaluateArgs,
        ← exprCommutes, ← argsCommutes, bind, Except.bind, pure, Except.pure]
      all_goals repeat' split
      all_goals simp_all [eraseResult, eraseArgumentsResult, eraseValues]
    · intro env previous expressions
      cases expressions <;> simp only [Surface.evaluateSequence, eraseList, evaluateSequence,
        ← exprCommutes, ← sequenceCommutes, bind, Except.bind, pure, Except.pure]
      all_goals repeat' split
      all_goals simp_all [eraseResult, eraseArgumentsResult, eraseValue]

theorem execution_success_iff {program : Surface.Definitions} {fuel : Nat}
    {env : List Surface.Value} {expression : Surface.Expr} {value : Value} :
    evaluate (eraseDefinitions program) fuel (eraseValues env) (erase expression) = .ok value ↔
      ∃ sourceValue, Surface.evaluate program fuel env expression = .ok sourceValue ∧
        eraseValue sourceValue = value := by
  have commutes := (execution_commutes program fuel).1 env expression
  cases result : Surface.evaluate program fuel env expression with
  | error error => simp [result, eraseResult] at commutes; simp [← commutes, result]
  | ok sourceValue =>
    simp [result, eraseResult] at commutes
    simp [← commutes, result]

theorem finite_evaluation_iff {program : Surface.Definitions} {env : List Surface.Value}
    {expression : Surface.Expr} {value : Value} :
    Evaluates (eraseDefinitions program) (eraseValues env) (erase expression) value ↔
      ∃ sourceValue, Surface.Evaluates program env expression sourceValue ∧ eraseValue sourceValue = value := by
  constructor
  · intro target
    obtain ⟨fuel, result⟩ := evaluate_complete target
    obtain ⟨sourceValue, sourceResult, same⟩ := execution_success_iff.mp result
    exact ⟨sourceValue, Surface.evaluate_sound sourceResult, same⟩
  · intro ⟨sourceValue, derivation, same⟩
    simpa [same] using evaluation_preserved derivation

theorem execution_error_iff {program : Surface.Definitions} {fuel : Nat}
    {env : List Surface.Value} {expression : Surface.Expr} {error : Fault} :
    evaluate (eraseDefinitions program) fuel (eraseValues env) (erase expression) = .error error ↔
      Surface.evaluate program fuel env expression = .error error := by
  have commutes := (execution_commutes program fuel).1 env expression
  cases result : Surface.evaluate program fuel env expression with
  | error failure => simp [result, eraseResult] at commutes; simp [← commutes, result]
  | ok value => simp [result, eraseResult] at commutes; simp [← commutes, result]

/- Operational divergence for these deterministic, depth-fuel interpreters:
every finite depth budget is exhausted. This does not classify a single
Unknown as divergence, and does not conflate finite errors with divergence. -/
theorem fuel_divergence_iff (program : Surface.Definitions) (env : List Surface.Value)
    (expression : Surface.Expr) :
    (∀ fuel, evaluate (eraseDefinitions program) fuel (eraseValues env) (erase expression) =
      .error .outOfFuel) ↔
    (∀ fuel, Surface.evaluate program fuel env expression = .error .outOfFuel) := by
  constructor
  · intro h fuel; exact execution_error_iff.mp (h fuel)
  · intro h fuel; exact execution_error_iff.mpr (h fuel)

end NLisp.PolyIR
