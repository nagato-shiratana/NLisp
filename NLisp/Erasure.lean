import NLisp.RuntimeSemantics
import NLisp.SurfaceSemantics

namespace NLisp.PolyIR

mutual
def eraseValue (value : Surface.Value) : Value :=
  match value with
  | .bool b => .bool b
  | .int n => .int n
  | .unit => .unit
  | .closure ps _ body env => .closure ps.length (erase body) (eraseValues env)
  | .global i _ => .global i
  | .nil => .nil
  | .cons head tail => .cons (eraseValue head) (eraseValue tail)
  | .none => .none
  | .some v => .some (eraseValue v)
termination_by sizeOf value
decreasing_by all_goals simp_wf; omega

def eraseValues (values : List Surface.Value) : List Value :=
  match values with
  | [] => []
  | v :: vs => eraseValue v :: eraseValues vs
termination_by sizeOf values
decreasing_by all_goals simp_wf; omega
end

def eraseDefinitions (program : Surface.Definitions) : List RuntimeDefinition :=
  program.map (fun d => ⟨d.1.parameters.length, erase d.2⟩)

@[simp] theorem eraseValues_length (values : List Surface.Value) :
    (eraseValues values).length = values.length := by
  induction values with
  | nil => simp [eraseValues]
  | cons _ _ ih => simp [eraseValues, ih]

@[simp] theorem eraseValues_append (a b : List Surface.Value) :
    eraseValues (a ++ b) = eraseValues a ++ eraseValues b := by
  induction a with
  | nil => simp [eraseValues]
  | cons _ _ ih => simp [eraseValues, ih]

theorem eraseValues_lookup {env : List Surface.Value} {index : Nat} {value : Surface.Value}
    (h : env[index]? = some value) :
    (eraseValues env)[index]? = some (eraseValue value) := by
  induction env generalizing index with
  | nil => simp [getElem?_def, Nat.not_lt_zero] at h
  | cons head tail ih =>
    cases index with
    | zero =>
      have hh : some head = some value := by simpa [getElem?_def] using h
      cases Option.some.inj hh
      simp [eraseValues, getElem?_def]
    | succ i =>
      have hh := ih (index := i) (by simpa [getElem?_def, Nat.succ_lt_succ_iff] using h)
      simpa [eraseValues, getElem?_def, Nat.succ_lt_succ_iff] using hh

theorem eraseDefinitions_lookup {program : Surface.Definitions} {index : Nat}
    {definition : Surface.Signature × Surface.Expr} (h : program[index]? = some definition) :
    (eraseDefinitions program)[index]? = some (RuntimeDefinition.mk definition.1.parameters.length (erase definition.2)) := by
  induction program generalizing index with
  | nil => simp [getElem?_def, Nat.not_lt_zero] at h
  | cons head tail ih =>
    cases index with
    | zero =>
      have hh : some head = some definition := by simpa [getElem?_def] using h
      cases Option.some.inj hh
      simp [eraseDefinitions, getElem?_def]
    | succ i =>
      have hh := ih (index := i) (by simpa [getElem?_def, Nat.succ_lt_succ_iff] using h)
      simpa [eraseDefinitions, getElem?_def, Nat.succ_lt_succ_iff] using hh

theorem erased_arity {values : List Surface.Value} {count : Nat}
    (h : values.length = count) : (eraseValues values).length = count := by
  simpa using h

/- Forward simulation for every finite source evaluation derivation,
including arbitrary finite self/mutual recursion. No source typing or
termination assumption is smuggled into the conclusion. -/
theorem evaluation_preserved {program : Surface.Definitions}
    {env : List Surface.Value} {expression : Surface.Expr} {value : Surface.Value}
    (h : Surface.Evaluates program env expression value) :
    Evaluates (eraseDefinitions program) (eraseValues env) (erase expression) (eraseValue value) := by
  apply Surface.Evaluates.rec
    (motive_1 := fun env expression value _ =>
      Evaluates (eraseDefinitions program) (eraseValues env) (erase expression) (eraseValue value))
    (motive_2 := fun env expressions values _ =>
      ArgumentsEvaluate (eraseDefinitions program) (eraseValues env) (eraseList expressions) (eraseValues values))
    (motive_3 := fun env expressions previous value _ =>
      SequenceEvaluates (eraseDefinitions program) (eraseValues env) (eraseList expressions)
        (eraseValue previous) (eraseValue value))
    (t := h)
  all_goals intros
  all_goals simp only [erase, eraseList, eraseValue, eraseValues, eraseValues_append,
    eraseValues_length] at *
  case appGlobal =>
    rename_i env f index types args values signature body value _hf _ha lookup arity _hb iha ihb ihf
    exact Evaluates.appGlobal ihf iha
      (eraseDefinitions_lookup lookup) (by simpa using arity) ihb
  all_goals solve_by_elim (config := { maxDepth := 8 }) [Evaluates.var, Evaluates.global,
    Evaluates.bool, Evaluates.int, Evaluates.unit, Evaluates.lam,
    Evaluates.appClosure, Evaluates.appGlobal, Evaluates.ifTrue, Evaluates.ifFalse,
    Evaluates.add, Evaluates.sub, Evaluates.mul, Evaluates.le, Evaluates.intEq,
    Evaluates.letMany, Evaluates.begin, Evaluates.nil, Evaluates.cons,
    Evaluates.none, Evaluates.some, Evaluates.matchNil, Evaluates.matchCons,
    Evaluates.matchNone, Evaluates.matchSome, ArgumentsEvaluate.nil, ArgumentsEvaluate.cons,
    SequenceEvaluates.nil, SequenceEvaluates.cons, eraseValues_lookup, eraseDefinitions_lookup, erased_arity]

theorem closed_integer_result {program : Surface.Definitions} {expression : Surface.Expr} {n : Int}
    (h : Surface.Evaluates program [] expression (.int n)) :
    Evaluates (eraseDefinitions program) [] (erase expression) (.int n) := by
  simpa [eraseValues, eraseValue] using evaluation_preserved h

end NLisp.PolyIR
