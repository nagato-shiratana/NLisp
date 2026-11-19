import NLisp.NamedSemantics

namespace NLisp.Named

noncomputable section

/- Unknown identities are mapped one past the current environment. For a
well-scoped source they cannot occur; this choice also preserves unboundness. -/
def position (id : Nat) : List Nat → Nat
  | [] => 0
  | key :: tail => if key = id then 0 else position id tail + 1

/- Nested structural recursion avoids reducing a sizeOf measure containing
the numeric values of source identities or arbitrary-precision literals. -/
macro "lower_using " recursor:term : term => `(
  $recursor
    (motive_1 := fun _ => List Nat → PolyIR.Term)
    (motive_2 := fun _ => List Nat → List PolyIR.Term)
    (fun id locals => .var (position id locals))
    (fun index _ => .global index)
    (fun b _ => .bool b) (fun n _ => .int n) (fun _ => .unit)
    (fun ps _ body locals => .lam ps.length (body (ps ++ locals)))
    (fun _ _ f args locals => .app (f locals) (args locals))
    (fun _ _ _ c y n locals => .ite (c locals) (y locals) (n locals))
    (fun _ _ a b locals => .add (a locals) (b locals))
    (fun _ _ a b locals => .sub (a locals) (b locals))
    (fun _ _ a b locals => .mul (a locals) (b locals))
    (fun _ _ a b locals => .le (a locals) (b locals))
    (fun _ _ a b locals => .intEq (a locals) (b locals))
    (fun ps _ _ values body locals => .letMany (values locals) (body (ps ++ locals)))
    (fun _ _ first rest locals => .begin (first locals) (rest locals))
    (fun _ => .nil) (fun _ _ h t locals => .cons (h locals) (t locals))
    (fun _ => .none) (fun _ value locals => .some (value locals))
    (fun _ _ h t _ target empty full locals =>
      .matchList (target locals) (empty locals) (full (h :: t :: locals)))
    (fun _ _ id _ target empty full locals =>
      .matchOption (target locals) (empty locals) (full (id :: locals)))
    (fun _ => []) (fun _ _ head tail locals => head locals :: tail locals))

def lower (locals : List Nat) (expression : Expr) : PolyIR.Term :=
  (lower_using Expr.rec) expression locals

def lowerMany (locals : List Nat) (expressions : List Expr) : List PolyIR.Term :=
  (lower_using Expr.rec_1) expressions locals

theorem lower_eq (locals : List Nat) (expression : Expr) :
    lower locals expression = match expression with
    | .var id => .var (position id locals)
    | .global i => .global i
    | .bool b => .bool b
    | .int n => .int n
    | .unit => .unit
    | .lam ps body => .lam ps.length (lower (ps ++ locals) body)
    | .app f args => .app (lower locals f) (lowerMany locals args)
    | .ite c y n => .ite (lower locals c) (lower locals y) (lower locals n)
    | .add a b => .add (lower locals a) (lower locals b)
    | .sub a b => .sub (lower locals a) (lower locals b)
    | .mul a b => .mul (lower locals a) (lower locals b)
    | .le a b => .le (lower locals a) (lower locals b)
    | .intEq a b => .intEq (lower locals a) (lower locals b)
    | .letMany ps values body => .letMany (lowerMany locals values) (lower (ps ++ locals) body)
    | .begin first rest => .begin (lower locals first) (lowerMany locals rest)
    | .nil => .nil
    | .cons h t => .cons (lower locals h) (lower locals t)
    | .none => .none
    | .some v => .some (lower locals v)
    | .matchList target empty h t full =>
      .matchList (lower locals target) (lower locals empty) (lower (h :: t :: locals) full)
    | .matchOption target empty id full =>
      .matchOption (lower locals target) (lower locals empty) (lower (id :: locals) full) := by
  cases expression <;> rfl

theorem lowerMany_eq (locals : List Nat) (expressions : List Expr) :
    lowerMany locals expressions = match expressions with
    | [] => []
    | e :: es => lower locals e :: lowerMany locals es := by
  cases expressions <;> rfl

def identities (env : Environment) : List Nat := env.map Prod.fst

@[simp] theorem identities_nil : identities [] = [] := rfl
@[simp] theorem identities_cons (id : Nat) (value : Value) (env : Environment) :
    identities ((id, value) :: env) = id :: identities env := rfl

mutual
def lowerValue (value : Value) : PolyIR.Value :=
  match value with
  | .bool b => .bool b
  | .int n => .int n
  | .unit => .unit
  | .closure ps body env => .closure ps.length (lower (ps ++ identities env) body) (lowerEnv env)
  | .global i => .global i
  | .nil => .nil
  | .cons h t => .cons (lowerValue h) (lowerValue t)
  | .none => .none
  | .some v => .some (lowerValue v)
termination_by sizeOf value
decreasing_by all_goals simp_wf; omega

def lowerEnv (env : Environment) : List PolyIR.Value :=
  match env with
  | [] => []
  | (_, value) :: tail => lowerValue value :: lowerEnv tail
termination_by sizeOf env
decreasing_by all_goals simp_wf; omega
end

def lowerValues (values : List Value) : List PolyIR.Value := values.map lowerValue

def lowerDefinitions (program : Definitions) : List PolyIR.RuntimeDefinition :=
  program.map (fun d => ⟨d.1.length, lower d.1 d.2⟩)

@[simp] theorem identities_append (a b : Environment) :
    identities (a ++ b) = identities a ++ identities b := by simp [identities]

@[simp] theorem lowerEnv_append (a b : Environment) :
    lowerEnv (a ++ b) = lowerEnv a ++ lowerEnv b := by
  induction a with
  | nil => simp [lowerEnv]
  | cons head tail ih => cases head; simp [lowerEnv, ih]

@[simp] theorem lowerValues_length (values : List Value) :
    (lowerValues values).length = values.length := by simp [lowerValues]

theorem lowered_arity {values : List Value} {count : Nat} (h : values.length = count) :
    (values.map lowerValue).length = count := by simpa using h

theorem bind_identifiers (ids : List Nat) (values : List Value) (arity : values.length = ids.length) :
    identities (bind ids values) = ids := by
  induction ids generalizing values with
  | nil => cases values <;> simp_all [bind, identities]
  | cons id ids ih =>
    cases values with
    | nil => simp at arity
    | cons value values =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at arity
      simpa [bind, identities] using congrArg (List.cons id) (ih values (by omega))

theorem lowerEnv_bind (ids : List Nat) (values : List Value) (arity : values.length = ids.length) :
    lowerEnv (bind ids values) = lowerValues values := by
  induction ids generalizing values with
  | nil => cases values <;> simp_all [bind, lowerEnv, lowerValues]
  | cons id ids ih =>
    cases values with
    | nil => simp at arity
    | cons value values =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at arity
      simpa [bind, lowerEnv, lowerValues] using congrArg (List.cons (lowerValue value)) (ih values (by omega))

theorem lookup_lowered (env : Environment) (id : Nat) (h : lookup id env = some value) :
    (lowerEnv env)[position id (identities env)]? = some (lowerValue value) := by
  induction env with
  | nil => simp [lookup] at h
  | cons head tail ih =>
    rcases head with ⟨key, item⟩
    by_cases same : key = id
    · simp [lookup, same] at h
      subst value
      simp [lowerEnv, identities, position, same, getElem?_def]
    · have ht : lookup id tail = some value := by simpa [lookup, same] using h
      simpa [lowerEnv, identities, position, same, getElem?_def, Nat.succ_lt_succ_iff] using ih ht

theorem definitions_lookup (program : Definitions) {index : Nat} {ids : List Nat} {body : Expr}
    (h : program[index]? = some (ids, body)) :
    (lowerDefinitions program)[index]? = some (PolyIR.RuntimeDefinition.mk ids.length (lower ids body)) := by
  induction program generalizing index with
  | nil => simp [getElem?_def, Nat.not_lt_zero] at h
  | cons head tail ih =>
    cases index with
    | zero =>
      have same : head = (ids, body) := by simpa [getElem?_def] using h
      subst head
      simp [lowerDefinitions, getElem?_def]
    | succ index =>
      simpa [lowerDefinitions, getElem?_def, Nat.succ_lt_succ_iff] using
        ih (index := index) (by simpa [getElem?_def, Nat.succ_lt_succ_iff] using h)

/- A general forward simulation from independent, identity-based source
semantics. It applies to arbitrary finite recursive executions, not just to
a closed example or to the types of a generated term. -/
theorem evaluation_preserved (h : Evaluates program env expression value) :
    PolyIR.Evaluates (lowerDefinitions program) (lowerEnv env)
      (lower (identities env) expression) (lowerValue value) := by
  apply Evaluates.rec
    (motive_1 := fun env expression value _ => PolyIR.Evaluates (lowerDefinitions program)
      (lowerEnv env) (lower (identities env) expression) (lowerValue value))
    (motive_2 := fun env expressions values _ => PolyIR.ArgumentsEvaluate (lowerDefinitions program)
      (lowerEnv env) (lowerMany (identities env) expressions) (lowerValues values))
    (motive_3 := fun env expressions previous value _ => PolyIR.SequenceEvaluates (lowerDefinitions program)
      (lowerEnv env) (lowerMany (identities env) expressions) (lowerValue previous) (lowerValue value))
    (t := h)
  all_goals intros
  all_goals simp only [lower, lowerMany, lowerValue, lowerEnv, lowerValues, List.map_cons,
    List.map_nil, identities_nil, identities_cons, identities_append] at *
  all_goals try (simp_all only [lowerEnv_append, bind_identifiers, lowerEnv_bind, lowerValues,
    List.length_map])
  case appGlobal =>
    rename_i env f index args values ps body value _hf _ha found arity _hb iha ihb ihf
    exact PolyIR.Evaluates.appGlobal ihf iha (definitions_lookup program found)
      (by simpa using arity) ihb
  all_goals solve_by_elim (config := { maxDepth := 8 }) [PolyIR.Evaluates.var, PolyIR.Evaluates.global,
    PolyIR.Evaluates.bool, PolyIR.Evaluates.int, PolyIR.Evaluates.unit, PolyIR.Evaluates.lam,
    PolyIR.Evaluates.appClosure, PolyIR.Evaluates.appGlobal, PolyIR.Evaluates.ifTrue, PolyIR.Evaluates.ifFalse,
    PolyIR.Evaluates.add, PolyIR.Evaluates.sub, PolyIR.Evaluates.mul, PolyIR.Evaluates.le, PolyIR.Evaluates.intEq,
    PolyIR.Evaluates.letMany, PolyIR.Evaluates.begin, PolyIR.Evaluates.nil, PolyIR.Evaluates.cons,
    PolyIR.Evaluates.none, PolyIR.Evaluates.some, PolyIR.Evaluates.matchNil, PolyIR.Evaluates.matchCons,
    PolyIR.Evaluates.matchNone, PolyIR.Evaluates.matchSome, PolyIR.ArgumentsEvaluate.nil,
    PolyIR.ArgumentsEvaluate.cons, PolyIR.SequenceEvaluates.nil, PolyIR.SequenceEvaluates.cons,
    lookup_lowered, definitions_lookup, lowered_arity]

end
end NLisp.Named
