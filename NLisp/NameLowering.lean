import NLisp.NamedSemantics

namespace NLisp.Named

noncomputable section

/- Unknown identities are mapped one past the current environment. For a
well-scoped source they cannot occur; this choice also preserves unboundness. -/
def position (id : Nat) : List Nat → Nat
  | [] => 0
  | key :: tail => if key = id then 0 else position id tail + 1

theorem position_eq_length_of_not_mem (id : Nat) (locals : List Nat)
    (absent : id ∉ locals) : position id locals = locals.length := by
  induction locals with
  | nil => rfl
  | cons key tail ih =>
      have different : key ≠ id := by
        intro same
        subst key
        exact absent (by simp)
      have tailAbsent : id ∉ tail := by
        intro member
        exact absent (by simp [member])
      simp [position, different, ih tailAbsent]

theorem position_lt_length_of_mem (id : Nat) (locals : List Nat)
    (present : id ∈ locals) : position id locals < locals.length := by
  induction locals with
  | nil => simp at present
  | cons key tail ih =>
      rcases List.mem_cons.mp present with same | member
      · subst key
        simp [position]
      · by_cases different : key = id
        · simp [position, different]
        · have tailBound := ih member
          simp [position, different]
          omega

/- Nested structural recursion avoids reducing a sizeOf measure containing
the numeric values of source identities or arbitrary-precision literals. -/
macro "lower_using " recursor:term : term => `(
  $recursor
    (motive_1 := fun _ => List Nat → PolyIR.Term)
    (motive_2 := fun _ => List Nat → List PolyIR.Term)
    (fun id locals => .var (position id locals))
    (fun index _ => .global index)
    (fun b _ => .bool b) (fun n _ => .int n) (fun x _ => .float x)
    (fun s _ => .string s) (fun c _ => .character c) (fun _ => .unit)
    (fun ps _ body locals => .lam ps.length (body (ps ++ locals)))
    (fun _ _ f args locals => .app (f locals) (args locals))
    (fun _ _ _ c y n locals => .ite (c locals) (y locals) (n locals))
    (fun _ _ a b locals => .add (a locals) (b locals))
    (fun _ _ a b locals => .sub (a locals) (b locals))
    (fun _ _ a b locals => .mul (a locals) (b locals))
    (fun _ _ a b locals => .le (a locals) (b locals))
    (fun _ _ a b locals => .intEq (a locals) (b locals))
    (fun op _ _ left right locals => .floatBin op (left locals) (right locals))
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
    | .float x => .float x
    | .string s => .string s
    | .character c => .character c
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
      .matchOption (lower locals target) (lower locals empty) (lower (id :: locals) full)
    | .floatBin op left right => .floatBin op (lower locals left) (lower locals right) := by
  cases expression <;> rfl

theorem lowerMany_eq (locals : List Nat) (expressions : List Expr) :
    lowerMany locals expressions = match expressions with
    | [] => []
    | e :: es => lower locals e :: lowerMany locals es := by
  cases expressions <;> rfl

theorem lowerMany_length (locals : List Nat) (expressions : List Expr) :
    (lowerMany locals expressions).length = expressions.length := by
  induction expressions with
  | nil => rfl
  | cons expression rest ih =>
      change (lower locals expression :: lowerMany locals rest).length = _
      simp [ih]

def identities (env : Environment) : List Nat := env.map Prod.fst

@[simp] theorem identities_nil : identities [] = [] := rfl
@[simp] theorem identities_cons (id : Nat) (value : Value) (env : Environment) :
    identities ((id, value) :: env) = id :: identities env := rfl

mutual
def lowerValue (value : Value) : PolyIR.Value :=
  match value with
  | .bool b => .bool b
  | .int n => .int n
  | .float x => .float x
  | .string s => .string s
  | .character c => .character c
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

/-- Inverting closure lowering recovers all three runtime components. This is
the value-level bridge needed when an application evaluates its callee before
dispatching: a related IR closure has the same arity, lowered body, and
captured environment. -/
theorem lowerValue_closure_injective (parameters : List Nat) (body : Expr)
    (environment : Environment) (arity : Nat) (loweredBody : PolyIR.Term)
    (loweredEnvironment : List PolyIR.Value)
    (same : lowerValue (.closure parameters body environment) =
      .closure arity loweredBody loweredEnvironment) :
    parameters.length = arity ∧
      lower (parameters ++ identities environment) body = loweredBody ∧
      lowerEnv environment = loweredEnvironment := by
  simp [lowerValue] at same
  exact same

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

theorem lowerEnv_bind_append (ids : List Nat) (values : List Value) (env : Environment)
    (arity : values.length = ids.length) :
    lowerEnv (bind ids values ++ env) = lowerValues values ++ lowerEnv env := by
  rw [lowerEnv_append, lowerEnv_bind ids values arity]

theorem identities_bind_append (ids : List Nat) (values : List Value) (env : Environment)
    (arity : values.length = ids.length) :
    identities (bind ids values ++ env) = ids ++ identities env := by
  rw [identities_append, bind_identifiers ids values arity]

theorem lower_call_body (ids : List Nat) (values : List Value) (env : Environment)
    (body : Expr) (arity : values.length = ids.length) :
    lower (identities (bind ids values ++ env)) body =
      lower (ids ++ identities env) body := by
  rw [identities_bind_append ids values env arity]

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

theorem lookup_lowered_reflects (env : Environment) (id : Nat) (loweredValue : PolyIR.Value)
    (h : (lowerEnv env)[position id (identities env)]? = some loweredValue) :
    ∃ value, lookup id env = some value ∧ lowerValue value = loweredValue := by
  induction env with
  | nil => simp [lowerEnv, identities, position, getElem?_def] at h
  | cons entry tail ih =>
      rcases entry with ⟨key, item⟩
      by_cases same : key = id
      · subst key
        refine ⟨item, ?_, ?_⟩
        · simp [lookup]
        · simpa [lowerEnv, identities, position, getElem?_def] using h
      · have tailValue :
            (lowerEnv tail)[position id (identities tail)]? = some loweredValue := by
          simpa [lowerEnv, identities, position, same, getElem?_def,
            Nat.succ_lt_succ_iff] using h
        obtain ⟨value, found, lowered⟩ := ih tailValue
        exact ⟨value, by simp [lookup, same, found], lowered⟩

theorem variable_evaluation_reflected (program : Definitions) (env : Environment) (id : Nat)
    (value : PolyIR.Value)
    (evaluated : PolyIR.Evaluates (lowerDefinitions program) (lowerEnv env)
      (.var (position id (identities env))) value) :
    ∃ sourceValue, Evaluates program env (.var id) sourceValue ∧ lowerValue sourceValue = value := by
  cases evaluated with
  | var found =>
      obtain ⟨sourceValue, sourceFound, sameValue⟩ :=
        lookup_lowered_reflects env id value found
      exact ⟨sourceValue, .var sourceFound, sameValue⟩

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

theorem definitions_lookup_reflects (program : Definitions) (index : Nat)
    (runtimeDefinition : PolyIR.RuntimeDefinition)
    (h : (lowerDefinitions program)[index]? = some runtimeDefinition) :
    ∃ ids body, program[index]? = some (ids, body) ∧
      runtimeDefinition = PolyIR.RuntimeDefinition.mk ids.length (lower ids body) := by
  induction program generalizing index with
  | nil => simp [lowerDefinitions, getElem?_def, Nat.not_lt_zero] at h
  | cons first tail ih =>
      rcases first with ⟨ids, body⟩
      cases index with
      | zero =>
          have definitionEq :
              PolyIR.RuntimeDefinition.mk ids.length (lower ids body) = runtimeDefinition := by
            simpa [lowerDefinitions, getElem?_def] using h
          exact ⟨ids, body, by simp [getElem?_def], definitionEq.symm⟩
      | succ index =>
          obtain ⟨ids, body, found, definitionEq⟩ := ih index (by
            simpa [lowerDefinitions, getElem?_def, Nat.succ_lt_succ_iff] using h)
          exact ⟨ids, body, by simpa [getElem?_def, Nat.succ_lt_succ_iff] using found,
            definitionEq⟩

theorem global_evaluation_reflected (program : Definitions) (env : Environment) (index : Nat)
    (evaluated : PolyIR.Evaluates (lowerDefinitions program) (lowerEnv env)
      (.global index) (.global index)) :
    Evaluates program env (.global index) (.global index) := by
  cases evaluated with
  | global found =>
      obtain ⟨ids, body, sourceFound, _definitionEq⟩ :=
        definitions_lookup_reflects program index _ found
      exact .global sourceFound

theorem boolean_evaluation_reflected (program : Definitions) (env : Environment) (b : Bool)
    (value : PolyIR.Value)
    (evaluated : PolyIR.Evaluates (lowerDefinitions program) (lowerEnv env) (.bool b) value) :
    ∃ sourceValue, Evaluates program env (.bool b) sourceValue ∧ lowerValue sourceValue = value := by
  cases evaluated with
  | bool =>
      refine ⟨Value.bool b, Evaluates.bool, ?_⟩
      simp [lowerValue]

theorem integer_evaluation_reflected (program : Definitions) (env : Environment) (n : Int)
    (value : PolyIR.Value)
    (evaluated : PolyIR.Evaluates (lowerDefinitions program) (lowerEnv env) (.int n) value) :
    ∃ sourceValue, Evaluates program env (.int n) sourceValue ∧ lowerValue sourceValue = value := by
  cases evaluated with
  | int =>
      refine ⟨Value.int n, Evaluates.int, ?_⟩
      simp [lowerValue]

theorem float_evaluation_reflected (program : Definitions) (env : Environment) (x : Float)
    (value : PolyIR.Value)
    (evaluated : PolyIR.Evaluates (lowerDefinitions program) (lowerEnv env) (.float x) value) :
    ∃ sourceValue, Evaluates program env (.float x) sourceValue ∧ lowerValue sourceValue = value := by
  cases evaluated with
  | float => exact ⟨Value.float x, Evaluates.float, rfl⟩

theorem string_evaluation_reflected (program : Definitions) (env : Environment) (s : String)
    (value : PolyIR.Value)
    (evaluated : PolyIR.Evaluates (lowerDefinitions program) (lowerEnv env) (.string s) value) :
    ∃ sourceValue, Evaluates program env (.string s) sourceValue ∧ lowerValue sourceValue = value := by
  cases evaluated with
  | string => exact ⟨Value.string s, Evaluates.string, by simp [lowerValue]⟩

theorem character_evaluation_reflected (program : Definitions) (env : Environment) (c : Char)
    (value : PolyIR.Value)
    (evaluated : PolyIR.Evaluates (lowerDefinitions program) (lowerEnv env) (.character c) value) :
    ∃ sourceValue, Evaluates program env (.character c) sourceValue ∧ lowerValue sourceValue = value := by
  cases evaluated with
  | character => exact ⟨Value.character c, Evaluates.character, by simp [lowerValue]⟩

theorem floatBin_evaluation_reflected (program : Definitions) (env : Environment)
    (op : Surface.FloatBinOp) (left right : Expr)
    (leftReflected : ∀ {value},
      PolyIR.Evaluates (lowerDefinitions program) (lowerEnv env)
        (lower (identities env) left) value →
      ∃ sourceValue, Evaluates program env left sourceValue ∧ lowerValue sourceValue = value)
    (rightReflected : ∀ {value},
      PolyIR.Evaluates (lowerDefinitions program) (lowerEnv env)
        (lower (identities env) right) value →
      ∃ sourceValue, Evaluates program env right sourceValue ∧ lowerValue sourceValue = value)
    (value : PolyIR.Value)
    (evaluated : PolyIR.Evaluates (lowerDefinitions program) (lowerEnv env)
      (lower (identities env) (.floatBin op left right)) value) :
    ∃ sourceValue, Evaluates program env (.floatBin op left right) sourceValue ∧
      lowerValue sourceValue = value := by
  rw [lower_eq] at evaluated
  cases evaluated with
  | floatBin leftEval rightEval =>
      rename_i leftFloat rightFloat
      obtain ⟨sourceLeft, sourceLeftEval, leftLowered⟩ := leftReflected leftEval
      obtain ⟨sourceRight, sourceRightEval, rightLowered⟩ := rightReflected rightEval
      cases sourceLeft <;> simp_all [lowerValue]
      cases sourceRight <;> simp_all [lowerValue]
      cases leftLowered
      cases rightLowered
      exact ⟨.float (match op with
        | .add => leftFloat.add rightFloat | .sub => leftFloat.sub rightFloat
        | .mul => leftFloat.mul rightFloat | .div => leftFloat.div rightFloat),
        .floatBin sourceLeftEval sourceRightEval, by cases op <;> rfl⟩

theorem unit_evaluation_reflected (program : Definitions) (env : Environment)
    (value : PolyIR.Value)
    (evaluated : PolyIR.Evaluates (lowerDefinitions program) (lowerEnv env) .unit value) :
    ∃ sourceValue, Evaluates program env .unit sourceValue ∧ lowerValue sourceValue = value := by
  cases evaluated with
  | unit => exact ⟨Value.unit, Evaluates.unit, rfl⟩

theorem nil_evaluation_reflected (program : Definitions) (env : Environment)
    (value : PolyIR.Value)
    (evaluated : PolyIR.Evaluates (lowerDefinitions program) (lowerEnv env) .nil value) :
    ∃ sourceValue, Evaluates program env .nil sourceValue ∧ lowerValue sourceValue = value := by
  cases evaluated with
  | nil => exact ⟨Value.nil, Evaluates.nil, rfl⟩

theorem none_evaluation_reflected (program : Definitions) (env : Environment)
    (value : PolyIR.Value)
    (evaluated : PolyIR.Evaluates (lowerDefinitions program) (lowerEnv env) .none value) :
    ∃ sourceValue, Evaluates program env .none sourceValue ∧ lowerValue sourceValue = value := by
  cases evaluated with
  | none => exact ⟨Value.none, Evaluates.none, rfl⟩

theorem lambda_evaluation_reflected (program : Definitions) (env : Environment)
    (parameters : List Nat) (body : Expr) (value : PolyIR.Value)
    (evaluated : PolyIR.Evaluates (lowerDefinitions program) (lowerEnv env)
      (lower (identities env) (.lam parameters body)) value) :
    ∃ sourceValue, Evaluates program env (.lam parameters body) sourceValue ∧
      lowerValue sourceValue = value := by
  change PolyIR.Evaluates (lowerDefinitions program) (lowerEnv env)
    (.lam parameters.length (lower (parameters ++ identities env) body)) value at evaluated
  cases evaluated with
  | lam =>
      refine ⟨Value.closure parameters body env, Evaluates.lam, ?_⟩
      simp [lowerValue]

theorem add_evaluation_reflected (program : Definitions) (env : Environment)
    (left right : Expr)
    (leftReflected : ∀ {value},
      PolyIR.Evaluates (lowerDefinitions program) (lowerEnv env)
        (lower (identities env) left) value →
      ∃ sourceValue, Evaluates program env left sourceValue ∧ lowerValue sourceValue = value)
    (rightReflected : ∀ {value},
      PolyIR.Evaluates (lowerDefinitions program) (lowerEnv env)
        (lower (identities env) right) value →
      ∃ sourceValue, Evaluates program env right sourceValue ∧ lowerValue sourceValue = value)
    (value : PolyIR.Value)
    (evaluated : PolyIR.Evaluates (lowerDefinitions program) (lowerEnv env)
      (lower (identities env) (.add left right)) value) :
    ∃ sourceValue, Evaluates program env (.add left right) sourceValue ∧
      lowerValue sourceValue = value := by
  rw [lower_eq] at evaluated
  cases evaluated with
  | add leftEval rightEval =>
      obtain ⟨leftValue, leftSourceEval, leftLowered⟩ := leftReflected leftEval
      obtain ⟨rightValue, rightSourceEval, rightLowered⟩ := rightReflected rightEval
      cases leftValue <;> simp_all [lowerValue]
      cases rightValue <;> simp_all [lowerValue]
      exact ⟨.int (_ + _), .add leftSourceEval rightSourceEval, by simp_all [lowerValue]⟩

theorem sub_evaluation_reflected (program : Definitions) (env : Environment)
    (left right : Expr)
    (leftReflected : ∀ {value},
      PolyIR.Evaluates (lowerDefinitions program) (lowerEnv env)
        (lower (identities env) left) value →
      ∃ sourceValue, Evaluates program env left sourceValue ∧ lowerValue sourceValue = value)
    (rightReflected : ∀ {value},
      PolyIR.Evaluates (lowerDefinitions program) (lowerEnv env)
        (lower (identities env) right) value →
      ∃ sourceValue, Evaluates program env right sourceValue ∧ lowerValue sourceValue = value)
    (value : PolyIR.Value)
    (evaluated : PolyIR.Evaluates (lowerDefinitions program) (lowerEnv env)
      (lower (identities env) (.sub left right)) value) :
    ∃ sourceValue, Evaluates program env (.sub left right) sourceValue ∧
      lowerValue sourceValue = value := by
  rw [lower_eq] at evaluated
  cases evaluated with
  | sub leftEval rightEval =>
      obtain ⟨leftValue, leftSourceEval, leftLowered⟩ := leftReflected leftEval
      obtain ⟨rightValue, rightSourceEval, rightLowered⟩ := rightReflected rightEval
      cases leftValue <;> simp_all [lowerValue]
      cases rightValue <;> simp_all [lowerValue]
      exact ⟨.int (_ - _), .sub leftSourceEval rightSourceEval, by simp_all [lowerValue]⟩

theorem mul_evaluation_reflected (program : Definitions) (env : Environment)
    (left right : Expr)
    (leftReflected : ∀ {value},
      PolyIR.Evaluates (lowerDefinitions program) (lowerEnv env)
        (lower (identities env) left) value →
      ∃ sourceValue, Evaluates program env left sourceValue ∧ lowerValue sourceValue = value)
    (rightReflected : ∀ {value},
      PolyIR.Evaluates (lowerDefinitions program) (lowerEnv env)
        (lower (identities env) right) value →
      ∃ sourceValue, Evaluates program env right sourceValue ∧ lowerValue sourceValue = value)
    (value : PolyIR.Value)
    (evaluated : PolyIR.Evaluates (lowerDefinitions program) (lowerEnv env)
      (lower (identities env) (.mul left right)) value) :
    ∃ sourceValue, Evaluates program env (.mul left right) sourceValue ∧
      lowerValue sourceValue = value := by
  rw [lower_eq] at evaluated
  cases evaluated with
  | mul leftEval rightEval =>
      obtain ⟨leftValue, leftSourceEval, leftLowered⟩ := leftReflected leftEval
      obtain ⟨rightValue, rightSourceEval, rightLowered⟩ := rightReflected rightEval
      cases leftValue <;> simp_all [lowerValue]
      cases rightValue <;> simp_all [lowerValue]
      exact ⟨.int (_ * _), .mul leftSourceEval rightSourceEval, by simp_all [lowerValue]⟩

theorem le_evaluation_reflected (program : Definitions) (env : Environment)
    (left right : Expr)
    (leftReflected : ∀ {value},
      PolyIR.Evaluates (lowerDefinitions program) (lowerEnv env)
        (lower (identities env) left) value →
      ∃ sourceValue, Evaluates program env left sourceValue ∧ lowerValue sourceValue = value)
    (rightReflected : ∀ {value},
      PolyIR.Evaluates (lowerDefinitions program) (lowerEnv env)
        (lower (identities env) right) value →
      ∃ sourceValue, Evaluates program env right sourceValue ∧ lowerValue sourceValue = value)
    (value : PolyIR.Value)
    (evaluated : PolyIR.Evaluates (lowerDefinitions program) (lowerEnv env)
      (lower (identities env) (.le left right)) value) :
    ∃ sourceValue, Evaluates program env (.le left right) sourceValue ∧
      lowerValue sourceValue = value := by
  rw [lower_eq] at evaluated
  cases evaluated with
  | le leftEval rightEval =>
      obtain ⟨leftValue, leftSourceEval, leftLowered⟩ := leftReflected leftEval
      obtain ⟨rightValue, rightSourceEval, rightLowered⟩ := rightReflected rightEval
      cases leftValue <;> simp_all [lowerValue]
      cases rightValue <;> simp_all [lowerValue]
      exact ⟨.bool (decide (_ ≤ _)), .le leftSourceEval rightSourceEval,
        by simp_all [lowerValue]⟩

theorem intEq_evaluation_reflected (program : Definitions) (env : Environment)
    (left right : Expr)
    (leftReflected : ∀ {value},
      PolyIR.Evaluates (lowerDefinitions program) (lowerEnv env)
        (lower (identities env) left) value →
      ∃ sourceValue, Evaluates program env left sourceValue ∧ lowerValue sourceValue = value)
    (rightReflected : ∀ {value},
      PolyIR.Evaluates (lowerDefinitions program) (lowerEnv env)
        (lower (identities env) right) value →
      ∃ sourceValue, Evaluates program env right sourceValue ∧ lowerValue sourceValue = value)
    (value : PolyIR.Value)
    (evaluated : PolyIR.Evaluates (lowerDefinitions program) (lowerEnv env)
      (lower (identities env) (.intEq left right)) value) :
    ∃ sourceValue, Evaluates program env (.intEq left right) sourceValue ∧
      lowerValue sourceValue = value := by
  rw [lower_eq] at evaluated
  cases evaluated with
  | intEq leftEval rightEval =>
      obtain ⟨leftValue, leftSourceEval, leftLowered⟩ := leftReflected leftEval
      obtain ⟨rightValue, rightSourceEval, rightLowered⟩ := rightReflected rightEval
      cases leftValue <;> simp_all [lowerValue]
      cases rightValue <;> simp_all [lowerValue]
      exact ⟨.bool (_ == _), .intEq leftSourceEval rightSourceEval,
        by simp_all [lowerValue]⟩

theorem ite_evaluation_reflected (program : Definitions) (env : Environment)
    (condition yes no : Expr)
    (conditionReflected : ∀ {value},
      PolyIR.Evaluates (lowerDefinitions program) (lowerEnv env)
        (lower (identities env) condition) value →
      ∃ sourceValue, Evaluates program env condition sourceValue ∧ lowerValue sourceValue = value)
    (yesReflected : ∀ {value},
      PolyIR.Evaluates (lowerDefinitions program) (lowerEnv env)
        (lower (identities env) yes) value →
      ∃ sourceValue, Evaluates program env yes sourceValue ∧ lowerValue sourceValue = value)
    (noReflected : ∀ {value},
      PolyIR.Evaluates (lowerDefinitions program) (lowerEnv env)
        (lower (identities env) no) value →
      ∃ sourceValue, Evaluates program env no sourceValue ∧ lowerValue sourceValue = value)
    (value : PolyIR.Value)
    (evaluated : PolyIR.Evaluates (lowerDefinitions program) (lowerEnv env)
      (lower (identities env) (.ite condition yes no)) value) :
    ∃ sourceValue, Evaluates program env (.ite condition yes no) sourceValue ∧
      lowerValue sourceValue = value := by
  rw [lower_eq] at evaluated
  cases evaluated with
  | ifTrue conditionEval yesEval =>
      obtain ⟨conditionValue, conditionSourceEval, conditionLowered⟩ :=
        conditionReflected conditionEval
      cases conditionValue <;> simp_all [lowerValue]
      obtain ⟨yesValue, yesSourceEval, yesLowered⟩ := yesReflected yesEval
      exact ⟨yesValue, .ifTrue conditionSourceEval yesSourceEval, yesLowered⟩
  | ifFalse conditionEval noEval =>
      obtain ⟨conditionValue, conditionSourceEval, conditionLowered⟩ :=
        conditionReflected conditionEval
      cases conditionValue <;> simp_all [lowerValue]
      obtain ⟨noValue, noSourceEval, noLowered⟩ := noReflected noEval
      exact ⟨noValue, .ifFalse conditionSourceEval noSourceEval, noLowered⟩

theorem matchList_evaluation_reflected (program : Definitions) (env : Environment)
    (target empty : Expr) (headId tailId : Nat) (full : Expr)
    (targetReflected : ∀ {value},
      PolyIR.Evaluates (lowerDefinitions program) (lowerEnv env)
        (lower (identities env) target) value →
      ∃ sourceValue, Evaluates program env target sourceValue ∧ lowerValue sourceValue = value)
    (emptyReflected : ∀ {value},
      PolyIR.Evaluates (lowerDefinitions program) (lowerEnv env)
        (lower (identities env) empty) value →
      ∃ sourceValue, Evaluates program env empty sourceValue ∧ lowerValue sourceValue = value)
    (consBodyReflected : ∀ (sourceHead sourceTail : Value) (irHead irTail : PolyIR.Value),
      lowerValue sourceHead = irHead → lowerValue sourceTail = irTail → ∀ {value},
      PolyIR.Evaluates (lowerDefinitions program) (irHead :: irTail :: lowerEnv env)
        (lower (headId :: tailId :: identities env) full) value →
      ∃ sourceValue,
        Evaluates program ((headId, sourceHead) :: (tailId, sourceTail) :: env) full sourceValue ∧
          lowerValue sourceValue = value)
    (value : PolyIR.Value)
    (evaluated : PolyIR.Evaluates (lowerDefinitions program) (lowerEnv env)
      (lower (identities env) (.matchList target empty headId tailId full)) value) :
    ∃ sourceValue,
      Evaluates program env (.matchList target empty headId tailId full) sourceValue ∧
        lowerValue sourceValue = value := by
  rw [lower_eq] at evaluated
  cases evaluated with
  | matchNil targetEval emptyEval =>
      obtain ⟨sourceTarget, sourceTargetEval, targetLowered⟩ :=
        targetReflected targetEval
      cases sourceTarget <;> simp_all [lowerValue]
      obtain ⟨sourceEmpty, sourceEmptyEval, emptyLowered⟩ := emptyReflected emptyEval
      exact ⟨sourceEmpty, .matchNil sourceTargetEval sourceEmptyEval, emptyLowered⟩
  | matchCons targetEval bodyEval =>
      obtain ⟨sourceTarget, sourceTargetEval, targetLowered⟩ :=
        targetReflected targetEval
      cases sourceTarget with
      | cons sourceHead sourceTail =>
          simp [lowerValue] at targetLowered
          obtain ⟨headLowered, tailLowered⟩ := targetLowered
          obtain ⟨sourceBody, sourceBodyEval, bodyLowered⟩ :=
            consBodyReflected sourceHead sourceTail _ _ headLowered tailLowered bodyEval
          exact ⟨sourceBody, .matchCons sourceTargetEval sourceBodyEval, bodyLowered⟩
      | bool _ => simp [lowerValue] at targetLowered
      | int _ => simp [lowerValue] at targetLowered
      | float _ => simp [lowerValue] at targetLowered
      | string _ => simp [lowerValue] at targetLowered
      | character _ => simp [lowerValue] at targetLowered
      | unit => simp [lowerValue] at targetLowered
      | closure _ _ _ => simp [lowerValue] at targetLowered
      | global _ => simp [lowerValue] at targetLowered
      | nil => simp [lowerValue] at targetLowered
      | none => simp [lowerValue] at targetLowered
      | some _ => simp [lowerValue] at targetLowered

theorem matchOption_evaluation_reflected (program : Definitions) (env : Environment)
    (target empty : Expr) (binderId : Nat) (full : Expr)
    (targetReflected : ∀ {value},
      PolyIR.Evaluates (lowerDefinitions program) (lowerEnv env)
        (lower (identities env) target) value →
      ∃ sourceValue, Evaluates program env target sourceValue ∧ lowerValue sourceValue = value)
    (emptyReflected : ∀ {value},
      PolyIR.Evaluates (lowerDefinitions program) (lowerEnv env)
        (lower (identities env) empty) value →
      ∃ sourceValue, Evaluates program env empty sourceValue ∧ lowerValue sourceValue = value)
    (someBodyReflected : ∀ (sourceItem : Value) (irItem : PolyIR.Value),
      lowerValue sourceItem = irItem → ∀ {value},
      PolyIR.Evaluates (lowerDefinitions program) (irItem :: lowerEnv env)
        (lower (binderId :: identities env) full) value →
      ∃ sourceValue,
        Evaluates program ((binderId, sourceItem) :: env) full sourceValue ∧
          lowerValue sourceValue = value)
    (value : PolyIR.Value)
    (evaluated : PolyIR.Evaluates (lowerDefinitions program) (lowerEnv env)
      (lower (identities env) (.matchOption target empty binderId full)) value) :
    ∃ sourceValue,
      Evaluates program env (.matchOption target empty binderId full) sourceValue ∧
        lowerValue sourceValue = value := by
  rw [lower_eq] at evaluated
  cases evaluated with
  | matchNone targetEval emptyEval =>
      obtain ⟨sourceTarget, sourceTargetEval, targetLowered⟩ :=
        targetReflected targetEval
      cases sourceTarget <;> simp_all [lowerValue]
      obtain ⟨sourceEmpty, sourceEmptyEval, emptyLowered⟩ := emptyReflected emptyEval
      exact ⟨sourceEmpty, .matchNone sourceTargetEval sourceEmptyEval, emptyLowered⟩
  | matchSome targetEval bodyEval =>
      obtain ⟨sourceTarget, sourceTargetEval, targetLowered⟩ :=
        targetReflected targetEval
      cases sourceTarget with
      | some sourceItem =>
          simp [lowerValue] at targetLowered
          obtain ⟨sourceBody, sourceBodyEval, bodyLowered⟩ :=
            someBodyReflected sourceItem _ targetLowered bodyEval
          exact ⟨sourceBody, .matchSome sourceTargetEval sourceBodyEval, bodyLowered⟩
      | bool _ => simp [lowerValue] at targetLowered
      | int _ => simp [lowerValue] at targetLowered
      | float _ => simp [lowerValue] at targetLowered
      | string _ => simp [lowerValue] at targetLowered
      | character _ => simp [lowerValue] at targetLowered
      | unit => simp [lowerValue] at targetLowered
      | closure _ _ _ => simp [lowerValue] at targetLowered
      | global _ => simp [lowerValue] at targetLowered
      | nil => simp [lowerValue] at targetLowered
      | cons _ _ => simp [lowerValue] at targetLowered
      | none => simp [lowerValue] at targetLowered

theorem some_evaluation_reflected (program : Definitions) (env : Environment)
    (expression : Expr)
    (innerReflected : ∀ {value},
      PolyIR.Evaluates (lowerDefinitions program) (lowerEnv env)
        (lower (identities env) expression) value →
      ∃ sourceValue, Evaluates program env expression sourceValue ∧ lowerValue sourceValue = value)
    (value : PolyIR.Value)
    (evaluated : PolyIR.Evaluates (lowerDefinitions program) (lowerEnv env)
      (lower (identities env) (.some expression)) value) :
    ∃ sourceValue, Evaluates program env (.some expression) sourceValue ∧
      lowerValue sourceValue = value := by
  rw [lower_eq] at evaluated
  cases evaluated with
  | some innerEval =>
      obtain ⟨sourceInner, sourceEval, lowered⟩ := innerReflected innerEval
      exact ⟨.some sourceInner, .some sourceEval, by simp [lowerValue, lowered]⟩

theorem cons_evaluation_reflected (program : Definitions) (env : Environment)
    (head tail : Expr)
    (headReflected : ∀ {value},
      PolyIR.Evaluates (lowerDefinitions program) (lowerEnv env)
        (lower (identities env) head) value →
      ∃ sourceValue, Evaluates program env head sourceValue ∧ lowerValue sourceValue = value)
    (tailReflected : ∀ {value},
      PolyIR.Evaluates (lowerDefinitions program) (lowerEnv env)
        (lower (identities env) tail) value →
      ∃ sourceValue, Evaluates program env tail sourceValue ∧ lowerValue sourceValue = value)
    (value : PolyIR.Value)
    (evaluated : PolyIR.Evaluates (lowerDefinitions program) (lowerEnv env)
      (lower (identities env) (.cons head tail)) value) :
    ∃ sourceValue, Evaluates program env (.cons head tail) sourceValue ∧
      lowerValue sourceValue = value := by
  rw [lower_eq] at evaluated
  cases evaluated with
  | cons headEval tailEval =>
      obtain ⟨sourceHead, headSourceEval, headLowered⟩ := headReflected headEval
      obtain ⟨sourceTail, tailSourceEval, tailLowered⟩ := tailReflected tailEval
      exact ⟨.cons sourceHead sourceTail, .cons headSourceEval tailSourceEval,
        by simp [lowerValue, headLowered, tailLowered]⟩

theorem arguments_evaluation_reflected (program : Definitions) (env : Environment)
    (expressions : List Expr)
    (expressionReflected : ∀ expression {value},
      PolyIR.Evaluates (lowerDefinitions program) (lowerEnv env)
        (lower (identities env) expression) value →
      ∃ sourceValue, Evaluates program env expression sourceValue ∧ lowerValue sourceValue = value)
    (values : List PolyIR.Value)
    (evaluated : PolyIR.ArgumentsEvaluate (lowerDefinitions program) (lowerEnv env)
      (lowerMany (identities env) expressions) values) :
    ∃ sourceValues, ArgumentsEvaluate program env expressions sourceValues ∧
      lowerValues sourceValues = values := by
  induction expressions generalizing values with
  | nil =>
      cases evaluated
      exact ⟨[], .nil, rfl⟩
  | cons expression rest ih =>
      rw [lowerMany_eq] at evaluated
      cases evaluated with
      | cons headEval tailEval =>
          obtain ⟨headValue, headSourceEval, headLowered⟩ :=
            expressionReflected expression headEval
          obtain ⟨tailValues, tailSourceEval, tailLowered⟩ := ih (values := _) tailEval
          exact ⟨headValue :: tailValues, .cons headSourceEval tailSourceEval,
            by simp_all [lowerValues]⟩

private theorem irArguments_value_length {program : List PolyIR.RuntimeDefinition}
    {env : List PolyIR.Value} {expressions : List PolyIR.Term} {values : List PolyIR.Value}
    (evaluated : PolyIR.ArgumentsEvaluate program env expressions values) :
    values.length = expressions.length := by
  induction expressions generalizing values with
  | nil => cases evaluated; rfl
  | cons expression rest ih =>
      cases evaluated with
      | cons _ tailEval => simp [ih tailEval]

theorem letMany_evaluation_reflected (program : Definitions) (env : Environment)
    (ids : List Nat) (initializers : List Expr) (body : Expr)
    (wellScoped : initializers.length = ids.length)
    (argumentsReflected : ∀ {irValues},
      PolyIR.ArgumentsEvaluate (lowerDefinitions program) (lowerEnv env)
        (lowerMany (identities env) initializers) irValues →
      ∃ sourceValues, ArgumentsEvaluate program env initializers sourceValues ∧
        lowerValues sourceValues = irValues)
    (bodyReflected : ∀ (sourceValues : List Value) (irValues : List PolyIR.Value),
      sourceValues.length = ids.length → lowerValues sourceValues = irValues →
      ∀ {value},
        PolyIR.Evaluates (lowerDefinitions program) (irValues ++ lowerEnv env)
          (lower (ids ++ identities env) body) value →
        ∃ sourceValue, Evaluates program (bind ids sourceValues ++ env) body sourceValue ∧
          lowerValue sourceValue = value)
    (value : PolyIR.Value)
    (evaluated : PolyIR.Evaluates (lowerDefinitions program) (lowerEnv env)
      (lower (identities env) (.letMany ids initializers body)) value) :
    ∃ sourceValue, Evaluates program env (.letMany ids initializers body) sourceValue ∧
      lowerValue sourceValue = value := by
  rw [lower_eq] at evaluated
  cases evaluated with
  | letMany argumentsEval bodyEval =>
      obtain ⟨sourceValues, sourceArgumentsEval, argumentsLowered⟩ :=
        argumentsReflected argumentsEval
      have sourceArity : sourceValues.length = ids.length := by
        calc
          sourceValues.length = (lowerValues sourceValues).length := by
            simp [lowerValues]
          _ = _ := congrArg List.length argumentsLowered
          _ = (lowerMany (identities env) initializers).length :=
            irArguments_value_length argumentsEval
          _ = initializers.length := lowerMany_length (identities env) initializers
          _ = ids.length := wellScoped
      obtain ⟨sourceBodyValue, sourceBodyEval, bodyLowered⟩ :=
        bodyReflected sourceValues _ sourceArity argumentsLowered bodyEval
      exact ⟨sourceBodyValue, .letMany sourceArgumentsEval sourceArity sourceBodyEval,
        bodyLowered⟩

theorem sequence_evaluation_reflected (program : Definitions) (env : Environment)
    (expressions : List Expr) (sourcePrevious : Value) (irPrevious : PolyIR.Value)
    (previousLowered : lowerValue sourcePrevious = irPrevious)
    (expressionReflected : ∀ expression {value},
      PolyIR.Evaluates (lowerDefinitions program) (lowerEnv env)
        (lower (identities env) expression) value →
      ∃ sourceValue, Evaluates program env expression sourceValue ∧ lowerValue sourceValue = value)
    (value : PolyIR.Value)
    (evaluated : PolyIR.SequenceEvaluates (lowerDefinitions program) (lowerEnv env)
      (lowerMany (identities env) expressions) irPrevious value) :
    ∃ sourceValue, SequenceEvaluates program env expressions sourcePrevious sourceValue ∧
      lowerValue sourceValue = value := by
  induction expressions generalizing sourcePrevious irPrevious value with
  | nil =>
      cases evaluated
      exact ⟨sourcePrevious, .nil, previousLowered⟩
  | cons expression rest ih =>
      rw [lowerMany_eq] at evaluated
      cases evaluated with
      | cons headEval tailEval =>
          obtain ⟨headValue, headSourceEval, headLowered⟩ :=
            expressionReflected expression headEval
          obtain ⟨result, restSourceEval, resultLowered⟩ :=
            ih (sourcePrevious := headValue) (irPrevious := _) (value := value)
              headLowered tailEval
          exact ⟨result, .cons headSourceEval restSourceEval, resultLowered⟩

theorem begin_evaluation_reflected (program : Definitions) (env : Environment)
    (first : Expr) (rest : List Expr)
    (firstReflected : ∀ {value},
      PolyIR.Evaluates (lowerDefinitions program) (lowerEnv env)
        (lower (identities env) first) value →
      ∃ sourceValue, Evaluates program env first sourceValue ∧ lowerValue sourceValue = value)
    (restReflected : ∀ expression {value},
      PolyIR.Evaluates (lowerDefinitions program) (lowerEnv env)
        (lower (identities env) expression) value →
      ∃ sourceValue, Evaluates program env expression sourceValue ∧ lowerValue sourceValue = value)
    (value : PolyIR.Value)
    (evaluated : PolyIR.Evaluates (lowerDefinitions program) (lowerEnv env)
      (lower (identities env) (.begin first rest)) value) :
    ∃ sourceValue, Evaluates program env (.begin first rest) sourceValue ∧
      lowerValue sourceValue = value := by
  rw [lower_eq] at evaluated
  cases evaluated with
  | begin firstEval restEval =>
      obtain ⟨firstValue, firstSourceEval, firstLowered⟩ := firstReflected firstEval
      obtain ⟨result, restSourceEval, resultLowered⟩ :=
        sequence_evaluation_reflected program env rest firstValue _ firstLowered
          restReflected value restEval
      exact ⟨result, .begin firstSourceEval restSourceEval, resultLowered⟩

def EvaluationReflection (program : Definitions) : Prop :=
  ∀ (env : Environment) (locals : List Nat) (expression : Expr)
    (irEnv : List PolyIR.Value) (irExpression : PolyIR.Term),
    irEnv = lowerEnv env → locals = identities env → irExpression = lower locals expression →
    ∀ {value},
      PolyIR.Evaluates (lowerDefinitions program) irEnv irExpression value →
      ∃ sourceValue, Evaluates program env expression sourceValue ∧ lowerValue sourceValue = value

theorem appClosure_evaluation_reflected (program : Definitions) (env : Environment)
    (function : Expr) (arguments : List Expr) (arity : Nat) (irBody : PolyIR.Term)
    (irCaptured irArguments : List PolyIR.Value) (value : PolyIR.Value)
    (reflection : EvaluationReflection program)
    (functionEval : PolyIR.Evaluates (lowerDefinitions program) (lowerEnv env)
      (lower (identities env) function) (.closure arity irBody irCaptured))
    (argumentsEval : PolyIR.ArgumentsEvaluate (lowerDefinitions program) (lowerEnv env)
      (lowerMany (identities env) arguments) irArguments)
    (argumentsArity : irArguments.length = arity)
    (bodyEval : PolyIR.Evaluates (lowerDefinitions program) (irArguments ++ irCaptured)
      irBody value) :
    ∃ sourceValue, Evaluates program env (.app function arguments) sourceValue ∧
      lowerValue sourceValue = value := by
  obtain ⟨sourceFunction, sourceFunctionEval, sourceFunctionLowered⟩ :=
    reflection env (identities env) function (lowerEnv env)
      (lower (identities env) function) rfl rfl rfl functionEval
  cases sourceFunction with
  | closure parameters body captured =>
      simp [lowerValue] at sourceFunctionLowered
      rcases sourceFunctionLowered with ⟨arityEq, bodyEq, capturedEq⟩
      have sourceArgumentsReflection : ∀ {irValues},
          PolyIR.ArgumentsEvaluate (lowerDefinitions program) (lowerEnv env)
            (lowerMany (identities env) arguments) irValues →
          ∃ sourceValues, ArgumentsEvaluate program env arguments sourceValues ∧
            lowerValues sourceValues = irValues := by
        intro irValues argsEval
        exact arguments_evaluation_reflected program env arguments
          (fun expression {irValue} expressionEval =>
            reflection env (identities env) expression (lowerEnv env)
              (lower (identities env) expression) rfl rfl rfl expressionEval)
          irValues argsEval
      obtain ⟨sourceArguments, sourceArgumentsEval, argumentsLowered⟩ :=
        sourceArgumentsReflection argumentsEval
      have sourceArity : sourceArguments.length = parameters.length := by
        calc
          sourceArguments.length = (lowerValues sourceArguments).length := by
            simp [lowerValues]
          _ = _ := congrArg List.length argumentsLowered
          _ = arity := argumentsArity
          _ = parameters.length := arityEq.symm
      have bodyEnvironmentEq :
          lowerEnv (bind parameters sourceArguments ++ captured) =
            irArguments ++ irCaptured := by
        rw [lowerEnv_bind_append parameters sourceArguments captured sourceArity,
          argumentsLowered, capturedEq]
      have bodyLocalsEq := identities_bind_append parameters sourceArguments captured sourceArity
      have bodyTermEq : irBody =
          lower (identities (bind parameters sourceArguments ++ captured)) body := by
        rw [bodyLocalsEq, ← bodyEq]
      obtain ⟨sourceResult, sourceBodyEval, resultLowered⟩ :=
        reflection (bind parameters sourceArguments ++ captured)
          (identities (bind parameters sourceArguments ++ captured)) body
          (irArguments ++ irCaptured) irBody bodyEnvironmentEq.symm rfl bodyTermEq bodyEval
      exact ⟨sourceResult,
        .appClosure sourceFunctionEval sourceArgumentsEval sourceArity sourceBodyEval,
        resultLowered⟩
  | bool _ => simp [lowerValue] at sourceFunctionLowered
  | int _ => simp [lowerValue] at sourceFunctionLowered
  | float _ => simp [lowerValue] at sourceFunctionLowered
  | string _ => simp [lowerValue] at sourceFunctionLowered
  | character _ => simp [lowerValue] at sourceFunctionLowered
  | unit => simp [lowerValue] at sourceFunctionLowered
  | global _ => simp [lowerValue] at sourceFunctionLowered
  | nil => simp [lowerValue] at sourceFunctionLowered
  | cons _ _ => simp [lowerValue] at sourceFunctionLowered
  | none => simp [lowerValue] at sourceFunctionLowered
  | some _ => simp [lowerValue] at sourceFunctionLowered

theorem appGlobal_evaluation_reflected (program : Definitions) (env : Environment)
    (function : Expr) (arguments : List Expr) (index : Nat)
    (irArguments : List PolyIR.Value) (irDefinition : PolyIR.RuntimeDefinition)
    (value : PolyIR.Value) (reflection : EvaluationReflection program)
    (functionEval : PolyIR.Evaluates (lowerDefinitions program) (lowerEnv env)
      (lower (identities env) function) (.global index))
    (argumentsEval : PolyIR.ArgumentsEvaluate (lowerDefinitions program) (lowerEnv env)
      (lowerMany (identities env) arguments) irArguments)
    (definitionFound : (lowerDefinitions program)[index]? = some irDefinition)
    (argumentsArity : irArguments.length = irDefinition.arity)
    (bodyEval : PolyIR.Evaluates (lowerDefinitions program) irArguments irDefinition.body value) :
    ∃ sourceValue, Evaluates program env (.app function arguments) sourceValue ∧
      lowerValue sourceValue = value := by
  obtain ⟨sourceFunction, sourceFunctionEval, sourceFunctionLowered⟩ :=
    reflection env (identities env) function (lowerEnv env)
      (lower (identities env) function) rfl rfl rfl functionEval
  have sourceGlobal : sourceFunction = .global index := by
    cases sourceFunction <;> simp_all [lowerValue]
  subst sourceFunction
  obtain ⟨ids, sourceBody, sourceDefinitionFound, definitionEq⟩ :=
    definitions_lookup_reflects program index irDefinition definitionFound
  have sourceArgumentsReflection : ∀ {irValues},
      PolyIR.ArgumentsEvaluate (lowerDefinitions program) (lowerEnv env)
        (lowerMany (identities env) arguments) irValues →
      ∃ sourceValues, ArgumentsEvaluate program env arguments sourceValues ∧
        lowerValues sourceValues = irValues := by
    intro irValues argsEval
    exact arguments_evaluation_reflected program env arguments
      (fun expression {irValue} expressionEval =>
        reflection env (identities env) expression (lowerEnv env)
          (lower (identities env) expression) rfl rfl rfl expressionEval)
      irValues argsEval
  obtain ⟨sourceArguments, sourceArgumentsEval, argumentsLowered⟩ :=
    sourceArgumentsReflection argumentsEval
  have sourceArity : sourceArguments.length = ids.length := by
    calc
      sourceArguments.length = (lowerValues sourceArguments).length := by simp [lowerValues]
      _ = _ := congrArg List.length argumentsLowered
      _ = irDefinition.arity := argumentsArity
      _ = ids.length := by
        have fields := congrArg PolyIR.RuntimeDefinition.arity definitionEq
        simpa using fields
  have bodyEnvironmentEq :
      lowerEnv (bind ids sourceArguments) = irArguments := by
    rw [lowerEnv_bind ids sourceArguments sourceArity, argumentsLowered]
  have bodyTermEq : irDefinition.body = lower (identities (bind ids sourceArguments)) sourceBody := by
    have bodyField := congrArg PolyIR.RuntimeDefinition.body definitionEq
    simpa [bind_identifiers ids sourceArguments sourceArity] using bodyField
  obtain ⟨sourceResult, sourceBodyEval, resultLowered⟩ :=
    reflection (bind ids sourceArguments) (identities (bind ids sourceArguments)) sourceBody
      irArguments irDefinition.body bodyEnvironmentEq.symm rfl bodyTermEq bodyEval
  exact ⟨sourceResult,
    .appGlobal sourceFunctionEval sourceArgumentsEval sourceDefinitionFound sourceArity sourceBodyEval,
    resultLowered⟩

theorem app_evaluation_reflected (program : Definitions) (env : Environment)
    (function : Expr) (arguments : List Expr) (value : PolyIR.Value)
    (reflection : EvaluationReflection program)
    (evaluated : PolyIR.Evaluates (lowerDefinitions program) (lowerEnv env)
      (.app (lower (identities env) function) (lowerMany (identities env) arguments)) value) :
    ∃ sourceValue, Evaluates program env (.app function arguments) sourceValue ∧
      lowerValue sourceValue = value := by
  cases evaluated with
  | appClosure functionEval argumentsEval argumentsArity bodyEval =>
      exact appClosure_evaluation_reflected program env function arguments _ _ _ _ value reflection
        functionEval argumentsEval argumentsArity bodyEval
  | appGlobal functionEval argumentsEval definitionFound argumentsArity bodyEval =>
      exact appGlobal_evaluation_reflected program env function arguments _ _ _ value reflection
        functionEval argumentsEval definitionFound argumentsArity bodyEval

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
    PolyIR.Evaluates.bool, PolyIR.Evaluates.int, PolyIR.Evaluates.floatBin,
    PolyIR.Evaluates.string, PolyIR.Evaluates.character, PolyIR.Evaluates.unit, PolyIR.Evaluates.lam,
    PolyIR.Evaluates.appClosure, PolyIR.Evaluates.appGlobal, PolyIR.Evaluates.ifTrue, PolyIR.Evaluates.ifFalse,
    PolyIR.Evaluates.add, PolyIR.Evaluates.sub, PolyIR.Evaluates.mul, PolyIR.Evaluates.le, PolyIR.Evaluates.intEq,
    PolyIR.Evaluates.letMany, PolyIR.Evaluates.begin, PolyIR.Evaluates.nil, PolyIR.Evaluates.cons,
    PolyIR.Evaluates.none, PolyIR.Evaluates.some, PolyIR.Evaluates.matchNil, PolyIR.Evaluates.matchCons,
    PolyIR.Evaluates.matchNone, PolyIR.Evaluates.matchSome, PolyIR.ArgumentsEvaluate.nil,
    PolyIR.ArgumentsEvaluate.cons, PolyIR.SequenceEvaluates.nil, PolyIR.SequenceEvaluates.cons,
    lookup_lowered, definitions_lookup, lowered_arity]

/-- Termination in the independent identity-based source semantics means that
there is a finite big-step derivation. Divergence is the absence of every such
finite result; it is not fuel exhaustion in an evaluator. -/
def SourceTerminates (program : Definitions) (env : Environment) (expression : Expr) : Prop :=
  ∃ value, Evaluates program env expression value

def SourceDiverges (program : Definitions) (env : Environment) (expression : Expr) : Prop :=
  ¬ SourceTerminates program env expression

def LoweredTerminates (program : Definitions) (env : Environment) (expression : Expr) : Prop :=
  ∃ value, PolyIR.Evaluates (lowerDefinitions program) (lowerEnv env)
    (lower (identities env) expression) value

def LoweredDiverges (program : Definitions) (env : Environment) (expression : Expr) : Prop :=
  ¬ LoweredTerminates program env expression

/-- Finite source termination always yields finite lowered termination. The
reverse direction is exactly the general evaluation-reflection obligation. -/
theorem termination_preserved_and_reflected (program : Definitions) (env : Environment)
    (expression : Expr) (reflection : EvaluationReflection program) :
    SourceTerminates program env expression ↔ LoweredTerminates program env expression := by
  constructor
  · rintro ⟨value, evaluated⟩
    exact ⟨lowerValue value, evaluation_preserved evaluated⟩
  · rintro ⟨value, evaluated⟩
    obtain ⟨sourceValue, sourceEval, _⟩ := reflection env (identities env) expression
      (lowerEnv env) (lower (identities env) expression) rfl rfl rfl evaluated
    exact ⟨sourceValue, sourceEval⟩

/-- Under the same evaluation-reflection premise, the finite-derivation
definition of divergence is preserved and reflected exactly. -/
theorem divergence_preserved_and_reflected (program : Definitions) (env : Environment)
    (expression : Expr) (reflection : EvaluationReflection program) :
    SourceDiverges program env expression ↔ LoweredDiverges program env expression := by
  constructor
  · intro sourceDiverges loweredTerminates
    exact sourceDiverges ((termination_preserved_and_reflected program env expression
      reflection).2 loweredTerminates)
  · intro loweredDiverges sourceTerminates
    exact loweredDiverges ((termination_preserved_and_reflected program env expression
      reflection).1 sourceTerminates)

/-- Binder arity is necessary for reverse reflection: lowering erases the
identity list of a parallel `letMany`, so an unaligned source let can still
evaluate in PolyIR even though the Named rule rejects its initializer count.
Checked decoding rules out this counterexample through
`decodeExprChecked_letMany_lengths`. -/
theorem unaligned_letMany_lowered_terminates_without_named_evaluation :
    LoweredTerminates [] [] (.letMany [] [.int 7] (.int 9)) ∧
      ¬ SourceTerminates [] [] (.letMany [] [.int 7] (.int 9)) := by
  constructor
  · refine ⟨.int 9, ?_⟩
    rw [lower_eq]
    exact PolyIR.Evaluates.letMany
      (PolyIR.ArgumentsEvaluate.cons PolyIR.Evaluates.int PolyIR.ArgumentsEvaluate.nil)
      PolyIR.Evaluates.int
  · rintro ⟨value, evaluated⟩
    cases evaluated with
    | letMany argumentsEval arity bodyEval =>
        cases argumentsEval with
        | cons _ tailEval =>
            cases tailEval with
            | nil => simp at arity

end
end NLisp.Named
