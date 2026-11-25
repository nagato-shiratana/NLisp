import NLisp.Erasure
import NLisp.TypeArguments

namespace NLisp.Surface

mutual
def interpret (assignment : Nat → Ty) (type : Ty) : Ty :=
  match type with
  | .var i => assignment i
  | .fn ps result => .fn (interpretTypes assignment ps) (interpret assignment result)
  | .list t => .list (interpret assignment t)
  | .option t => .option (interpret assignment t)
  | t => t
termination_by sizeOf type
decreasing_by all_goals simp_wf; omega

def interpretTypes (assignment : Nat → Ty) (types : List Ty) : List Ty :=
  match types with
  | [] => []
  | t :: ts => interpret assignment t :: interpretTypes assignment ts
termination_by sizeOf types
decreasing_by all_goals simp_wf; omega
end

@[simp] theorem interpretTypes_length (assignment : Nat → Ty) (types : List Ty) :
    (interpretTypes assignment types).length = types.length := by
  induction types with
  | nil => simp [interpretTypes]
  | cons head tail ih => simp [interpretTypes, ih]

@[simp] theorem interpretTypes_append (assignment : Nat → Ty) (a b : List Ty) :
    interpretTypes assignment (a ++ b) = interpretTypes assignment a ++ interpretTypes assignment b := by
  induction a with
  | nil => simp [interpretTypes]
  | cons head tail ih => simp [interpretTypes, ih]

def specialize (assignment : Nat → Ty) (arguments : List Ty) (index : Nat) : Ty :=
  ((arguments[index]?).map (interpret assignment)).getD .unit

mutual
theorem interpret_instantiate (type : Ty) (assignment : Nat → Ty) (arguments : List Ty)
    (valid : type.wellFormed arguments.length) :
    interpret assignment (type.instantiate arguments) = interpret (specialize assignment arguments) type := by
  cases type with
  | boolean | integer | float | string | character | unit => simp [Ty.instantiate, interpret]
  | var index =>
    have bound : index < arguments.length := by simpa [Ty.wellFormed] using valid
    simp [Ty.instantiate, interpret, specialize, getElem?_def, bound]
  | fn ps result =>
    obtain ⟨psValid, retValid⟩ := (by simpa [Ty.wellFormed] using valid :
      (∀ t ∈ ps, t.wellFormed arguments.length) ∧ result.wellFormed arguments.length)
    simp only [Ty.instantiate, interpret]
    rw [interpretTypes_instantiate ps assignment arguments psValid,
      interpret_instantiate result assignment arguments retValid]
  | list element =>
    simp only [Ty.instantiate, interpret]
    rw [interpret_instantiate element assignment arguments (by simpa [Ty.wellFormed] using valid)]
  | option element =>
    simp only [Ty.instantiate, interpret]
    rw [interpret_instantiate element assignment arguments (by simpa [Ty.wellFormed] using valid)]
termination_by sizeOf type
decreasing_by all_goals simp_wf; subst_vars; simp_all; omega

theorem interpretTypes_instantiate (types : List Ty) (assignment : Nat → Ty) (arguments : List Ty)
    (valid : ∀ t ∈ types, t.wellFormed arguments.length) :
    interpretTypes assignment (instantiateTypes arguments types) =
      interpretTypes (specialize assignment arguments) types := by
  cases types with
  | nil => simp [instantiateTypes, interpretTypes]
  | cons head tail =>
    simp only [instantiateTypes, interpretTypes]
    rw [interpret_instantiate head assignment arguments (valid head (by simp)),
      interpretTypes_instantiate tail assignment arguments (by intro t ht; exact valid t (by simp [ht]))]
termination_by sizeOf types
decreasing_by all_goals simp_wf; subst_vars; simp_all; omega
end

theorem instantiateTypes_eq_map (arguments : List Ty) (types : List Ty) :
    instantiateTypes arguments types = types.map (Ty.instantiate arguments) := by
  induction types with
  | nil => simp [instantiateTypes]
  | cons head tail ih => simp [instantiateTypes, ih]

end NLisp.Surface

namespace NLisp.PolyIR
open Surface

/- Logical typing of erased values. Closures retain an existential source
body and type valuation; global functions share their one generic body. -/
mutual
inductive ValueTyped (globals : List Signature) : Value → Ty → Prop where
  | bool : ValueTyped globals (.bool b) .boolean
  | int : ValueTyped globals (.int n) .integer
  | float : ValueTyped globals (.float x) .float
  | string : ValueTyped globals (.string value) .string
  | character : ValueTyped globals (.character value) .character
  | unit : ValueTyped globals .unit .unit
  | closure : HasType globals count (parameters ++ context) body result →
      ValuesTyped globals captured (interpretTypes assignment context) →
      ValueTyped globals (.closure parameters.length (erase body) captured)
        (.fn (interpretTypes assignment parameters) (interpret assignment result))
  | global : globals[index]? = some signature →
      ValueTyped globals (.global index)
        (.fn (interpretTypes assignment signature.parameters) (interpret assignment signature.result))
  | nil : ValueTyped globals .nil (.list t)
  | cons : ValueTyped globals head t → ValueTyped globals tail (.list t) →
      ValueTyped globals (.cons head tail) (.list t)
  | none : ValueTyped globals .none (.option t)
  | some : ValueTyped globals value t → ValueTyped globals (.some value) (.option t)
inductive ValuesTyped (globals : List Signature) : List Value → List Ty → Prop where
  | nil : ValuesTyped globals [] []
  | cons : ValueTyped globals value t → ValuesTyped globals values types →
      ValuesTyped globals (value :: values) (t :: types)
end

structure ProgramTyped (globals : List Signature) (definitions : Surface.Definitions) : Prop where
  lookup : ∀ (index : Nat) (signature : Signature), globals[index]? = some signature →
    ∃ body, definitions[index]? = some (signature, body) ∧
      HasType globals signature.typeArity signature.parameters body signature.result

theorem ValuesTyped.length (h : ValuesTyped globals values types) : values.length = types.length := by
  apply ValuesTyped.rec (motive_1 := fun _ _ _ => True)
    (motive_2 := fun values types _ => values.length = types.length) (t := h)
  all_goals intros
  all_goals first | exact True.intro | rfl | solve | simp_all

theorem ValuesTyped.append (a : ValuesTyped globals left first) (b : ValuesTyped globals right second) :
    ValuesTyped globals (left ++ right) (first ++ second) := by
  induction left generalizing first with
  | nil => cases a; exact b
  | cons head tail ih =>
    cases a with
    | cons h t => exact .cons h (ih t)

theorem ValuesTyped.lookup {index : Nat} {type : Ty}
    (h : ValuesTyped globals values (interpretTypes assignment types))
    (found : types[index]? = some type) : ∃ value, values[index]? = some value ∧
      ValueTyped globals value (interpret assignment type) := by
  induction types generalizing values index with
  | nil => simp [getElem?_def, Nat.not_lt_zero] at found
  | cons head tail ih =>
    simp only [interpretTypes] at h
    cases h with
    | cons headTyped tailTyped =>
      cases index with
      | zero =>
        have same : head = type := by simpa [getElem?_def] using found
        subst type
        refine ⟨_, ?_, headTyped⟩
        simp [getElem?_def]
      | succ index =>
        obtain ⟨value, entry, typed⟩ := ih tailTyped (index := index)
          (by simpa [getElem?_def, Nat.succ_lt_succ_iff] using found)
        exact ⟨value, by simpa [getElem?_def, Nat.succ_lt_succ_iff] using entry, typed⟩

inductive OutcomeTyped (predicate : α → Prop) : Except Fault α → Prop where
  | exhausted : OutcomeTyped predicate (.error .outOfFuel)
  | ok : predicate value → OutcomeTyped predicate (.ok value)

theorem OutcomeTyped.bind (h : OutcomeTyped P result)
    (next : ∀ value, P value → OutcomeTyped Q (continuation value)) :
    OutcomeTyped Q (result >>= continuation) := by
  cases h with
  | exhausted => exact .exhausted
  | ok typed => exact next _ typed

theorem OutcomeTyped.value_ok (h : ValueTyped globals value type) :
    OutcomeTyped (fun v => ValueTyped globals v type) (.ok value) := .ok h

theorem generic_global_typed (found : globals[index]? = some signature)
    (arity : arguments.length = signature.typeArity) (valid : signature.wellFormed) :
    ValueTyped globals (.global index)
      (interpret assignment (.fn (signature.parameters.map (Ty.instantiate arguments))
        (signature.result.instantiate arguments))) := by
  obtain ⟨psValid, retValid⟩ := valid
  simp only [interpret, ← instantiateTypes_eq_map]
  rw [interpretTypes_instantiate signature.parameters assignment arguments (by simpa [arity] using psValid),
    interpret_instantiate signature.result assignment arguments (by simpa [arity] using retValid)]
  exact ValueTyped.global found

theorem function_view (h : ValueTyped globals value (.fn parameters result)) :
    (∃ (count : Nat) (sourceParameters context : List Ty) (body : Surface.Expr)
      (captured : List Value) (assignment : Nat → Ty) (sourceResult : Ty),
      value = .closure sourceParameters.length (erase body) captured ∧
      parameters = interpretTypes assignment sourceParameters ∧ result = interpret assignment sourceResult ∧
      HasType globals count (sourceParameters ++ context) body sourceResult ∧
      ValuesTyped globals captured (interpretTypes assignment context)) ∨
    (∃ (index : Nat) (signature : Signature) (assignment : Nat → Ty),
      value = .global index ∧ globals[index]? = some signature ∧
      parameters = interpretTypes assignment signature.parameters ∧ result = interpret assignment signature.result) := by
  cases h with
  | closure bodyTyped capturedTyped => exact Or.inl ⟨_, _, _, _, _, _, _, rfl, rfl, rfl, bodyTyped, capturedTyped⟩
  | global found => exact Or.inr ⟨_, _, _, rfl, found, rfl, rfl⟩

theorem evaluator_type_safe (wellTyped : ProgramTyped globals definitions) (fuel : Nat) :
    (∀ {count context expression type} (assignment : Nat → Ty) {env},
      HasType globals count context expression type →
      ValuesTyped globals env (interpretTypes assignment context) →
      OutcomeTyped (fun value => ValueTyped globals value (interpret assignment type))
        (evaluate (eraseDefinitions definitions) fuel env (erase expression))) ∧
    (∀ {count context expressions types} (assignment : Nat → Ty) {env},
      ArgsHaveTypes globals count context expressions types →
      ValuesTyped globals env (interpretTypes assignment context) →
      OutcomeTyped (fun values => ValuesTyped globals values (interpretTypes assignment types))
        (evaluateArgs (eraseDefinitions definitions) fuel env (eraseList expressions))) ∧
    (∀ {count context expressions previous result} (assignment : Nat → Ty) {env value},
      SequenceHasType globals count context expressions previous result →
      ValueTyped globals value (interpret assignment previous) →
      ValuesTyped globals env (interpretTypes assignment context) →
      OutcomeTyped (fun value => ValueTyped globals value (interpret assignment result))
        (evaluateSequence (eraseDefinitions definitions) fuel env value (eraseList expressions))) := by
  induction fuel with
  | zero =>
    refine ⟨?_, ?_, ?_⟩
    all_goals intros; exact .exhausted
  | succ fuel ih =>
    obtain ⟨exprSafe, argsSafe, sequenceSafe⟩ := ih
    refine ⟨?_, ?_, ?_⟩
    · intro count context expression type assignment env typing environment
      cases typing with
      | var found =>
        obtain ⟨value, entry, typed⟩ := environment.lookup found
        simpa [erase, evaluate, entry] using OutcomeTyped.value_ok typed
      | global found arity _ valid =>
        obtain ⟨body, entry, _⟩ := wellTyped.lookup _ _ found
        have runtime := eraseDefinitions_lookup entry
        simpa [erase, evaluate, runtime] using OutcomeTyped.value_ok
          (generic_global_typed (assignment := assignment) found arity valid)
      | bool => simp only [erase, evaluate, interpret]; exact .ok .bool
      | int => simp only [erase, evaluate, interpret]; exact .ok .int
      | float => simp only [erase, evaluate, interpret]; exact .ok .float
      | string => simp only [erase, evaluate, interpret]; exact .ok .string
      | character => simp only [erase, evaluate, interpret]; exact .ok .character
      | floatBin leftTyped rightTyped =>
        simp only [erase, evaluate]
        apply OutcomeTyped.bind (exprSafe assignment leftTyped environment)
        intro leftValue leftValueTyped
        apply OutcomeTyped.bind (exprSafe assignment rightTyped environment)
        intro rightValue rightValueTyped
        cases leftValueTyped with
        | float =>
          cases rightValueTyped with
          | float =>
            simp only [interpret]
            exact .ok .float
      | unit => simp only [erase, evaluate, interpret]; exact .ok .unit
      | lam _ _ bodyTyped =>
        simp only [erase, evaluate, interpret]
        exact .ok (.closure (assignment := assignment) bodyTyped environment)
      | app functionTyped argumentsTyped =>
        simp only [erase, evaluate]
        apply OutcomeTyped.bind (exprSafe assignment functionTyped environment)
        intro function functionValue
        apply OutcomeTyped.bind (argsSafe assignment argumentsTyped environment)
        intro values valuesTyped
        simp only [interpret] at functionValue
        rcases function_view functionValue with closure | global
        · rcases closure with ⟨count, ps, ctx, body, captured, sigma, ret,
            shape, parameterEq, resultEq, bodyTyped, capturedTyped⟩
          subst function
          rw [parameterEq] at valuesTyped
          rw [resultEq]
          have arity := valuesTyped.length
          simp only [interpretTypes_length] at arity
          simp only [arity, ↓reduceIte]
          apply exprSafe sigma bodyTyped
          simpa only [interpretTypes_append] using valuesTyped.append capturedTyped
        · rcases global with ⟨index, signature, sigma, shape, found, parameterEq, resultEq⟩
          subst function
          rw [parameterEq] at valuesTyped
          rw [resultEq]
          obtain ⟨body, entry, bodyTyped⟩ := wellTyped.lookup _ _ found
          have runtime := eraseDefinitions_lookup entry
          have arity := valuesTyped.length
          simp only [interpretTypes_length] at arity
          simp only [runtime, arity, ↓reduceIte]
          exact exprSafe sigma bodyTyped valuesTyped
      | ite conditionTyped yesTyped noTyped =>
        simp only [erase, evaluate]
        apply OutcomeTyped.bind (exprSafe assignment conditionTyped environment)
        intro condition conditionValue
        simp only [interpret] at conditionValue
        cases conditionValue with
        | bool =>
          rename_i b
          cases b
          · exact exprSafe assignment noTyped environment
          · exact exprSafe assignment yesTyped environment
      | add a b | sub a b | mul a b | le a b | intEq a b =>
        simp only [erase, evaluate]
        apply OutcomeTyped.bind (exprSafe assignment a environment)
        intro left leftTyped
        apply OutcomeTyped.bind (exprSafe assignment b environment)
        intro right rightTyped
        simp only [interpret] at leftTyped rightTyped ⊢
        cases leftTyped
        cases rightTyped
        first | exact .ok .int | exact .ok .bool
      | letMany _ valuesTyped bodyTyped =>
        simp only [erase, evaluate]
        apply OutcomeTyped.bind (argsSafe assignment valuesTyped environment)
        intro values typed
        apply exprSafe assignment bodyTyped
        simpa only [interpretTypes_append] using typed.append environment
      | begin firstTyped restTyped =>
        simp only [erase, evaluate]
        apply OutcomeTyped.bind (exprSafe assignment firstTyped environment)
        intro value typed
        exact sequenceSafe assignment restTyped typed environment
      | nil _ => simp only [erase, evaluate, interpret]; exact .ok .nil
      | cons _ headTyped tailTyped =>
        simp only [erase, evaluate]
        apply OutcomeTyped.bind (exprSafe assignment headTyped environment)
        intro head headValue
        apply OutcomeTyped.bind (exprSafe assignment tailTyped environment)
        intro tail tailValue
        simp only [interpret] at tailValue ⊢
        exact .ok (.cons headValue tailValue)
      | none _ => simp only [erase, evaluate, interpret]; exact .ok .none
      | some _ valueTyped =>
        simp only [erase, evaluate]
        apply OutcomeTyped.bind (exprSafe assignment valueTyped environment)
        intro value typed
        simp only [interpret]
        exact .ok (.some typed)
      | matchList targetTyped emptyTyped fullTyped =>
        simp only [erase, evaluate]
        apply OutcomeTyped.bind (exprSafe assignment targetTyped environment)
        intro value typed
        simp only [interpret] at typed
        cases typed with
        | nil => exact exprSafe assignment emptyTyped environment
        | cons head tail =>
          apply exprSafe assignment fullTyped
          simpa only [interpretTypes, interpret] using ValuesTyped.cons head (.cons tail environment)
      | matchOption targetTyped emptyTyped fullTyped =>
        simp only [erase, evaluate]
        apply OutcomeTyped.bind (exprSafe assignment targetTyped environment)
        intro value typed
        simp only [interpret] at typed
        cases typed with
        | none => exact exprSafe assignment emptyTyped environment
        | some value =>
          apply exprSafe assignment fullTyped
          simpa only [interpretTypes] using ValuesTyped.cons value environment
    · intro count context expressions types assignment env typing environment
      cases typing with
      | nil => simp only [eraseList, evaluateArgs, interpretTypes]; exact .ok .nil
      | cons headTyped tailTyped =>
        simp only [eraseList, evaluateArgs]
        apply OutcomeTyped.bind (exprSafe assignment headTyped environment)
        intro head typed
        apply OutcomeTyped.bind (argsSafe assignment tailTyped environment)
        intro tail types
        simp only [interpretTypes]
        exact .ok (.cons typed types)
    · intro count context expressions previous result assignment env value typing previousTyped environment
      cases typing with
      | nil => exact .ok previousTyped
      | cons headTyped tailTyped =>
        simp only [eraseList, evaluateSequence]
        apply OutcomeTyped.bind (exprSafe assignment headTyped environment)
        intro head typed
        exact sequenceSafe assignment tailTyped typed environment

theorem evaluation_preserves_type (wellTyped : ProgramTyped globals definitions)
    (typing : HasType globals count context expression type)
    (environment : ValuesTyped globals env (interpretTypes assignment context))
    (success : evaluate (eraseDefinitions definitions) fuel env (erase expression) = .ok value) :
    ValueTyped globals value (interpret assignment type) := by
  have safe := (evaluator_type_safe wellTyped fuel).1 assignment typing environment
  rw [success] at safe
  cases safe with
  | ok typed => exact typed

theorem evaluation_no_type_error (wellTyped : ProgramTyped globals definitions)
    (typing : HasType globals count context expression type)
    (environment : ValuesTyped globals env (interpretTypes assignment context))
    (failure : evaluate (eraseDefinitions definitions) fuel env (erase expression) = .error fault) :
    fault = .outOfFuel := by
  have safe := (evaluator_type_safe wellTyped fuel).1 assignment typing environment
  rw [failure] at safe
  cases safe
  rfl

end NLisp.PolyIR

namespace NLisp.Surface

theorem elaborate_expression (success : elaborate fuel globals count context expression type = some checked) :
    checked.expression = expression := by
  unfold elaborate at success
  cases inferred : infer fuel globals count context expression with
  | none => simp [inferred, bind, Option.bind] at success
  | some result =>
    cases expected : result.expect type with
    | none => simp [inferred, expected, bind, Option.bind] at success
    | some proof =>
      simp only [inferred, expected, bind, Option.bind, pure] at success
      have same := Option.some.inj success
      cases same
      rfl

theorem elaborate_typed (success : (elaborate fuel globals count context expression type).isSome = true) :
    HasType globals count context expression type := by
  cases result : elaborate fuel globals count context expression type with
  | none => simp [result] at success
  | some checked =>
    simpa [elaborate_expression result] using checked.typing

theorem elaborateDefinition_expression
    (success : elaborateDefinition fuel globals signature body = some checked) : checked.body.expression = body := by
  unfold elaborateDefinition at success
  cases ps : checkTypesWF fuel signature.typeArity signature.parameters with
  | none => simp [ps, bind, Option.bind] at success
  | some parameters =>
    cases rt : checkWF fuel signature.typeArity signature.result with
    | none => simp [ps, rt, bind, Option.bind] at success
    | some result =>
      cases bd : elaborate fuel globals signature.typeArity signature.parameters body signature.result with
      | none => simp [ps, rt, bd, bind, Option.bind] at success
      | some typed =>
        simp only [ps, rt, bd, bind, Option.bind, pure] at success
        have equal := Option.some.inj success
        cases equal
        exact elaborate_expression bd

inductive BodiesHaveTypes (globals : List Signature) : List Signature → List Expr → Prop where
  | nil : BodiesHaveTypes globals [] []
  | cons : signature.wellFormed → HasType globals signature.typeArity signature.parameters body signature.result →
      BodiesHaveTypes globals signatures bodies → BodiesHaveTypes globals (signature :: signatures) (body :: bodies)

theorem BodiesHaveTypes.length_eq (typed : BodiesHaveTypes globals signatures bodies) :
    signatures.length = bodies.length := by
  induction typed <;> simp_all

theorem BodiesHaveTypes.signature_valid_at
    (typed : BodiesHaveTypes globals signatures bodies) (index : Nat)
    (signature : Signature) (found : signatures[index]? = some signature) :
    signature.wellFormed := by
  induction typed generalizing index with
  | nil => simp [getElem?_def, Nat.not_lt_zero] at found
  | @cons head signatures bodies body valid bodyTyped rest ih =>
      cases index with
      | zero =>
          have same : body = signature := by simpa [getElem?_def] using found
          cases same
          exact valid
      | succ index =>
          exact ih index (by simpa [getElem?_def, Nat.succ_lt_succ_iff] using found)

theorem elaborateDefinitions_typed
    (success : (elaborateDefinitions fuel globals signatures bodies).isSome = true) :
    BodiesHaveTypes globals signatures bodies := by
  induction signatures generalizing bodies with
  | nil =>
    cases bodies with
    | nil => exact .nil
    | cons head tail => simp [elaborateDefinitions] at success
  | cons signature signatures ih =>
    cases bodies with
    | nil => simp [elaborateDefinitions] at success
    | cons body bodies =>
      cases head : elaborateDefinition fuel globals signature body with
      | none => simp [elaborateDefinitions, head, bind, Option.bind] at success
      | some checked =>
        cases tail : elaborateDefinitions fuel globals signatures bodies with
        | none => simp [elaborateDefinitions, head, tail, bind, Option.bind] at success
        | some rest =>
          apply BodiesHaveTypes.cons checked.signature_valid
          · simpa [elaborateDefinition_expression head] using checked.body.typing
          · exact ih (by simp [tail])

theorem elaborateProgram_typed
    (success : (elaborateProgram fuel signatures bodies).isSome = true) :
    BodiesHaveTypes signatures signatures bodies := by
  unfold elaborateProgram at success
  cases result : elaborateDefinitions fuel signatures signatures bodies with
  | none => simp [result, bind, Option.bind] at success
  | some definitions => exact elaborateDefinitions_typed (fuel := fuel) (by simp [result])

theorem BodiesHaveTypes.lookup {index : Nat} {signature : Signature}
    (typed : BodiesHaveTypes globals signatures bodies) (found : signatures[index]? = some signature) :
    ∃ body, (signatures.zip bodies)[index]? = some (signature, body) ∧
      HasType globals signature.typeArity signature.parameters body signature.result := by
  induction typed generalizing index with
  | nil => simp [getElem?_def, Nat.not_lt_zero] at found
  | @cons head signatures bodies sig _valid bodyTyped _rest ih =>
    cases index with
    | zero =>
      have same : sig = signature := by simpa [getElem?_def] using found
      subst signature
      refine ⟨head, ?_, bodyTyped⟩
      simp [getElem?_def]
    | succ index =>
      obtain ⟨body, entry, type⟩ := ih (index := index)
        (by simpa [getElem?_def, Nat.succ_lt_succ_iff] using found)
      exact ⟨body, by simpa [getElem?_def, Nat.succ_lt_succ_iff] using entry, type⟩

theorem BodiesHaveTypes.lookupDefinition {index : Nat} {signature : Signature}
    {body : Expr} (typed : BodiesHaveTypes globals signatures bodies)
    (found : (signatures.zip bodies)[index]? = some (signature, body)) :
    signature.wellFormed ∧ HasType globals signature.typeArity signature.parameters body signature.result := by
  induction typed generalizing index with
  | nil =>
      have impossible : ¬ index < ([] : List (Signature × Expr)).length := by simp
      simp only [getElem?_def, dif_neg impossible] at found
      cases found
  | @cons head signatures bodies sig headValid headTyped tailTyped ih =>
      cases index with
      | zero =>
          have same : (sig, head) = (signature, body) := by
            simpa [getElem?_def] using found
          cases same
          exact ⟨headValid, headTyped⟩
      | succ index =>
          have tailFound : (signatures.zip bodies)[index]? = some (signature, body) := by
            simpa [getElem?_def, Nat.succ_lt_succ_iff] using found
          exact ih tailFound

theorem elaborateProgram_programTyped
    (success : (elaborateProgram fuel signatures bodies).isSome = true) :
    PolyIR.ProgramTyped signatures (signatures.zip bodies) :=
  ⟨fun _ _ found => (elaborateProgram_typed success).lookup found⟩

end NLisp.Surface
