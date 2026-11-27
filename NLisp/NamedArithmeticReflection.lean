import NLisp.NamedDecoder
import NLisp.SemanticDeterminism

namespace NLisp.Named

/-- Expression forms whose finite lowered evaluations can be reflected from
the corresponding subexpression lemmas. -/
inductive ArithmeticFragment : Expr → Prop where
  | var (id : Nat) : ArithmeticFragment (.var id)
  | global (index : Nat) : ArithmeticFragment (.global index)
  | bool (value : Bool) : ArithmeticFragment (.bool value)
  | int (value : Int) : ArithmeticFragment (.int value)
  | float (value : Float) : ArithmeticFragment (.float value)
  | string (value : String) : ArithmeticFragment (.string value)
  | character (value : Char) : ArithmeticFragment (.character value)
  | unit : ArithmeticFragment .unit
  | lam (parameters : List Nat) (body : Expr) :
      ArithmeticFragment (.lam parameters body)
  | letOne (id : Nat) (initializer body : Expr) :
      ArithmeticFragment initializer → ArithmeticFragment body →
      ArithmeticFragment (.letMany [id] [initializer] body)
  | letTwo (id₁ id₂ : Nat) (initializer₁ initializer₂ body : Expr) :
      ArithmeticFragment initializer₁ → ArithmeticFragment initializer₂ →
      ArithmeticFragment body →
      ArithmeticFragment (.letMany [id₁, id₂] [initializer₁, initializer₂] body)
  | beginOne (expression : Expr) : ArithmeticFragment expression →
      ArithmeticFragment (.begin expression [])
  | beginTwo (first second : Expr) : ArithmeticFragment first →
      ArithmeticFragment second → ArithmeticFragment (.begin first [second])
  | nil : ArithmeticFragment .nil
  | none : ArithmeticFragment .none
  | some (value : Expr) : ArithmeticFragment value → ArithmeticFragment (.some value)
  | cons (head tail : Expr) : ArithmeticFragment head → ArithmeticFragment tail →
      ArithmeticFragment (.cons head tail)
  | ite (condition yes no : Expr) : ArithmeticFragment condition → ArithmeticFragment yes →
      ArithmeticFragment no → ArithmeticFragment (.ite condition yes no)
  | matchOption (target empty : Expr) (binder : Nat) (full : Expr) :
      ArithmeticFragment target → ArithmeticFragment empty → ArithmeticFragment full →
      ArithmeticFragment (.matchOption target empty binder full)
  | matchList (target empty : Expr) (headBinder tailBinder : Nat) (full : Expr) :
      ArithmeticFragment target → ArithmeticFragment empty → ArithmeticFragment full →
      ArithmeticFragment (.matchList target empty headBinder tailBinder full)
  | add (left right : Expr) : ArithmeticFragment left → ArithmeticFragment right →
      ArithmeticFragment (.add left right)
  | sub (left right : Expr) : ArithmeticFragment left → ArithmeticFragment right →
      ArithmeticFragment (.sub left right)
  | mul (left right : Expr) : ArithmeticFragment left → ArithmeticFragment right →
      ArithmeticFragment (.mul left right)
  | le (left right : Expr) : ArithmeticFragment left → ArithmeticFragment right →
      ArithmeticFragment (.le left right)
  | intEq (left right : Expr) : ArithmeticFragment left → ArithmeticFragment right →
      ArithmeticFragment (.intEq left right)
  | floatBin (op : Surface.FloatBinOp) (left right : Expr) :
      ArithmeticFragment left → ArithmeticFragment right →
      ArithmeticFragment (.floatBin op left right)
  | appLambdaZero (parameters : List Nat) (body : Expr) :
      ArithmeticFragment body →
      ArithmeticFragment (.app (.lam parameters body) [])
  | appLambdaOne (parameters : List Nat) (body argument : Expr) :
      ArithmeticFragment body → ArithmeticFragment argument →
      ArithmeticFragment (.app (.lam parameters body) [argument])
  | appLambdaTwo (parameters : List Nat) (body first second : Expr) :
      ArithmeticFragment body → ArithmeticFragment first → ArithmeticFragment second →
      ArithmeticFragment (.app (.lam parameters body) [first, second])
  | appLambdaThree (parameters : List Nat) (body first second third : Expr) :
      ArithmeticFragment body → ArithmeticFragment first → ArithmeticFragment second →
      ArithmeticFragment third →
      ArithmeticFragment (.app (.lam parameters body) [first, second, third])

inductive ArithmeticFragmentList : List Expr → Prop where
  | nil : ArithmeticFragmentList []
  | cons (head : Expr) (tail : List Expr) : ArithmeticFragment head →
      ArithmeticFragmentList tail → ArithmeticFragmentList (head :: tail)

/-! An arbitrary-length initializer list with a fragment proof for each row. -/
inductive ArithmeticFragmentRows : List Expr → Prop where
  | nil : ArithmeticFragmentRows []
  | cons (head : Expr) (tail : List Expr) : ArithmeticFragment head →
      ArithmeticFragmentRows tail → ArithmeticFragmentRows (head :: tail)

/-- Lambda applications with an arbitrary number of arguments, whose body
and arguments belong to the finite reflection fragment. -/
inductive LambdaApplicationFragment : Expr → Prop where
  | apply (parameters : List Nat) (body : Expr) (arguments : List Expr) :
      ArithmeticFragment body → ArithmeticFragmentList arguments →
      LambdaApplicationFragment (.app (.lam parameters body) arguments)

/-- Explicit-lambda and resolved-global applications with arbitrary argument
counts. The target body and each argument carry finite reflection evidence. -/
inductive ApplicationFragment (program : Definitions) : Expr → Prop where
  | lambda (parameters : List Nat) (body : Expr) (arguments : List Expr) :
      ArithmeticFragment body → ArithmeticFragmentList arguments →
      ApplicationFragment program (.app (.lam parameters body) arguments)
  | global (index : Nat) (parameters : List Nat) (body : Expr)
      (arguments : List Expr) :
      program[index]? = some (parameters, body) →
      ArithmeticFragment body → ArithmeticFragmentList arguments →
      ApplicationFragment program (.app (.global index) arguments)

/-- A `begin` expression with any finite number of expressions. -/
inductive BeginFragment : Expr → Prop where
  | sequence (first : Expr) (rest : List Expr) :
      ArithmeticFragment first → ArithmeticFragmentList rest →
      BeginFragment (.begin first rest)

/-- A parallel let with any finite number of initializers. The binder and
initializer counts are required to agree because lowering erases binder IDs. -/
inductive LetManyFragment : Expr → Prop where
  | bindings (ids : List Nat) (initializers : List Expr) (body : Expr) :
      ArithmeticFragmentList initializers → ids.length = initializers.length →
      ArithmeticFragment body → LetManyFragment (.letMany ids initializers body)

/-- Every finite PolyIR evaluation in this syntax fragment has a Named
evaluation with the same lowered value, for arbitrary programs and
environments. -/
theorem arithmeticFragment_evaluation_reflected (program : Definitions)
    (expression : Expr) (fragment : ArithmeticFragment expression) :
    ∀ (env : Environment) (value : PolyIR.Value),
      PolyIR.Evaluates (lowerDefinitions program) (lowerEnv env)
        (lower (identities env) expression) value →
      ∃ sourceValue, Evaluates program env expression sourceValue ∧
        lowerValue sourceValue = value := by
  induction fragment with
  | var id =>
      intro env value evaluated
      exact variable_evaluation_reflected program env id value evaluated
  | global index =>
      intro env value evaluated
      cases evaluated with
      | global found =>
          exact ⟨.global index, global_evaluation_reflected program env index
            (.global found), by simp [lowerValue]⟩
  | bool b =>
      intro env value evaluated
      exact boolean_evaluation_reflected program env b value evaluated
  | int n =>
      intro env value evaluated
      exact integer_evaluation_reflected program env n value evaluated
  | float x =>
      intro env value evaluated
      exact float_evaluation_reflected program env x value evaluated
  | string s =>
      intro env value evaluated
      exact string_evaluation_reflected program env s value evaluated
  | character c =>
      intro env value evaluated
      exact character_evaluation_reflected program env c value evaluated
  | unit =>
      intro env value evaluated
      exact unit_evaluation_reflected program env value evaluated
  | lam parameters body =>
      intro env value evaluated
      exact lambda_evaluation_reflected program env parameters body value evaluated
  | letOne id initializer body _ _ initializerIH bodyIH =>
      intro env value evaluated
      exact letMany_evaluation_reflected program env [id] [initializer] body (by simp)
        (fun {irValues} argsEval => by
          cases argsEval with
          | cons firstEval restEval =>
              cases restEval
              obtain ⟨sourceValue, sourceEval, sourceLower⟩ :=
                initializerIH env _ firstEval
              exact ⟨[sourceValue], .cons sourceEval .nil,
                by simp [lowerValues, sourceLower]⟩)
        (fun sourceValues irValues sourceLength valuesLower {result} bodyEval => by
          cases sourceValues with
          | nil => simp at sourceLength
          | cons sourceValue sourceTail =>
              cases sourceTail with
              | nil =>
                  have envEq : lowerEnv ((id, sourceValue) :: env) =
                      irValues ++ lowerEnv env := by
                    have irValuesEq : irValues = [lowerValue sourceValue] := by
                      simpa [lowerValues] using valuesLower.symm
                    simp [lowerEnv, irValuesEq]
                  have localsEq : identities ((id, sourceValue) :: env) =
                      [id] ++ identities env := by simp [identities]
                  have bodyTermEq : lower (identities ((id, sourceValue) :: env)) body =
                      lower ([id] ++ identities env) body := by rw [localsEq]
                  have reflected := bodyIH ((id, sourceValue) :: env) result (by
                    rw [envEq, bodyTermEq]
                    exact bodyEval)
                  exact reflected
              | cons _ _ => simp at sourceLength)
        value evaluated
  | letTwo id₁ id₂ initializer₁ initializer₂ body _ _ _ firstIH secondIH bodyIH =>
      intro env value evaluated
      exact letMany_evaluation_reflected program env [id₁, id₂]
        [initializer₁, initializer₂] body (by simp)
        (fun {irValues} argsEval => by
          cases argsEval with
          | cons firstEval restEval =>
              cases restEval with
              | cons secondEval finalEval =>
                  cases finalEval
                  obtain ⟨firstValue, firstSourceEval, firstLower⟩ :=
                    firstIH env _ firstEval
                  obtain ⟨secondValue, secondSourceEval, secondLower⟩ :=
                    secondIH env _ secondEval
                  exact ⟨[firstValue, secondValue],
                    .cons firstSourceEval (.cons secondSourceEval .nil), by
                      simp [lowerValues, firstLower, secondLower]⟩)
        (fun sourceValues irValues sourceLength valuesLower {result} bodyEval => by
          have sourceCount : sourceValues.length = 2 := by simpa using sourceLength
          cases sourceValues with
          | nil => simp at sourceLength
          | cons value₁ tail₁ =>
              cases tail₁ with
              | nil => simp at sourceLength
              | cons value₂ tail₂ =>
                  cases tail₂ with
                  | nil =>
                      have envEq : lowerEnv
                          (bind [id₁, id₂] [value₁, value₂] ++ env) =
                          irValues ++ lowerEnv env := by
                        have irValuesEq : irValues =
                            [lowerValue value₁, lowerValue value₂] := by
                          simpa [lowerValues] using valuesLower.symm
                        rw [lowerEnv_bind_append _ _ _ (by simp)]
                        simp [lowerValues, irValuesEq]
                      have localsEq : identities
                          (bind [id₁, id₂] [value₁, value₂] ++ env) =
                          [id₁, id₂] ++ identities env :=
                        identities_bind_append _ _ _ (by simp)
                      have bodyTermEq :
                          lower (identities
                            (bind [id₁, id₂] [value₁, value₂] ++ env)) body =
                          lower ([id₁, id₂] ++ identities env) body := by
                        rw [localsEq]
                      exact bodyIH
                        (bind [id₁, id₂] [value₁, value₂] ++ env) result (by
                          rw [envEq, bodyTermEq]
                          exact bodyEval)
                  | cons _ _ => simp at sourceCount)
        value evaluated
  | beginOne expression _ expressionIH =>
      intro env value evaluated
      rw [lower_eq] at evaluated
      cases evaluated with
      | begin firstEval restEval =>
          cases restEval with
          | nil =>
              obtain ⟨sourceValue, sourceEval, sourceLower⟩ :=
                expressionIH env _ firstEval
              exact ⟨sourceValue, .begin sourceEval .nil, sourceLower⟩
  | beginTwo first second _ _ firstIH secondIH =>
      intro env value evaluated
      rw [lower_eq] at evaluated
      cases evaluated with
      | begin firstEval restEval =>
          cases restEval with
          | cons secondEval tailEval =>
              cases tailEval with
              | nil =>
                  obtain ⟨sourceFirst, firstSourceEval, _⟩ :=
                    firstIH env _ firstEval
                  obtain ⟨sourceSecond, secondSourceEval, secondLower⟩ :=
                    secondIH env _ secondEval
                  exact ⟨sourceSecond,
                    .begin firstSourceEval (.cons secondSourceEval .nil), secondLower⟩
  | nil =>
      intro env value evaluated
      exact nil_evaluation_reflected program env value evaluated
  | none =>
      intro env value evaluated
      exact none_evaluation_reflected program env value evaluated
  | some inner _ innerIH =>
      intro env value evaluated
      exact some_evaluation_reflected program env inner
        (fun {innerValue} innerEval => innerIH env innerValue innerEval) value evaluated
  | cons head tail _ _ headIH tailIH =>
      intro env value evaluated
      exact cons_evaluation_reflected program env head tail
        (fun {headValue} headEval => headIH env headValue headEval)
        (fun {tailValue} tailEval => tailIH env tailValue tailEval) value evaluated
  | ite condition yes no _ _ _ conditionIH yesIH noIH =>
      intro env value evaluated
      exact ite_evaluation_reflected program env condition yes no
        (fun {conditionValue} conditionEval => conditionIH env conditionValue conditionEval)
        (fun {yesValue} yesEval => yesIH env yesValue yesEval)
        (fun {noValue} noEval => noIH env noValue noEval) value evaluated
  | matchOption target empty binder full _ _ _ targetIH emptyIH fullIH =>
      intro env value evaluated
      exact matchOption_evaluation_reflected program env target empty binder full
        (fun {targetValue} targetEval => targetIH env targetValue targetEval)
        (fun {emptyValue} emptyEval => emptyIH env emptyValue emptyEval)
        (fun sourceItem irItem sourceLower {bodyValue} bodyEval => by
          have reflected := fullIH ((binder, sourceItem) :: env) bodyValue (by
            simpa [identities, lowerEnv, sourceLower] using bodyEval)
          exact reflected)
        value evaluated
  | matchList target empty headBinder tailBinder full _ _ _ targetIH emptyIH fullIH =>
      intro env value evaluated
      exact matchList_evaluation_reflected program env target empty headBinder tailBinder full
        (fun {targetValue} targetEval => targetIH env targetValue targetEval)
        (fun {emptyValue} emptyEval => emptyIH env emptyValue emptyEval)
        (fun sourceHead sourceTail irHead irTail headLower tailLower {bodyValue} bodyEval => by
          have reflected := fullIH
            ((headBinder, sourceHead) :: (tailBinder, sourceTail) :: env) bodyValue (by
              simpa [identities, lowerEnv, headLower, tailLower] using bodyEval)
          exact reflected)
        value evaluated
  | add left right _ _ leftIH rightIH =>
      intro env value evaluated
      exact add_evaluation_reflected program env left right
        (fun {leftValue} leftEval => leftIH env leftValue leftEval)
        (fun {rightValue} rightEval => rightIH env rightValue rightEval) value evaluated
  | sub left right _ _ leftIH rightIH =>
      intro env value evaluated
      exact sub_evaluation_reflected program env left right
        (fun {leftValue} leftEval => leftIH env leftValue leftEval)
        (fun {rightValue} rightEval => rightIH env rightValue rightEval) value evaluated
  | mul left right _ _ leftIH rightIH =>
      intro env value evaluated
      exact mul_evaluation_reflected program env left right
        (fun {leftValue} leftEval => leftIH env leftValue leftEval)
        (fun {rightValue} rightEval => rightIH env rightValue rightEval) value evaluated
  | le left right _ _ leftIH rightIH =>
      intro env value evaluated
      exact le_evaluation_reflected program env left right
        (fun {leftValue} leftEval => leftIH env leftValue leftEval)
        (fun {rightValue} rightEval => rightIH env rightValue rightEval) value evaluated
  | intEq left right _ _ leftIH rightIH =>
      intro env value evaluated
      exact intEq_evaluation_reflected program env left right
        (fun {leftValue} leftEval => leftIH env leftValue leftEval)
        (fun {rightValue} rightEval => rightIH env rightValue rightEval) value evaluated
  | floatBin op left right _ _ leftIH rightIH =>
      intro env value evaluated
      exact floatBin_evaluation_reflected program env op left right
        (fun {leftValue} leftEval => leftIH env leftValue leftEval)
        (fun {rightValue} rightEval => rightIH env rightValue rightEval) value evaluated
  | appLambdaOne parameters body argument _ _ bodyIH argumentIH =>
      intro env value evaluated
      rw [lower_eq] at evaluated
      cases evaluated with
      | appClosure functionEval argumentsEval argumentsArity bodyEval =>
          rw [lower_eq] at functionEval
          cases functionEval with
          | lam =>
              rw [lowerMany_eq] at argumentsEval
              cases argumentsEval with
              | cons argumentEval tailEval =>
                  cases tailEval
                  obtain ⟨sourceArgument, sourceArgumentEval, argumentLowered⟩ :=
                    argumentIH env _ argumentEval
                  have sourceArity : [sourceArgument].length = parameters.length := by
                    simpa [lowerValues] using argumentsArity
                  have environmentEq :
                      lowerEnv (bind parameters [sourceArgument] ++ env) =
                        [lowerValue sourceArgument] ++ lowerEnv env :=
                    lowerEnv_bind_append parameters [sourceArgument] env sourceArity
                  have localsEq :
                      identities (bind parameters [sourceArgument] ++ env) =
                        parameters ++ identities env :=
                    identities_bind_append parameters [sourceArgument] env sourceArity
                  have bodyTermEq :
                      lower (identities (bind parameters [sourceArgument] ++ env)) body =
                        lower (parameters ++ identities env) body := by rw [localsEq]
                  have alignedBody : PolyIR.Evaluates (lowerDefinitions program)
                      (lowerEnv (bind parameters [sourceArgument] ++ env))
                      (lower (identities (bind parameters [sourceArgument] ++ env)) body) value := by
                    rw [environmentEq, argumentLowered, bodyTermEq]
                    exact bodyEval
                  obtain ⟨sourceResult, sourceBodyEval, resultLowered⟩ :=
                    bodyIH (bind parameters [sourceArgument] ++ env) value alignedBody
                  exact ⟨sourceResult,
                    .appClosure .lam (.cons sourceArgumentEval .nil) sourceArity sourceBodyEval,
                    resultLowered⟩
      | appGlobal functionEval _ _ _ _ =>
          rw [lower_eq] at functionEval
          cases functionEval

  | appLambdaTwo parameters body first second _ _ _ bodyIH firstIH secondIH =>
      intro env value evaluated
      rw [lower_eq] at evaluated
      cases evaluated with
      | appClosure functionEval argumentsEval argumentsArity bodyEval =>
          rw [lower_eq] at functionEval
          cases functionEval with
          | lam =>
              rw [lowerMany_eq] at argumentsEval
              cases argumentsEval with
              | cons firstEval restEval =>
                  rename_i irFirst irRest
                  cases restEval with
                  | cons secondEval tailEval =>
                      rename_i irSecond irTail
                      cases tailEval
                      obtain ⟨sourceFirst, sourceFirstEval, firstLowered⟩ :=
                        firstIH env _ firstEval
                      obtain ⟨sourceSecond, sourceSecondEval, secondLowered⟩ :=
                        secondIH env _ secondEval
                      have argumentsLowered :
                          lowerValues [sourceFirst, sourceSecond] = [irFirst, irSecond] := by
                        simp [lowerValues, firstLowered, secondLowered]
                      have sourceArity : [sourceFirst, sourceSecond].length = parameters.length := by
                        calc
                          [sourceFirst, sourceSecond].length =
                              (lowerValues [sourceFirst, sourceSecond]).length := by simp [lowerValues]
                          _ = [irFirst, irSecond].length := congrArg List.length argumentsLowered
                          _ = parameters.length := by simpa using argumentsArity
                      have environmentEq :
                          lowerEnv (bind parameters [sourceFirst, sourceSecond] ++ env) =
                            lowerValues [sourceFirst, sourceSecond] ++ lowerEnv env :=
                        lowerEnv_bind_append parameters [sourceFirst, sourceSecond] env sourceArity
                      have localsEq :
                          identities (bind parameters [sourceFirst, sourceSecond] ++ env) =
                            parameters ++ identities env :=
                        identities_bind_append parameters [sourceFirst, sourceSecond] env sourceArity
                      have bodyTermEq :
                          lower (identities (bind parameters [sourceFirst, sourceSecond] ++ env)) body =
                            lower (parameters ++ identities env) body := by rw [localsEq]
                      have alignedBody : PolyIR.Evaluates (lowerDefinitions program)
                          (lowerEnv (bind parameters [sourceFirst, sourceSecond] ++ env))
                          (lower (identities (bind parameters [sourceFirst, sourceSecond] ++ env)) body) value := by
                        rw [environmentEq, bodyTermEq]
                        simpa [lowerValues, firstLowered, secondLowered] using bodyEval
                      obtain ⟨sourceResult, sourceBodyEval, resultLowered⟩ :=
                        bodyIH (bind parameters [sourceFirst, sourceSecond] ++ env) value alignedBody
                      exact ⟨sourceResult,
                        .appClosure .lam
                          (.cons sourceFirstEval (.cons sourceSecondEval .nil)) sourceArity sourceBodyEval,
                        resultLowered⟩
      | appGlobal functionEval _ _ _ _ =>
          rw [lower_eq] at functionEval
          cases functionEval

  | appLambdaThree parameters body first second third _ _ _ _
      bodyIH firstIH secondIH thirdIH =>
      intro env value evaluated
      rw [lower_eq] at evaluated
      cases evaluated with
      | appClosure functionEval argumentsEval argumentsArity bodyEval =>
          rw [lower_eq] at functionEval
          cases functionEval with
          | lam =>
              rw [lowerMany_eq] at argumentsEval
              cases argumentsEval with
              | cons firstEval restEval =>
                  rename_i irFirst irRest
                  cases restEval with
                  | cons secondEval restEval =>
                      rename_i irSecond irRest
                      cases restEval with
                      | cons thirdEval finalEval =>
                          rename_i irThird irFinal
                          cases finalEval
                          obtain ⟨sourceFirst, sourceFirstEval, firstLowered⟩ :=
                            firstIH env _ firstEval
                          obtain ⟨sourceSecond, sourceSecondEval, secondLowered⟩ :=
                            secondIH env _ secondEval
                          obtain ⟨sourceThird, sourceThirdEval, thirdLowered⟩ :=
                            thirdIH env _ thirdEval
                          have argumentsLowered : lowerValues
                              [sourceFirst, sourceSecond, sourceThird] =
                              [irFirst, irSecond, irThird] := by
                            simp [lowerValues, firstLowered, secondLowered, thirdLowered]
                          have sourceArity :
                              [sourceFirst, sourceSecond, sourceThird].length = parameters.length := by
                            calc
                              [sourceFirst, sourceSecond, sourceThird].length =
                                  (lowerValues [sourceFirst, sourceSecond, sourceThird]).length := by
                                    simp [lowerValues]
                              _ = [irFirst, irSecond, irThird].length :=
                                congrArg List.length argumentsLowered
                              _ = parameters.length := by
                                simpa using argumentsArity
                          have environmentEq :
                              lowerEnv (bind parameters [sourceFirst, sourceSecond, sourceThird] ++ env) =
                                lowerValues [sourceFirst, sourceSecond, sourceThird] ++ lowerEnv env :=
                            lowerEnv_bind_append parameters
                              [sourceFirst, sourceSecond, sourceThird] env sourceArity
                          have bodyLocalsEq :
                              identities (bind parameters [sourceFirst, sourceSecond, sourceThird] ++ env) =
                                parameters ++ identities env :=
                            identities_bind_append parameters
                              [sourceFirst, sourceSecond, sourceThird] env sourceArity
                          have bodyTermEq :
                              lower (identities
                                (bind parameters [sourceFirst, sourceSecond, sourceThird] ++ env)) body =
                                lower (parameters ++ identities env) body := by
                            rw [bodyLocalsEq]
                          have alignedBody : PolyIR.Evaluates (lowerDefinitions program)
                              (lowerEnv
                                (bind parameters [sourceFirst, sourceSecond, sourceThird] ++ env))
                              (lower (identities
                                (bind parameters [sourceFirst, sourceSecond, sourceThird] ++ env)) body)
                              value := by
                            rw [environmentEq, bodyTermEq, argumentsLowered]
                            exact bodyEval
                          obtain ⟨sourceResult, sourceBodyEval, resultLowered⟩ :=
                            bodyIH
                              (bind parameters [sourceFirst, sourceSecond, sourceThird] ++ env)
                              value alignedBody
                          exact ⟨sourceResult,
                            .appClosure .lam
                              (.cons sourceFirstEval
                                (.cons sourceSecondEval (.cons sourceThirdEval .nil)))
                              sourceArity sourceBodyEval,
                            resultLowered⟩
      | appGlobal functionEval _ _ _ _ =>
          rw [lower_eq] at functionEval
          cases functionEval

  | appLambdaZero parameters body _ bodyIH =>
      intro env value evaluated
      rw [lower_eq] at evaluated
      cases evaluated with
      | appClosure functionEval argumentsEval argumentsArity bodyEval =>
          rw [lower_eq] at functionEval
          cases functionEval with
          | lam =>
              cases argumentsEval
              have parametersEmpty : parameters = [] :=
                List.length_eq_zero.mp (by simpa using argumentsArity.symm)
              subst parameters
              have alignedBody : PolyIR.Evaluates (lowerDefinitions program)
                  (lowerEnv env) (lower (identities env) body) value := by
                simpa only [List.nil_append] using bodyEval
              obtain ⟨sourceResult, sourceBodyEval, resultLowered⟩ :=
                bodyIH env value alignedBody
              exact ⟨sourceResult,
                .appClosure .lam .nil (by simp) sourceBodyEval, resultLowered⟩
      | appGlobal functionEval _ _ _ _ =>
          rw [lower_eq] at functionEval
          cases functionEval

/- Finite termination is equivalent in both directions on the fragment: the
forward direction uses the structural erasure simulation, and the reverse
direction uses the evaluation-reflection theorem above. -/
theorem arithmeticFragment_termination_preserved_and_reflected
    (program : Definitions) (environment : Environment) (expression : Expr)
    (fragment : ArithmeticFragment expression) :
    SourceTerminates program environment expression ↔
      LoweredTerminates program environment expression := by
  constructor
  · rintro ⟨sourceValue, evaluated⟩
    exact ⟨lowerValue sourceValue, evaluation_preserved evaluated⟩
  · rintro ⟨value, evaluated⟩
    obtain ⟨sourceValue, sourceEvaluates, _⟩ :=
      arithmeticFragment_evaluation_reflected program expression fragment
        environment value evaluated
    exact ⟨sourceValue, sourceEvaluates⟩

/-- Since divergence is absence of a finite big-step result, the termination
equivalence above gives exact divergence preservation and reflection on the
same fragment. -/
theorem arithmeticFragment_divergence_preserved_and_reflected
    (program : Definitions) (environment : Environment) (expression : Expr)
    (fragment : ArithmeticFragment expression) :
    SourceDiverges program environment expression ↔
      LoweredDiverges program environment expression := by
  exact not_congr
    (arithmeticFragment_termination_preserved_and_reflected
      program environment expression fragment)

/-- For bodies actually obtained from a successful source decode, the
arithmetic-fragment reflection theorem composes with the decoder's program
scope invariant. In particular, the reflected result remains safe to use as a
closure environment in a later application proof. -/
theorem decodedBody_arithmetic_evaluation_reflected
    (fuel : Nat) (forms : List CBindingWalk.Node) (definitions : Definitions)
    (decoded : decodeProgram fuel forms = some definitions)
    (index : Nat) (parameters : List Nat) (body : Expr)
    (found : definitions[index]? = some (parameters, body))
    (fragment : ArithmeticFragment body)
    (environment : Environment) (value : PolyIR.Value)
    (environmentScoped : environmentWellScoped environment)
    (evaluated : PolyIR.Evaluates (lowerDefinitions definitions) (lowerEnv environment)
      (lower (identities environment) body) value) :
    ∃ sourceValue, Evaluates definitions environment body sourceValue ∧
      lowerValue sourceValue = value ∧ valueWellScoped sourceValue := by
  obtain ⟨sourceValue, sourceEvaluates, lowers⟩ :=
    arithmeticFragment_evaluation_reflected definitions body fragment
      environment value evaluated
  have sourceScoped := decodeProgram_body_evaluation_preserves_valueWellScoped
    fuel forms definitions decoded index parameters body found environment sourceValue
    environmentScoped sourceEvaluates
  exact ⟨sourceValue, sourceEvaluates, lowers, sourceScoped⟩

/-- The same reflection and closure-scope guarantee applies to an initializer
selected from a successfully decoded mixed top-level program. -/
theorem decodedInitializer_arithmetic_evaluation_reflected
    (fuel : Nat) (forms : List CBindingWalk.Node) (definitions : Definitions)
    (slotTypes : List Surface.Ty) (initializers : List Expr)
    (decoded : decodeTopLevelProgram fuel forms =
      some (definitions, slotTypes, initializers))
    (expression : Expr) (member : expression ∈ initializers)
    (fragment : ArithmeticFragment expression)
    (environment : Environment) (value : PolyIR.Value)
    (environmentScoped : environmentWellScoped environment)
    (evaluated : PolyIR.Evaluates (lowerDefinitions definitions) (lowerEnv environment)
      (lower (identities environment) expression) value) :
    ∃ sourceValue, Evaluates definitions environment expression sourceValue ∧
      lowerValue sourceValue = value ∧ valueWellScoped sourceValue := by
  obtain ⟨sourceValue, sourceEvaluates, lowers⟩ :=
    arithmeticFragment_evaluation_reflected definitions expression fragment
      environment value evaluated
  have sourceScoped := decodeTopLevel_initializer_evaluation_preserves_valueWellScoped
    fuel forms definitions slotTypes initializers decoded environment expression sourceValue
    member environmentScoped sourceEvaluates
  exact ⟨sourceValue, sourceEvaluates, lowers, sourceScoped⟩

theorem arithmeticFragmentList_arguments_reflected (program : Definitions)
    (expressions : List Expr) (fragments : ArithmeticFragmentList expressions)
    (env : Environment) :
    ∀ {values},
      PolyIR.ArgumentsEvaluate (lowerDefinitions program) (lowerEnv env)
        (lowerMany (identities env) expressions) values →
      ∃ sourceValues, ArgumentsEvaluate program env expressions sourceValues ∧
        lowerValues sourceValues = values := by
  induction fragments with
  | nil =>
      intro values evaluated
      cases evaluated
      exact ⟨[], .nil, rfl⟩
  | cons head tail headFragment _tailFragment tailIH =>
      intro values evaluated
      rw [lowerMany_eq] at evaluated
      cases evaluated with
      | cons headEval tailEval =>
          obtain ⟨sourceHead, headSourceEval, headLowered⟩ :=
            arithmeticFragment_evaluation_reflected program head headFragment env _ headEval
          obtain ⟨sourceTail, tailSourceEval, tailLowered⟩ := tailIH tailEval
          exact ⟨sourceHead :: sourceTail, .cons headSourceEval tailSourceEval, by
            change lowerValue sourceHead :: lowerValues sourceTail = _
            rw [headLowered, tailLowered]⟩

theorem arithmeticFragmentList_sequence_reflected (program : Definitions)
    (expressions : List Expr) (fragments : ArithmeticFragmentList expressions)
    (env : Environment) (sourcePrevious : Value) (irPrevious : PolyIR.Value)
    (previousLowered : lowerValue sourcePrevious = irPrevious) :
    ∀ {value},
      PolyIR.SequenceEvaluates (lowerDefinitions program) (lowerEnv env)
        (lowerMany (identities env) expressions) irPrevious value →
      ∃ sourceValue, SequenceEvaluates program env expressions sourcePrevious sourceValue ∧
        lowerValue sourceValue = value := by
  induction fragments generalizing sourcePrevious irPrevious with
  | nil =>
      intro value evaluated
      cases evaluated
      exact ⟨sourcePrevious, .nil, previousLowered⟩
  | cons head tail headFragment _tailFragment tailIH =>
      intro value evaluated
      rw [lowerMany_eq] at evaluated
      cases evaluated with
      | cons headEval tailEval =>
          obtain ⟨sourceHead, headSourceEval, headLowered⟩ :=
            arithmeticFragment_evaluation_reflected program head headFragment env _ headEval
          obtain ⟨sourceValue, tailSourceEval, valueLowered⟩ :=
            tailIH sourceHead _ headLowered tailEval
          exact ⟨sourceValue, .cons headSourceEval tailSourceEval, valueLowered⟩

theorem begin_evaluation_reflected_of_first
    (program : Definitions) (env : Environment) (first : Expr) (rest : List Expr)
    (firstReflected : ∀ {irValue},
      PolyIR.Evaluates (lowerDefinitions program) (lowerEnv env)
        (lower (identities env) first) irValue →
      ∃ sourceValue, Evaluates program env first sourceValue ∧
        lowerValue sourceValue = irValue)
    (restFragments : ArithmeticFragmentList rest) (value : PolyIR.Value)
    (evaluated : PolyIR.Evaluates (lowerDefinitions program) (lowerEnv env)
      (lower (identities env) (.begin first rest)) value) :
    ∃ sourceValue, Evaluates program env (.begin first rest) sourceValue ∧
      lowerValue sourceValue = value := by
  rw [lower_eq] at evaluated
  cases evaluated with
  | begin firstEval restEval =>
      obtain ⟨sourceFirst, firstSourceEval, firstLowered⟩ := firstReflected firstEval
      obtain ⟨sourceValue, restSourceEval, valueLowered⟩ :=
        arithmeticFragmentList_sequence_reflected program rest restFragments env sourceFirst _
          firstLowered restEval
      exact ⟨sourceValue, .begin firstSourceEval restSourceEval, valueLowered⟩

theorem begin_evaluation_reflected_of_fragments (program : Definitions)
    (env : Environment) (first : Expr) (rest : List Expr)
    (firstFragment : ArithmeticFragment first)
    (restFragments : ArithmeticFragmentList rest) (value : PolyIR.Value)
    (evaluated : PolyIR.Evaluates (lowerDefinitions program) (lowerEnv env)
      (lower (identities env) (.begin first rest)) value) :
    ∃ sourceValue, Evaluates program env (.begin first rest) sourceValue ∧
      lowerValue sourceValue = value := by
  rw [lower_eq] at evaluated
  cases evaluated with
  | begin firstEval restEval =>
      obtain ⟨sourceFirst, firstSourceEval, firstLowered⟩ :=
        arithmeticFragment_evaluation_reflected program first firstFragment env _ firstEval
      obtain ⟨sourceValue, restSourceEval, valueLowered⟩ :=
        arithmeticFragmentList_sequence_reflected program rest restFragments env sourceFirst _
          firstLowered restEval
      exact ⟨sourceValue, .begin firstSourceEval restSourceEval, valueLowered⟩

theorem letMany_evaluation_reflected_of_fragments (program : Definitions)
    (env : Environment) (ids : List Nat) (initializers : List Expr) (body : Expr)
    (initializersFragments : ArithmeticFragmentList initializers)
    (layout : ids.length = initializers.length) (bodyFragment : ArithmeticFragment body)
    (value : PolyIR.Value)
    (evaluated : PolyIR.Evaluates (lowerDefinitions program) (lowerEnv env)
      (lower (identities env) (.letMany ids initializers body)) value) :
    ∃ sourceValue, Evaluates program env (.letMany ids initializers body) sourceValue ∧
      lowerValue sourceValue = value := by
  exact letMany_evaluation_reflected program env ids initializers body layout.symm
    (fun {irValues} argumentsEval =>
      arithmeticFragmentList_arguments_reflected program initializers initializersFragments env
        argumentsEval)
    (fun sourceValues irValues sourceLength valuesLower {result} bodyEval => by
      have environmentEq : lowerEnv (bind ids sourceValues ++ env) =
          irValues ++ lowerEnv env := by
        rw [lowerEnv_bind_append ids sourceValues env sourceLength, valuesLower]
      have identitiesEq : identities (bind ids sourceValues ++ env) = ids ++ identities env :=
        identities_bind_append ids sourceValues env sourceLength
      have termEq : lower (identities (bind ids sourceValues ++ env)) body =
          lower (ids ++ identities env) body := by rw [identitiesEq]
      exact arithmeticFragment_evaluation_reflected program body bodyFragment
        (bind ids sourceValues ++ env) result (by
          rw [environmentEq, termEq]
          exact bodyEval)) value evaluated

/-- Reflection for every finite `begin` sequence, packaged as one expression
fragment instead of exposing the first expression and tail separately. -/
theorem beginFragment_evaluation_reflected (program : Definitions)
    (expression : Expr) (fragment : BeginFragment expression) :
    ∀ (environment : Environment) (value : PolyIR.Value),
      PolyIR.Evaluates (lowerDefinitions program) (lowerEnv environment)
        (lower (identities environment) expression) value →
      ∃ sourceValue, Evaluates program environment expression sourceValue ∧
        lowerValue sourceValue = value := by
  cases fragment with
  | sequence first rest firstFragment restFragments =>
      intro environment value evaluated
      exact begin_evaluation_reflected_of_fragments program environment first rest
        firstFragment restFragments value evaluated

/-- Reflection for an arbitrary finite parallel let, provided its binder
layout is aligned with the initializer list. -/
theorem letManyFragment_evaluation_reflected (program : Definitions)
    (expression : Expr) (fragment : LetManyFragment expression) :
    ∀ (environment : Environment) (value : PolyIR.Value),
      PolyIR.Evaluates (lowerDefinitions program) (lowerEnv environment)
        (lower (identities environment) expression) value →
      ∃ sourceValue, Evaluates program environment expression sourceValue ∧
        lowerValue sourceValue = value := by
  cases fragment with
  | bindings ids initializers body initializersFragments layout bodyFragment =>
      intro environment value evaluated
      exact letMany_evaluation_reflected_of_fragments program environment ids initializers body
        initializersFragments layout bodyFragment value evaluated

/-- The main reflection fragment extended with arbitrary-length parallel
lets. Initializer rows use the arithmetic fragment, and the body may contain
further parallel lets recursively. -/
inductive ArithmeticWithParallelLets : Expr → Prop where
  | arithmetic (expression : Expr) : ArithmeticFragment expression →
      ArithmeticWithParallelLets expression
  | letMany (ids : List Nat) (initializers : List Expr) (body : Expr) :
      ArithmeticFragmentList initializers → ids.length = initializers.length →
      ArithmeticWithParallelLets body →
      ArithmeticWithParallelLets (.letMany ids initializers body)

theorem arithmeticWithParallelLets_evaluation_reflected (program : Definitions)
    (expression : Expr) (fragment : ArithmeticWithParallelLets expression) :
    ∀ (environment : Environment) (value : PolyIR.Value),
      PolyIR.Evaluates (lowerDefinitions program) (lowerEnv environment)
        (lower (identities environment) expression) value →
      ∃ sourceValue, Evaluates program environment expression sourceValue ∧
        lowerValue sourceValue = value := by
  induction fragment with
  | arithmetic expression arithmeticFragment =>
      exact arithmeticFragment_evaluation_reflected program expression arithmeticFragment
  | letMany ids initializers body initializersFragments layout bodyFragment bodyIH =>
      intro environment value evaluated
      exact letMany_evaluation_reflected program environment ids initializers body layout.symm
        (fun {irValues} argumentsEval =>
          arithmeticFragmentList_arguments_reflected program initializers
            initializersFragments environment argumentsEval)
        (fun sourceValues irValues sourceLength valuesLower {result} bodyEval => by
          have environmentEq : lowerEnv (bind ids sourceValues ++ environment) =
              irValues ++ lowerEnv environment := by
            rw [lowerEnv_bind_append ids sourceValues environment sourceLength, valuesLower]
          have identitiesEq : identities (bind ids sourceValues ++ environment) =
              ids ++ identities environment :=
            identities_bind_append ids sourceValues environment sourceLength
          have termEq : lower (identities (bind ids sourceValues ++ environment)) body =
              lower (ids ++ identities environment) body := by rw [identitiesEq]
          exact bodyIH (bind ids sourceValues ++ environment) result (by
            rw [environmentEq, termEq]
            exact bodyEval)) value evaluated

theorem arithmeticWithParallelLets_termination_preserved_and_reflected
    (program : Definitions) (environment : Environment) (expression : Expr)
    (fragment : ArithmeticWithParallelLets expression) :
    SourceTerminates program environment expression ↔
      LoweredTerminates program environment expression := by
  constructor
  · rintro ⟨value, sourceEvaluation⟩
    exact ⟨lowerValue value, evaluation_preserved sourceEvaluation⟩
  · rintro ⟨value, loweredEvaluation⟩
    obtain ⟨sourceValue, sourceEvaluation, _⟩ :=
      arithmeticWithParallelLets_evaluation_reflected program expression fragment
        environment value loweredEvaluation
    exact ⟨sourceValue, sourceEvaluation⟩

theorem arithmeticWithParallelLets_divergence_preserved_and_reflected
    (program : Definitions) (environment : Environment) (expression : Expr)
    (fragment : ArithmeticWithParallelLets expression) :
    SourceDiverges program environment expression ↔
      LoweredDiverges program environment expression := by
  exact not_congr
    (arithmeticWithParallelLets_termination_preserved_and_reflected
      program environment expression fragment)

/-- Top-level initializer reflection and returned-value scope preservation
also cover arbitrary-length parallel lets whose initializer rows and body are
in the arithmetic reflection fragment. -/
theorem decodedInitializer_parallelLet_evaluation_reflected
    (fuel : Nat) (forms : List CBindingWalk.Node) (definitions : Definitions)
    (slotTypes : List Surface.Ty) (initializers : List Expr)
    (decoded : decodeTopLevelProgram fuel forms =
      some (definitions, slotTypes, initializers))
    (expression : Expr) (member : expression ∈ initializers)
    (fragment : ArithmeticWithParallelLets expression)
    (environment : Environment) (value : PolyIR.Value)
    (environmentScoped : environmentWellScoped environment)
    (evaluated : PolyIR.Evaluates (lowerDefinitions definitions) (lowerEnv environment)
      (lower (identities environment) expression) value) :
    ∃ sourceValue, Evaluates definitions environment expression sourceValue ∧
      lowerValue sourceValue = value ∧ valueWellScoped sourceValue := by
  obtain ⟨sourceValue, sourceEvaluates, lowers⟩ :=
    arithmeticWithParallelLets_evaluation_reflected definitions expression fragment
      environment value evaluated
  have sourceScoped := decodeTopLevel_initializer_evaluation_preserves_valueWellScoped
    fuel forms definitions slotTypes initializers decoded environment expression sourceValue
    member environmentScoped sourceEvaluates
  exact ⟨sourceValue, sourceEvaluates, lowers, sourceScoped⟩

theorem beginFragment_termination_preserved_and_reflected
    (program : Definitions) (environment : Environment) (expression : Expr)
    (fragment : BeginFragment expression) :
    SourceTerminates program environment expression ↔
      LoweredTerminates program environment expression := by
  constructor
  · rintro ⟨value, sourceEvaluation⟩
    exact ⟨lowerValue value, evaluation_preserved sourceEvaluation⟩
  · rintro ⟨value, loweredEvaluation⟩
    obtain ⟨sourceValue, sourceEvaluation, _⟩ :=
      beginFragment_evaluation_reflected program expression fragment environment value loweredEvaluation
    exact ⟨sourceValue, sourceEvaluation⟩

theorem beginFragment_divergence_preserved_and_reflected
    (program : Definitions) (environment : Environment) (expression : Expr)
    (fragment : BeginFragment expression) :
    SourceDiverges program environment expression ↔
      LoweredDiverges program environment expression := by
  exact not_congr (beginFragment_termination_preserved_and_reflected
    program environment expression fragment)

theorem letManyFragment_termination_preserved_and_reflected
    (program : Definitions) (environment : Environment) (expression : Expr)
    (fragment : LetManyFragment expression) :
    SourceTerminates program environment expression ↔
      LoweredTerminates program environment expression := by
  constructor
  · rintro ⟨value, sourceEvaluation⟩
    exact ⟨lowerValue value, evaluation_preserved sourceEvaluation⟩
  · rintro ⟨value, loweredEvaluation⟩
    obtain ⟨sourceValue, sourceEvaluation, _⟩ :=
      letManyFragment_evaluation_reflected program expression fragment environment value loweredEvaluation
    exact ⟨sourceValue, sourceEvaluation⟩

theorem letManyFragment_divergence_preserved_and_reflected
    (program : Definitions) (environment : Environment) (expression : Expr)
    (fragment : LetManyFragment expression) :
    SourceDiverges program environment expression ↔
      LoweredDiverges program environment expression := by
  exact not_congr (letManyFragment_termination_preserved_and_reflected
    program environment expression fragment)

theorem lambda_application_evaluation_reflected_of_fragments (program : Definitions)
    (env : Environment) (parameters : List Nat) (body : Expr) (arguments : List Expr)
    (bodyFragment : ArithmeticFragment body)
    (argumentsFragments : ArithmeticFragmentList arguments) (value : PolyIR.Value)
    (evaluated : PolyIR.Evaluates (lowerDefinitions program) (lowerEnv env)
      (lower (identities env) (.app (.lam parameters body) arguments)) value) :
    ∃ sourceValue, Evaluates program env (.app (.lam parameters body) arguments) sourceValue ∧
      lowerValue sourceValue = value := by
  rw [lower_eq] at evaluated
  cases evaluated with
  | appClosure functionEval argumentsEval argumentsArity bodyEval =>
      rw [lower_eq] at functionEval
      cases functionEval with
      | lam =>
          obtain ⟨sourceArguments, sourceArgumentsEval, argumentsLowered⟩ :=
            arithmeticFragmentList_arguments_reflected program arguments argumentsFragments env
              argumentsEval
          have sourceArity : sourceArguments.length = parameters.length := by
            calc
              sourceArguments.length = (lowerValues sourceArguments).length := by simp [lowerValues]
              _ = _ := congrArg List.length argumentsLowered
              _ = parameters.length := by
                simpa [lowerValues] using argumentsArity
          have bodyEnvironmentEq :
              lowerEnv (bind parameters sourceArguments ++ env) =
                lowerValues sourceArguments ++ lowerEnv env :=
            lowerEnv_bind_append parameters sourceArguments env sourceArity
          have bodyLocalsEq :
              identities (bind parameters sourceArguments ++ env) =
                parameters ++ identities env :=
            identities_bind_append parameters sourceArguments env sourceArity
          have bodyTermEq : lower (identities (bind parameters sourceArguments ++ env)) body =
              lower (parameters ++ identities env) body := by rw [bodyLocalsEq]
          have bodyEvalAligned :
              PolyIR.Evaluates (lowerDefinitions program)
                (lowerEnv (bind parameters sourceArguments ++ env))
                (lower (identities (bind parameters sourceArguments ++ env)) body) value := by
            rw [bodyEnvironmentEq, argumentsLowered, bodyTermEq]
            exact bodyEval
          obtain ⟨sourceResult, sourceBodyEval, resultLowered⟩ :=
            arithmeticFragment_evaluation_reflected program body bodyFragment
              (bind parameters sourceArguments ++ env) value bodyEvalAligned
          exact ⟨sourceResult,
            .appClosure .lam sourceArgumentsEval sourceArity sourceBodyEval, resultLowered⟩
  | appGlobal functionEval _ _ _ _ =>
      rw [lower_eq] at functionEval
      cases functionEval

theorem lambda_application_evaluation_reflected_of_first_argument
    (program : Definitions) (env : Environment) (parameters : List Nat) (body first : Expr)
    (rest : List Expr)
    (bodyReflected : ∀ (bodyEnvironment : Environment) (irValue : PolyIR.Value),
      PolyIR.Evaluates (lowerDefinitions program) (lowerEnv bodyEnvironment)
        (lower (identities bodyEnvironment) body) irValue →
      ∃ sourceValue, Evaluates program bodyEnvironment body sourceValue ∧
        lowerValue sourceValue = irValue)
    (firstReflected : ∀ {irValue},
      PolyIR.Evaluates (lowerDefinitions program) (lowerEnv env)
        (lower (identities env) first) irValue →
      ∃ sourceValue, Evaluates program env first sourceValue ∧
        lowerValue sourceValue = irValue)
    (restFragments : ArithmeticFragmentList rest) (value : PolyIR.Value)
    (evaluated : PolyIR.Evaluates (lowerDefinitions program) (lowerEnv env)
      (lower (identities env) (.app (.lam parameters body) (first :: rest))) value) :
    ∃ sourceValue,
      Evaluates program env (.app (.lam parameters body) (first :: rest)) sourceValue ∧
      lowerValue sourceValue = value := by
  rw [lower_eq] at evaluated
  cases evaluated with
  | appClosure functionEval argumentsEval argumentsArity bodyEval =>
      rw [lower_eq] at functionEval
      cases functionEval with
      | lam =>
          rw [lowerMany_eq] at argumentsEval
          cases argumentsEval with
          | cons firstEval restEval =>
              rename_i firstIRValue restIRValues
              obtain ⟨sourceFirst, firstSourceEval, firstLowered⟩ :=
                firstReflected firstEval
              obtain ⟨sourceRest, restSourceEval, restLowered⟩ :=
                arithmeticFragmentList_arguments_reflected program rest restFragments env restEval
              have argumentsLowered :
                  lowerValues (sourceFirst :: sourceRest) = firstIRValue :: restIRValues := by
                change lowerValue sourceFirst :: lowerValues sourceRest = _
                rw [firstLowered, restLowered]
              have sourceArity : (sourceFirst :: sourceRest).length = parameters.length := by
                calc
                  (sourceFirst :: sourceRest).length = (firstIRValue :: restIRValues).length := by
                    simpa [lowerValues] using congrArg List.length argumentsLowered
                  _ = parameters.length := argumentsArity
              have bodyEnvironmentEq :
                  lowerEnv (bind parameters (sourceFirst :: sourceRest) ++ env) =
                    lowerValues (sourceFirst :: sourceRest) ++ lowerEnv env :=
                lowerEnv_bind_append parameters (sourceFirst :: sourceRest) env sourceArity
              have bodyLocalsEq :
                  identities (bind parameters (sourceFirst :: sourceRest) ++ env) =
                    parameters ++ identities env :=
                identities_bind_append parameters (sourceFirst :: sourceRest) env sourceArity
              have bodyTermEq :
                  lower (identities (bind parameters (sourceFirst :: sourceRest) ++ env)) body =
                    lower (parameters ++ identities env) body := by rw [bodyLocalsEq]
              have bodyEvalAligned :
                  PolyIR.Evaluates (lowerDefinitions program)
                    (lowerEnv (bind parameters (sourceFirst :: sourceRest) ++ env))
                    (lower (identities (bind parameters (sourceFirst :: sourceRest) ++ env)) body)
                    value := by
                rw [bodyEnvironmentEq, bodyTermEq]
                rw [argumentsLowered]
                simp only [List.cons_append]
                exact bodyEval
              obtain ⟨sourceResult, sourceBodyEval, resultLowered⟩ :=
                bodyReflected (bind parameters (sourceFirst :: sourceRest) ++ env)
                  value bodyEvalAligned
              exact ⟨sourceResult,
                .appClosure .lam (.cons firstSourceEval restSourceEval) sourceArity sourceBodyEval,
                resultLowered⟩
  | appGlobal functionEval _ _ _ _ =>
      rw [lower_eq] at functionEval
      cases functionEval

/-- Every finite lowered evaluation in the arbitrary-arity lambda-application
fragment has a source derivation with the corresponding lowered value. -/
theorem lambdaApplicationFragment_evaluation_reflected (program : Definitions)
    (expression : Expr) (fragment : LambdaApplicationFragment expression) :
    ∀ (environment : Environment) (value : PolyIR.Value),
      PolyIR.Evaluates (lowerDefinitions program) (lowerEnv environment)
        (lower (identities environment) expression) value →
      ∃ sourceValue, Evaluates program environment expression sourceValue ∧
        lowerValue sourceValue = value := by
  cases fragment with
  | apply parameters body arguments bodyFragment argumentsFragments =>
      intro environment value evaluated
      exact lambda_application_evaluation_reflected_of_fragments program environment
        parameters body arguments bodyFragment argumentsFragments value evaluated

/-- Finite termination is preserved and reflected for every expression in
the arbitrary-arity lambda-application fragment. -/
theorem lambdaApplicationFragment_termination_preserved_and_reflected
    (program : Definitions) (environment : Environment) (expression : Expr)
    (fragment : LambdaApplicationFragment expression) :
    SourceTerminates program environment expression ↔
      LoweredTerminates program environment expression := by
  constructor
  · rintro ⟨value, sourceEvaluation⟩
    exact ⟨lowerValue value, evaluation_preserved sourceEvaluation⟩
  · rintro ⟨value, loweredEvaluation⟩
    obtain ⟨sourceValue, sourceEvaluation, _⟩ :=
      lambdaApplicationFragment_evaluation_reflected program expression fragment
        environment value loweredEvaluation
    exact ⟨sourceValue, sourceEvaluation⟩

/-- Absence of a finite big-step derivation is preserved and reflected for
the arbitrary-arity lambda-application fragment. -/
theorem lambdaApplicationFragment_divergence_preserved_and_reflected
    (program : Definitions) (environment : Environment) (expression : Expr)
    (fragment : LambdaApplicationFragment expression) :
    SourceDiverges program environment expression ↔
      LoweredDiverges program environment expression := by
  exact not_congr (lambdaApplicationFragment_termination_preserved_and_reflected
    program environment expression fragment)

theorem global_application_evaluation_reflected_of_fragments (program : Definitions)
    (env : Environment) (index : Nat) (parameters : List Nat) (body : Expr)
    (arguments : List Expr) (definitionFound : program[index]? = some (parameters, body))
    (bodyFragment : ArithmeticFragment body)
    (argumentsFragments : ArithmeticFragmentList arguments) (value : PolyIR.Value)
    (evaluated : PolyIR.Evaluates (lowerDefinitions program) (lowerEnv env)
      (lower (identities env) (.app (.global index) arguments)) value) :
    ∃ sourceValue, Evaluates program env (.app (.global index) arguments) sourceValue ∧
      lowerValue sourceValue = value := by
  rw [lower_eq] at evaluated
  cases evaluated with
  | appClosure functionEval _ _ _ =>
      rw [lower_eq] at functionEval
      cases functionEval
  | appGlobal functionEval argumentsEval runtimeDefinitionFound argumentsArity bodyEval =>
      rename_i _runtimeIndex irArguments irDefinition
      cases functionEval with
      | global functionFound =>
          have sourceFunctionEval : Evaluates program env (.global index) (.global index) :=
            .global definitionFound
          have runtimeDefinitionEq : irDefinition =
              PolyIR.RuntimeDefinition.mk parameters.length (lower parameters body) := by
            obtain ⟨sourceParameters, sourceBody, found, definitionEq⟩ :=
              definitions_lookup_reflects program index irDefinition runtimeDefinitionFound
            have pairEq : (sourceParameters, sourceBody) = (parameters, body) :=
              Option.some.inj (found.symm.trans definitionFound)
            cases pairEq
            exact definitionEq
          obtain ⟨sourceArguments, sourceArgumentsEval, argumentsLowered⟩ :=
            arithmeticFragmentList_arguments_reflected program arguments argumentsFragments env
              argumentsEval
          have sourceArity : sourceArguments.length = parameters.length := by
            calc
              sourceArguments.length = (lowerValues sourceArguments).length := by simp [lowerValues]
              _ = _ := congrArg List.length argumentsLowered
              _ = irDefinition.arity := argumentsArity
              _ = parameters.length := by
                have arityField := congrArg PolyIR.RuntimeDefinition.arity runtimeDefinitionEq
                simpa using arityField
          have bodyEnvironmentEq :
              lowerEnv (bind parameters sourceArguments) = lowerValues sourceArguments :=
            lowerEnv_bind parameters sourceArguments sourceArity
          have bodyTermEq :
              lower (identities (bind parameters sourceArguments)) body =
                irDefinition.body := by
            rw [bind_identifiers parameters sourceArguments sourceArity]
            have bodyField := congrArg PolyIR.RuntimeDefinition.body runtimeDefinitionEq
            simpa using bodyField.symm
          have bodyEvalAligned :
              PolyIR.Evaluates (lowerDefinitions program)
                (lowerEnv (bind parameters sourceArguments))
                (lower (identities (bind parameters sourceArguments)) body) value := by
            rw [bodyEnvironmentEq, argumentsLowered, bodyTermEq]
            exact bodyEval
          obtain ⟨sourceResult, sourceBodyEval, resultLowered⟩ :=
            arithmeticFragment_evaluation_reflected program body bodyFragment
              (bind parameters sourceArguments) value bodyEvalAligned
          exact ⟨sourceResult,
            .appGlobal sourceFunctionEval sourceArgumentsEval definitionFound sourceArity sourceBodyEval,
            resultLowered⟩

/-- Every finite evaluation of an explicit-lambda or resolved-global
application in this fragment reflects, for arbitrary argument counts. -/
theorem applicationFragment_evaluation_reflected (program : Definitions)
    (expression : Expr) (fragment : ApplicationFragment program expression) :
    ∀ (environment : Environment) (value : PolyIR.Value),
      PolyIR.Evaluates (lowerDefinitions program) (lowerEnv environment)
        (lower (identities environment) expression) value →
      ∃ sourceValue, Evaluates program environment expression sourceValue ∧
        lowerValue sourceValue = value := by
  cases fragment with
  | lambda parameters body arguments bodyFragment argumentsFragments =>
      intro environment value evaluated
      exact lambda_application_evaluation_reflected_of_fragments program environment
        parameters body arguments bodyFragment argumentsFragments value evaluated
  | global index parameters body arguments definitionFound bodyFragment argumentsFragments =>
      intro environment value evaluated
      exact global_application_evaluation_reflected_of_fragments program environment
        index parameters body arguments definitionFound bodyFragment argumentsFragments value evaluated

theorem applicationFragment_termination_preserved_and_reflected
    (program : Definitions) (environment : Environment) (expression : Expr)
    (fragment : ApplicationFragment program expression) :
    SourceTerminates program environment expression ↔
      LoweredTerminates program environment expression := by
  constructor
  · rintro ⟨value, sourceEvaluation⟩
    exact ⟨lowerValue value, evaluation_preserved sourceEvaluation⟩
  · rintro ⟨value, loweredEvaluation⟩
    obtain ⟨sourceValue, sourceEvaluation, _⟩ :=
      applicationFragment_evaluation_reflected program expression fragment environment value loweredEvaluation
    exact ⟨sourceValue, sourceEvaluation⟩

theorem applicationFragment_divergence_preserved_and_reflected
    (program : Definitions) (environment : Environment) (expression : Expr)
    (fragment : ApplicationFragment program expression) :
    SourceDiverges program environment expression ↔
      LoweredDiverges program environment expression := by
  exact not_congr (applicationFragment_termination_preserved_and_reflected
    program environment expression fragment)

/-- A compositional fragment packages the expression families for which
evaluation reflection has been proved: arithmetic forms, arbitrary finite
`begin` and aligned `letMany`, and arbitrary-arity lambda/global calls. -/
inductive CompositionalReflectionFragment (program : Definitions) : Expr → Prop where
  | arithmetic {expression} : ArithmeticFragment expression →
      CompositionalReflectionFragment program expression
  | application {expression} : ApplicationFragment program expression →
      CompositionalReflectionFragment program expression
  | lambdaRows (parameters : List Nat) (body : Expr) (arguments : List Expr) :
      CompositionalReflectionFragment program body →
      (∀ argument, argument ∈ arguments →
        CompositionalReflectionFragment program argument) →
      CompositionalReflectionFragment program (.app (.lam parameters body) arguments)
  | begin {expression} : BeginFragment expression →
      CompositionalReflectionFragment program expression
  | beginRows (first : Expr) (rest : List Expr) :
      CompositionalReflectionFragment program first →
      (∀ expression, expression ∈ rest →
        CompositionalReflectionFragment program expression) →
      CompositionalReflectionFragment program (.begin first rest)
  | letMany {expression} : LetManyFragment expression →
      CompositionalReflectionFragment program expression
  | beginFirst (first : Expr) (rest : List Expr) :
      CompositionalReflectionFragment program first → ArithmeticFragmentList rest →
      CompositionalReflectionFragment program (.begin first rest)
  | beginSecond (first second : Expr) (rest : List Expr) :
      ArithmeticFragment first → CompositionalReflectionFragment program second →
      ArithmeticFragmentList rest →
      CompositionalReflectionFragment program (.begin first (second :: rest))
  | beginFirstSecond (first second : Expr) :
      CompositionalReflectionFragment program first →
      CompositionalReflectionFragment program second →
      CompositionalReflectionFragment program (.begin first [second])
  | letManyBody (ids : List Nat) (initializers : List Expr) (body : Expr) :
      ArithmeticFragmentList initializers → ids.length = initializers.length →
      CompositionalReflectionFragment program body →
      CompositionalReflectionFragment program (.letMany ids initializers body)
  | letManyFirstInitializer (ids : List Nat) (first : Expr) (rest : List Expr)
      (body : Expr) :
      CompositionalReflectionFragment program first → ArithmeticFragmentList rest →
      ids.length = (first :: rest).length → ArithmeticFragment body →
      CompositionalReflectionFragment program (.letMany ids (first :: rest) body)
  | letManyFirstInitializerBody (ids : List Nat) (first : Expr) (rest : List Expr)
      (body : Expr) :
      CompositionalReflectionFragment program first → ArithmeticFragmentList rest →
      ids.length = (first :: rest).length → CompositionalReflectionFragment program body →
      CompositionalReflectionFragment program (.letMany ids (first :: rest) body)
  | letManyRows (ids : List Nat) (initializers : List Expr) (body : Expr) :
      (∀ initializer, initializer ∈ initializers →
        CompositionalReflectionFragment program initializer) →
      ids.length = initializers.length →
      CompositionalReflectionFragment program body →
      CompositionalReflectionFragment program (.letMany ids initializers body)
  | lambdaFirstArgument (parameters : List Nat) (body first : Expr) (rest : List Expr) :
      ArithmeticFragment body → CompositionalReflectionFragment program first →
      ArithmeticFragmentList rest →
      CompositionalReflectionFragment program (.app (.lam parameters body) (first :: rest))
  | lambdaBodyFirstArgument (parameters : List Nat) (body first : Expr) (rest : List Expr) :
      CompositionalReflectionFragment program body →
      CompositionalReflectionFragment program first → ArithmeticFragmentList rest →
      CompositionalReflectionFragment program (.app (.lam parameters body) (first :: rest))
  | lambdaBody (parameters : List Nat) (body : Expr) :
      CompositionalReflectionFragment program body →
      CompositionalReflectionFragment program (.lam parameters body)
  | globalApplicationBody (index : Nat) (parameters : List Nat) (body : Expr)
      (arguments : List Expr) :
      program[index]? = some (parameters, body) →
      CompositionalReflectionFragment program body → ArithmeticFragmentList arguments →
      CompositionalReflectionFragment program (.app (.global index) arguments)
  | globalApplicationBodyFirstArgument (index : Nat) (parameters : List Nat)
      (body first : Expr) (rest : List Expr) :
      program[index]? = some (parameters, body) →
      CompositionalReflectionFragment program body →
      CompositionalReflectionFragment program first → ArithmeticFragmentList rest →
      CompositionalReflectionFragment program
        (.app (.global index) (first :: rest))
  | globalApplicationRows (index : Nat) (parameters : List Nat) (body : Expr)
      (arguments : List Expr) :
      program[index]? = some (parameters, body) →
      CompositionalReflectionFragment program body →
      (∀ argument, argument ∈ arguments → CompositionalReflectionFragment program argument) →
      CompositionalReflectionFragment program (.app (.global index) arguments)
  | someChild (child : Expr) :
      CompositionalReflectionFragment program child →
      CompositionalReflectionFragment program (.some child)
  | consChildren (head tail : Expr) :
      CompositionalReflectionFragment program head →
      CompositionalReflectionFragment program tail →
      CompositionalReflectionFragment program (.cons head tail)
  | floatBinChildren (operation : Surface.FloatBinOp) (left right : Expr) :
      CompositionalReflectionFragment program left →
      CompositionalReflectionFragment program right →
      CompositionalReflectionFragment program (.floatBin operation left right)
  | addChildren (left right : Expr) :
      CompositionalReflectionFragment program left →
      CompositionalReflectionFragment program right →
      CompositionalReflectionFragment program (.add left right)
  | subChildren (left right : Expr) :
      CompositionalReflectionFragment program left →
      CompositionalReflectionFragment program right →
      CompositionalReflectionFragment program (.sub left right)
  | mulChildren (left right : Expr) :
      CompositionalReflectionFragment program left →
      CompositionalReflectionFragment program right →
      CompositionalReflectionFragment program (.mul left right)
  | leChildren (left right : Expr) :
      CompositionalReflectionFragment program left →
      CompositionalReflectionFragment program right →
      CompositionalReflectionFragment program (.le left right)
  | intEqChildren (left right : Expr) :
      CompositionalReflectionFragment program left →
      CompositionalReflectionFragment program right →
      CompositionalReflectionFragment program (.intEq left right)
  | iteChildren (condition yes no : Expr) :
      CompositionalReflectionFragment program condition →
      CompositionalReflectionFragment program yes →
      CompositionalReflectionFragment program no →
      CompositionalReflectionFragment program (.ite condition yes no)
  | matchOptionChildren (target empty : Expr) (binder : Nat) (full : Expr) :
      CompositionalReflectionFragment program target →
      CompositionalReflectionFragment program empty →
      CompositionalReflectionFragment program full →
      CompositionalReflectionFragment program (.matchOption target empty binder full)
  | matchListChildren (target empty : Expr) (headBinder tailBinder : Nat) (full : Expr) :
      CompositionalReflectionFragment program target →
      CompositionalReflectionFragment program empty →
      CompositionalReflectionFragment program full →
      CompositionalReflectionFragment program
        (.matchList target empty headBinder tailBinder full)

def CompositionalReflectionRows (program : Definitions) (expressions : List Expr) : Prop :=
  ∀ expression, expression ∈ expressions → CompositionalReflectionFragment program expression

/-- One reflection theorem for the union of the compositional fragments. -/
theorem compositionalReflection_evaluation_reflected (program : Definitions)
    {expression : Expr} (fragment : CompositionalReflectionFragment program expression)
    (environment : Environment) (value : PolyIR.Value)
    (evaluated : PolyIR.Evaluates (lowerDefinitions program) (lowerEnv environment)
      (lower (identities environment) expression) value) :
    ∃ sourceValue, Evaluates program environment expression sourceValue ∧
      lowerValue sourceValue = value := by
  induction fragment generalizing environment value with
  | @arithmetic expression proof =>
      exact arithmeticFragment_evaluation_reflected program expression proof environment value evaluated
  | @application expression proof =>
      exact applicationFragment_evaluation_reflected program expression proof environment value evaluated
  | @lambdaRows parameters body arguments _ _ bodyIH argumentsIH =>
      rw [lower_eq] at evaluated
      cases evaluated with
      | appClosure functionEval argumentsEval argumentsArity bodyEval =>
          rw [lower_eq] at functionEval
          cases functionEval with
          | lam =>
              have argumentsReflected : ∀ (expressions : List Expr),
                  (∀ argument, argument ∈ expressions → ∀ (irArgument : PolyIR.Value),
                    PolyIR.Evaluates (lowerDefinitions program) (lowerEnv environment)
                      (lower (identities environment) argument) irArgument →
                    ∃ sourceArgument, Evaluates program environment argument sourceArgument ∧
                      lowerValue sourceArgument = irArgument) →
                  ∀ {irArguments},
                    PolyIR.ArgumentsEvaluate (lowerDefinitions program) (lowerEnv environment)
                      (lowerMany (identities environment) expressions) irArguments →
                    ∃ sourceArguments, ArgumentsEvaluate program environment expressions
                      sourceArguments ∧ lowerValues sourceArguments = irArguments := by
                intro expressions
                induction expressions with
                | nil =>
                    intro rows irArguments argumentsEval
                    cases argumentsEval
                    exact ⟨[], .nil, by simp [lowerValues]⟩
                | cons argument rest ih =>
                    intro rows irArguments argumentsEval
                    rw [lowerMany_eq] at argumentsEval
                    cases argumentsEval with
                    | cons argumentEval restEval =>
                        obtain ⟨sourceArgument, sourceArgumentEval, argumentLowered⟩ :=
                          rows argument (by simp) _ argumentEval
                        have restRows : ∀ expression, expression ∈ rest →
                            ∀ (irValue : PolyIR.Value),
                              PolyIR.Evaluates (lowerDefinitions program) (lowerEnv environment)
                                (lower (identities environment) expression) irValue →
                              ∃ sourceValue, Evaluates program environment expression sourceValue ∧
                                lowerValue sourceValue = irValue := by
                          intro expression member irValue expressionEval
                          exact rows expression (List.mem_cons_of_mem _ member) irValue expressionEval
                        obtain ⟨sourceRest, sourceRestEval, restLowered⟩ := ih restRows restEval
                        exact ⟨sourceArgument :: sourceRest, .cons sourceArgumentEval sourceRestEval,
                          by
                            simpa [lowerValues, argumentLowered] using
                              congrArg (List.cons (lowerValue sourceArgument)) restLowered⟩
              obtain ⟨sourceArguments, sourceArgumentsEval, argumentsLowered⟩ :=
                argumentsReflected arguments
                  (fun argument member irArgument argumentEval =>
                    argumentsIH argument member environment irArgument argumentEval)
                  argumentsEval
              have sourceArity : sourceArguments.length = parameters.length := by
                calc
                  sourceArguments.length = (lowerValues sourceArguments).length := by
                    simp [lowerValues]
                  _ = _ := congrArg List.length argumentsLowered
                  _ = parameters.length := by simpa [lowerValues] using argumentsArity
              have bodyEnvironmentEq :
                  lowerEnv (bind parameters sourceArguments ++ environment) =
                    lowerValues sourceArguments ++ lowerEnv environment :=
                lowerEnv_bind_append parameters sourceArguments environment sourceArity
              have bodyLocalsEq :
                  identities (bind parameters sourceArguments ++ environment) =
                    parameters ++ identities environment :=
                identities_bind_append parameters sourceArguments environment sourceArity
              have bodyTermEq :
                  lower (identities (bind parameters sourceArguments ++ environment)) body =
                    lower (parameters ++ identities environment) body := by rw [bodyLocalsEq]
              have bodyEvalAligned :
                  PolyIR.Evaluates (lowerDefinitions program)
                    (lowerEnv (bind parameters sourceArguments ++ environment))
                    (lower (identities (bind parameters sourceArguments ++ environment)) body)
                    value := by
                rw [bodyEnvironmentEq, argumentsLowered, bodyTermEq]
                exact bodyEval
              obtain ⟨sourceResult, sourceBodyEval, resultLowered⟩ :=
                bodyIH (bind parameters sourceArguments ++ environment) value bodyEvalAligned
              exact ⟨sourceResult,
                .appClosure .lam sourceArgumentsEval sourceArity sourceBodyEval, resultLowered⟩
      | appGlobal functionEval _ _ _ _ =>
          rw [lower_eq] at functionEval
          cases functionEval
  | @begin expression proof =>
      exact beginFragment_evaluation_reflected program expression proof environment value evaluated
  | @beginRows first rest _ _ firstIH restIH =>
      rw [lower_eq] at evaluated
      cases evaluated with
      | begin firstEval restEval =>
          obtain ⟨sourceFirst, firstSourceEval, firstLowered⟩ :=
            firstIH environment _ firstEval
          have sequenceReflected : ∀ (expressions : List Expr)
              (rows : ∀ expression, expression ∈ expressions →
                ∀ (irValue : PolyIR.Value),
                  PolyIR.Evaluates (lowerDefinitions program) (lowerEnv environment)
                    (lower (identities environment) expression) irValue →
                  ∃ sourceValue, Evaluates program environment expression sourceValue ∧
                    lowerValue sourceValue = irValue)
              (sourcePrevious : Value) (irPrevious : PolyIR.Value),
              lowerValue sourcePrevious = irPrevious →
              ∀ {irValue},
                PolyIR.SequenceEvaluates (lowerDefinitions program) (lowerEnv environment)
                  (lowerMany (identities environment) expressions) irPrevious irValue →
                ∃ sourceValue, SequenceEvaluates program environment expressions
                  sourcePrevious sourceValue ∧ lowerValue sourceValue = irValue := by
            intro expressions
            induction expressions with
            | nil =>
                intro rows sourcePrevious irPrevious previousLowered irValue sequenceEval
                cases sequenceEval
                exact ⟨sourcePrevious, .nil, previousLowered⟩
            | cons head tail ih =>
                intro rows sourcePrevious irPrevious previousLowered irValue sequenceEval
                rw [lowerMany_eq] at sequenceEval
                cases sequenceEval with
                | cons headEval tailEval =>
                    obtain ⟨sourceHead, headSourceEval, headLowered⟩ :=
                      rows head (by simp) _ headEval
                    have tailRows : ∀ expression, expression ∈ tail →
                        ∀ (irValue : PolyIR.Value),
                          PolyIR.Evaluates (lowerDefinitions program) (lowerEnv environment)
                            (lower (identities environment) expression) irValue →
                          ∃ sourceValue, Evaluates program environment expression sourceValue ∧
                            lowerValue sourceValue = irValue := by
                      intro expression member irValue expressionEval
                      exact rows expression (List.mem_cons_of_mem _ member) irValue expressionEval
                    obtain ⟨sourceResult, tailSourceEval, resultLowered⟩ :=
                      ih tailRows sourceHead _ headLowered tailEval
                    exact ⟨sourceResult, .cons headSourceEval tailSourceEval, resultLowered⟩
          obtain ⟨sourceResult, restSourceEval, resultLowered⟩ :=
            sequenceReflected rest
              (fun expression member irValue expressionEval =>
                restIH expression member environment irValue expressionEval)
              sourceFirst _ firstLowered restEval
          exact ⟨sourceResult, .begin firstSourceEval restSourceEval, resultLowered⟩
  | @letMany expression proof =>
      exact letManyFragment_evaluation_reflected program expression proof environment value evaluated
  | @beginFirst first rest _ restFragments firstIH =>
      exact begin_evaluation_reflected_of_first program environment first rest
        (by
          intro irFirst firstEval
          exact firstIH environment irFirst firstEval)
        restFragments value evaluated
  | @beginSecond first second rest firstFragment _ restFragments secondIH =>
      rw [lower_eq] at evaluated
      cases evaluated with
      | begin firstEval restEval =>
          rw [lowerMany_eq] at restEval
          cases restEval with
          | cons secondEval tailEval =>
              obtain ⟨sourceFirst, firstSourceEval, firstLowered⟩ :=
                arithmeticFragment_evaluation_reflected program first firstFragment
                  environment _ firstEval
              obtain ⟨sourceSecond, secondSourceEval, secondLowered⟩ :=
                secondIH environment _ secondEval
              obtain ⟨sourceResult, tailSourceEval, resultLowered⟩ :=
                arithmeticFragmentList_sequence_reflected program rest restFragments
                  environment sourceSecond _ secondLowered tailEval
              exact ⟨sourceResult,
                .begin firstSourceEval (.cons secondSourceEval tailSourceEval), resultLowered⟩
  | @beginFirstSecond first second _ _ firstIH secondIH =>
      rw [lower_eq] at evaluated
      cases evaluated with
      | begin firstEval restEval =>
          rw [lowerMany_eq] at restEval
          cases restEval with
          | cons secondEval tailEval =>
              cases tailEval
              obtain ⟨sourceFirst, firstSourceEval, firstLowered⟩ :=
                firstIH environment _ firstEval
              obtain ⟨sourceSecond, secondSourceEval, secondLowered⟩ :=
                secondIH environment _ secondEval
              have resultLowered : lowerValue sourceSecond = value := by
                simpa [lowerValue] using secondLowered
              exact ⟨sourceSecond,
                .begin firstSourceEval (.cons secondSourceEval .nil), resultLowered⟩
  | @letManyBody ids initializers body initializerFragments layout _ bodyIH =>
      exact letMany_evaluation_reflected program environment ids initializers body layout.symm
        (fun {irValues} argumentsEval =>
          arithmeticFragmentList_arguments_reflected program initializers initializerFragments
            environment argumentsEval)
        (fun sourceValues irValues sourceLength valuesLower {result} bodyEval => by
          have environmentEq : lowerEnv (bind ids sourceValues ++ environment) =
              irValues ++ lowerEnv environment := by
            rw [lowerEnv_bind_append ids sourceValues environment sourceLength, valuesLower]
          have identitiesEq : identities (bind ids sourceValues ++ environment) =
              ids ++ identities environment :=
            identities_bind_append ids sourceValues environment sourceLength
          have termEq : lower (identities (bind ids sourceValues ++ environment)) body =
              lower (ids ++ identities environment) body := by rw [identitiesEq]
          exact bodyIH (bind ids sourceValues ++ environment) result (by
            rw [environmentEq, termEq]
            exact bodyEval)) value evaluated
  | @letManyFirstInitializer ids first rest body firstFragment restFragments layout bodyFragment firstIH =>
      exact letMany_evaluation_reflected program environment ids (first :: rest) body
        layout.symm
        (fun {irValues} argumentsEval => by
          rw [lowerMany_eq] at argumentsEval
          cases argumentsEval with
          | cons firstEval restEval =>
              obtain ⟨sourceFirst, firstSourceEval, firstLowered⟩ :=
                firstIH environment _ firstEval
              obtain ⟨sourceRest, restSourceEval, restLowered⟩ :=
                arithmeticFragmentList_arguments_reflected program rest restFragments
                  environment restEval
              exact ⟨sourceFirst :: sourceRest, .cons firstSourceEval restSourceEval, by
                change lowerValue sourceFirst :: lowerValues sourceRest = _
                rw [firstLowered, restLowered]⟩)
        (fun sourceValues irValues sourceLength valuesLower {result} bodyEval => by
          have environmentEq : lowerEnv (bind ids sourceValues ++ environment) =
              irValues ++ lowerEnv environment := by
            rw [lowerEnv_bind_append ids sourceValues environment sourceLength, valuesLower]
          have identitiesEq : identities (bind ids sourceValues ++ environment) =
              ids ++ identities environment :=
            identities_bind_append ids sourceValues environment sourceLength
          have termEq : lower (identities (bind ids sourceValues ++ environment)) body =
              lower (ids ++ identities environment) body := by rw [identitiesEq]
          exact arithmeticFragment_evaluation_reflected program body bodyFragment
            (bind ids sourceValues ++ environment) result (by
              rw [environmentEq, termEq]
              exact bodyEval)) value evaluated
  | @letManyFirstInitializerBody ids first rest body firstFragment restFragments layout _ firstIH bodyIH =>
      exact letMany_evaluation_reflected program environment ids (first :: rest) body
        layout.symm
        (fun {irValues} argumentsEval => by
          rw [lowerMany_eq] at argumentsEval
          cases argumentsEval with
          | cons firstEval restEval =>
              obtain ⟨sourceFirst, firstSourceEval, firstLowered⟩ :=
                firstIH environment _ firstEval
              obtain ⟨sourceRest, restSourceEval, restLowered⟩ :=
                arithmeticFragmentList_arguments_reflected program rest restFragments
                  environment restEval
              exact ⟨sourceFirst :: sourceRest, .cons firstSourceEval restSourceEval, by
                change lowerValue sourceFirst :: lowerValues sourceRest = _
                rw [firstLowered, restLowered]⟩)
        (fun sourceValues irValues sourceLength valuesLower {result} bodyEval => by
          have environmentEq : lowerEnv (bind ids sourceValues ++ environment) =
              irValues ++ lowerEnv environment := by
            rw [lowerEnv_bind_append ids sourceValues environment sourceLength, valuesLower]
          have identitiesEq : identities (bind ids sourceValues ++ environment) =
              ids ++ identities environment :=
            identities_bind_append ids sourceValues environment sourceLength
          have termEq : lower (identities (bind ids sourceValues ++ environment)) body =
              lower (ids ++ identities environment) body := by rw [identitiesEq]
          exact bodyIH (bind ids sourceValues ++ environment) result (by
            rw [environmentEq, termEq]
            exact bodyEval)) value evaluated
  | @letManyRows ids initializers body _ layout _ initializerIH bodyIH =>
      have initializersReflected : ∀ (expressions : List Expr),
          (∀ expression, expression ∈ expressions → expression ∈ initializers) →
          ∀ {irValues},
            PolyIR.ArgumentsEvaluate (lowerDefinitions program) (lowerEnv environment)
              (lowerMany (identities environment) expressions) irValues →
            ∃ sourceValues, ArgumentsEvaluate program environment expressions sourceValues ∧
              lowerValues sourceValues = irValues := by
        intro expressions
        induction expressions with
        | nil =>
            intro _ irValues irEval
            cases irEval
            exact ⟨[], .nil, by simp [lowerValues]⟩
        | cons head tail ih =>
            intro subset irValues irEval
            rw [lowerMany_eq] at irEval
            cases irEval with
            | cons headEval tailEval =>
                obtain ⟨sourceHead, headSourceEval, headLowered⟩ :=
                  initializerIH head (subset head (by simp)) environment _ headEval
                have tailSubset : ∀ expression, expression ∈ tail → expression ∈ initializers := by
                  intro expression member
                  exact subset expression (List.mem_cons_of_mem head member)
                obtain ⟨sourceTail, tailSourceEval, tailLowered⟩ :=
                  ih tailSubset tailEval
                refine ⟨sourceHead :: sourceTail, .cons headSourceEval tailSourceEval, ?_⟩
                change lowerValue sourceHead :: List.map lowerValue sourceTail = _
                rw [headLowered]
                simpa [lowerValues] using tailLowered
      exact letMany_evaluation_reflected program environment ids initializers body layout.symm
        (fun {irValues} initializerEval =>
          initializersReflected initializers (by intro initializer member; exact member)
            initializerEval)
        (fun sourceValues irValues sourceLength valuesLower {result} bodyEval => by
          have environmentEq : lowerEnv (bind ids sourceValues ++ environment) =
              irValues ++ lowerEnv environment := by
            rw [lowerEnv_bind_append ids sourceValues environment sourceLength, valuesLower]
          have identitiesEq : identities (bind ids sourceValues ++ environment) =
              ids ++ identities environment :=
            identities_bind_append ids sourceValues environment sourceLength
          have termEq : lower (identities (bind ids sourceValues ++ environment)) body =
              lower (ids ++ identities environment) body := by rw [identitiesEq]
          exact bodyIH (bind ids sourceValues ++ environment) result (by
            rw [environmentEq, termEq]
            exact bodyEval)) value evaluated
  | @lambdaFirstArgument parameters body first rest bodyFragment _ restFragments firstIH =>
      exact lambda_application_evaluation_reflected_of_first_argument program environment
        parameters body first rest
        (fun bodyEnvironment irValue bodyEval =>
          arithmeticFragment_evaluation_reflected program body bodyFragment
            bodyEnvironment irValue bodyEval)
        (by
          intro irFirst firstEval
          exact firstIH environment irFirst firstEval)
        restFragments value evaluated
  | @lambdaBodyFirstArgument parameters body first rest _ _ restFragments bodyIH firstIH =>
      exact lambda_application_evaluation_reflected_of_first_argument program environment
        parameters body first rest
        (fun bodyEnvironment irValue bodyEval => bodyIH bodyEnvironment irValue bodyEval)
        (by
          intro irFirst firstEval
          exact firstIH environment irFirst firstEval)
        restFragments value evaluated
  | @lambdaBody parameters body _ =>
      exact lambda_evaluation_reflected program environment parameters body value evaluated
  | @globalApplicationBody index parameters body arguments definitionFound _
      argumentFragments bodyIH =>
      rw [lower_eq] at evaluated
      cases evaluated with
      | appClosure functionEval _ _ _ =>
          rw [lower_eq] at functionEval
          cases functionEval
      | appGlobal functionEval argumentsEval runtimeDefinitionFound argumentsArity bodyEval =>
          rename_i _runtimeIndex irArguments irDefinition
          cases functionEval with
          | global _ =>
              have sourceFunctionEval : Evaluates program environment (.global index) (.global index) :=
                .global definitionFound
              have runtimeDefinitionEq : irDefinition =
                  PolyIR.RuntimeDefinition.mk parameters.length (lower parameters body) := by
                obtain ⟨sourceParameters, sourceBody, found, definitionEq⟩ :=
                  definitions_lookup_reflects program index irDefinition runtimeDefinitionFound
                have pairEq : (sourceParameters, sourceBody) = (parameters, body) :=
                  Option.some.inj (found.symm.trans definitionFound)
                cases pairEq
                exact definitionEq
              obtain ⟨sourceArguments, sourceArgumentsEval, argumentsLowered⟩ :=
                arithmeticFragmentList_arguments_reflected program arguments argumentFragments
                  environment argumentsEval
              have sourceArity : sourceArguments.length = parameters.length := by
                calc
                  sourceArguments.length = (lowerValues sourceArguments).length := by simp [lowerValues]
                  _ = _ := congrArg List.length argumentsLowered
                  _ = irDefinition.arity := argumentsArity
                  _ = parameters.length := by
                    have arityField := congrArg PolyIR.RuntimeDefinition.arity runtimeDefinitionEq
                    simpa using arityField
              have bodyEnvironmentEq :
                  lowerEnv (bind parameters sourceArguments) = lowerValues sourceArguments :=
                lowerEnv_bind parameters sourceArguments sourceArity
              have bodyTermEq : lower (identities (bind parameters sourceArguments)) body =
                  irDefinition.body := by
                rw [bind_identifiers parameters sourceArguments sourceArity]
                have bodyField := congrArg PolyIR.RuntimeDefinition.body runtimeDefinitionEq
                simpa using bodyField.symm
              have bodyEvalAligned :
                  PolyIR.Evaluates (lowerDefinitions program)
                    (lowerEnv (bind parameters sourceArguments))
                    (lower (identities (bind parameters sourceArguments)) body) value := by
                rw [bodyEnvironmentEq, argumentsLowered, bodyTermEq]
                exact bodyEval
              obtain ⟨sourceResult, sourceBodyEval, resultLowered⟩ :=
                bodyIH (bind parameters sourceArguments) value bodyEvalAligned
              exact ⟨sourceResult,
                .appGlobal sourceFunctionEval sourceArgumentsEval definitionFound sourceArity
                  sourceBodyEval, resultLowered⟩
  | @globalApplicationBodyFirstArgument index parameters body first rest definitionFound
      _ _ restFragments bodyIH firstIH =>
      rw [lower_eq] at evaluated
      cases evaluated with
      | appClosure functionEval _ _ _ =>
          rw [lower_eq] at functionEval
          cases functionEval
      | appGlobal functionEval argumentsEval runtimeDefinitionFound argumentsArity bodyEval =>
          rename_i _runtimeIndex irArguments irDefinition
          cases functionEval with
          | global _ =>
              have sourceFunctionEval : Evaluates program environment (.global index) (.global index) :=
                .global definitionFound
              have runtimeDefinitionEq : irDefinition =
                  PolyIR.RuntimeDefinition.mk parameters.length (lower parameters body) := by
                obtain ⟨sourceParameters, sourceBody, found, definitionEq⟩ :=
                  definitions_lookup_reflects program index irDefinition runtimeDefinitionFound
                have pairEq : (sourceParameters, sourceBody) = (parameters, body) :=
                  Option.some.inj (found.symm.trans definitionFound)
                cases pairEq
                exact definitionEq
              rw [lowerMany_eq] at argumentsEval
              cases argumentsEval with
              | cons firstEval restEval =>
                  rename_i irFirst irRest
                  obtain ⟨sourceFirst, firstSourceEval, firstLowered⟩ :=
                    firstIH environment _ firstEval
                  obtain ⟨sourceRest, restSourceEval, restLowered⟩ :=
                    arithmeticFragmentList_arguments_reflected program rest restFragments
                      environment restEval
                  let sourceArguments := sourceFirst :: sourceRest
                  have sourceArgumentsEval : ArgumentsEvaluate program environment
                      (first :: rest) sourceArguments :=
                    .cons firstSourceEval restSourceEval
                  have argumentsLowered : lowerValues sourceArguments = irFirst :: irRest := by
                    change lowerValue sourceFirst :: lowerValues sourceRest = irFirst :: irRest
                    rw [firstLowered, restLowered]
                  have sourceArity : sourceArguments.length = parameters.length := by
                    calc
                      sourceArguments.length = (lowerValues sourceArguments).length := by
                        simp [lowerValues]
                      _ = _ := congrArg List.length argumentsLowered
                      _ = irDefinition.arity := argumentsArity
                      _ = parameters.length := by
                        have arityField := congrArg PolyIR.RuntimeDefinition.arity runtimeDefinitionEq
                        simpa using arityField
                  have bodyEnvironmentEq :
                      lowerEnv (bind parameters sourceArguments) = lowerValues sourceArguments :=
                    lowerEnv_bind parameters sourceArguments sourceArity
                  have bodyTermEq :
                      lower (identities (bind parameters sourceArguments)) body = irDefinition.body := by
                    rw [bind_identifiers parameters sourceArguments sourceArity]
                    have bodyField := congrArg PolyIR.RuntimeDefinition.body runtimeDefinitionEq
                    simpa using bodyField.symm
                  have bodyEvalAligned :
                      PolyIR.Evaluates (lowerDefinitions program)
                        (lowerEnv (bind parameters sourceArguments))
                        (lower (identities (bind parameters sourceArguments)) body) value := by
                    rw [bodyEnvironmentEq, argumentsLowered, bodyTermEq]
                    exact bodyEval
                  obtain ⟨sourceResult, sourceBodyEval, resultLowered⟩ :=
                    bodyIH (bind parameters sourceArguments) value bodyEvalAligned
                  exact ⟨sourceResult,
                    .appGlobal sourceFunctionEval sourceArgumentsEval definitionFound sourceArity
                      sourceBodyEval, resultLowered⟩
  | @globalApplicationRows index parameters body arguments definitionFound _ _ bodyIH rowsIH =>
      rw [lower_eq] at evaluated
      cases evaluated with
      | appClosure functionEval _ _ _ =>
          rw [lower_eq] at functionEval
          cases functionEval
      | appGlobal functionEval argumentsEval runtimeDefinitionFound argumentsArity bodyEval =>
          rename_i _runtimeIndex irArguments irDefinition
          cases functionEval with
          | global _ =>
              have sourceFunctionEval : Evaluates program environment (.global index) (.global index) :=
                .global definitionFound
              have runtimeDefinitionEq : irDefinition =
                  PolyIR.RuntimeDefinition.mk parameters.length (lower parameters body) := by
                obtain ⟨sourceParameters, sourceBody, found, definitionEq⟩ :=
                  definitions_lookup_reflects program index irDefinition runtimeDefinitionFound
                have pairEq : (sourceParameters, sourceBody) = (parameters, body) :=
                  Option.some.inj (found.symm.trans definitionFound)
                cases pairEq
                exact definitionEq
              have argumentsReflected : ∀ (expressions : List Expr),
                  (∀ expression, expression ∈ expressions → expression ∈ arguments) →
                  ∀ {irValues},
                    PolyIR.ArgumentsEvaluate (lowerDefinitions program) (lowerEnv environment)
                      (lowerMany (identities environment) expressions) irValues →
                    ∃ sourceValues, ArgumentsEvaluate program environment expressions sourceValues ∧
                      lowerValues sourceValues = irValues := by
                intro expressions
                induction expressions with
                | nil =>
                    intro _ irValues irEval
                    cases irEval
                    exact ⟨[], .nil, by simp [lowerValues]⟩
                | cons head tail ih =>
                    intro subset irValues irEval
                    rw [lowerMany_eq] at irEval
                    cases irEval with
                    | cons headEval tailEval =>
                        obtain ⟨sourceHead, headSourceEval, headLowered⟩ :=
                          rowsIH head (subset head (by simp)) environment _ headEval
                        have tailSubset : ∀ expression, expression ∈ tail → expression ∈ arguments := by
                          intro expression member
                          exact subset expression (List.mem_cons_of_mem head member)
                        obtain ⟨sourceTail, tailSourceEval, tailLowered⟩ :=
                          ih tailSubset tailEval
                        refine ⟨sourceHead :: sourceTail, .cons headSourceEval tailSourceEval, ?_⟩
                        change lowerValue sourceHead :: List.map lowerValue sourceTail = _
                        rw [headLowered]
                        simpa [lowerValues] using tailLowered
              obtain ⟨sourceArguments, sourceArgumentsEval, argumentsLowered⟩ :=
                argumentsReflected arguments (by intro argument member; exact member) argumentsEval
              have sourceArity : sourceArguments.length = parameters.length := by
                calc
                  sourceArguments.length = (lowerValues sourceArguments).length := by simp [lowerValues]
                  _ = _ := congrArg List.length argumentsLowered
                  _ = irDefinition.arity := argumentsArity
                  _ = parameters.length := by
                    have arityField := congrArg PolyIR.RuntimeDefinition.arity runtimeDefinitionEq
                    simpa using arityField
              have bodyEnvironmentEq :
                  lowerEnv (bind parameters sourceArguments) = lowerValues sourceArguments :=
                lowerEnv_bind parameters sourceArguments sourceArity
              have bodyTermEq : lower (identities (bind parameters sourceArguments)) body =
                  irDefinition.body := by
                rw [bind_identifiers parameters sourceArguments sourceArity]
                have bodyField := congrArg PolyIR.RuntimeDefinition.body runtimeDefinitionEq
                simpa using bodyField.symm
              have bodyEvalAligned :
                  PolyIR.Evaluates (lowerDefinitions program)
                    (lowerEnv (bind parameters sourceArguments))
                    (lower (identities (bind parameters sourceArguments)) body) value := by
                rw [bodyEnvironmentEq, argumentsLowered, bodyTermEq]
                exact bodyEval
              obtain ⟨sourceResult, sourceBodyEval, resultLowered⟩ :=
                bodyIH (bind parameters sourceArguments) value bodyEvalAligned
              exact ⟨sourceResult,
                .appGlobal sourceFunctionEval sourceArgumentsEval definitionFound sourceArity
                  sourceBodyEval, resultLowered⟩
  | @someChild child _ childIH =>
      exact some_evaluation_reflected program environment child
        (fun {innerValue} innerEval => childIH environment innerValue innerEval) value evaluated
  | @consChildren head tail _ _ headIH tailIH =>
      exact cons_evaluation_reflected program environment head tail
        (fun {headValue} headEval => headIH environment headValue headEval)
        (fun {tailValue} tailEval => tailIH environment tailValue tailEval) value evaluated
  | @floatBinChildren operation left right _ _ leftIH rightIH =>
      exact floatBin_evaluation_reflected program environment operation left right
        (fun {leftValue} leftEval => leftIH environment leftValue leftEval)
        (fun {rightValue} rightEval => rightIH environment rightValue rightEval)
        value evaluated
  | @addChildren left right _ _ leftIH rightIH =>
      exact add_evaluation_reflected program environment left right
        (fun {leftValue} leftEval => leftIH environment leftValue leftEval)
        (fun {rightValue} rightEval => rightIH environment rightValue rightEval)
        value evaluated
  | @subChildren left right _ _ leftIH rightIH =>
      exact sub_evaluation_reflected program environment left right
        (fun {leftValue} leftEval => leftIH environment leftValue leftEval)
        (fun {rightValue} rightEval => rightIH environment rightValue rightEval)
        value evaluated
  | @mulChildren left right _ _ leftIH rightIH =>
      exact mul_evaluation_reflected program environment left right
        (fun {leftValue} leftEval => leftIH environment leftValue leftEval)
        (fun {rightValue} rightEval => rightIH environment rightValue rightEval)
        value evaluated
  | @leChildren left right _ _ leftIH rightIH =>
      exact le_evaluation_reflected program environment left right
        (fun {leftValue} leftEval => leftIH environment leftValue leftEval)
        (fun {rightValue} rightEval => rightIH environment rightValue rightEval)
        value evaluated
  | @intEqChildren left right _ _ leftIH rightIH =>
      exact intEq_evaluation_reflected program environment left right
        (fun {leftValue} leftEval => leftIH environment leftValue leftEval)
        (fun {rightValue} rightEval => rightIH environment rightValue rightEval)
        value evaluated
  | @iteChildren condition yes no _ _ _ conditionIH yesIH noIH =>
      exact ite_evaluation_reflected program environment condition yes no
        (fun {conditionValue} conditionEval => conditionIH environment conditionValue conditionEval)
        (fun {yesValue} yesEval => yesIH environment yesValue yesEval)
        (fun {noValue} noEval => noIH environment noValue noEval) value evaluated
  | @matchOptionChildren target empty binder full _ _ _ targetIH emptyIH fullIH =>
      exact matchOption_evaluation_reflected program environment target empty binder full
        (fun {targetValue} targetEval => targetIH environment targetValue targetEval)
        (fun {emptyValue} emptyEval => emptyIH environment emptyValue emptyEval)
        (fun sourceItem irItem sourceLower {bodyValue} bodyEval => by
          exact fullIH ((binder, sourceItem) :: environment) bodyValue (by
            simpa [identities, lowerEnv, sourceLower] using bodyEval))
        value evaluated
  | @matchListChildren target empty headBinder tailBinder full _ _ _ targetIH emptyIH fullIH =>
      exact matchList_evaluation_reflected program environment target empty headBinder tailBinder full
        (fun {targetValue} targetEval => targetIH environment targetValue targetEval)
        (fun {emptyValue} emptyEval => emptyIH environment emptyValue emptyEval)
        (fun sourceHead sourceTail irHead irTail headLower tailLower {bodyValue} bodyEval => by
          exact fullIH
            ((headBinder, sourceHead) :: (tailBinder, sourceTail) :: environment)
            bodyValue (by
              simpa [identities, lowerEnv, headLower, tailLower] using bodyEval))
        value evaluated

theorem compositionalReflectionRows_arguments_reflected (program : Definitions)
    (environment : Environment) (expressions : List Expr)
    (rows : CompositionalReflectionRows program expressions) :
    ∀ {irValues},
      PolyIR.ArgumentsEvaluate (lowerDefinitions program) (lowerEnv environment)
        (lowerMany (identities environment) expressions) irValues →
      ∃ sourceValues, ArgumentsEvaluate program environment expressions sourceValues ∧
        lowerValues sourceValues = irValues := by
  induction expressions with
  | nil =>
      intro irValues evaluated
      cases evaluated
      exact ⟨[], .nil, by simp [lowerValues]⟩
  | cons head tail ih =>
      intro irValues evaluated
      rw [lowerMany_eq] at evaluated
      cases evaluated with
      | cons headEval tailEval =>
          obtain ⟨sourceHead, headSourceEval, headLowered⟩ :=
            compositionalReflection_evaluation_reflected program (rows head (by simp))
              environment _ headEval
          have tailRows : CompositionalReflectionRows program tail := by
            intro expression member
            exact rows expression (List.mem_cons_of_mem head member)
          obtain ⟨sourceTail, tailSourceEval, tailLowered⟩ := ih tailRows tailEval
          exact ⟨sourceHead :: sourceTail, .cons headSourceEval tailSourceEval, by
            change lowerValue sourceHead :: lowerValues sourceTail = _
            rw [headLowered, tailLowered]⟩

/-- Reflection for an application whose callee is computed by an arbitrary
compositional expression and evaluates to a closure.  The closure's body may
be any compositional expression and its captured IR environment need not be
the caller environment. -/
theorem compositionalReflection_computedClosureApplication_reflected
    (program : Definitions) (environment : Environment)
    (function : Expr) (arguments : List Expr)
    (functionFragment : CompositionalReflectionFragment program function)
    (argumentsFragments : CompositionalReflectionRows program arguments)
    (arity : Nat) (bodyIR : PolyIR.Term) (capturedIR : List PolyIR.Value)
    (bodyFragment : ∀ parameters sourceBody captured,
      lowerValue (.closure parameters sourceBody captured) =
        .closure arity bodyIR capturedIR →
      CompositionalReflectionFragment program sourceBody)
    (functionSuccess : PolyIR.Evaluates (lowerDefinitions program) (lowerEnv environment)
      (lower (identities environment) function) (.closure arity bodyIR capturedIR))
    (result : PolyIR.Value)
    (evaluated : PolyIR.Evaluates (lowerDefinitions program) (lowerEnv environment)
      (lower (identities environment) (.app function arguments)) result) :
    ∃ sourceResult, Evaluates program environment (.app function arguments) sourceResult ∧
      lowerValue sourceResult = result := by
  rw [lower_eq] at evaluated functionSuccess
  cases evaluated with
  | appClosure functionEval argumentsEval argumentArity bodyEval =>
      have closureValueEq := PolyIR.evaluation_deterministic functionSuccess
        (by simpa only [← lower_eq] using functionEval)
      cases closureValueEq
      obtain ⟨sourceFunction, sourceFunctionEval, functionLowered⟩ :=
        compositionalReflection_evaluation_reflected program functionFragment
          environment (.closure arity bodyIR capturedIR) functionEval
      cases sourceFunction with
      | closure parameters sourceBody captured =>
          have sourceBodyFragment := bodyFragment parameters sourceBody captured functionLowered
          simp only [lowerValue] at functionLowered
          injection functionLowered with arityEq bodyEq capturedEq
          obtain ⟨sourceArguments, sourceArgumentsEval, argumentsLowered⟩ :=
            compositionalReflectionRows_arguments_reflected program environment arguments
              argumentsFragments argumentsEval
          have sourceArity : sourceArguments.length = parameters.length := by
            calc
              sourceArguments.length = (lowerValues sourceArguments).length := by simp [lowerValues]
              _ = _ := congrArg List.length argumentsLowered
              _ = arity := argumentArity
              _ = parameters.length := arityEq.symm
          have bodyEnvironmentEq :
              lowerEnv (bind parameters sourceArguments ++ captured) =
                lowerValues sourceArguments ++ lowerEnv captured := by
            rw [lowerEnv_bind_append parameters sourceArguments captured sourceArity]
          have bodyLocalsEq :
              identities (bind parameters sourceArguments ++ captured) =
                parameters ++ identities captured :=
            identities_bind_append parameters sourceArguments captured sourceArity
          have bodyEvalAligned :
              PolyIR.Evaluates (lowerDefinitions program)
                (lowerEnv (bind parameters sourceArguments ++ captured))
                (lower (identities (bind parameters sourceArguments ++ captured)) sourceBody)
                result := by
            rw [bodyEnvironmentEq, argumentsLowered, capturedEq, bodyLocalsEq, bodyEq]
            exact bodyEval
          obtain ⟨sourceResult, sourceBodyEval, resultLowered⟩ :=
            compositionalReflection_evaluation_reflected program
              sourceBodyFragment (bind parameters sourceArguments ++ captured)
              result bodyEvalAligned
          exact ⟨sourceResult,
            .appClosure sourceFunctionEval sourceArgumentsEval sourceArity sourceBodyEval,
            resultLowered⟩
      | _ => simp [lowerValue] at functionLowered
  | appGlobal functionEval _ _ _ _ =>
      have impossible := PolyIR.evaluation_deterministic functionSuccess
        (by simpa only [← lower_eq] using functionEval)
      cases impossible

/-- Reflection for an application whose computed callee evaluates to a
global function value. This complements the computed-closure case and
constructs the Named `appGlobal` derivation from the evaluated callee,
argument rows, runtime definition layout, and compositional body reflection.
-/
theorem compositionalReflection_computedGlobalApplication_reflected
    (program : Definitions) (environment : Environment)
    (function : Expr) (arguments : List Expr)
    (functionFragment : CompositionalReflectionFragment program function)
    (argumentsFragments : CompositionalReflectionRows program arguments)
    (index : Nat) (parameters : List Nat) (body : Expr)
    (definitionFound : program[index]? = some (parameters, body))
    (bodyFragment : CompositionalReflectionFragment program body)
    (functionSuccess : PolyIR.Evaluates (lowerDefinitions program) (lowerEnv environment)
      (lower (identities environment) function) (.global index))
    (result : PolyIR.Value)
    (evaluated : PolyIR.Evaluates (lowerDefinitions program) (lowerEnv environment)
      (lower (identities environment) (.app function arguments)) result) :
    ∃ sourceResult, Evaluates program environment (.app function arguments) sourceResult ∧
      lowerValue sourceResult = result := by
  rw [lower_eq] at evaluated functionSuccess
  cases evaluated with
  | appClosure functionEval _ _ _ =>
      have impossible := PolyIR.evaluation_deterministic functionSuccess
        (by simpa only [← lower_eq] using functionEval)
      cases impossible
  | appGlobal functionEval argumentsEval runtimeDefinitionFound argumentsArity bodyEval =>
      rename_i _runtimeIndex _irArguments irDefinition
      have functionValueEq := PolyIR.evaluation_deterministic functionSuccess
        (by simpa only [← lower_eq] using functionEval)
      cases functionValueEq
      obtain ⟨sourceFunction, sourceFunctionEval, functionLowered⟩ :=
        compositionalReflection_evaluation_reflected program functionFragment environment
          (.global index) functionEval
      have sourceFunctionEq : sourceFunction = .global index := by
        cases sourceFunction with
        | global sourceIndex =>
            have sourceIndexEq : sourceIndex = index := by
              have mappedEq : PolyIR.Value.global sourceIndex = PolyIR.Value.global index := by
                simpa [lowerValue] using functionLowered
              injection mappedEq
            subst sourceIndex
            rfl
        | _ => simp [lowerValue] at functionLowered
      subst sourceFunction
      obtain ⟨sourceArguments, sourceArgumentsEval, argumentsLowered⟩ :=
        compositionalReflectionRows_arguments_reflected program environment arguments
          argumentsFragments argumentsEval
      obtain ⟨sourceParameters, sourceBody, sourceDefinitionFound, runtimeDefinitionEq⟩ :=
        definitions_lookup_reflects program index irDefinition runtimeDefinitionFound
      have pairEq : (sourceParameters, sourceBody) = (parameters, body) :=
        Option.some.inj (sourceDefinitionFound.symm.trans definitionFound)
      cases pairEq
      have sourceArity : sourceArguments.length = parameters.length := by
        calc
          sourceArguments.length = (lowerValues sourceArguments).length := by simp [lowerValues]
          _ = _ := congrArg List.length argumentsLowered
          _ = irDefinition.arity := argumentsArity
          _ = parameters.length := by
            have arityField := congrArg PolyIR.RuntimeDefinition.arity runtimeDefinitionEq
            simpa using arityField
      have bodyEnvironmentEq :
          lowerEnv (bind parameters sourceArguments) = lowerValues sourceArguments :=
        lowerEnv_bind parameters sourceArguments sourceArity
      have bodyTermEq :
          lower (identities (bind parameters sourceArguments)) body =
            irDefinition.body := by
        rw [bind_identifiers parameters sourceArguments sourceArity]
        have bodyField := congrArg PolyIR.RuntimeDefinition.body runtimeDefinitionEq
        simpa using bodyField.symm
      have bodyEvalAligned :
          PolyIR.Evaluates (lowerDefinitions program)
            (lowerEnv (bind parameters sourceArguments))
            (lower (identities (bind parameters sourceArguments)) body) result := by
        rw [bodyEnvironmentEq, argumentsLowered, bodyTermEq]
        exact bodyEval
      obtain ⟨sourceResult, sourceBodyEval, resultLowered⟩ :=
        compositionalReflection_evaluation_reflected program bodyFragment
          (bind parameters sourceArguments) result bodyEvalAligned
      exact ⟨sourceResult,
        .appGlobal sourceFunctionEval sourceArgumentsEval definitionFound sourceArity sourceBodyEval,
        resultLowered⟩

/-- Dispatch reflection for a computed callee that may evaluate either to a
closure or to a global function. The contracts state that every callable
body reached at this site belongs to the compositional reflection fragment;
the evaluator derivation then selects the matching closure/global proof. -/
theorem compositionalReflection_computedCallableApplication_reflected
    (program : Definitions) (environment : Environment)
    (function : Expr) (arguments : List Expr)
    (functionFragment : CompositionalReflectionFragment program function)
    (argumentsFragments : CompositionalReflectionRows program arguments)
    (globalBodies : ∀ (index : Nat) (parameters : List Nat) (body : Expr),
      program[index]? = some (parameters, body) →
        CompositionalReflectionFragment program body)
    (closureBodies : ∀ (arity : Nat) (bodyIR : PolyIR.Term)
      (capturedIR : List PolyIR.Value) (parameters : List Nat)
      (sourceBody : Expr) (captured : Environment),
      lowerValue (.closure parameters sourceBody captured) =
        .closure arity bodyIR capturedIR →
        CompositionalReflectionFragment program sourceBody)
    (result : PolyIR.Value)
    (evaluated : PolyIR.Evaluates (lowerDefinitions program) (lowerEnv environment)
      (lower (identities environment) (.app function arguments)) result) :
    ∃ sourceResult, Evaluates program environment (.app function arguments) sourceResult ∧
      lowerValue sourceResult = result := by
  rw [lower_eq] at evaluated
  cases evaluated with
  | appClosure functionEval argumentsEval argumentsArity bodyEval =>
      exact compositionalReflection_computedClosureApplication_reflected program environment
        function arguments functionFragment argumentsFragments _ _ _
        (fun parameters sourceBody captured closureEq =>
          closureBodies _ _ _ parameters sourceBody captured closureEq)
        functionEval result
        (PolyIR.Evaluates.appClosure functionEval argumentsEval argumentsArity bodyEval)
  | appGlobal functionEval argumentsEval runtimeFound argumentsArity bodyEval =>
      obtain ⟨parameters, body, definitionFound, _runtimeDefinitionEq⟩ :=
        definitions_lookup_reflects program _ _ runtimeFound
      exact compositionalReflection_computedGlobalApplication_reflected program environment
        function arguments functionFragment argumentsFragments _ parameters body
        definitionFound (globalBodies _ parameters body definitionFound) functionEval
        result (PolyIR.Evaluates.appGlobal functionEval argumentsEval runtimeFound
          argumentsArity bodyEval)

theorem compositionalReflection_computedCallableApplication_localBodies_termination_iff
    (program : Definitions) (environment : Environment)
    (function : Expr) (arguments : List Expr)
    (functionFragment : CompositionalReflectionFragment program function)
    (argumentsFragments : CompositionalReflectionRows program arguments)
    (globalBodies : ∀ (index : Nat) (parameters : List Nat) (body : Expr),
      program[index]? = some (parameters, body) →
        CompositionalReflectionFragment program body)
    (closureBodies : ∀ (arity : Nat) (bodyIR : PolyIR.Term)
      (capturedIR : List PolyIR.Value) (parameters : List Nat)
      (sourceBody : Expr) (captured : Environment),
      lowerValue (.closure parameters sourceBody captured) =
        .closure arity bodyIR capturedIR →
        CompositionalReflectionFragment program sourceBody) :
    SourceTerminates program environment (.app function arguments) ↔
      LoweredTerminates program environment (.app function arguments) := by
  constructor
  · rintro ⟨sourceValue, sourceEval⟩
    exact ⟨lowerValue sourceValue, evaluation_preserved sourceEval⟩
  · rintro ⟨irValue, irEval⟩
    obtain ⟨sourceValue, sourceEval, _⟩ :=
      compositionalReflection_computedCallableApplication_reflected program environment
        function arguments functionFragment argumentsFragments globalBodies closureBodies
        irValue irEval
    exact ⟨sourceValue, sourceEval⟩

 theorem compositionalReflection_computedCallableApplication_localBodies_divergence_iff
    (program : Definitions) (environment : Environment)
    (function : Expr) (arguments : List Expr)
    (functionFragment : CompositionalReflectionFragment program function)
    (argumentsFragments : CompositionalReflectionRows program arguments)
    (globalBodies : ∀ (index : Nat) (parameters : List Nat) (body : Expr),
      program[index]? = some (parameters, body) →
        CompositionalReflectionFragment program body)
    (closureBodies : ∀ (arity : Nat) (bodyIR : PolyIR.Term)
      (capturedIR : List PolyIR.Value) (parameters : List Nat)
      (sourceBody : Expr) (captured : Environment),
      lowerValue (.closure parameters sourceBody captured) =
        .closure arity bodyIR capturedIR →
        CompositionalReflectionFragment program sourceBody) :
    SourceDiverges program environment (.app function arguments) ↔
      LoweredDiverges program environment (.app function arguments) :=
  not_congr (compositionalReflection_computedCallableApplication_localBodies_termination_iff
    program environment function arguments functionFragment argumentsFragments globalBodies
    closureBodies)

theorem compositionalReflection_computedCallableApplication_localBodies_reflected_scoped
    (program : Definitions) (programScoped : programWellScoped program)
    (environment : Environment) (environmentScoped : environmentWellScoped environment)
    (function : Expr) (arguments : List Expr)
    (functionFragment : CompositionalReflectionFragment program function)
    (argumentsFragments : CompositionalReflectionRows program arguments)
    (globalBodies : ∀ (index : Nat) (parameters : List Nat) (body : Expr),
      program[index]? = some (parameters, body) →
        CompositionalReflectionFragment program body)
    (closureBodies : ∀ (arity : Nat) (bodyIR : PolyIR.Term)
      (capturedIR : List PolyIR.Value) (parameters : List Nat)
      (sourceBody : Expr) (captured : Environment),
      lowerValue (.closure parameters sourceBody captured) =
        .closure arity bodyIR capturedIR →
        CompositionalReflectionFragment program sourceBody)
    (result : PolyIR.Value)
    (evaluated : PolyIR.Evaluates (lowerDefinitions program) (lowerEnv environment)
      (lower (identities environment) (.app function arguments)) result)
    (aligned : letLayoutsAligned (.app function arguments) = true) :
    ∃ sourceResult, Evaluates program environment (.app function arguments) sourceResult ∧
      lowerValue sourceResult = result ∧ valueWellScoped sourceResult := by
  obtain ⟨sourceResult, sourceEval, loweredEq⟩ :=
    compositionalReflection_computedCallableApplication_reflected program environment
      function arguments functionFragment argumentsFragments globalBodies closureBodies
      result evaluated
  have resultScoped := evaluation_preserves_valueWellScoped program programScoped
    sourceEval environmentScoped aligned
  exact ⟨sourceResult, sourceEval, loweredEq, resultScoped⟩

theorem compositionalReflection_computedGlobalApplication_termination_iff
    (program : Definitions) (environment : Environment)
    (function : Expr) (arguments : List Expr)
    (functionFragment : CompositionalReflectionFragment program function)
    (argumentsFragments : CompositionalReflectionRows program arguments)
    (index : Nat) (parameters : List Nat) (body : Expr)
    (definitionFound : program[index]? = some (parameters, body))
    (bodyFragment : CompositionalReflectionFragment program body)
    (functionSuccess : PolyIR.Evaluates (lowerDefinitions program) (lowerEnv environment)
      (lower (identities environment) function) (.global index)) :
    SourceTerminates program environment (.app function arguments) ↔
      LoweredTerminates program environment (.app function arguments) := by
  constructor
  · rintro ⟨sourceValue, sourceEvaluation⟩
    exact ⟨lowerValue sourceValue, evaluation_preserved sourceEvaluation⟩
  · rintro ⟨result, evaluated⟩
    obtain ⟨sourceResult, sourceEvaluation, _⟩ :=
      compositionalReflection_computedGlobalApplication_reflected program environment function
        arguments functionFragment argumentsFragments index parameters body definitionFound
        bodyFragment functionSuccess result evaluated
    exact ⟨sourceResult, sourceEvaluation⟩

theorem compositionalReflection_computedGlobalApplication_divergence_iff
    (program : Definitions) (environment : Environment)
    (function : Expr) (arguments : List Expr)
    (functionFragment : CompositionalReflectionFragment program function)
    (argumentsFragments : CompositionalReflectionRows program arguments)
    (index : Nat) (parameters : List Nat) (body : Expr)
    (definitionFound : program[index]? = some (parameters, body))
    (bodyFragment : CompositionalReflectionFragment program body)
    (functionSuccess : PolyIR.Evaluates (lowerDefinitions program) (lowerEnv environment)
      (lower (identities environment) function) (.global index)) :
    SourceDiverges program environment (.app function arguments) ↔
      LoweredDiverges program environment (.app function arguments) :=
  not_congr (compositionalReflection_computedGlobalApplication_termination_iff program
    environment function arguments functionFragment argumentsFragments index parameters body
    definitionFound bodyFragment functionSuccess)

theorem compositionalReflection_computedGlobalApplication_reflected_scoped
    (program : Definitions) (programScoped : programWellScoped program)
    (environment : Environment) (environmentScoped : environmentWellScoped environment)
    (function : Expr) (arguments : List Expr)
    (functionFragment : CompositionalReflectionFragment program function)
    (argumentsFragments : CompositionalReflectionRows program arguments)
    (index : Nat) (parameters : List Nat) (body : Expr)
    (definitionFound : program[index]? = some (parameters, body))
    (bodyFragment : CompositionalReflectionFragment program body)
    (functionSuccess : PolyIR.Evaluates (lowerDefinitions program) (lowerEnv environment)
      (lower (identities environment) function) (.global index))
    (result : PolyIR.Value)
    (evaluated : PolyIR.Evaluates (lowerDefinitions program) (lowerEnv environment)
      (lower (identities environment) (.app function arguments)) result)
    (aligned : letLayoutsAligned (.app function arguments) = true) :
    ∃ sourceResult, Evaluates program environment (.app function arguments) sourceResult ∧
      lowerValue sourceResult = result ∧ valueWellScoped sourceResult := by
  obtain ⟨sourceResult, sourceEvaluation, loweredEq⟩ :=
    compositionalReflection_computedGlobalApplication_reflected program environment function
      arguments functionFragment argumentsFragments index parameters body definitionFound
      bodyFragment functionSuccess result evaluated
  have resultScoped := evaluation_preserves_valueWellScoped program programScoped
    sourceEvaluation environmentScoped aligned
  exact ⟨sourceResult, sourceEvaluation, loweredEq, resultScoped⟩

theorem compositionalReflection_computedGlobalApplication_reflected_identityScoped
    (program : Definitions) (programScoped : programIdentityScoped program)
    (environment : Environment) (environmentScoped : EnvironmentIdentityScoped environment)
    (function : Expr) (arguments : List Expr)
    (functionFragment : CompositionalReflectionFragment program function)
    (argumentsFragments : CompositionalReflectionRows program arguments)
    (index : Nat) (parameters : List Nat) (body : Expr)
    (definitionFound : program[index]? = some (parameters, body))
    (bodyFragment : CompositionalReflectionFragment program body)
    (expressionScoped : IdentityScoped (identities environment)
      (.app function arguments))
    (functionSuccess : PolyIR.Evaluates (lowerDefinitions program) (lowerEnv environment)
      (lower (identities environment) function) (.global index))
    (result : PolyIR.Value)
    (evaluated : PolyIR.Evaluates (lowerDefinitions program) (lowerEnv environment)
      (lower (identities environment) (.app function arguments)) result) :
    ∃ sourceResult, Evaluates program environment (.app function arguments) sourceResult ∧
      lowerValue sourceResult = result ∧ ValueIdentityScoped sourceResult := by
  obtain ⟨sourceResult, sourceEvaluation, loweredEq⟩ :=
    compositionalReflection_computedGlobalApplication_reflected program environment function
      arguments functionFragment argumentsFragments index parameters body definitionFound
      bodyFragment functionSuccess result evaluated
  have sourceScoped := evaluation_preserves_valueIdentityScoped program programScoped
    sourceEvaluation environmentScoped expressionScoped
  exact ⟨sourceResult, sourceEvaluation, loweredEq, sourceScoped⟩

theorem decodeExprChecked_compositionalReflection_computedGlobalApplication_reflected_scoped
    {fuel : Nat} {headers : List ExpansionLowering.Header} {node : CBindingWalk.Node}
    {function : Expr} {arguments : List Expr}
    (decoded : NLisp.Named.decodeExprChecked fuel headers node =
      some (.app function arguments))
    (program : Definitions) (programScoped : programWellScoped program)
    (environment : Environment) (environmentScoped : environmentWellScoped environment)
    (functionFragment : CompositionalReflectionFragment program function)
    (argumentsFragments : CompositionalReflectionRows program arguments)
    (index : Nat) (parameters : List Nat) (body : Expr)
    (definitionFound : program[index]? = some (parameters, body))
    (bodyFragment : CompositionalReflectionFragment program body)
    (functionSuccess : PolyIR.Evaluates (lowerDefinitions program) (lowerEnv environment)
      (lower (identities environment) function) (.global index))
    (result : PolyIR.Value)
    (evaluated : PolyIR.Evaluates (lowerDefinitions program) (lowerEnv environment)
      (lower (identities environment) (.app function arguments)) result) :
    ∃ sourceResult, Evaluates program environment (.app function arguments) sourceResult ∧
      lowerValue sourceResult = result ∧ valueWellScoped sourceResult := by
  exact compositionalReflection_computedGlobalApplication_reflected_scoped program programScoped
    environment environmentScoped function arguments functionFragment argumentsFragments index
    parameters body definitionFound bodyFragment functionSuccess result evaluated
    (NLisp.Named.decodeExprChecked_spec decoded).2

theorem decodeExprChecked_compositionalReflection_computedGlobalApplication_termination_iff
    {fuel : Nat} {headers : List ExpansionLowering.Header} {node : CBindingWalk.Node}
    {function : Expr} {arguments : List Expr}
    (decoded : NLisp.Named.decodeExprChecked fuel headers node =
      some (.app function arguments))
    (program : Definitions) (environment : Environment)
    (functionFragment : CompositionalReflectionFragment program function)
    (argumentsFragments : CompositionalReflectionRows program arguments)
    (index : Nat) (parameters : List Nat) (body : Expr)
    (definitionFound : program[index]? = some (parameters, body))
    (bodyFragment : CompositionalReflectionFragment program body)
    (functionSuccess : PolyIR.Evaluates (lowerDefinitions program) (lowerEnv environment)
      (lower (identities environment) function) (.global index)) :
    (SourceTerminates program environment (.app function arguments) ↔
      LoweredTerminates program environment (.app function arguments)) ∧
      letLayoutsAligned (.app function arguments) = true := by
  exact ⟨compositionalReflection_computedGlobalApplication_termination_iff program environment
      function arguments functionFragment argumentsFragments index parameters body definitionFound
      bodyFragment functionSuccess,
    (NLisp.Named.decodeExprChecked_spec decoded).2⟩

theorem decodeExprChecked_compositionalReflection_computedGlobalApplication_divergence_iff
    {fuel : Nat} {headers : List ExpansionLowering.Header} {node : CBindingWalk.Node}
    {function : Expr} {arguments : List Expr}
    (decoded : NLisp.Named.decodeExprChecked fuel headers node =
      some (.app function arguments))
    (program : Definitions) (environment : Environment)
    (functionFragment : CompositionalReflectionFragment program function)
    (argumentsFragments : CompositionalReflectionRows program arguments)
    (index : Nat) (parameters : List Nat) (body : Expr)
    (definitionFound : program[index]? = some (parameters, body))
    (bodyFragment : CompositionalReflectionFragment program body)
    (functionSuccess : PolyIR.Evaluates (lowerDefinitions program) (lowerEnv environment)
      (lower (identities environment) function) (.global index)) :
    SourceDiverges program environment (.app function arguments) ↔
      LoweredDiverges program environment (.app function arguments) :=
  compositionalReflection_computedGlobalApplication_divergence_iff program environment function
    arguments functionFragment argumentsFragments index parameters body definitionFound
    bodyFragment functionSuccess

/-- The computed-closure application theorem also preserves the recursive
well-scopedness invariant of its result under the checked-program and
checked-environment assumptions. -/
theorem compositionalReflection_computedClosureApplication_reflected_scoped
    (program : Definitions) (programScoped : programWellScoped program)
    (environment : Environment) (environmentScoped : environmentWellScoped environment)
    (function : Expr) (arguments : List Expr)
    (functionFragment : CompositionalReflectionFragment program function)
    (argumentsFragments : CompositionalReflectionRows program arguments)
    (arity : Nat) (bodyIR : PolyIR.Term) (capturedIR : List PolyIR.Value)
    (bodyFragment : ∀ parameters sourceBody captured,
      lowerValue (.closure parameters sourceBody captured) =
        .closure arity bodyIR capturedIR →
      CompositionalReflectionFragment program sourceBody)
    (functionSuccess : PolyIR.Evaluates (lowerDefinitions program) (lowerEnv environment)
      (lower (identities environment) function) (.closure arity bodyIR capturedIR))
    (result : PolyIR.Value)
    (evaluated : PolyIR.Evaluates (lowerDefinitions program) (lowerEnv environment)
      (lower (identities environment) (.app function arguments)) result)
    (aligned : letLayoutsAligned (.app function arguments) = true) :
    ∃ sourceResult, Evaluates program environment (.app function arguments) sourceResult ∧
      lowerValue sourceResult = result ∧ valueWellScoped sourceResult := by
  obtain ⟨sourceResult, sourceEvaluation, loweredEq⟩ :=
    compositionalReflection_computedClosureApplication_reflected program environment
      function arguments functionFragment argumentsFragments arity bodyIR capturedIR
      bodyFragment functionSuccess result evaluated
  have resultScoped := evaluation_preserves_valueWellScoped program programScoped
    sourceEvaluation environmentScoped aligned
  exact ⟨sourceResult, sourceEvaluation, loweredEq, resultScoped⟩

/-- A checked C-node decode supplies layout alignment for the computed-
closure application theorem and therefore needs no separate binder-count
proof from its caller. -/
theorem decodeExprChecked_compositionalReflection_computedClosureApplication_reflected_scoped
    {fuel : Nat} {headers : List ExpansionLowering.Header} {node : CBindingWalk.Node}
    {function : Expr} {arguments : List Expr}
    (decoded : NLisp.Named.decodeExprChecked fuel headers node =
      some (.app function arguments))
    (program : Definitions) (programScoped : programWellScoped program)
    (environment : Environment) (environmentScoped : environmentWellScoped environment)
    (functionFragment : CompositionalReflectionFragment program function)
    (argumentsFragments : CompositionalReflectionRows program arguments)
    (arity : Nat) (bodyIR : PolyIR.Term) (capturedIR : List PolyIR.Value)
    (bodyFragment : ∀ parameters sourceBody captured,
      lowerValue (.closure parameters sourceBody captured) =
        .closure arity bodyIR capturedIR →
      CompositionalReflectionFragment program sourceBody)
    (functionSuccess : PolyIR.Evaluates (lowerDefinitions program) (lowerEnv environment)
      (lower (identities environment) function) (.closure arity bodyIR capturedIR))
    (result : PolyIR.Value)
    (evaluated : PolyIR.Evaluates (lowerDefinitions program) (lowerEnv environment)
      (lower (identities environment) (.app function arguments)) result) :
    ∃ sourceResult, Evaluates program environment (.app function arguments) sourceResult ∧
      lowerValue sourceResult = result ∧ valueWellScoped sourceResult := by
  exact compositionalReflection_computedClosureApplication_reflected_scoped
    program programScoped environment environmentScoped function arguments functionFragment
    argumentsFragments arity bodyIR capturedIR bodyFragment functionSuccess result evaluated
    (NLisp.Named.decodeExprChecked_spec decoded).2

/-- Finite termination equivalence for a computed-closure application. -/
theorem compositionalReflection_computedClosureApplication_termination_iff
    (program : Definitions) (environment : Environment)
    (function : Expr) (arguments : List Expr)
    (functionFragment : CompositionalReflectionFragment program function)
    (argumentsFragments : CompositionalReflectionRows program arguments)
    (arity : Nat) (bodyIR : PolyIR.Term) (capturedIR : List PolyIR.Value)
    (bodyFragment : ∀ parameters sourceBody captured,
      lowerValue (.closure parameters sourceBody captured) =
        .closure arity bodyIR capturedIR →
      CompositionalReflectionFragment program sourceBody)
    (functionSuccess : PolyIR.Evaluates (lowerDefinitions program) (lowerEnv environment)
      (lower (identities environment) function) (.closure arity bodyIR capturedIR)) :
    SourceTerminates program environment (.app function arguments) ↔
      LoweredTerminates program environment (.app function arguments) := by
  constructor
  · rintro ⟨sourceValue, sourceEvaluation⟩
    exact ⟨lowerValue sourceValue, evaluation_preserved sourceEvaluation⟩
  · rintro ⟨result, evaluated⟩
    obtain ⟨sourceResult, sourceEvaluation, _⟩ :=
      compositionalReflection_computedClosureApplication_reflected program environment
        function arguments functionFragment argumentsFragments arity bodyIR capturedIR
        bodyFragment functionSuccess result evaluated
    exact ⟨sourceResult, sourceEvaluation⟩

/-- Absence of every finite big-step result is equivalent for the same
computed-closure application fragment. -/
theorem compositionalReflection_computedClosureApplication_divergence_iff
    (program : Definitions) (environment : Environment)
    (function : Expr) (arguments : List Expr)
    (functionFragment : CompositionalReflectionFragment program function)
    (argumentsFragments : CompositionalReflectionRows program arguments)
    (arity : Nat) (bodyIR : PolyIR.Term) (capturedIR : List PolyIR.Value)
    (bodyFragment : ∀ parameters sourceBody captured,
      lowerValue (.closure parameters sourceBody captured) =
        .closure arity bodyIR capturedIR →
      CompositionalReflectionFragment program sourceBody)
    (functionSuccess : PolyIR.Evaluates (lowerDefinitions program) (lowerEnv environment)
      (lower (identities environment) function) (.closure arity bodyIR capturedIR)) :
    SourceDiverges program environment (.app function arguments) ↔
      LoweredDiverges program environment (.app function arguments) :=
  not_congr (compositionalReflection_computedClosureApplication_termination_iff
    program environment function arguments functionFragment argumentsFragments arity bodyIR
    capturedIR bodyFragment functionSuccess)

/-- Checked decoding preserves finite termination equivalence for the
computed-closure application fragment and returns the layout invariant used
by the source evaluator. -/
theorem decodeExprChecked_compositionalReflection_computedClosureApplication_termination_iff
    {fuel : Nat} {headers : List ExpansionLowering.Header} {node : CBindingWalk.Node}
    {function : Expr} {arguments : List Expr}
    (decoded : NLisp.Named.decodeExprChecked fuel headers node =
      some (.app function arguments))
    (program : Definitions) (environment : Environment)
    (functionFragment : CompositionalReflectionFragment program function)
    (argumentsFragments : CompositionalReflectionRows program arguments)
    (arity : Nat) (bodyIR : PolyIR.Term) (capturedIR : List PolyIR.Value)
    (bodyFragment : ∀ parameters sourceBody captured,
      lowerValue (.closure parameters sourceBody captured) =
        .closure arity bodyIR capturedIR →
      CompositionalReflectionFragment program sourceBody)
    (functionSuccess : PolyIR.Evaluates (lowerDefinitions program) (lowerEnv environment)
      (lower (identities environment) function) (.closure arity bodyIR capturedIR)) :
    (SourceTerminates program environment (.app function arguments) ↔
      LoweredTerminates program environment (.app function arguments)) ∧
      letLayoutsAligned (.app function arguments) = true := by
  exact ⟨compositionalReflection_computedClosureApplication_termination_iff program
      environment function arguments functionFragment argumentsFragments arity bodyIR
      capturedIR bodyFragment functionSuccess,
    (NLisp.Named.decodeExprChecked_spec decoded).2⟩

/-- Checked decoding also transfers finite-big-step divergence for the
computed-closure application fragment. -/
theorem decodeExprChecked_compositionalReflection_computedClosureApplication_divergence_iff
    {fuel : Nat} {headers : List ExpansionLowering.Header} {node : CBindingWalk.Node}
    {function : Expr} {arguments : List Expr}
    (decoded : NLisp.Named.decodeExprChecked fuel headers node =
      some (.app function arguments))
    (program : Definitions) (environment : Environment)
    (functionFragment : CompositionalReflectionFragment program function)
    (argumentsFragments : CompositionalReflectionRows program arguments)
    (arity : Nat) (bodyIR : PolyIR.Term) (capturedIR : List PolyIR.Value)
    (bodyFragment : ∀ parameters sourceBody captured,
      lowerValue (.closure parameters sourceBody captured) =
        .closure arity bodyIR capturedIR →
      CompositionalReflectionFragment program sourceBody)
    (functionSuccess : PolyIR.Evaluates (lowerDefinitions program) (lowerEnv environment)
      (lower (identities environment) function) (.closure arity bodyIR capturedIR)) :
    SourceDiverges program environment (.app function arguments) ↔
      LoweredDiverges program environment (.app function arguments) :=
  not_congr (compositionalReflection_computedClosureApplication_termination_iff program
    environment function arguments functionFragment argumentsFragments arity bodyIR capturedIR
    bodyFragment functionSuccess)

/-- A finite evaluation exists for a list of Named initializers exactly when
one exists for the identity-lowered PolyIR list, provided each initializer is
in the compositional reflection fragment. This turns pointwise reflection
into a list-level nontermination correspondence. -/
theorem compositionalReflectionRows_arguments_terminates_iff (program : Definitions)
    (environment : Environment) (expressions : List Expr)
    (rows : CompositionalReflectionRows program expressions) :
    (∃ values, ArgumentsEvaluate program environment expressions values) ↔
      ∃ irValues, PolyIR.ArgumentsEvaluate (lowerDefinitions program) (lowerEnv environment)
        (lowerMany (identities environment) expressions) irValues := by
  constructor
  · rintro ⟨values, evaluated⟩
    have forward : ∀ {items sourceValues},
        ArgumentsEvaluate program environment items sourceValues →
        ∃ irValues, PolyIR.ArgumentsEvaluate (lowerDefinitions program) (lowerEnv environment)
          (lowerMany (identities environment) items) irValues := by
      intro items
      induction items with
      | nil =>
          intro sourceValues evaluated
          cases evaluated
          exact ⟨[], PolyIR.ArgumentsEvaluate.nil⟩
      | cons head tail ih =>
          intro sourceValues evaluated
          cases evaluated with
          | cons headEval tailEval =>
              obtain ⟨irTail, tailEvaluated⟩ := ih tailEval
              exact ⟨lowerValue _ :: irTail,
                PolyIR.ArgumentsEvaluate.cons (evaluation_preserved headEval) tailEvaluated⟩
    exact forward evaluated
  · rintro ⟨irValues, evaluated⟩
    obtain ⟨sourceValues, sourceEvaluated, _⟩ :=
      compositionalReflectionRows_arguments_reflected program environment expressions rows evaluated
    exact ⟨sourceValues, sourceEvaluated⟩

/-- Absence of a finite initializer-list derivation is preserved and reflected
by identity lowering on the same compositional fragment. -/
theorem compositionalReflectionRows_arguments_diverge_iff (program : Definitions)
    (environment : Environment) (expressions : List Expr)
    (rows : CompositionalReflectionRows program expressions) :
    (¬ ∃ values, ArgumentsEvaluate program environment expressions values) ↔
      ¬ ∃ irValues, PolyIR.ArgumentsEvaluate (lowerDefinitions program) (lowerEnv environment)
        (lowerMany (identities environment) expressions) irValues := by
  exact not_congr (compositionalReflectionRows_arguments_terminates_iff
    program environment expressions rows)

theorem compositionalReflection_lambdaApplication_evaluation_reflected
    (program : Definitions) (environment : Environment) (parameters : List Nat)
    (body : Expr) (arguments : List Expr)
    (bodyFragment : CompositionalReflectionFragment program body)
    (argumentsFragments : CompositionalReflectionRows program arguments)
    (value : PolyIR.Value)
    (evaluated : PolyIR.Evaluates (lowerDefinitions program) (lowerEnv environment)
      (lower (identities environment) (.app (.lam parameters body) arguments)) value) :
    ∃ sourceValue,
      Evaluates program environment (.app (.lam parameters body) arguments) sourceValue ∧
        lowerValue sourceValue = value := by
  rw [lower_eq] at evaluated
  cases evaluated with
  | appClosure functionEval argumentsEval argumentsArity bodyEval =>
      rw [lower_eq] at functionEval
      cases functionEval with
      | lam =>
          obtain ⟨sourceArguments, sourceArgumentsEval, argumentsLowered⟩ :=
            compositionalReflectionRows_arguments_reflected program environment arguments
              argumentsFragments argumentsEval
          have sourceArity : sourceArguments.length = parameters.length := by
            calc
              sourceArguments.length = (lowerValues sourceArguments).length := by simp [lowerValues]
              _ = _ := congrArg List.length argumentsLowered
              _ = parameters.length := by simpa [lowerValues] using argumentsArity
          have bodyEnvironmentEq :
              lowerEnv (bind parameters sourceArguments ++ environment) =
                lowerValues sourceArguments ++ lowerEnv environment :=
            lowerEnv_bind_append parameters sourceArguments environment sourceArity
          have bodyLocalsEq :
              identities (bind parameters sourceArguments ++ environment) =
                parameters ++ identities environment :=
            identities_bind_append parameters sourceArguments environment sourceArity
          have bodyTermEq :
              lower (identities (bind parameters sourceArguments ++ environment)) body =
                lower (parameters ++ identities environment) body := by rw [bodyLocalsEq]
          have bodyEvalAligned :
              PolyIR.Evaluates (lowerDefinitions program)
                (lowerEnv (bind parameters sourceArguments ++ environment))
                (lower (identities (bind parameters sourceArguments ++ environment)) body) value := by
            rw [bodyEnvironmentEq, argumentsLowered, bodyTermEq]
            exact bodyEval
          obtain ⟨sourceResult, sourceBodyEval, resultLowered⟩ :=
            compositionalReflection_evaluation_reflected program bodyFragment
              (bind parameters sourceArguments ++ environment) value bodyEvalAligned
          exact ⟨sourceResult,
            .appClosure .lam sourceArgumentsEval sourceArity sourceBodyEval, resultLowered⟩
  | appGlobal functionEval _ _ _ _ =>
      rw [lower_eq] at functionEval
      cases functionEval

/-- Reflection for an application whose arbitrary callee expression evaluates
to a closure or global function. The supplied body-family covers whichever
runtime body is selected by dispatch. -/
theorem compositionalReflection_computedCallableApplication_evaluation_reflected
    (program : Definitions) (environment : Environment) (function : Expr)
    (arguments : List Expr)
    (functionFragment : CompositionalReflectionFragment program function)
    (bodyFragments : ∀ (body : Expr),
      CompositionalReflectionFragment program body)
    (argumentsFragments : CompositionalReflectionRows program arguments)
    (value : PolyIR.Value)
    (evaluated : PolyIR.Evaluates (lowerDefinitions program) (lowerEnv environment)
      (lower (identities environment) (.app function arguments)) value) :
    ∃ sourceValue,
      Evaluates program environment (.app function arguments) sourceValue ∧
        lowerValue sourceValue = value := by
  rw [lower_eq] at evaluated
  cases evaluated with
  | appClosure functionEval argumentsEval argumentsArity bodyEval =>
      obtain ⟨sourceFunction, sourceFunctionEval, functionLowered⟩ :=
        compositionalReflection_evaluation_reflected program functionFragment environment
          (.closure _ _ _) functionEval
      cases sourceFunction with
      | closure parameters body captured =>
          obtain ⟨arityEq, bodyEq, capturedEq⟩ :=
            lowerValue_closure_injective parameters body captured _ _ _ functionLowered
          obtain ⟨sourceArguments, sourceArgumentsEval, argumentsLowered⟩ :=
            compositionalReflectionRows_arguments_reflected program environment arguments
              argumentsFragments argumentsEval
          have sourceArity : sourceArguments.length = parameters.length := by
            calc
              sourceArguments.length = (lowerValues sourceArguments).length := by simp [lowerValues]
              _ = _ := congrArg List.length argumentsLowered
              _ = _ := argumentsArity
              _ = parameters.length := arityEq.symm
          have bodyEnvironmentEq :
              lowerEnv (bind parameters sourceArguments ++ captured) =
                lowerValues sourceArguments ++ lowerEnv captured := by
            rw [lowerEnv_bind_append parameters sourceArguments captured sourceArity]
          have bodyLocalsEq :
              identities (bind parameters sourceArguments ++ captured) =
                parameters ++ identities captured :=
            identities_bind_append parameters sourceArguments captured sourceArity
          have bodyEvalAligned :
              PolyIR.Evaluates (lowerDefinitions program)
                (lowerEnv (bind parameters sourceArguments ++ captured))
                (lower (identities (bind parameters sourceArguments ++ captured)) body) value := by
            rw [bodyEnvironmentEq, argumentsLowered, capturedEq, bodyLocalsEq, bodyEq]
            exact bodyEval
          obtain ⟨sourceResult, sourceBodyEval, resultLowered⟩ :=
            compositionalReflection_evaluation_reflected program
              (bodyFragments body) (bind parameters sourceArguments ++ captured)
              value bodyEvalAligned
          exact ⟨sourceResult,
            .appClosure sourceFunctionEval sourceArgumentsEval sourceArity sourceBodyEval,
            resultLowered⟩
      | bool boolean => simp [lowerValue] at functionLowered
      | int integer => simp [lowerValue] at functionLowered
      | float number => simp [lowerValue] at functionLowered
      | string text => simp [lowerValue] at functionLowered
      | character character => simp [lowerValue] at functionLowered
      | unit => simp [lowerValue] at functionLowered
      | global index => simp [lowerValue] at functionLowered
      | nil => simp [lowerValue] at functionLowered
      | cons head tail => simp [lowerValue] at functionLowered
      | none => simp [lowerValue] at functionLowered
      | some inner => simp [lowerValue] at functionLowered
  | appGlobal functionEval argumentsEval runtimeDefinitionFound argumentsArity bodyEval =>
      rename_i _runtimeIndex irArguments irDefinition
      obtain ⟨sourceFunction, sourceFunctionEval, functionLowered⟩ :=
        compositionalReflection_evaluation_reflected program functionFragment environment
          (.global _runtimeIndex) functionEval
      cases sourceFunction with
      | global sourceIndex =>
          have functionIndexEq : sourceIndex = _runtimeIndex := by
            simpa [lowerValue] using functionLowered
          subst sourceIndex
          have runtimeDefinitionEq : ∃ parameters body,
              program[_runtimeIndex]? = some (parameters, body) ∧
              PolyIR.RuntimeDefinition.arity irDefinition = parameters.length ∧
              irDefinition.body = lower parameters body := by
            obtain ⟨parameters, body, definitionFound, definitionEq⟩ :=
              definitions_lookup_reflects program _runtimeIndex irDefinition runtimeDefinitionFound
            exact ⟨parameters, body, definitionFound,
              ⟨by simpa using congrArg PolyIR.RuntimeDefinition.arity definitionEq,
                by simpa using congrArg PolyIR.RuntimeDefinition.body definitionEq⟩⟩
          obtain ⟨parameters, body, definitionFound, arityEq, bodyEq⟩ := runtimeDefinitionEq
          obtain ⟨sourceArguments, sourceArgumentsEval, argumentsLowered⟩ :=
            compositionalReflectionRows_arguments_reflected program environment arguments
              argumentsFragments argumentsEval
          have sourceArity : sourceArguments.length = parameters.length := by
            calc
              sourceArguments.length = (lowerValues sourceArguments).length := by simp [lowerValues]
              _ = _ := congrArg List.length argumentsLowered
              _ = irDefinition.arity := argumentsArity
              _ = parameters.length := arityEq
          have bodyEnvironmentEq :
              lowerEnv (bind parameters sourceArguments) = lowerValues sourceArguments :=
            lowerEnv_bind parameters sourceArguments sourceArity
          have bodyTermEq :
              lower (identities (bind parameters sourceArguments)) body = irDefinition.body := by
            rw [bind_identifiers parameters sourceArguments sourceArity]
            exact bodyEq.symm
          have bodyEvalAligned :
              PolyIR.Evaluates (lowerDefinitions program)
                (lowerEnv (bind parameters sourceArguments))
                (lower (identities (bind parameters sourceArguments)) body) value := by
            rw [bodyEnvironmentEq, argumentsLowered, bodyTermEq]
            exact bodyEval
          obtain ⟨sourceResult, sourceBodyEval, resultLowered⟩ :=
            compositionalReflection_evaluation_reflected program
              (bodyFragments body) (bind parameters sourceArguments)
              value bodyEvalAligned
          exact ⟨sourceResult,
            .appGlobal sourceFunctionEval sourceArgumentsEval definitionFound sourceArity sourceBodyEval,
            resultLowered⟩
      | bool boolean => simp [lowerValue] at functionLowered
      | int integer => simp [lowerValue] at functionLowered
      | float number => simp [lowerValue] at functionLowered
      | string text => simp [lowerValue] at functionLowered
      | character character => simp [lowerValue] at functionLowered
      | unit => simp [lowerValue] at functionLowered
      | closure parameters body captured => simp [lowerValue] at functionLowered
      | nil => simp [lowerValue] at functionLowered
      | cons head tail => simp [lowerValue] at functionLowered
      | none => simp [lowerValue] at functionLowered
      | some inner => simp [lowerValue] at functionLowered

theorem compositionalReflection_computedCallableApplication_termination_iff
    (program : Definitions) (environment : Environment) (function : Expr)
    (arguments : List Expr)
    (functionFragment : CompositionalReflectionFragment program function)
    (bodyFragments : ∀ (body : Expr),
      CompositionalReflectionFragment program body)
    (argumentsFragments : CompositionalReflectionRows program arguments) :
    SourceTerminates program environment (.app function arguments) ↔
      LoweredTerminates program environment (.app function arguments) := by
  constructor
  · rintro ⟨value, sourceEvaluation⟩
    exact ⟨lowerValue value, evaluation_preserved sourceEvaluation⟩
  · rintro ⟨value, loweredEvaluation⟩
    obtain ⟨sourceValue, sourceEvaluation, _⟩ :=
      compositionalReflection_computedCallableApplication_evaluation_reflected
        program environment function arguments functionFragment bodyFragments
        argumentsFragments value loweredEvaluation
    exact ⟨sourceValue, sourceEvaluation⟩

theorem compositionalReflection_computedCallableApplication_divergence_iff
    (program : Definitions) (environment : Environment) (function : Expr)
    (arguments : List Expr)
    (functionFragment : CompositionalReflectionFragment program function)
    (bodyFragments : ∀ (body : Expr),
      CompositionalReflectionFragment program body)
    (argumentsFragments : CompositionalReflectionRows program arguments) :
    SourceDiverges program environment (.app function arguments) ↔
      LoweredDiverges program environment (.app function arguments) :=
  not_congr (compositionalReflection_computedCallableApplication_termination_iff
    program environment function arguments functionFragment bodyFragments argumentsFragments)

/-- The computed-call reflection also preserves recursive scope of the result
value, including any closure environment returned by the selected body. -/
theorem compositionalReflection_computedCallableApplication_reflected_scoped
    (program : Definitions) (programScoped : programWellScoped program)
    (environment : Environment) (environmentScoped : environmentWellScoped environment)
    (function : Expr) (arguments : List Expr)
    (functionFragment : CompositionalReflectionFragment program function)
    (bodyFragments : ∀ (body : Expr), CompositionalReflectionFragment program body)
    (argumentsFragments : CompositionalReflectionRows program arguments)
    (layoutAligned : letLayoutsAligned (.app function arguments) = true)
    (value : PolyIR.Value)
    (evaluated : PolyIR.Evaluates (lowerDefinitions program) (lowerEnv environment)
      (lower (identities environment) (.app function arguments)) value) :
    ∃ sourceValue,
      Evaluates program environment (.app function arguments) sourceValue ∧
        lowerValue sourceValue = value ∧ valueWellScoped sourceValue := by
  obtain ⟨sourceValue, sourceEvaluation, loweredEq⟩ :=
    compositionalReflection_computedCallableApplication_evaluation_reflected
      program environment function arguments functionFragment bodyFragments
      argumentsFragments value evaluated
  have resultScoped := evaluation_preserves_valueWellScoped program programScoped
    sourceEvaluation environmentScoped layoutAligned
  exact ⟨sourceValue, sourceEvaluation, loweredEq, resultScoped⟩

/-- Checked C-node decoding supplies the application layout invariant needed
for the computed-call scope theorem. -/
theorem decodeExprChecked_compositionalReflection_computedCallableApplication_reflected_scoped
    {fuel : Nat} {headers : List ExpansionLowering.Header} {node : CBindingWalk.Node}
    {function : Expr} {arguments : List Expr}
    (decoded : NLisp.Named.decodeExprChecked fuel headers node =
      some (.app function arguments))
    (program : Definitions) (programScoped : programWellScoped program)
    (environment : Environment) (environmentScoped : environmentWellScoped environment)
    (functionFragment : CompositionalReflectionFragment program function)
    (bodyFragments : ∀ (body : Expr), CompositionalReflectionFragment program body)
    (argumentsFragments : CompositionalReflectionRows program arguments)
    (value : PolyIR.Value)
    (evaluated : PolyIR.Evaluates (lowerDefinitions program) (lowerEnv environment)
      (lower (identities environment) (.app function arguments)) value) :
    ∃ sourceValue,
      Evaluates program environment (.app function arguments) sourceValue ∧
        lowerValue sourceValue = value ∧ valueWellScoped sourceValue := by
  exact compositionalReflection_computedCallableApplication_reflected_scoped program
    programScoped environment environmentScoped function arguments functionFragment bodyFragments
    argumentsFragments (NLisp.Named.decodeExprChecked_spec decoded).2 value evaluated

/-- Checked decoding also supplies the layout invariant for the local-body
computed-call theorem, whose closure contract is restricted to the runtime
closure shape and whose global contract ranges over declared definitions. -/
theorem decodeExprChecked_compositionalReflection_computedCallableApplication_localBodies_reflected_scoped
    {fuel : Nat} {headers : List ExpansionLowering.Header} {node : CBindingWalk.Node}
    {function : Expr} {arguments : List Expr}
    (decoded : NLisp.Named.decodeExprChecked fuel headers node =
      some (.app function arguments))
    (program : Definitions) (programScoped : programWellScoped program)
    (environment : Environment) (environmentScoped : environmentWellScoped environment)
    (functionFragment : CompositionalReflectionFragment program function)
    (argumentsFragments : CompositionalReflectionRows program arguments)
    (globalBodies : ∀ (index : Nat) (parameters : List Nat) (body : Expr),
      program[index]? = some (parameters, body) →
        CompositionalReflectionFragment program body)
    (closureBodies : ∀ (arity : Nat) (bodyIR : PolyIR.Term)
      (capturedIR : List PolyIR.Value) (parameters : List Nat)
      (sourceBody : Expr) (captured : Environment),
      lowerValue (.closure parameters sourceBody captured) =
        .closure arity bodyIR capturedIR →
        CompositionalReflectionFragment program sourceBody)
    (result : PolyIR.Value)
    (evaluated : PolyIR.Evaluates (lowerDefinitions program) (lowerEnv environment)
      (lower (identities environment) (.app function arguments)) result) :
    ∃ sourceResult, Evaluates program environment (.app function arguments) sourceResult ∧
      lowerValue sourceResult = result ∧ valueWellScoped sourceResult := by
  exact compositionalReflection_computedCallableApplication_localBodies_reflected_scoped
    program programScoped environment environmentScoped function arguments functionFragment
    argumentsFragments globalBodies closureBodies result evaluated
    (NLisp.Named.decodeExprChecked_spec decoded).2

/-- Reflection for a higher-order call whose callee is a binding in the
current Named environment. The binding may contain an arbitrary captured
environment; the closure body and every argument need only belong to the
compositional reflection fragment. -/
theorem compositionalReflection_variableClosureApplication_evaluation_reflected
    (program : Definitions) (environment : Environment) (identifier : Nat)
    (parameters : List Nat) (body : Expr) (captured : Environment)
    (arguments : List Expr)
    (calleeLookup : lookup identifier environment =
      some (.closure parameters body captured))
    (bodyFragment : CompositionalReflectionFragment program body)
    (argumentsFragments : CompositionalReflectionRows program arguments)
    (value : PolyIR.Value)
    (evaluated : PolyIR.Evaluates (lowerDefinitions program) (lowerEnv environment)
      (lower (identities environment) (.app (.var identifier) arguments)) value) :
    ∃ sourceValue,
      Evaluates program environment (.app (.var identifier) arguments) sourceValue ∧
        lowerValue sourceValue = value := by
  rw [lower_eq] at evaluated
  cases evaluated with
  | appClosure functionEval argumentsEval argumentsArity bodyEval =>
      rw [lower_eq] at functionEval
      cases functionEval with
      | var loweredLookup =>
          have sourceClosureLowered := lookup_lowered environment identifier calleeLookup
          have closureEq : lowerValue (.closure parameters body captured) = .closure _ _ _ :=
            Option.some.inj (sourceClosureLowered.symm.trans loweredLookup)
          simp only [lowerValue] at closureEq
          injection closureEq with arityEq bodyEq capturedEq
          obtain ⟨sourceArguments, sourceArgumentsEval, argumentsLowered⟩ :=
            compositionalReflectionRows_arguments_reflected program environment arguments
              argumentsFragments argumentsEval
          have sourceArity : sourceArguments.length = parameters.length := by
            calc
              sourceArguments.length = (lowerValues sourceArguments).length := by simp [lowerValues]
              _ = _ := congrArg List.length argumentsLowered
              _ = _ := argumentsArity
              _ = parameters.length := arityEq.symm
          have bodyEnvironmentEq :
              lowerEnv (bind parameters sourceArguments ++ captured) =
                lowerValues sourceArguments ++ lowerEnv captured := by
            rw [lowerEnv_bind_append parameters sourceArguments captured sourceArity]
          have bodyLocalsEq :
              identities (bind parameters sourceArguments ++ captured) =
                parameters ++ identities captured :=
            identities_bind_append parameters sourceArguments captured sourceArity
          have bodyEvalAligned :
              PolyIR.Evaluates (lowerDefinitions program)
                (lowerEnv (bind parameters sourceArguments ++ captured))
                (lower (identities (bind parameters sourceArguments ++ captured)) body) value := by
            rw [bodyEnvironmentEq, argumentsLowered, capturedEq, bodyLocalsEq, bodyEq]
            exact bodyEval
          obtain ⟨sourceResult, sourceBodyEval, resultLowered⟩ :=
            compositionalReflection_evaluation_reflected program bodyFragment
              (bind parameters sourceArguments ++ captured) value bodyEvalAligned
          exact ⟨sourceResult,
            .appClosure (.var calleeLookup) sourceArgumentsEval sourceArity sourceBodyEval,
            resultLowered⟩
  | appGlobal functionEval _ _ _ _ =>
      rw [lower_eq] at functionEval
      cases functionEval with
      | var loweredLookup =>
          have sourceClosureLowered := lookup_lowered environment identifier calleeLookup
          have impossible : lowerValue (.closure parameters body captured) = .global _ :=
            Option.some.inj (sourceClosureLowered.symm.trans loweredLookup)
          simp [lowerValue] at impossible

theorem compositionalReflection_variableClosureApplication_termination_iff
    (program : Definitions) (environment : Environment) (identifier : Nat)
    (parameters : List Nat) (body : Expr) (captured : Environment)
    (arguments : List Expr)
    (calleeLookup : lookup identifier environment =
      some (.closure parameters body captured))
    (bodyFragment : CompositionalReflectionFragment program body)
    (argumentsFragments : CompositionalReflectionRows program arguments) :
    SourceTerminates program environment (.app (.var identifier) arguments) ↔
      LoweredTerminates program environment (.app (.var identifier) arguments) := by
  constructor
  · rintro ⟨value, sourceEval⟩
    exact ⟨lowerValue value, evaluation_preserved sourceEval⟩
  · rintro ⟨value, loweredEval⟩
    obtain ⟨sourceValue, sourceEval, _⟩ :=
      compositionalReflection_variableClosureApplication_evaluation_reflected
        program environment identifier parameters body captured arguments calleeLookup
        bodyFragment argumentsFragments value loweredEval
    exact ⟨sourceValue, sourceEval⟩

theorem compositionalReflection_variableClosureApplication_divergence_iff
    (program : Definitions) (environment : Environment) (identifier : Nat)
    (parameters : List Nat) (body : Expr) (captured : Environment)
    (arguments : List Expr)
    (calleeLookup : lookup identifier environment =
      some (.closure parameters body captured))
    (bodyFragment : CompositionalReflectionFragment program body)
    (argumentsFragments : CompositionalReflectionRows program arguments) :
    SourceDiverges program environment (.app (.var identifier) arguments) ↔
      LoweredDiverges program environment (.app (.var identifier) arguments) :=
  not_congr (compositionalReflection_variableClosureApplication_termination_iff
    program environment identifier parameters body captured arguments calleeLookup
    bodyFragment argumentsFragments)

/-- Variable-callee closure reflection also preserves recursive closure
well-scopedness when the decoded program, current environment, and complete
application layout satisfy their decoder invariants. -/
theorem compositionalReflection_variableClosureApplication_evaluation_reflected_scoped
    (program : Definitions) (programScoped : programWellScoped program)
    (environment : Environment) (environmentScoped : environmentWellScoped environment)
    (parameters : List Nat) (body : Expr) (captured : Environment)
    (arguments : List Expr)
    (calleeLookup : lookup identifier environment =
      some (.closure parameters body captured))
    (bodyFragment : CompositionalReflectionFragment program body)
    (argumentsFragments : CompositionalReflectionRows program arguments)
    (aligned : letLayoutsAligned (.app (.var identifier) arguments) = true)
    (value : PolyIR.Value)
    (evaluated : PolyIR.Evaluates (lowerDefinitions program) (lowerEnv environment)
      (lower (identities environment) (.app (.var identifier) arguments)) value) :
    ∃ sourceValue,
      Evaluates program environment (.app (.var identifier) arguments) sourceValue ∧
        lowerValue sourceValue = value ∧ valueWellScoped sourceValue := by
  obtain ⟨sourceValue, sourceEval, loweredEq⟩ :=
    compositionalReflection_variableClosureApplication_evaluation_reflected
      program environment identifier parameters body captured arguments calleeLookup
      bodyFragment argumentsFragments value evaluated
  have scopedValue := evaluation_preserves_valueWellScoped program programScoped
    sourceEval environmentScoped aligned
  exact ⟨sourceValue, sourceEval, loweredEq, scopedValue⟩

/-- Checked source decoding supplies the layout invariant for reflection of
applications whose callee is a closure stored in the current environment. -/
theorem decodeExprChecked_compositionalReflection_variableClosureApplication_reflected_scoped
    {fuel : Nat} {headers : List ExpansionLowering.Header} {node : CBindingWalk.Node}
    {identifier : Nat} {arguments : List Expr}
    (decoded : NLisp.Named.decodeExprChecked fuel headers node =
      some (.app (.var identifier) arguments))
    (program : Definitions) (programScoped : programWellScoped program)
    (environment : Environment) (environmentScoped : environmentWellScoped environment)
    (parameters : List Nat) (body : Expr) (captured : Environment)
    (calleeLookup : lookup identifier environment = some (.closure parameters body captured))
    (bodyFragment : CompositionalReflectionFragment program body)
    (argumentsFragments : CompositionalReflectionRows program arguments)
    (value : PolyIR.Value)
    (evaluated : PolyIR.Evaluates (lowerDefinitions program) (lowerEnv environment)
      (lower (identities environment) (.app (.var identifier) arguments)) value) :
    ∃ sourceValue,
      Evaluates program environment (.app (.var identifier) arguments) sourceValue ∧
        lowerValue sourceValue = value ∧ valueWellScoped sourceValue := by
  exact compositionalReflection_variableClosureApplication_evaluation_reflected_scoped
    program programScoped environment environmentScoped (identifier := identifier)
    parameters body captured
    arguments calleeLookup bodyFragment argumentsFragments
    (NLisp.Named.decodeExprChecked_spec decoded).2 value evaluated

/-- The arbitrary-arity compositional lambda-application reflection also
preserves recursive closure well-scopedness under decoder-style invariants. -/
theorem compositionalReflection_lambdaApplication_evaluation_reflected_scoped
    (program : Definitions) (programScoped : programWellScoped program)
    (environment : Environment) (environmentScoped : environmentWellScoped environment)
    (parameters : List Nat) (body : Expr) (arguments : List Expr)
    (bodyFragment : CompositionalReflectionFragment program body)
    (argumentsFragments : CompositionalReflectionRows program arguments)
    (aligned : letLayoutsAligned (.app (.lam parameters body) arguments) = true)
    (value : PolyIR.Value)
    (evaluated : PolyIR.Evaluates (lowerDefinitions program) (lowerEnv environment)
      (lower (identities environment) (.app (.lam parameters body) arguments)) value) :
    ∃ sourceValue,
      Evaluates program environment (.app (.lam parameters body) arguments) sourceValue ∧
      lowerValue sourceValue = value ∧ valueWellScoped sourceValue := by
  obtain ⟨sourceValue, sourceEvaluation, loweredEq⟩ :=
    compositionalReflection_lambdaApplication_evaluation_reflected program environment
      parameters body arguments bodyFragment argumentsFragments value evaluated
  have scopedValue := evaluation_preserves_valueWellScoped program programScoped
    sourceEvaluation environmentScoped aligned
  exact ⟨sourceValue, sourceEvaluation, loweredEq, scopedValue⟩

/-- The same lambda-application reflection preserves identity-indexed captured
scope when the source program, environment, and expression satisfy the
identity invariants used by name lowering. -/
theorem compositionalReflection_globalApplication_evaluation_reflected
    (program : Definitions) (environment : Environment) (index : Nat)
    (parameters : List Nat) (body : Expr) (arguments : List Expr)
    (definitionFound : program[index]? = some (parameters, body))
    (bodyFragment : CompositionalReflectionFragment program body)
    (argumentsFragments : CompositionalReflectionRows program arguments)
    (value : PolyIR.Value)
    (evaluated : PolyIR.Evaluates (lowerDefinitions program) (lowerEnv environment)
      (lower (identities environment) (.app (.global index) arguments)) value) :
    ∃ sourceValue,
      Evaluates program environment (.app (.global index) arguments) sourceValue ∧
        lowerValue sourceValue = value := by
  rw [lower_eq] at evaluated
  cases evaluated with
  | appClosure functionEval _ _ _ =>
      rw [lower_eq] at functionEval
      cases functionEval
  | appGlobal functionEval argumentsEval runtimeDefinitionFound argumentsArity bodyEval =>
      rename_i _runtimeIndex irArguments irDefinition
      cases functionEval with
      | global _ =>
          have sourceFunctionEval : Evaluates program environment (.global index) (.global index) :=
            .global definitionFound
          have runtimeDefinitionEq : irDefinition =
              PolyIR.RuntimeDefinition.mk parameters.length (lower parameters body) := by
            obtain ⟨sourceParameters, sourceBody, found, definitionEq⟩ :=
              definitions_lookup_reflects program index irDefinition runtimeDefinitionFound
            have pairEq : (sourceParameters, sourceBody) = (parameters, body) :=
              Option.some.inj (found.symm.trans definitionFound)
            cases pairEq
            exact definitionEq
          obtain ⟨sourceArguments, sourceArgumentsEval, argumentsLowered⟩ :=
            compositionalReflectionRows_arguments_reflected program environment arguments
              argumentsFragments argumentsEval
          have sourceArity : sourceArguments.length = parameters.length := by
            calc
              sourceArguments.length = (lowerValues sourceArguments).length := by simp [lowerValues]
              _ = _ := congrArg List.length argumentsLowered
              _ = irDefinition.arity := argumentsArity
              _ = parameters.length := by
                have arityField := congrArg PolyIR.RuntimeDefinition.arity runtimeDefinitionEq
                simpa using arityField
          have bodyEnvironmentEq :
              lowerEnv (bind parameters sourceArguments) = lowerValues sourceArguments :=
            lowerEnv_bind parameters sourceArguments sourceArity
          have bodyTermEq : lower (identities (bind parameters sourceArguments)) body =
              irDefinition.body := by
            rw [bind_identifiers parameters sourceArguments sourceArity]
            have bodyField := congrArg PolyIR.RuntimeDefinition.body runtimeDefinitionEq
            simpa using bodyField.symm
          have bodyEvalAligned :
              PolyIR.Evaluates (lowerDefinitions program)
                (lowerEnv (bind parameters sourceArguments))
                (lower (identities (bind parameters sourceArguments)) body) value := by
            rw [bodyEnvironmentEq, argumentsLowered, bodyTermEq]
            exact bodyEval
          obtain ⟨sourceResult, sourceBodyEval, resultLowered⟩ :=
            compositionalReflection_evaluation_reflected program bodyFragment
              (bind parameters sourceArguments) value bodyEvalAligned
          exact ⟨sourceResult,
            .appGlobal sourceFunctionEval sourceArgumentsEval definitionFound sourceArity sourceBodyEval,
            resultLowered⟩

/-- Reflected global calls preserve recursive closure well-scopedness under
the decoded program and environment invariants. -/
theorem compositionalReflection_globalApplication_evaluation_reflected_scoped
    (program : Definitions) (programScoped : programWellScoped program)
    (environment : Environment) (environmentScoped : EnvironmentWellScoped environment)
    (index : Nat) (parameters : List Nat) (body : Expr) (arguments : List Expr)
    (definitionFound : program[index]? = some (parameters, body))
    (bodyFragment : CompositionalReflectionFragment program body)
    (argumentsFragments : CompositionalReflectionRows program arguments)
    (aligned : letLayoutsAligned (.app (.global index) arguments) = true)
    (value : PolyIR.Value)
    (evaluated : PolyIR.Evaluates (lowerDefinitions program) (lowerEnv environment)
      (lower (identities environment) (.app (.global index) arguments)) value) :
    ∃ sourceValue,
      Evaluates program environment (.app (.global index) arguments) sourceValue ∧
      lowerValue sourceValue = value ∧ valueWellScoped sourceValue := by
  obtain ⟨sourceValue, sourceEvaluation, loweredEq⟩ :=
    compositionalReflection_globalApplication_evaluation_reflected program environment index
      parameters body arguments definitionFound bodyFragment argumentsFragments value evaluated
  have scopedValue := evaluation_preserves_valueWellScoped program programScoped
    sourceEvaluation environmentScoped aligned
  exact ⟨sourceValue, sourceEvaluation, loweredEq, scopedValue⟩

theorem compositionalReflection_globalApplication_termination_iff
    (program : Definitions) (environment : Environment) (index : Nat)
    (parameters : List Nat) (body : Expr) (arguments : List Expr)
    (definitionFound : program[index]? = some (parameters, body))
    (bodyFragment : CompositionalReflectionFragment program body)
    (argumentsFragments : CompositionalReflectionRows program arguments) :
    SourceTerminates program environment (.app (.global index) arguments) ↔
      LoweredTerminates program environment (.app (.global index) arguments) := by
  constructor
  · rintro ⟨value, sourceEval⟩
    exact ⟨lowerValue value, evaluation_preserved sourceEval⟩
  · rintro ⟨value, loweredEval⟩
    obtain ⟨sourceValue, sourceEval, _⟩ :=
      compositionalReflection_globalApplication_evaluation_reflected program environment index
        parameters body arguments definitionFound bodyFragment argumentsFragments value loweredEval
    exact ⟨sourceValue, sourceEval⟩

theorem compositionalReflection_globalApplication_divergence_iff
    (program : Definitions) (environment : Environment) (index : Nat)
    (parameters : List Nat) (body : Expr) (arguments : List Expr)
    (definitionFound : program[index]? = some (parameters, body))
    (bodyFragment : CompositionalReflectionFragment program body)
    (argumentsFragments : CompositionalReflectionRows program arguments) :
    SourceDiverges program environment (.app (.global index) arguments) ↔
      LoweredDiverges program environment (.app (.global index) arguments) :=
  not_congr (compositionalReflection_globalApplication_termination_iff program environment index
    parameters body arguments definitionFound bodyFragment argumentsFragments)

theorem compositionalReflection_globalApplication_evaluation_reflected_identityScoped
    (program : Definitions) (programScoped : programIdentityScoped program)
    (environment : Environment) (environmentScoped : EnvironmentIdentityScoped environment)
    (index : Nat) (parameters : List Nat) (body : Expr) (arguments : List Expr)
    (definitionFound : program[index]? = some (parameters, body))
    (bodyFragment : CompositionalReflectionFragment program body)
    (argumentsFragments : CompositionalReflectionRows program arguments)
    (expressionScoped : IdentityScoped (identities environment)
      (.app (.global index) arguments)) (value : PolyIR.Value)
    (evaluated : PolyIR.Evaluates (lowerDefinitions program) (lowerEnv environment)
      (lower (identities environment) (.app (.global index) arguments)) value) :
    ∃ sourceValue,
      Evaluates program environment (.app (.global index) arguments) sourceValue ∧
        lowerValue sourceValue = value ∧ ValueIdentityScoped sourceValue := by
  obtain ⟨sourceValue, sourceEval, loweredEq⟩ :=
    compositionalReflection_globalApplication_evaluation_reflected program environment index
      parameters body arguments definitionFound bodyFragment argumentsFragments value evaluated
  have sourceScoped := evaluation_preserves_valueIdentityScoped program programScoped
    sourceEval environmentScoped expressionScoped
  exact ⟨sourceValue, sourceEval, loweredEq, sourceScoped⟩

theorem compositionalReflection_lambdaApplication_termination_iff
    (program : Definitions) (environment : Environment) (parameters : List Nat)
    (body : Expr) (arguments : List Expr)
    (bodyFragment : CompositionalReflectionFragment program body)
    (argumentsFragments : CompositionalReflectionRows program arguments) :
    SourceTerminates program environment (.app (.lam parameters body) arguments) ↔
      LoweredTerminates program environment (.app (.lam parameters body) arguments) := by
  constructor
  · rintro ⟨value, sourceEval⟩
    exact ⟨lowerValue value, evaluation_preserved sourceEval⟩
  · rintro ⟨value, loweredEval⟩
    obtain ⟨sourceValue, sourceEval, _⟩ :=
      compositionalReflection_lambdaApplication_evaluation_reflected program environment
        parameters body arguments bodyFragment argumentsFragments value loweredEval
    exact ⟨sourceValue, sourceEval⟩

theorem compositionalReflection_lambdaApplication_divergence_iff
    (program : Definitions) (environment : Environment) (parameters : List Nat)
    (body : Expr) (arguments : List Expr)
    (bodyFragment : CompositionalReflectionFragment program body)
    (argumentsFragments : CompositionalReflectionRows program arguments) :
    SourceDiverges program environment (.app (.lam parameters body) arguments) ↔
      LoweredDiverges program environment (.app (.lam parameters body) arguments) :=
  not_congr (compositionalReflection_lambdaApplication_termination_iff program environment
    parameters body arguments bodyFragment argumentsFragments)

theorem compositionalReflection_lambdaApplication_evaluation_reflected_identityScoped
    (program : Definitions) (programScoped : programIdentityScoped program)
    (environment : Environment) (environmentScoped : EnvironmentIdentityScoped environment)
    (parameters : List Nat) (body : Expr) (arguments : List Expr)
    (bodyFragment : CompositionalReflectionFragment program body)
    (argumentsFragments : CompositionalReflectionRows program arguments)
    (expressionScoped : IdentityScoped (identities environment)
      (.app (.lam parameters body) arguments)) (value : PolyIR.Value)
    (evaluated : PolyIR.Evaluates (lowerDefinitions program) (lowerEnv environment)
      (lower (identities environment) (.app (.lam parameters body) arguments)) value) :
    ∃ sourceValue,
      Evaluates program environment (.app (.lam parameters body) arguments) sourceValue ∧
        lowerValue sourceValue = value ∧ ValueIdentityScoped sourceValue := by
  obtain ⟨sourceValue, sourceEval, loweredEq⟩ :=
    compositionalReflection_lambdaApplication_evaluation_reflected program environment
      parameters body arguments bodyFragment argumentsFragments value evaluated
  have sourceScoped := evaluation_preserves_valueIdentityScoped program programScoped
    sourceEval environmentScoped expressionScoped
  exact ⟨sourceValue, sourceEval, loweredEq, sourceScoped⟩

theorem compositionalReflectionRows_sequence_reflected (program : Definitions)
    (environment : Environment) (expressions : List Expr)
    (rows : CompositionalReflectionRows program expressions)
    (sourcePrevious : Value) (irPrevious : PolyIR.Value)
    (previousLowered : lowerValue sourcePrevious = irPrevious) :
    ∀ {value},
      PolyIR.SequenceEvaluates (lowerDefinitions program) (lowerEnv environment)
        (lowerMany (identities environment) expressions) irPrevious value →
      ∃ sourceValue,
        SequenceEvaluates program environment expressions sourcePrevious sourceValue ∧
          lowerValue sourceValue = value := by
  induction expressions generalizing sourcePrevious irPrevious with
  | nil =>
      intro value evaluated
      cases evaluated
      exact ⟨sourcePrevious, .nil, previousLowered⟩
  | cons head tail ih =>
      intro value evaluated
      rw [lowerMany_eq] at evaluated
      cases evaluated with
      | cons headEval tailEval =>
          obtain ⟨sourceHead, headSourceEval, headLowered⟩ :=
            compositionalReflection_evaluation_reflected program (rows head (by simp))
              environment _ headEval
          have tailRows : CompositionalReflectionRows program tail := by
            intro expression member
            exact rows expression (List.mem_cons_of_mem head member)
          obtain ⟨sourceValue, tailSourceEval, valueLowered⟩ :=
            ih tailRows sourceHead _ headLowered tailEval
          exact ⟨sourceValue, .cons headSourceEval tailSourceEval, valueLowered⟩

theorem compositionalReflection_begin_evaluation_reflected (program : Definitions)
    (environment : Environment) (first : Expr) (rest : List Expr)
    (firstFragment : CompositionalReflectionFragment program first)
    (restFragments : CompositionalReflectionRows program rest) (value : PolyIR.Value)
    (evaluated : PolyIR.Evaluates (lowerDefinitions program) (lowerEnv environment)
      (lower (identities environment) (.begin first rest)) value) :
    ∃ sourceValue, Evaluates program environment (.begin first rest) sourceValue ∧
      lowerValue sourceValue = value := by
  rw [lower_eq] at evaluated
  cases evaluated with
  | begin firstEval restEval =>
      obtain ⟨sourceFirst, firstSourceEval, firstLowered⟩ :=
        compositionalReflection_evaluation_reflected program firstFragment environment _ firstEval
      obtain ⟨sourceValue, restSourceEval, valueLowered⟩ :=
        compositionalReflectionRows_sequence_reflected program environment rest restFragments
          sourceFirst _ firstLowered restEval
      exact ⟨sourceValue, .begin firstSourceEval restSourceEval, valueLowered⟩

theorem compositionalReflection_letMany_evaluation_reflected (program : Definitions)
    (environment : Environment) (ids : List Nat) (initializers : List Expr) (body : Expr)
    (initializerFragments : CompositionalReflectionRows program initializers)
    (layout : ids.length = initializers.length)
    (bodyFragment : CompositionalReflectionFragment program body) (value : PolyIR.Value)
    (evaluated : PolyIR.Evaluates (lowerDefinitions program) (lowerEnv environment)
      (lower (identities environment) (.letMany ids initializers body)) value) :
    ∃ sourceValue,
      Evaluates program environment (.letMany ids initializers body) sourceValue ∧
        lowerValue sourceValue = value := by
  exact letMany_evaluation_reflected program environment ids initializers body layout.symm
    (fun {irValues} argumentsEval =>
      compositionalReflectionRows_arguments_reflected program environment initializers
        initializerFragments argumentsEval)
    (fun sourceValues irValues sourceLength valuesLower {result} bodyEval => by
      have environmentEq : lowerEnv (bind ids sourceValues ++ environment) =
          irValues ++ lowerEnv environment := by
        rw [lowerEnv_bind_append ids sourceValues environment sourceLength, valuesLower]
      have identitiesEq : identities (bind ids sourceValues ++ environment) =
          ids ++ identities environment :=
        identities_bind_append ids sourceValues environment sourceLength
      have termEq : lower (identities (bind ids sourceValues ++ environment)) body =
          lower (ids ++ identities environment) body := by rw [identitiesEq]
      exact compositionalReflection_evaluation_reflected program bodyFragment
        (bind ids sourceValues ++ environment) result (by
          rw [environmentEq, termEq]
          exact bodyEval)) value evaluated

theorem compositionalReflection_begin_termination_iff (program : Definitions)
    (environment : Environment) (first : Expr) (rest : List Expr)
    (firstFragment : CompositionalReflectionFragment program first)
    (restFragments : CompositionalReflectionRows program rest) :
    SourceTerminates program environment (.begin first rest) ↔
      LoweredTerminates program environment (.begin first rest) := by
  constructor
  · rintro ⟨value, sourceEval⟩
    exact ⟨lowerValue value, evaluation_preserved sourceEval⟩
  · rintro ⟨value, loweredEval⟩
    obtain ⟨sourceValue, sourceEval, _⟩ := compositionalReflection_begin_evaluation_reflected
      program environment first rest firstFragment restFragments value loweredEval
    exact ⟨sourceValue, sourceEval⟩

theorem compositionalReflection_begin_divergence_iff (program : Definitions)
    (environment : Environment) (first : Expr) (rest : List Expr)
    (firstFragment : CompositionalReflectionFragment program first)
    (restFragments : CompositionalReflectionRows program rest) :
    SourceDiverges program environment (.begin first rest) ↔
      LoweredDiverges program environment (.begin first rest) :=
  not_congr (compositionalReflection_begin_termination_iff program environment first rest
    firstFragment restFragments)

theorem decodeExprChecked_compositionalReflection_begin_evaluation_reflected_scoped
    {fuel : Nat} {headers : List ExpansionLowering.Header} {node : CBindingWalk.Node}
    {first : Expr} {rest : List Expr}
    (decoded : NLisp.Named.decodeExprChecked fuel headers node = some (.begin first rest))
    (program : Definitions) (programScoped : programWellScoped program)
    (firstFragment : CompositionalReflectionFragment program first)
    (restFragments : CompositionalReflectionRows program rest)
    (environment : Environment) (environmentScoped : environmentWellScoped environment)
    (value : PolyIR.Value)
    (evaluated : PolyIR.Evaluates (lowerDefinitions program) (lowerEnv environment)
      (lower (identities environment) (.begin first rest)) value) :
    ∃ sourceValue, Evaluates program environment (.begin first rest) sourceValue ∧
      lowerValue sourceValue = value ∧ valueWellScoped sourceValue := by
  obtain ⟨sourceValue, sourceEvaluation, loweredEq⟩ :=
    compositionalReflection_begin_evaluation_reflected program environment first rest
      firstFragment restFragments value evaluated
  have scopedValue := evaluation_preserves_valueWellScoped program programScoped
    sourceEvaluation environmentScoped (NLisp.Named.decodeExprChecked_spec decoded).2
  exact ⟨sourceValue, sourceEvaluation, loweredEq, scopedValue⟩

theorem decodeExprChecked_compositionalReflection_begin_termination_iff
    {fuel : Nat} {headers : List ExpansionLowering.Header} {node : CBindingWalk.Node}
    {first : Expr} {rest : List Expr}
    (decoded : NLisp.Named.decodeExprChecked fuel headers node = some (.begin first rest))
    (program : Definitions) (firstFragment : CompositionalReflectionFragment program first)
    (restFragments : CompositionalReflectionRows program rest)
    (environment : Environment) :
    SourceTerminates program environment (.begin first rest) ↔
      LoweredTerminates program environment (.begin first rest) :=
  compositionalReflection_begin_termination_iff program environment first rest
    firstFragment restFragments

theorem decodeExprChecked_compositionalReflection_begin_divergence_iff
    {fuel : Nat} {headers : List ExpansionLowering.Header} {node : CBindingWalk.Node}
    {first : Expr} {rest : List Expr}
    (decoded : NLisp.Named.decodeExprChecked fuel headers node = some (.begin first rest))
    (program : Definitions) (firstFragment : CompositionalReflectionFragment program first)
    (restFragments : CompositionalReflectionRows program rest)
    (environment : Environment) :
    SourceDiverges program environment (.begin first rest) ↔
      LoweredDiverges program environment (.begin first rest) :=
  compositionalReflection_begin_divergence_iff program environment first rest
    firstFragment restFragments

theorem compositionalReflection_letMany_termination_iff (program : Definitions)
    (environment : Environment) (ids : List Nat) (initializers : List Expr) (body : Expr)
    (initializerFragments : CompositionalReflectionRows program initializers)
    (layout : ids.length = initializers.length)
    (bodyFragment : CompositionalReflectionFragment program body) :
    SourceTerminates program environment (.letMany ids initializers body) ↔
      LoweredTerminates program environment (.letMany ids initializers body) := by
  constructor
  · rintro ⟨value, sourceEval⟩
    exact ⟨lowerValue value, evaluation_preserved sourceEval⟩
  · rintro ⟨value, loweredEval⟩
    obtain ⟨sourceValue, sourceEval, _⟩ := compositionalReflection_letMany_evaluation_reflected
      program environment ids initializers body initializerFragments layout bodyFragment
      value loweredEval
    exact ⟨sourceValue, sourceEval⟩

theorem compositionalReflection_letMany_divergence_iff (program : Definitions)
    (environment : Environment) (ids : List Nat) (initializers : List Expr) (body : Expr)
    (initializerFragments : CompositionalReflectionRows program initializers)
    (layout : ids.length = initializers.length)
    (bodyFragment : CompositionalReflectionFragment program body) :
    SourceDiverges program environment (.letMany ids initializers body) ↔
      LoweredDiverges program environment (.letMany ids initializers body) :=
  not_congr (compositionalReflection_letMany_termination_iff program environment ids
    initializers body initializerFragments layout bodyFragment)

theorem decodeExprChecked_compositionalReflection_letMany_evaluation_reflected_scoped
    {fuel : Nat} {headers : List ExpansionLowering.Header} {node : CBindingWalk.Node}
    {ids : List Nat} {initializers : List Expr} {body : Expr}
    (decoded : NLisp.Named.decodeExprChecked fuel headers node =
      some (.letMany ids initializers body))
    (program : Definitions) (programScoped : programWellScoped program)
    (initializerFragments : CompositionalReflectionRows program initializers)
    (bodyFragment : CompositionalReflectionFragment program body)
    (environment : Environment) (environmentScoped : environmentWellScoped environment)
    (value : PolyIR.Value)
    (evaluated : PolyIR.Evaluates (lowerDefinitions program) (lowerEnv environment)
      (lower (identities environment) (.letMany ids initializers body)) value) :
    ∃ sourceValue, Evaluates program environment (.letMany ids initializers body) sourceValue ∧
      lowerValue sourceValue = value ∧ valueWellScoped sourceValue := by
  have layout := NLisp.Named.decodeExprChecked_letMany_lengths decoded
  obtain ⟨sourceValue, sourceEvaluation, loweredEq⟩ :=
    compositionalReflection_letMany_evaluation_reflected program environment ids initializers
      body initializerFragments layout bodyFragment value evaluated
  have scopedValue := evaluation_preserves_valueWellScoped program programScoped
    sourceEvaluation environmentScoped (NLisp.Named.decodeExprChecked_spec decoded).2
  exact ⟨sourceValue, sourceEvaluation, loweredEq, scopedValue⟩

theorem decodeExprChecked_compositionalReflection_letMany_termination_iff
    {fuel : Nat} {headers : List ExpansionLowering.Header} {node : CBindingWalk.Node}
    {ids : List Nat} {initializers : List Expr} {body : Expr}
    (decoded : NLisp.Named.decodeExprChecked fuel headers node =
      some (.letMany ids initializers body))
    (program : Definitions)
    (initializerFragments : CompositionalReflectionRows program initializers)
    (bodyFragment : CompositionalReflectionFragment program body)
    (environment : Environment) :
    SourceTerminates program environment (.letMany ids initializers body) ↔
      LoweredTerminates program environment (.letMany ids initializers body) :=
  compositionalReflection_letMany_termination_iff program environment ids initializers body
    initializerFragments (NLisp.Named.decodeExprChecked_letMany_lengths decoded) bodyFragment

theorem decodeExprChecked_compositionalReflection_letMany_divergence_iff
    {fuel : Nat} {headers : List ExpansionLowering.Header} {node : CBindingWalk.Node}
    {ids : List Nat} {initializers : List Expr} {body : Expr}
    (decoded : NLisp.Named.decodeExprChecked fuel headers node =
      some (.letMany ids initializers body))
    (program : Definitions)
    (initializerFragments : CompositionalReflectionRows program initializers)
    (bodyFragment : CompositionalReflectionFragment program body)
    (environment : Environment) :
    SourceDiverges program environment (.letMany ids initializers body) ↔
      LoweredDiverges program environment (.letMany ids initializers body) :=
  compositionalReflection_letMany_divergence_iff program environment ids initializers body
    initializerFragments (NLisp.Named.decodeExprChecked_letMany_lengths decoded) bodyFragment

/-- Termination equivalence follows for the entire compositional fragment. -/
theorem compositionalReflection_termination_iff (program : Definitions)
    (expression : Expr) (fragment : CompositionalReflectionFragment program expression)
    (environment : Environment) :
    SourceTerminates program environment expression ↔
      LoweredTerminates program environment expression := by
  constructor
  · rintro ⟨value, sourceEvaluation⟩
    exact ⟨lowerValue value, evaluation_preserved sourceEvaluation⟩
  · rintro ⟨value, loweredEvaluation⟩
    obtain ⟨sourceValue, sourceEvaluation, _⟩ :=
      compositionalReflection_evaluation_reflected (program := program)
        (expression := expression) fragment
        environment value loweredEvaluation
    exact ⟨sourceValue, sourceEvaluation⟩

/-- Divergence here means absence of any finite big-step derivation. -/
theorem compositionalReflection_divergence_iff (program : Definitions)
    (expression : Expr) (fragment : CompositionalReflectionFragment program expression)
    (environment : Environment) :
    SourceDiverges program environment expression ↔
      LoweredDiverges program environment expression := by
  exact not_congr (compositionalReflection_termination_iff program expression fragment
    environment)

/-- A successful checked C-node decode can be used directly at the boundary
between source reading and evaluation reflection.  The caller supplies the
compositional proof for the decoded expression; the checked decoder carries
the binder/layout invariant needed by the source semantics. -/
theorem decodeExprChecked_compositionalReflection_evaluation_reflected
    {fuel : Nat} {headers : List ExpansionLowering.Header} {node : CBindingWalk.Node}
    {expression : Expr}
    (decoded : NLisp.Named.decodeExprChecked fuel headers node = some expression)
    (program : Definitions) (fragment : CompositionalReflectionFragment program expression)
    (environment : Environment) (value : PolyIR.Value)
    (evaluated : PolyIR.Evaluates (lowerDefinitions program) (lowerEnv environment)
      (lower (identities environment) expression) value) :
    ∃ sourceValue, Evaluates program environment expression sourceValue ∧
      lowerValue sourceValue = value ∧ letLayoutsAligned expression = true := by
  obtain ⟨sourceValue, sourceEval, loweredEq⟩ :=
    compositionalReflection_evaluation_reflected program fragment environment value evaluated
  exact ⟨sourceValue, sourceEval, loweredEq,
    (NLisp.Named.decodeExprChecked_spec decoded).2⟩

/-- Checked decoding preserves the compositional fragment's finite
termination equivalence, including initializer and body forms outside the
older arithmetic-only `letMany` fragment. -/
theorem decodeExprChecked_compositionalReflection_termination_iff
    {fuel : Nat} {headers : List ExpansionLowering.Header} {node : CBindingWalk.Node}
    {expression : Expr}
    (decoded : NLisp.Named.decodeExprChecked fuel headers node = some expression)
    (program : Definitions) (fragment : CompositionalReflectionFragment program expression)
    (environment : Environment) :
    (SourceTerminates program environment expression ↔
      LoweredTerminates program environment expression) ∧
      letLayoutsAligned expression = true := by
  exact ⟨compositionalReflection_termination_iff program expression fragment environment,
    (NLisp.Named.decodeExprChecked_spec decoded).2⟩

/-- As above, absence of finite big-step derivations agrees after a
successful checked decode on the complete compositional fragment. -/
theorem decodeExprChecked_compositionalReflection_divergence_iff
    {fuel : Nat} {headers : List ExpansionLowering.Header} {node : CBindingWalk.Node}
    {expression : Expr}
    (decoded : NLisp.Named.decodeExprChecked fuel headers node = some expression)
    (program : Definitions) (fragment : CompositionalReflectionFragment program expression)
    (environment : Environment) :
    SourceDiverges program environment expression ↔
      LoweredDiverges program environment expression := by
  exact not_congr (decodeExprChecked_compositionalReflection_termination_iff decoded
    program fragment environment).1

/-- Under decoder-style scope invariants, reflected results also satisfy the
recursive closure well-scopedness invariant. -/
theorem compositionalReflection_evaluation_reflected_scoped (program : Definitions)
    (programScoped : programWellScoped program) (expression : Expr)
    (fragment : CompositionalReflectionFragment program expression)
    (environment : Environment) (environmentScoped : environmentWellScoped environment)
    (aligned : letLayoutsAligned expression = true)
    (value : PolyIR.Value)
    (evaluated : PolyIR.Evaluates (lowerDefinitions program) (lowerEnv environment)
      (lower (identities environment) expression) value) :
    ∃ sourceValue, Evaluates program environment expression sourceValue ∧
      lowerValue sourceValue = value ∧ valueWellScoped sourceValue := by
  obtain ⟨sourceValue, sourceEvaluation, loweredEq⟩ :=
    compositionalReflection_evaluation_reflected (program := program)
        (expression := expression) fragment
      environment value evaluated
  have scopedValue := evaluation_preserves_valueWellScoped program programScoped
    sourceEvaluation environmentScoped aligned
  exact ⟨sourceValue, sourceEvaluation, loweredEq, scopedValue⟩

/-- A checked decode supplies the let-layout invariant required by closure
well-scopedness preservation.  Thus the evaluation boundary needs only the
program and initial-environment invariants; callers do not reconstruct the
decoder's binder-count proof. -/
theorem decodeExprChecked_compositionalReflection_evaluation_reflected_scoped
    {fuel : Nat} {headers : List ExpansionLowering.Header} {node : CBindingWalk.Node}
    {expression : Expr}
    (decoded : NLisp.Named.decodeExprChecked fuel headers node = some expression)
    (program : Definitions) (programScoped : programWellScoped program)
    (fragment : CompositionalReflectionFragment program expression)
    (environment : Environment) (environmentScoped : environmentWellScoped environment)
    (value : PolyIR.Value)
    (evaluated : PolyIR.Evaluates (lowerDefinitions program) (lowerEnv environment)
      (lower (identities environment) expression) value) :
    ∃ sourceValue, Evaluates program environment expression sourceValue ∧
      lowerValue sourceValue = value ∧ valueWellScoped sourceValue := by
  exact compositionalReflection_evaluation_reflected_scoped program programScoped expression
    fragment environment environmentScoped (NLisp.Named.decodeExprChecked_spec decoded).2
    value evaluated

/-- Checked decoding of a global call constructs the corresponding recursive
reflection fragment directly from its definition lookup and child proofs. -/
theorem decodeExprChecked_compositionalReflection_globalApplication_reflected_scoped
    {fuel : Nat} {headers : List ExpansionLowering.Header} {node : CBindingWalk.Node}
    {index : Nat} {parameters : List Nat} {body : Expr} {arguments : List Expr}
    (decoded : NLisp.Named.decodeExprChecked fuel headers node =
      some (.app (.global index) arguments))
    (program : Definitions) (programScoped : programWellScoped program)
    (definitionFound : program[index]? = some (parameters, body))
    (bodyFragment : CompositionalReflectionFragment program body)
    (argumentFragments : ArithmeticFragmentList arguments)
    (environment : Environment) (environmentScoped : environmentWellScoped environment)
    (value : PolyIR.Value)
    (evaluated : PolyIR.Evaluates (lowerDefinitions program) (lowerEnv environment)
      (lower (identities environment) (.app (.global index) arguments)) value) :
    ∃ sourceValue,
      Evaluates program environment (.app (.global index) arguments) sourceValue ∧
        lowerValue sourceValue = value ∧ valueWellScoped sourceValue := by
  have fragment : CompositionalReflectionFragment program
      (.app (.global index) arguments) :=
    .globalApplicationBody index parameters body arguments definitionFound bodyFragment
      argumentFragments
  exact decodeExprChecked_compositionalReflection_evaluation_reflected_scoped decoded program
    programScoped fragment environment environmentScoped value evaluated

theorem decodeExprChecked_compositionalReflection_globalApplication_termination_iff
    {fuel : Nat} {headers : List ExpansionLowering.Header} {node : CBindingWalk.Node}
    {index : Nat} {parameters : List Nat} {body : Expr} {arguments : List Expr}
    (decoded : NLisp.Named.decodeExprChecked fuel headers node =
      some (.app (.global index) arguments))
    (program : Definitions) (definitionFound : program[index]? = some (parameters, body))
    (bodyFragment : CompositionalReflectionFragment program body)
    (argumentFragments : ArithmeticFragmentList arguments) (environment : Environment) :
    SourceTerminates program environment (.app (.global index) arguments) ↔
      LoweredTerminates program environment (.app (.global index) arguments) := by
  have fragment : CompositionalReflectionFragment program
      (.app (.global index) arguments) :=
    .globalApplicationBody index parameters body arguments definitionFound bodyFragment
      argumentFragments
  exact (decodeExprChecked_compositionalReflection_termination_iff decoded program fragment
    environment).1

theorem decodeExprChecked_compositionalReflection_globalApplication_divergence_iff
    {fuel : Nat} {headers : List ExpansionLowering.Header} {node : CBindingWalk.Node}
    {index : Nat} {parameters : List Nat} {body : Expr} {arguments : List Expr}
    (decoded : NLisp.Named.decodeExprChecked fuel headers node =
      some (.app (.global index) arguments))
    (program : Definitions) (definitionFound : program[index]? = some (parameters, body))
    (bodyFragment : CompositionalReflectionFragment program body)
    (argumentFragments : ArithmeticFragmentList arguments) (environment : Environment) :
    SourceDiverges program environment (.app (.global index) arguments) ↔
      LoweredDiverges program environment (.app (.global index) arguments) := by
  exact not_congr (decodeExprChecked_compositionalReflection_globalApplication_termination_iff
    decoded program definitionFound bodyFragment argumentFragments environment)

/-- Checked global calls also accept recursively reflected proofs for every
argument, rather than requiring the arithmetic-only argument fragment. -/
theorem decodeExprChecked_compositionalReflection_globalApplicationRows_reflected_scoped
    {fuel : Nat} {headers : List ExpansionLowering.Header} {node : CBindingWalk.Node}
    {index : Nat} {parameters : List Nat} {body : Expr} {arguments : List Expr}
    (decoded : NLisp.Named.decodeExprChecked fuel headers node =
      some (.app (.global index) arguments))
    (program : Definitions) (programScoped : programWellScoped program)
    (definitionFound : program[index]? = some (parameters, body))
    (bodyFragment : CompositionalReflectionFragment program body)
    (argumentRows : CompositionalReflectionRows program arguments)
    (environment : Environment) (environmentScoped : environmentWellScoped environment)
    (value : PolyIR.Value)
    (evaluated : PolyIR.Evaluates (lowerDefinitions program) (lowerEnv environment)
      (lower (identities environment) (.app (.global index) arguments)) value) :
    ∃ sourceValue,
      Evaluates program environment (.app (.global index) arguments) sourceValue ∧
        lowerValue sourceValue = value ∧ valueWellScoped sourceValue := by
  have fragment : CompositionalReflectionFragment program
      (.app (.global index) arguments) :=
    .globalApplicationRows index parameters body arguments definitionFound bodyFragment argumentRows
  exact decodeExprChecked_compositionalReflection_evaluation_reflected_scoped decoded program
    programScoped fragment environment environmentScoped value evaluated

theorem decodeExprChecked_compositionalReflection_globalApplicationRows_termination_iff
    {fuel : Nat} {headers : List ExpansionLowering.Header} {node : CBindingWalk.Node}
    {index : Nat} {parameters : List Nat} {body : Expr} {arguments : List Expr}
    (decoded : NLisp.Named.decodeExprChecked fuel headers node =
      some (.app (.global index) arguments))
    (program : Definitions) (definitionFound : program[index]? = some (parameters, body))
    (bodyFragment : CompositionalReflectionFragment program body)
    (argumentRows : CompositionalReflectionRows program arguments) (environment : Environment) :
    SourceTerminates program environment (.app (.global index) arguments) ↔
      LoweredTerminates program environment (.app (.global index) arguments) := by
  have fragment : CompositionalReflectionFragment program
      (.app (.global index) arguments) :=
    .globalApplicationRows index parameters body arguments definitionFound bodyFragment argumentRows
  exact (decodeExprChecked_compositionalReflection_termination_iff decoded program fragment
    environment).1

theorem decodeExprChecked_compositionalReflection_globalApplicationRows_divergence_iff
    {fuel : Nat} {headers : List ExpansionLowering.Header} {node : CBindingWalk.Node}
    {index : Nat} {parameters : List Nat} {body : Expr} {arguments : List Expr}
    (decoded : NLisp.Named.decodeExprChecked fuel headers node =
      some (.app (.global index) arguments))
    (program : Definitions) (definitionFound : program[index]? = some (parameters, body))
    (bodyFragment : CompositionalReflectionFragment program body)
    (argumentRows : CompositionalReflectionRows program arguments) (environment : Environment) :
    SourceDiverges program environment (.app (.global index) arguments) ↔
      LoweredDiverges program environment (.app (.global index) arguments) := by
  exact not_congr (decodeExprChecked_compositionalReflection_globalApplicationRows_termination_iff
    decoded program definitionFound bodyFragment argumentRows environment)

/-- Identity-indexed closure scope also survives reflection on the checked
compositional fragment. This connects the lexical identity invariant to the
captured environments of values produced by the source derivation. -/
theorem compositionalReflection_evaluation_reflected_identityScoped
    (program : Definitions) (programScoped : programIdentityScoped program)
    (expression : Expr) (fragment : CompositionalReflectionFragment program expression)
    (environment : Environment)
    (environmentScoped : EnvironmentIdentityScoped environment)
    (expressionScoped : IdentityScoped (identities environment) expression)
    (value : PolyIR.Value)
    (evaluated : PolyIR.Evaluates (lowerDefinitions program) (lowerEnv environment)
      (lower (identities environment) expression) value) :
    ∃ sourceValue, Evaluates program environment expression sourceValue ∧
      lowerValue sourceValue = value ∧ ValueIdentityScoped sourceValue := by
  obtain ⟨sourceValue, sourceEvaluation, loweredEq⟩ :=
    compositionalReflection_evaluation_reflected (program := program)
        (expression := expression) fragment
      environment value evaluated
  have scopedValue := evaluation_preserves_valueIdentityScoped program programScoped
    sourceEvaluation environmentScoped expressionScoped
  exact ⟨sourceValue, sourceEvaluation, loweredEq, scopedValue⟩

/-- Lambda application reflection and finite termination equivalence work for
any parameter and argument counts, provided each argument and the body lies
in the checked arithmetic fragment. -/
theorem lambda_application_termination_preserved_and_reflected
    (program : Definitions) (environment : Environment) (parameters : List Nat)
    (body : Expr) (arguments : List Expr)
    (bodyFragment : ArithmeticFragment body)
    (argumentsFragments : ArithmeticFragmentList arguments) :
    SourceTerminates program environment (.app (.lam parameters body) arguments) ↔
      LoweredTerminates program environment (.app (.lam parameters body) arguments) := by
  constructor
  · rintro ⟨sourceValue, sourceEval⟩
    exact ⟨lowerValue sourceValue, evaluation_preserved sourceEval⟩
  · rintro ⟨value, loweredEval⟩
    obtain ⟨sourceValue, sourceEval, _⟩ :=
      lambda_application_evaluation_reflected_of_fragments program environment parameters body
        arguments bodyFragment argumentsFragments value loweredEval
    exact ⟨sourceValue, sourceEval⟩

/-- Divergence, defined as absence of a finite big-step derivation, is also
preserved and reflected for the arbitrary-arity lambda fragment. -/
theorem lambda_application_divergence_preserved_and_reflected
    (program : Definitions) (environment : Environment) (parameters : List Nat)
    (body : Expr) (arguments : List Expr)
    (bodyFragment : ArithmeticFragment body)
    (argumentsFragments : ArithmeticFragmentList arguments) :
    SourceDiverges program environment (.app (.lam parameters body) arguments) ↔
      LoweredDiverges program environment (.app (.lam parameters body) arguments) := by
  exact not_congr (lambda_application_termination_preserved_and_reflected program environment
    parameters body arguments bodyFragment argumentsFragments)

/-- A well-formed global call whose body and arguments are in the arithmetic
reflection fragment preserves and reflects finite termination. Unlike the
closed arithmetic-expression theorem, this covers arbitrary call arity and a
global definition body evaluated in its own parameter environment. -/
theorem global_application_termination_preserved_and_reflected
    (program : Definitions) (environment : Environment) (index : Nat)
    (parameters : List Nat) (body : Expr) (arguments : List Expr)
    (definitionFound : program[index]? = some (parameters, body))
    (bodyFragment : ArithmeticFragment body)
    (argumentsFragments : ArithmeticFragmentList arguments) :
    SourceTerminates program environment (.app (.global index) arguments) ↔
      LoweredTerminates program environment (.app (.global index) arguments) := by
  constructor
  · rintro ⟨value, evaluated⟩
    exact ⟨lowerValue value, evaluation_preserved evaluated⟩
  · rintro ⟨value, evaluated⟩
    have reflected := global_application_evaluation_reflected_of_fragments
      program environment index parameters body arguments definitionFound bodyFragment
      argumentsFragments value (by simpa [lower_eq] using evaluated)
    obtain ⟨sourceValue, sourceEval, _⟩ := reflected
    exact ⟨sourceValue, sourceEval⟩

/-- Finite-derivation divergence agrees for the same global-call fragment;
the proof is the logical complement of the termination equivalence, so it
does not identify fuel exhaustion with nontermination. -/
theorem global_application_divergence_preserved_and_reflected
    (program : Definitions) (environment : Environment) (index : Nat)
    (parameters : List Nat) (body : Expr) (arguments : List Expr)
    (definitionFound : program[index]? = some (parameters, body))
    (bodyFragment : ArithmeticFragment body)
    (argumentsFragments : ArithmeticFragmentList arguments) :
    SourceDiverges program environment (.app (.global index) arguments) ↔
      LoweredDiverges program environment (.app (.global index) arguments) := by
  exact not_congr (global_application_termination_preserved_and_reflected
    program environment index parameters body arguments definitionFound bodyFragment
    argumentsFragments)

theorem arithmeticFragmentRows_arguments_reflected (program : Definitions)
    (environment : Environment) (expressions : List Expr)
    (fragments : ArithmeticFragmentRows expressions) :
    ∀ {irValues},
      PolyIR.ArgumentsEvaluate (lowerDefinitions program) (lowerEnv environment)
        (lowerMany (identities environment) expressions) irValues →
      ∃ sourceValues, ArgumentsEvaluate program environment expressions sourceValues ∧
        lowerValues sourceValues = irValues := by
  induction fragments with
  | nil =>
      intro irValues evaluated
      cases evaluated
      exact ⟨[], .nil, by simp [lowerValues]⟩
  | @cons head tail headFragment tailFragments tailIH =>
      intro irValues evaluated
      cases evaluated with
      | cons headEval tailEval =>
          obtain ⟨headValue, headSourceEval, headLowered⟩ :=
            arithmeticFragment_evaluation_reflected program head headFragment
              environment _ headEval
          obtain ⟨tailValues, tailSourceEval, tailLowered⟩ := tailIH tailEval
          exact ⟨headValue :: tailValues, .cons headSourceEval tailSourceEval, by
            simp [lowerValues, headLowered]
            simpa [lowerValues] using tailLowered⟩

/-- Reflect a finite evaluation of any-length `letMany` whose initializer
rows and body are in `ArithmeticFragment`. The only scope condition is the
source binder/initializer arity equality. -/
theorem arithmeticFragment_letMany_evaluation_reflected
    (program : Definitions) (environment : Environment) (identifiers : List Nat)
    (initializers : List Expr) (body : Expr)
    (scope : identifiers.length = initializers.length)
    (initializerFragments : ArithmeticFragmentRows initializers)
    (bodyFragment : ArithmeticFragment body) (value : PolyIR.Value)
    (evaluated : PolyIR.Evaluates (lowerDefinitions program) (lowerEnv environment)
      (lower (identities environment) (.letMany identifiers initializers body)) value) :
    ∃ sourceValue, Evaluates program environment
      (.letMany identifiers initializers body) sourceValue ∧ lowerValue sourceValue = value := by
  have bodyReflected : ∀ (sourceValues : List Value) (irValues : List PolyIR.Value),
      sourceValues.length = identifiers.length → lowerValues sourceValues = irValues →
      ∀ {result}, PolyIR.Evaluates (lowerDefinitions program)
        (irValues ++ lowerEnv environment) (lower (identifiers ++ identities environment) body)
        result → ∃ sourceResult, Evaluates program
          (bind identifiers sourceValues ++ environment) body sourceResult ∧
            lowerValue sourceResult = result := by
    intro sourceValues irValues sourceLength valuesLower result bodyEval
    have environmentAgreement :
        lowerEnv (bind identifiers sourceValues ++ environment) =
          irValues ++ lowerEnv environment := by
      rw [lowerEnv_bind_append identifiers sourceValues environment sourceLength,
        valuesLower]
    have localsAgreement : identities (bind identifiers sourceValues ++ environment) =
        identifiers ++ identities environment :=
      identities_bind_append identifiers sourceValues environment sourceLength
    have bodyTermAgreement :
        lower (identities (bind identifiers sourceValues ++ environment)) body =
          lower (identifiers ++ identities environment) body := by
      rw [localsAgreement]
    have bodyEval' : PolyIR.Evaluates (lowerDefinitions program)
        (lowerEnv (bind identifiers sourceValues ++ environment))
        (lower (identities (bind identifiers sourceValues ++ environment)) body) result := by
      rw [environmentAgreement, bodyTermAgreement]
      exact bodyEval
    have reflected := arithmeticFragment_evaluation_reflected program body bodyFragment
      (bind identifiers sourceValues ++ environment) result
      bodyEval'
    exact reflected
  rw [lower_eq] at evaluated
  exact letMany_evaluation_reflected program environment identifiers initializers body
    scope.symm (arithmeticFragmentRows_arguments_reflected program environment initializers
      initializerFragments) bodyReflected value evaluated

/-- A successful checked decode supplies the let layout condition for the
fragment reflection theorem, so callers need not provide a separate arity
assumption. -/
theorem decodeExprChecked_arithmeticFragment_letMany_evaluation_reflected
    {fuel : Nat} {headers : List ExpansionLowering.Header} {node : CBindingWalk.Node}
    {identifiers : List Nat} {initializers : List Expr} {body : Expr}
    (decoded : NLisp.Named.decodeExprChecked fuel headers node =
      some (.letMany identifiers initializers body))
    (initializerFragments : ArithmeticFragmentRows initializers)
    (bodyFragment : ArithmeticFragment body) (program : Definitions)
    (environment : Environment) (value : PolyIR.Value)
    (evaluated : PolyIR.Evaluates (lowerDefinitions program) (lowerEnv environment)
      (lower (identities environment) (.letMany identifiers initializers body)) value) :
    ∃ sourceValue, Evaluates program environment
      (.letMany identifiers initializers body) sourceValue ∧ lowerValue sourceValue = value := by
  exact arithmeticFragment_letMany_evaluation_reflected program environment identifiers
    initializers body (NLisp.Named.decodeExprChecked_letMany_lengths decoded) initializerFragments
    bodyFragment value evaluated

/-- The checked `letMany` fragment has matching finite-derivation termination
in Named and lowered semantics. -/
theorem decodeExprChecked_arithmeticFragment_letMany_termination_iff
    {fuel : Nat} {headers : List ExpansionLowering.Header} {node : CBindingWalk.Node}
    {identifiers : List Nat} {initializers : List Expr} {body : Expr}
    (decoded : NLisp.Named.decodeExprChecked fuel headers node =
      some (.letMany identifiers initializers body))
    (initializerFragments : ArithmeticFragmentRows initializers)
    (bodyFragment : ArithmeticFragment body) (program : Definitions)
    (environment : Environment) :
    SourceTerminates program environment (.letMany identifiers initializers body) ↔
      LoweredTerminates program environment (.letMany identifiers initializers body) := by
  constructor
  · rintro ⟨sourceValue, sourceEval⟩
    exact ⟨lowerValue sourceValue, evaluation_preserved sourceEval⟩
  · rintro ⟨value, evaluated⟩
    obtain ⟨sourceValue, sourceEval, _⟩ :=
      decodeExprChecked_arithmeticFragment_letMany_evaluation_reflected decoded
        initializerFragments bodyFragment program environment value evaluated
    exact ⟨sourceValue, sourceEval⟩

/-- The corresponding divergence statement is the complement of finite
termination equivalence, using divergence's derivation-based definition. -/
theorem decodeExprChecked_arithmeticFragment_letMany_divergence_iff
    {fuel : Nat} {headers : List ExpansionLowering.Header} {node : CBindingWalk.Node}
    {identifiers : List Nat} {initializers : List Expr} {body : Expr}
    (decoded : NLisp.Named.decodeExprChecked fuel headers node =
      some (.letMany identifiers initializers body))
    (initializerFragments : ArithmeticFragmentRows initializers)
    (bodyFragment : ArithmeticFragment body) (program : Definitions)
    (environment : Environment) :
    SourceDiverges program environment (.letMany identifiers initializers body) ↔
      LoweredDiverges program environment (.letMany identifiers initializers body) := by
  exact not_congr (decodeExprChecked_arithmeticFragment_letMany_termination_iff decoded
    initializerFragments bodyFragment program environment)

end NLisp.Named
