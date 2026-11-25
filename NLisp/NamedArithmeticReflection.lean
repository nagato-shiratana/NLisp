import NLisp.NamedDecoder

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
  | begin {expression} : BeginFragment expression →
      CompositionalReflectionFragment program expression
  | letMany {expression} : LetManyFragment expression →
      CompositionalReflectionFragment program expression

/-- One reflection theorem for the union of the compositional fragments. -/
theorem compositionalReflection_evaluation_reflected (program : Definitions)
    (expression : Expr) (fragment : CompositionalReflectionFragment program expression)
    (environment : Environment) (value : PolyIR.Value)
    (evaluated : PolyIR.Evaluates (lowerDefinitions program) (lowerEnv environment)
      (lower (identities environment) expression) value) :
    ∃ sourceValue, Evaluates program environment expression sourceValue ∧
      lowerValue sourceValue = value := by
  cases fragment with
  | arithmetic proof => exact arithmeticFragment_evaluation_reflected program expression proof environment value evaluated
  | application proof => exact applicationFragment_evaluation_reflected program expression proof environment value evaluated
  | begin proof => exact beginFragment_evaluation_reflected program expression proof environment value evaluated
  | letMany proof => exact letManyFragment_evaluation_reflected program expression proof environment value evaluated

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
      compositionalReflection_evaluation_reflected program expression fragment
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
    compositionalReflection_evaluation_reflected program expression fragment
      environment value evaluated
  have scopedValue := evaluation_preserves_valueWellScoped program programScoped
    sourceEvaluation environmentScoped aligned
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
