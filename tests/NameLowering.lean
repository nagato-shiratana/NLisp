import NLisp.NamedDecoder
import NLisp.EvaluatorCompleteness

open NLisp

private theorem closureSource : Named.Evaluates [] []
    (.app (.lam [13, 16] (.var 16)) [.int 1, .int 42]) (.int 42) :=
  .appClosure .lam (.cons .int (.cons .int .nil)) rfl (.var rfl)

example : PolyIR.Evaluates [] []
    (Named.lower [] (.app (.lam [13, 16] (.var 16)) [.int 1, .int 42])) (.int 42) :=
  Named.evaluation_preserved closureSource

private theorem parallelSource : Named.Evaluates [] [(13, .int 10)]
    (.letMany [16, 19] [.int 1, .var 13] (.var 19)) (.int 10) :=
  .letMany (.cons .int (.cons (.var rfl) .nil)) rfl (.var rfl)

example : PolyIR.Evaluates [] [.int 10]
    (Named.lower [13] (.letMany [16, 19] [.int 1, .var 13] (.var 19))) (.int 10) :=
  Named.evaluation_preserved parallelSource

example : Named.Evaluates [] []
    (.matchList (.cons (.int 42) .nil) (.int 0) 13 16 (.var 13)) (.int 42) :=
  .matchCons (.cons .int .nil) (.var rfl)

-- A source semantic derivation also yields eventual success of the real IR evaluator.
example : ∃ fuel, PolyIR.evaluate [] fuel []
    (Named.lower [] (.app (.lam [13, 16] (.var 16)) [.int 1, .int 42])) = .ok (.int 42) :=
  PolyIR.evaluate_complete (Named.evaluation_preserved closureSource)

private def a (n : String) (token : Nat := 4) (selected : Nat := 0) : CBindingWalk.Node :=
  .atom ⟨n, none, token⟩ selected

private def sourceForm : CBindingWalk.Node := .list [a "defun", a "main" 10,
  .list [], a "Integer", .list [a "+" 22 3, a "40", a "2"]]

example : Named.decodeExprs 10 [] [a "1", a "2"] =
    some [.int 1, .int 2] := by rfl

example {expressions : List Named.Expr}
    (decoded : Named.decodeExprs 10 [] [a "1", a "2"] = some expressions) :
    expressions.length = 2 :=
  Named.decodeExprs_length decoded

example {bindings : List CBindingWalk.Node} {ids : List Nat} {values : List CBindingWalk.Node}
    (decoded : Named.letParts bindings = some (ids, values)) :
    ids.length = values.length :=
  Named.letParts_lengths decoded

example : (Named.decodeProgram 40 [sourceForm]).isSome = true := by decide
example : ExpansionLowering.checkMain 40 [sourceForm] 0 = true := by decide
example : ExpansionLowering.checkMain 40 [sourceForm] 1 = false := by decide

-- Decoding preserves identities; conversion to positional locals is a separate function.
example : Named.decodeExpr 40 [] (a "x" 28 13) = some (.var 13) := by rfl
example : Named.lower [16, 13] (.var 13) = .var 1 := by rfl

example : Named.lowerEnv (Named.bind [13, 16] [.int 2, .bool true] ++ [(21, .unit)]) =
    [PolyIR.Value.int 2, .bool true, .unit] := by
  exact Named.lowerEnv_bind_append [13, 16] [.int 2, .bool true] [(21, .unit)] rfl

example : Named.identities (Named.bind [13, 16] [.int 2, .bool true] ++ [(21, .unit)]) =
    [13, 16, 21] := by
  exact Named.identities_bind_append [13, 16] [.int 2, .bool true] [(21, .unit)] rfl

example : Named.lower (Named.identities (Named.bind [13, 16] [.int 2, .bool true] ++
      [(21, .unit)])) (.var 13) = .var 0 := by
  exact Named.lower_call_body [13, 16] [.int 2, .bool true] [(21, .unit)] (.var 13) rfl

example : ∃ value,
    Named.Evaluates [] [] (.letMany [13] [.int 42] (.var 13)) value ∧
      Named.lowerValue value = PolyIR.Value.int 42 := by
  have argumentsReflected : ∀ {irValues},
      PolyIR.ArgumentsEvaluate [] [] [(.int 42)] irValues →
      ∃ sourceValues, Named.ArgumentsEvaluate [] [] [(.int 42)] sourceValues ∧
        Named.lowerValues sourceValues = irValues := by
    intro irValues evaluated
    cases evaluated with
    | cons headEval tailEval =>
        cases tailEval with
        | nil =>
            obtain ⟨sourceHead, sourceHeadEval, headLowered⟩ :=
              Named.integer_evaluation_reflected [] [] 42 _ headEval
            exact ⟨[sourceHead], .cons sourceHeadEval .nil, by
              simp [Named.lowerValues, headLowered]⟩
  have bodyReflected : ∀ (sourceValues : List Named.Value)
      (irValues : List PolyIR.Value), sourceValues.length = 1 →
      Named.lowerValues sourceValues = irValues → ∀ {result},
        PolyIR.Evaluates [] (irValues ++ []) (.var 0) result →
        ∃ sourceValue,
          Named.Evaluates [] (Named.bind [13] sourceValues ++ []) (.var 13) sourceValue ∧
            Named.lowerValue sourceValue = result := by
    intro sourceValues irValues arity lowered result evaluated
    cases sourceValues with
    | nil => simp at arity
    | cons sourceHead rest =>
        cases rest with
        | nil =>
            have irValuesEq : irValues = [Named.lowerValue sourceHead] := by
              simpa [Named.lowerValues] using lowered.symm
            subst irValues
            have sourceEval : PolyIR.Evaluates [] [Named.lowerValue sourceHead]
                (.var (Named.position 13 [13])) result := by
              simpa [Named.position] using evaluated
            exact Named.variable_evaluation_reflected [] [(13, sourceHead)] 13 result (by
              simpa [Named.lowerDefinitions, Named.lowerEnv, Named.identities, Named.position]
                using sourceEval)
        | cons _ _ => simp at arity
  have irEval : PolyIR.Evaluates [] []
      (.letMany [.int 42] (.var 0)) (.int 42) :=
    .letMany (.cons .int .nil) (.var (by rfl))
  exact Named.letMany_evaluation_reflected [] [] [13] [.int 42] (.var 13) rfl
    argumentsReflected bodyReflected (.int 42)
    (by simpa [Named.lower_eq, Named.lowerMany_eq] using irEval)

-- Reverse reflection requires well-scoped source letMany binders: lowering erases their IDs.
example : Named.lower [] (.letMany [] [.int 42] (.var 0)) =
    .letMany [.int 42] (.var 0) := rfl

example : PolyIR.Evaluates [] [] (.letMany [.int 42] (.var 0)) (.int 42) :=
  .letMany (.cons .int .nil) (.var (by rfl))

example : ¬ ∃ value,
    Named.Evaluates [] [] (.letMany [] [.int 42] (.var 0)) value := by
  intro evaluated
  obtain ⟨value, evaluated⟩ := evaluated
  cases evaluated with
  | letMany arguments arity _ =>
      cases arguments with
      | cons _ tail =>
          cases tail
          simp at arity

example : ∃ value,
    Named.Evaluates [] []
      (.matchList (.cons (.int 2) .nil) (.int 0) 13 16 (.var 13)) value ∧
      Named.lowerValue value = PolyIR.Value.int 2 := by
  have intTwo : ∀ {value}, PolyIR.Evaluates [] [] (.int 2) value →
      ∃ sourceValue, Named.Evaluates [] [] (.int 2) sourceValue ∧
        Named.lowerValue sourceValue = value := by
    intro value evaluated
    exact Named.integer_evaluation_reflected [] [] 2 value evaluated
  have nilReflected : ∀ {value}, PolyIR.Evaluates [] [] .nil value →
      ∃ sourceValue, Named.Evaluates [] [] .nil sourceValue ∧
        Named.lowerValue sourceValue = value := by
    intro value evaluated
    exact Named.nil_evaluation_reflected [] [] value evaluated
  have targetReflected : ∀ {value},
      PolyIR.Evaluates [] [] (.cons (.int 2) .nil) value →
      ∃ sourceValue, Named.Evaluates [] [] (.cons (.int 2) .nil) sourceValue ∧
        Named.lowerValue sourceValue = value := by
    intro value evaluated
    exact Named.cons_evaluation_reflected [] [] (.int 2) .nil intTwo nilReflected value evaluated
  have emptyReflected : ∀ {value}, PolyIR.Evaluates [] [] (.int 0) value →
      ∃ sourceValue, Named.Evaluates [] [] (.int 0) sourceValue ∧
        Named.lowerValue sourceValue = value := by
    intro value evaluated
    exact Named.integer_evaluation_reflected [] [] 0 value evaluated
  have consBodyReflected : ∀ (sourceHead sourceTail : Named.Value)
      (irHead irTail : PolyIR.Value), Named.lowerValue sourceHead = irHead →
      Named.lowerValue sourceTail = irTail → ∀ {value},
      PolyIR.Evaluates [] (irHead :: irTail :: []) (.var 0) value →
      ∃ sourceValue,
        Named.Evaluates [] [(13, sourceHead), (16, sourceTail)] (.var 13) sourceValue ∧
          Named.lowerValue sourceValue = value := by
    intro sourceHead sourceTail irHead irTail headLowered tailLowered value evaluated
    exact Named.variable_evaluation_reflected [] [(13, sourceHead), (16, sourceTail)] 13 value
      (by simpa [Named.lowerDefinitions, Named.lowerEnv, Named.identities,
        Named.position, headLowered, tailLowered]
        using evaluated)
  have irEval : PolyIR.Evaluates [] []
      (.matchList (.cons (.int 2) .nil) (.int 0) (.var 0)) (.int 2) :=
    .matchCons (.cons .int .nil) (.var (by rfl))
  exact Named.matchList_evaluation_reflected [] [] (.cons (.int 2) .nil) (.int 0) 13 16
    (.var 13) targetReflected emptyReflected consBodyReflected (.int 2)
    (by simpa [Named.lower_eq, Named.lowerMany_eq] using irEval)

example : ∃ value,
    Named.Evaluates [] [] (.matchOption (.some (.int 3)) (.int 0) 13 (.var 13)) value ∧
      Named.lowerValue value = PolyIR.Value.int 3 := by
  have intThree : ∀ {value}, PolyIR.Evaluates [] [] (.int 3) value →
      ∃ sourceValue, Named.Evaluates [] [] (.int 3) sourceValue ∧
        Named.lowerValue sourceValue = value := by
    intro value evaluated
    exact Named.integer_evaluation_reflected [] [] 3 value evaluated
  have targetReflected : ∀ {value}, PolyIR.Evaluates [] [] (.some (.int 3)) value →
      ∃ sourceValue, Named.Evaluates [] [] (.some (.int 3)) sourceValue ∧
        Named.lowerValue sourceValue = value := by
    intro value evaluated
    exact Named.some_evaluation_reflected [] [] (.int 3) intThree value evaluated
  have emptyReflected : ∀ {value}, PolyIR.Evaluates [] [] (.int 0) value →
      ∃ sourceValue, Named.Evaluates [] [] (.int 0) sourceValue ∧
        Named.lowerValue sourceValue = value := by
    intro value evaluated
    exact Named.integer_evaluation_reflected [] [] 0 value evaluated
  have someBodyReflected : ∀ (sourceItem : Named.Value) (irItem : PolyIR.Value),
      Named.lowerValue sourceItem = irItem → ∀ {value},
      PolyIR.Evaluates [] (irItem :: []) (.var 0) value →
      ∃ sourceValue,
        Named.Evaluates [] [(13, sourceItem)] (.var 13) sourceValue ∧
          Named.lowerValue sourceValue = value := by
    intro sourceItem irItem itemLowered value evaluated
    exact Named.variable_evaluation_reflected [] [(13, sourceItem)] 13 value (by
      simpa [Named.lowerDefinitions, Named.lowerEnv, Named.identities,
        Named.position, itemLowered] using evaluated)
  have irEval : PolyIR.Evaluates [] []
      (.matchOption (.some (.int 3)) (.int 0) (.var 0)) (.int 3) :=
    .matchSome (.some .int) (.var (by rfl))
  exact Named.matchOption_evaluation_reflected [] [] (.some (.int 3)) (.int 0) 13 (.var 13)
    targetReflected emptyReflected someBodyReflected (.int 3)
    (by simpa [Named.lower_eq, Named.lowerMany_eq] using irEval)

example : ∃ value,
    Named.lookup 13 [(7, .bool true), (13, .int 42)] = some value ∧
      Named.lowerValue value = .int 42 := by
  apply Named.lookup_lowered_reflects [(7, .bool true), (13, .int 42)] 13 (.int 42)
  rfl

example : ∃ value,
    Named.lookup 13 [(13, .int 42), (13, .int 0)] = some value ∧
      Named.lowerValue value = .int 42 := by
  apply Named.lookup_lowered_reflects [(13, .int 42), (13, .int 0)] 13 (.int 42)
  rfl

example : ∃ value, Named.Evaluates [] [(13, .int 42)] (.var 13) value ∧
    Named.lowerValue value = .int 42 := by
  apply Named.variable_evaluation_reflected [] [(13, .int 42)] 13 (.int 42)
  exact PolyIR.Evaluates.var (by rfl)

example : Named.Evaluates [([], .int 42)] [] (.global 0) (.global 0) := by
  have irEval : PolyIR.Evaluates (Named.lowerDefinitions [([], .int 42)]) []
      (.global 0) (.global 0) := .global (by rfl)
  exact Named.global_evaluation_reflected [([], .int 42)] [] 0 irEval

example : ∃ value, Named.Evaluates [] [] (.bool true) value ∧
    Named.lowerValue value = PolyIR.Value.bool true := by
  exact Named.boolean_evaluation_reflected [] [] true (.bool true) PolyIR.Evaluates.bool

example : ∃ value, Named.Evaluates [] [] .nil value ∧
    Named.lowerValue value = PolyIR.Value.nil := by
  exact Named.nil_evaluation_reflected [] [] PolyIR.Value.nil PolyIR.Evaluates.nil

example : ∃ value, Named.Evaluates [] [] (.lam [13] (.var 13)) value ∧
    Named.lowerValue value = PolyIR.Value.closure 1 (.var 0) [] := by
  have irEval : PolyIR.Evaluates [] [] (.lam 1 (.var 0)) (.closure 1 (.var 0) []) :=
    PolyIR.Evaluates.lam
  exact Named.lambda_evaluation_reflected [] [] [13] (.var 13) (.closure 1 (.var 0) [])
    (by simpa [Named.lower, Named.lower_eq, Named.lowerEnv, Named.identities, Named.position]
      using irEval)

example : ∃ value, Named.Evaluates [] [] (.add (.int 3) (.int 5)) value ∧
    Named.lowerValue value = PolyIR.Value.int 8 := by
  have literalReflected : ∀ {value},
      PolyIR.Evaluates [] [] (.int 3) value →
      ∃ sourceValue, Named.Evaluates [] [] (.int 3) sourceValue ∧
        Named.lowerValue sourceValue = value := by
    intro value evaluated
    exact Named.integer_evaluation_reflected [] [] 3 value evaluated
  have irEval : PolyIR.Evaluates [] [] (.add (.int 3) (.int 5)) (.int 8) :=
    .add .int .int
  exact Named.add_evaluation_reflected [] [] (.int 3) (.int 5)
    literalReflected (by
      intro value evaluated
      exact Named.integer_evaluation_reflected [] [] 5 value evaluated)
    (.int 8) irEval

private theorem reflectIntegerLiteral (n : Int) {value : PolyIR.Value}
    (evaluated : PolyIR.Evaluates [] [] (.int n) value) :
    ∃ sourceValue, Named.Evaluates [] [] (.int n) sourceValue ∧
      Named.lowerValue sourceValue = value :=
  Named.integer_evaluation_reflected [] [] n value evaluated

example : ∃ value, Named.Evaluates [] [] (.sub (.int 9) (.int 4)) value ∧
    Named.lowerValue value = .int 5 := by
  exact Named.sub_evaluation_reflected [] [] (.int 9) (.int 4)
    (reflectIntegerLiteral 9) (reflectIntegerLiteral 4) (.int 5) (.sub .int .int)

example : ∃ value, Named.Evaluates [] [] (.mul (.int 3) (.int 4)) value ∧
    Named.lowerValue value = .int 12 := by
  exact Named.mul_evaluation_reflected [] [] (.int 3) (.int 4)
    (reflectIntegerLiteral 3) (reflectIntegerLiteral 4) (.int 12) (.mul .int .int)

example : ∃ value, Named.Evaluates [] [] (.le (.int 2) (.int 3)) value ∧
    Named.lowerValue value = .bool true := by
  exact Named.le_evaluation_reflected [] [] (.int 2) (.int 3)
    (reflectIntegerLiteral 2) (reflectIntegerLiteral 3) (.bool true) (.le .int .int)

example : ∃ value, Named.Evaluates [] [] (.intEq (.int 5) (.int 5)) value ∧
    Named.lowerValue value = .bool true := by
  exact Named.intEq_evaluation_reflected [] [] (.int 5) (.int 5)
    (reflectIntegerLiteral 5) (reflectIntegerLiteral 5) (.bool true) (.intEq .int .int)

example : ∃ value, Named.Evaluates [] [] (.ite (.bool true) (.int 6) (.int 7)) value ∧
    Named.lowerValue value = .int 6 := by
  have boolReflected : ∀ {value},
      PolyIR.Evaluates [] [] (.bool true) value →
      ∃ sourceValue, Named.Evaluates [] [] (.bool true) sourceValue ∧
        Named.lowerValue sourceValue = value := by
    intro value evaluated
    exact Named.boolean_evaluation_reflected [] [] true value evaluated
  exact Named.ite_evaluation_reflected [] [] (.bool true) (.int 6) (.int 7)
    boolReflected (reflectIntegerLiteral 6) (reflectIntegerLiteral 7)
    (.int 6) (.ifTrue .bool .int)

example : ∃ value, Named.Evaluates [] [] (.some (.int 9)) value ∧
    Named.lowerValue value = PolyIR.Value.some (.int 9) := by
  have innerReflected : ∀ {value},
      PolyIR.Evaluates [] [] (.int 9) value →
      ∃ sourceValue, Named.Evaluates [] [] (.int 9) sourceValue ∧
        Named.lowerValue sourceValue = value := by
    intro value evaluated
    exact Named.integer_evaluation_reflected [] [] 9 value evaluated
  exact Named.some_evaluation_reflected [] [] (.int 9) innerReflected
    (.some (.int 9)) (.some .int)

example : ∃ value, Named.Evaluates [] [] (.cons (.int 4) .nil) value ∧
    Named.lowerValue value = PolyIR.Value.cons (.int 4) .nil := by
  have headReflected : ∀ {value},
      PolyIR.Evaluates [] [] (.int 4) value →
      ∃ sourceValue, Named.Evaluates [] [] (.int 4) sourceValue ∧
        Named.lowerValue sourceValue = value := by
    intro value evaluated
    exact Named.integer_evaluation_reflected [] [] 4 value evaluated
  have tailReflected : ∀ {value},
      PolyIR.Evaluates [] [] .nil value →
      ∃ sourceValue, Named.Evaluates [] [] .nil sourceValue ∧
        Named.lowerValue sourceValue = value := by
    intro value evaluated
    exact Named.nil_evaluation_reflected [] [] value evaluated
  exact Named.cons_evaluation_reflected [] [] (.int 4) .nil headReflected tailReflected
    (.cons (.int 4) .nil) (.cons .int .nil)

#print axioms Named.evaluation_preserved
#print axioms Named.letParts_lengths
#print axioms Named.decodeExprs_length
#print axioms Named.lookup_lowered
#print axioms Named.lookup_lowered_reflects
#print axioms Named.variable_evaluation_reflected
#print axioms Named.definitions_lookup_reflects
#print axioms Named.global_evaluation_reflected
#print axioms Named.boolean_evaluation_reflected
#print axioms Named.nil_evaluation_reflected
#print axioms Named.lambda_evaluation_reflected
#print axioms Named.add_evaluation_reflected
#print axioms Named.sub_evaluation_reflected
#print axioms Named.mul_evaluation_reflected
#print axioms Named.le_evaluation_reflected
#print axioms Named.intEq_evaluation_reflected
#print axioms Named.ite_evaluation_reflected
#print axioms Named.matchList_evaluation_reflected
#print axioms Named.matchOption_evaluation_reflected
#print axioms Named.appClosure_evaluation_reflected
#print axioms Named.appGlobal_evaluation_reflected
#print axioms Named.app_evaluation_reflected
#print axioms Named.some_evaluation_reflected
#print axioms Named.cons_evaluation_reflected
#print axioms Named.definitions_lookup
