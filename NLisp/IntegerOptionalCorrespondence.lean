import NLisp.Core
import NLisp.GlobalIR

namespace NLisp

/-- Shared result model for the integer quotient/remainder operations. -/
inductive IntegerOptionValue where
  | none
  | some (value : Int)
  deriving DecidableEq, Repr

def IntegerOptionValue.evaluate (operation : TypedExpansion.Primitive)
    (left right : Int) : IntegerOptionValue :=
  match TypedExpansion.integerOptional operation left right with
  | Option.none => IntegerOptionValue.none
  | Option.some value => IntegerOptionValue.some value

def IntegerOptionValue.toCore : IntegerOptionValue → Expr [] (.option .integer)
  | .none => .none
  | .some value => .some (.int value)

def IntegerOptionValue.toRuntimeValue : IntegerOptionValue → PolyIR.Value
  | .none => .none
  | .some value => .some (.int value)

/-- The shared value's Core representation is exactly the result produced by
the quotient/remainder small-step rules. -/
theorem integerOptionValue_toCore_matches_stepResult
    (operation : TypedExpansion.Primitive) (left right : Int) :
    (IntegerOptionValue.evaluate operation left right).toCore =
      integerOptionalResult operation left right := by
  unfold IntegerOptionValue.evaluate IntegerOptionValue.toCore integerOptionalResult
  cases TypedExpansion.integerOptional operation left right <;> rfl

/-- The concrete curried Core quotient builtin reaches the shared result
representation through ordinary beta steps and the Option Integer primitive
step. -/
theorem quotientBuiltin_application_steps_shared (dividend divisor : Int) :
    Steps
      (.app (.app quotientBuiltin (.int dividend)) (.int divisor))
      (IntegerOptionValue.evaluate .quotient dividend divisor).toCore := by
  rw [integerOptionValue_toCore_matches_stepResult]
  exact quotientBuiltin_application_steps dividend divisor

theorem remainderBuiltin_application_steps_shared (dividend divisor : Int) :
    Steps
      (.app (.app remainderBuiltin (.int dividend)) (.int divisor))
      (IntegerOptionValue.evaluate .remainder dividend divisor).toCore := by
  rw [integerOptionValue_toCore_matches_stepResult]
  exact remainderBuiltin_application_steps dividend divisor

/-- The concrete quotient call both evaluates to the shared result and
produces a value accepted by GlobalIR's Option Integer typing relation. -/
theorem quotientBuiltin_application_steps_and_runtime_typed
    (dividend divisor : Int) :
    Steps
        (.app (.app quotientBuiltin (.int dividend)) (.int divisor))
        (IntegerOptionValue.evaluate .quotient dividend divisor).toCore ∧
      PolyIR.ValueTyped []
        (IntegerOptionValue.evaluate .quotient dividend divisor).toRuntimeValue
        (.option .integer) := by
  refine ⟨quotientBuiltin_application_steps_shared dividend divisor, ?_⟩
  unfold IntegerOptionValue.evaluate IntegerOptionValue.toRuntimeValue
  cases TypedExpansion.integerOptional .quotient dividend divisor with
  | none => exact .none
  | some value => exact .some .int

/-- The corresponding evaluation and runtime typing guarantee for remainder,
including the zero-divisor `none` result. -/
theorem remainderBuiltin_application_steps_and_runtime_typed
    (dividend divisor : Int) :
    Steps
        (.app (.app remainderBuiltin (.int dividend)) (.int divisor))
        (IntegerOptionValue.evaluate .remainder dividend divisor).toCore ∧
      PolyIR.ValueTyped []
        (IntegerOptionValue.evaluate .remainder dividend divisor).toRuntimeValue
        (.option .integer) := by
  refine ⟨remainderBuiltin_application_steps_shared dividend divisor, ?_⟩
  unfold IntegerOptionValue.evaluate IntegerOptionValue.toRuntimeValue
  cases TypedExpansion.integerOptional .remainder dividend divisor with
  | none => exact .none
  | some value => exact .some .int

/-- The same value translates to GlobalIR's runtime Option representation. -/
theorem integerOptionValue_toRuntime_matches_global
    (operation : TypedExpansion.Primitive) (left right : Int) :
    (IntegerOptionValue.evaluate operation left right).toRuntimeValue =
      GlobalIR.integerOptionalRuntimeValue operation left right := by
  unfold IntegerOptionValue.evaluate IntegerOptionValue.toRuntimeValue
    GlobalIR.integerOptionalRuntimeValue
  cases TypedExpansion.integerOptional operation left right <;> rfl


/-- The shared result is accepted by the polymorphic runtime's Option Integer
value typing relation. -/
theorem integerOptionValue_runtime_typed
    (globals : List Surface.Signature) (operation : TypedExpansion.Primitive)
    (left right : Int) :
    PolyIR.ValueTyped globals
      (IntegerOptionValue.evaluate operation left right).toRuntimeValue
      (.option .integer) := by
  rw [integerOptionValue_toRuntime_matches_global]
  exact GlobalIR.integerOptionalRuntimeValue_typed globals operation left right

/-- Evaluation of the GlobalIR Option-integer call helper agrees with the
shared result model whenever both argument terms evaluate to integers. -/
theorem evaluateIntegerOptionalCall_matches_shared
    (globals : List Surface.Signature) (program : List GlobalIR.Definition)
    (store : GlobalIR.Store) (operation : GlobalIR.IntegerOptionalOperation)
    (fuel : Nat) (environment : List PolyIR.Value) (left right : PolyIR.Term)
    (dividend divisor : Int)
    (leftEvaluates : GlobalIR.evaluate program store fuel environment left =
      .ok (.int dividend))
    (rightEvaluates : GlobalIR.evaluate program store fuel environment right =
      .ok (.int divisor)) :
    GlobalIR.evaluateIntegerOptionalCall program store operation (fuel + 1)
        environment left right =
      .ok (IntegerOptionValue.evaluate operation.toPrimitive dividend divisor).toRuntimeValue ∧
    PolyIR.ValueTyped globals
      (IntegerOptionValue.evaluate operation.toPrimitive dividend divisor).toRuntimeValue
      (.option .integer) := by
  obtain ⟨evaluated, _typed⟩ := GlobalIR.evaluateIntegerOptionalCall_of_integer_children
    globals program store operation fuel environment left right dividend divisor
    leftEvaluates rightEvaluates
  refine ⟨?_, integerOptionValue_runtime_typed globals operation.toPrimitive dividend divisor⟩
  rw [integerOptionValue_toRuntime_matches_global]
  exact evaluated

/-- A zero divisor is represented by a successful Option result (`none`),
not by an evaluator fault. This lifts the partial arithmetic specification
to the GlobalIR native-call boundary for both quotient and remainder. -/
theorem evaluateIntegerOptionalCall_zero_divisor
    (program : List GlobalIR.Definition) (store : GlobalIR.Store)
    (operation : GlobalIR.IntegerOptionalOperation) (fuel : Nat)
    (environment : List PolyIR.Value) (dividend : Int) :
    GlobalIR.evaluateIntegerOptionalCall program store operation (fuel + 2)
      environment (.int dividend) (.int 0) = .ok .none := by
  have leftEvaluates : GlobalIR.evaluate program store (fuel + 1) environment
      (.int dividend) = .ok (.int dividend) := by rfl
  have rightEvaluates : GlobalIR.evaluate program store (fuel + 1) environment
      (.int 0) = .ok (.int 0) := by rfl
  obtain ⟨evaluated, _typed⟩ := evaluateIntegerOptionalCall_matches_shared [] program store
    operation (fuel + 1) environment (.int dividend) (.int 0) dividend 0
    leftEvaluates rightEvaluates
  simpa [IntegerOptionValue.evaluate, IntegerOptionValue.toRuntimeValue,
    TypedExpansion.integerOptional, GlobalIR.IntegerOptionalOperation.toPrimitive]
    using evaluated

/-- The zero-divisor result remains a well-typed Option Integer runtime value. -/
theorem evaluateIntegerOptionalCall_zero_divisor_typed
    (globals : List Surface.Signature) (program : List GlobalIR.Definition)
    (store : GlobalIR.Store) (operation : GlobalIR.IntegerOptionalOperation)
    (fuel : Nat) (environment : List PolyIR.Value) (dividend : Int) :
    GlobalIR.evaluateIntegerOptionalCall program store operation (fuel + 2)
      environment (.int dividend) (.int 0) = .ok .none ∧
    PolyIR.ValueTyped globals .none (.option .integer) := by
  exact ⟨evaluateIntegerOptionalCall_zero_divisor program store operation fuel
    environment dividend, .none⟩

/-- For a nonzero divisor, the GlobalIR quotient and remainder calls both
return the arithmetic results from the truncating integer specification,
and those returned integers reconstruct the dividend. -/
theorem evaluateIntegerOptionalCall_division_equation
    (globals : List Surface.Signature) (program : List GlobalIR.Definition)
    (store : GlobalIR.Store) (fuel : Nat) (environment : List PolyIR.Value)
    (dividend divisor : Int) (nonzero : divisor ≠ 0) :
    ∃ quotient remainder,
      GlobalIR.evaluateIntegerOptionalCall program store .quotient (fuel + 2)
        environment (.int dividend) (.int divisor) =
          .ok (.some (.int quotient)) ∧
      GlobalIR.evaluateIntegerOptionalCall program store .remainder (fuel + 2)
        environment (.int dividend) (.int divisor) =
          .ok (.some (.int remainder)) ∧
      dividend = quotient * divisor + remainder ∧
      quotient.natAbs = dividend.natAbs / divisor.natAbs ∧
      (if (dividend < 0) = (divisor < 0) then 0 ≤ quotient else quotient ≤ 0) ∧
      remainder.natAbs < divisor.natAbs ∧
      (dividend < 0 → remainder ≤ 0) ∧ (0 ≤ dividend → 0 ≤ remainder) ∧
      PolyIR.ValueTyped globals (.some (.int quotient)) (.option .integer) ∧
      PolyIR.ValueTyped globals (.some (.int remainder)) (.option .integer) := by
  obtain ⟨quotient, remainder, quotientSpec, remainderSpec, reconstructs⟩ :=
    TypedExpansion.integerOptional_division_equation dividend divisor nonzero
  have quotientSpec' : some (TypedExpansion.truncQuotient dividend divisor) = some quotient := by
    simpa [TypedExpansion.integerOptional, nonzero] using quotientSpec
  have quotientEq : quotient = TypedExpansion.truncQuotient dividend divisor :=
    (Option.some.inj quotientSpec').symm
  have remainderSpec' : some
      (dividend - TypedExpansion.truncQuotient dividend divisor * divisor) = some remainder := by
    simpa [TypedExpansion.integerOptional, nonzero] using remainderSpec
  have remainderEq : remainder =
      dividend - TypedExpansion.truncQuotient dividend divisor * divisor :=
    (Option.some.inj remainderSpec').symm
  have quotientMagnitude : quotient.natAbs = dividend.natAbs / divisor.natAbs := by
    rw [quotientEq]
    exact TypedExpansion.truncQuotient_natAbs dividend divisor
  have quotientSign :
      (if (dividend < 0) = (divisor < 0) then 0 ≤ quotient else quotient ≤ 0) := by
    by_cases sameSign : (dividend < 0) = (divisor < 0)
    · simp only [if_pos sameSign]
      rw [quotientEq]
      exact TypedExpansion.truncQuotient_nonneg_of_same_sign dividend divisor sameSign
    · simp only [if_neg sameSign]
      rw [quotientEq]
      exact TypedExpansion.truncQuotient_nonpos_of_opposite_sign dividend divisor sameSign
  have remainderMagnitude : remainder.natAbs < divisor.natAbs := by
    rw [remainderEq]
    exact TypedExpansion.truncRemainder_natAbs_lt dividend divisor nonzero
  have remainderSign : (dividend < 0 → remainder ≤ 0) ∧
      (0 ≤ dividend → 0 ≤ remainder) := by
    rw [remainderEq]
    exact TypedExpansion.truncRemainder_sign dividend divisor
  have leftEvaluates : GlobalIR.evaluate program store (fuel + 1) environment
      (.int dividend) = .ok (.int dividend) := by rfl
  have rightEvaluates : GlobalIR.evaluate program store (fuel + 1) environment
      (.int divisor) = .ok (.int divisor) := by rfl
  obtain ⟨quotientEval, quotientTyped⟩ := evaluateIntegerOptionalCall_matches_shared globals
    program store .quotient (fuel + 1) environment (.int dividend) (.int divisor)
    dividend divisor leftEvaluates rightEvaluates
  obtain ⟨remainderEval, remainderTyped⟩ := evaluateIntegerOptionalCall_matches_shared globals
    program store .remainder (fuel + 1) environment (.int dividend) (.int divisor)
    dividend divisor leftEvaluates rightEvaluates
  have quotientRuntime : GlobalIR.evaluateIntegerOptionalCall program store .quotient
      (fuel + 2) environment (.int dividend) (.int divisor) =
        .ok (.some (.int quotient)) := by
    simpa [Nat.add_assoc, IntegerOptionValue.evaluate, IntegerOptionValue.toRuntimeValue,
      GlobalIR.IntegerOptionalOperation.toPrimitive, TypedExpansion.integerOptional,
      nonzero, quotientEq] using quotientEval
  have remainderRuntime : GlobalIR.evaluateIntegerOptionalCall program store .remainder
      (fuel + 2) environment (.int dividend) (.int divisor) =
        .ok (.some (.int remainder)) := by
    simpa [Nat.add_assoc, IntegerOptionValue.evaluate, IntegerOptionValue.toRuntimeValue,
      GlobalIR.IntegerOptionalOperation.toPrimitive, TypedExpansion.integerOptional,
      nonzero, remainderEq] using remainderEval
  have quotientValueTyped : PolyIR.ValueTyped globals (.some (.int quotient))
      (.option .integer) := by
    simpa [Nat.add_assoc, IntegerOptionValue.evaluate, IntegerOptionValue.toRuntimeValue,
      GlobalIR.IntegerOptionalOperation.toPrimitive, TypedExpansion.integerOptional,
      nonzero, quotientEq] using quotientTyped
  have remainderValueTyped : PolyIR.ValueTyped globals (.some (.int remainder))
      (.option .integer) := by
    simpa [Nat.add_assoc, IntegerOptionValue.evaluate, IntegerOptionValue.toRuntimeValue,
      GlobalIR.IntegerOptionalOperation.toPrimitive, TypedExpansion.integerOptional,
      nonzero, remainderEq] using remainderTyped
  exact ⟨quotient, remainder, quotientRuntime, remainderRuntime, reconstructs,
    quotientMagnitude, quotientSign, remainderMagnitude, remainderSign.1,
    remainderSign.2, quotientValueTyped, remainderValueTyped⟩

/-- The concrete Core quotient builtin and GlobalIR's integer-call evaluator
produce the same Option value. The result remains typed when the divisor is
zero, where both sides represent failure to produce an integer quotient as
`none`. -/
theorem quotientBuiltin_steps_agree_with_globalIR_call
    (globals : List Surface.Signature) (program : List GlobalIR.Definition)
    (store : GlobalIR.Store) (fuel : Nat) (environment : List PolyIR.Value)
    (dividend divisor : Int) :
    Steps
        (.app (.app quotientBuiltin (.int dividend)) (.int divisor))
        (IntegerOptionValue.evaluate .quotient dividend divisor).toCore ∧
      GlobalIR.evaluateIntegerOptionalCall program store .quotient (fuel + 2)
        environment (.int dividend) (.int divisor) =
        .ok (IntegerOptionValue.evaluate .quotient dividend divisor).toRuntimeValue ∧
      PolyIR.ValueTyped globals
        (IntegerOptionValue.evaluate .quotient dividend divisor).toRuntimeValue
        (.option .integer) := by
  have leftEvaluates : GlobalIR.evaluate program store (fuel + 1) environment
      (.int dividend) = .ok (.int dividend) := by rfl
  have rightEvaluates : GlobalIR.evaluate program store (fuel + 1) environment
      (.int divisor) = .ok (.int divisor) := by rfl
  obtain ⟨runtimeEval, runtimeTyped⟩ := evaluateIntegerOptionalCall_matches_shared
    globals program store .quotient (fuel + 1) environment (.int dividend) (.int divisor)
    dividend divisor leftEvaluates rightEvaluates
  exact ⟨quotientBuiltin_application_steps_shared dividend divisor, runtimeEval, runtimeTyped⟩

/-- The corresponding whole-result agreement for remainder, including its
zero-divisor `none` result. -/
theorem remainderBuiltin_steps_agree_with_globalIR_call
    (globals : List Surface.Signature) (program : List GlobalIR.Definition)
    (store : GlobalIR.Store) (fuel : Nat) (environment : List PolyIR.Value)
    (dividend divisor : Int) :
    Steps
        (.app (.app remainderBuiltin (.int dividend)) (.int divisor))
        (IntegerOptionValue.evaluate .remainder dividend divisor).toCore ∧
      GlobalIR.evaluateIntegerOptionalCall program store .remainder (fuel + 2)
        environment (.int dividend) (.int divisor) =
        .ok (IntegerOptionValue.evaluate .remainder dividend divisor).toRuntimeValue ∧
      PolyIR.ValueTyped globals
        (IntegerOptionValue.evaluate .remainder dividend divisor).toRuntimeValue
        (.option .integer) := by
  have leftEvaluates : GlobalIR.evaluate program store (fuel + 1) environment
      (.int dividend) = .ok (.int dividend) := by rfl
  have rightEvaluates : GlobalIR.evaluate program store (fuel + 1) environment
      (.int divisor) = .ok (.int divisor) := by rfl
  obtain ⟨runtimeEval, runtimeTyped⟩ := evaluateIntegerOptionalCall_matches_shared
    globals program store .remainder (fuel + 1) environment (.int dividend) (.int divisor)
    dividend divisor leftEvaluates rightEvaluates
  exact ⟨remainderBuiltin_application_steps_shared dividend divisor, runtimeEval, runtimeTyped⟩

/-- Typed integer operands evaluated by the ordinary GlobalIR evaluator can
be passed to the Option-valued quotient/remainder evaluator. Successful child
results are forced to be integers by the contextual arithmetic preservation
theorem, and the resulting Option value retains its runtime type. -/
theorem evaluateIntegerOptionalCall_of_contextual_integer_operands
    (globals : List Surface.Signature) (assignment : Nat → Surface.Ty)
    (program : List GlobalIR.Definition) (store : GlobalIR.Store)
    (context : List Surface.Ty) (fuel : Nat) (environment : List PolyIR.Value)
    (environmentTyped : PolyIR.ValuesTyped globals environment
      (Surface.interpretTypes assignment context))
    (operation : GlobalIR.IntegerOptionalOperation) (left right : PolyIR.Term)
    (leftTyped : GlobalIR.ContextualArithmeticTerm globals assignment context left .integer)
    (rightTyped : GlobalIR.ContextualArithmeticTerm globals assignment context right .integer)
    (leftValue rightValue : PolyIR.Value)
    (leftEvaluates : GlobalIR.evaluate program store fuel environment left = .ok leftValue)
    (rightEvaluates : GlobalIR.evaluate program store fuel environment right = .ok rightValue) :
    ∃ dividend divisor,
      leftValue = .int dividend ∧ rightValue = .int divisor ∧
      GlobalIR.evaluateIntegerOptionalCall program store operation (fuel + 1)
        environment left right =
        .ok (IntegerOptionValue.evaluate operation.toPrimitive dividend divisor).toRuntimeValue ∧
      PolyIR.ValueTyped globals
        (IntegerOptionValue.evaluate operation.toPrimitive dividend divisor).toRuntimeValue
        (.option .integer) := by
  have leftValueTyped := GlobalIR.evaluate_contextualArithmetic_preserves_type globals
    assignment program store context fuel environment left .integer leftTyped environmentTyped
    leftValue leftEvaluates
  have rightValueTyped := GlobalIR.evaluate_contextualArithmetic_preserves_type globals
    assignment program store context fuel environment right .integer rightTyped environmentTyped
    rightValue rightEvaluates
  have leftIsInteger : ∃ dividend, leftValue = .int dividend := by
    cases leftValue with
    | int dividend => exact ⟨dividend, rfl⟩
    | bool value => cases leftValueTyped
    | float value => cases leftValueTyped
    | string value => cases leftValueTyped
    | character value => cases leftValueTyped
    | unit => cases leftValueTyped
    | closure arity body captured => cases leftValueTyped
    | global index => cases leftValueTyped
    | nil => cases leftValueTyped
    | cons head tail => cases leftValueTyped
    | none => cases leftValueTyped
    | some value => cases leftValueTyped
  have rightIsInteger : ∃ divisor, rightValue = .int divisor := by
    cases rightValue with
    | int divisor => exact ⟨divisor, rfl⟩
    | bool value => cases rightValueTyped
    | float value => cases rightValueTyped
    | string value => cases rightValueTyped
    | character value => cases rightValueTyped
    | unit => cases rightValueTyped
    | closure arity body captured => cases rightValueTyped
    | global index => cases rightValueTyped
    | nil => cases rightValueTyped
    | cons head tail => cases rightValueTyped
    | none => cases rightValueTyped
    | some value => cases rightValueTyped
  obtain ⟨dividend, leftValueEq⟩ := leftIsInteger
  obtain ⟨divisor, rightValueEq⟩ := rightIsInteger
  subst leftValue
  subst rightValue
  obtain ⟨evaluated, typed⟩ := evaluateIntegerOptionalCall_matches_shared
    globals program store operation fuel environment left right dividend divisor
    leftEvaluates rightEvaluates
  exact ⟨dividend, divisor, rfl, rfl, evaluated, typed⟩

/-- Getter-aware integer operands preserve the same shared Option arithmetic
model and the runtime type guarantee. This joins the typed-store getter path
to the existing GlobalIR/shared-semantics correspondence. -/
theorem evaluateIntegerOptionalCall_of_contextual_global_runtime_operands
    (globals : List Surface.Signature) (assignment : Nat → Surface.Ty)
    (definitions : Surface.Definitions) (slotTypes : List Surface.Ty)
    (functionSources : List (Nat × Nat)) (program : List GlobalIR.Definition)
    (programTyped : GlobalIR.GlobalProgramTyped globals definitions slotTypes
      functionSources program)
    (store : GlobalIR.Store) (storeLayout : store.length = slotTypes.length)
    (storeTyped : GlobalIR.StoreWellTyped globals slotTypes store)
    (context : List Surface.Ty) (fuel : Nat) (environment : List PolyIR.Value)
    (environmentTyped : PolyIR.ValuesTyped globals environment
      (Surface.interpretTypes assignment context))
    (operation : GlobalIR.IntegerOptionalOperation) (left right : PolyIR.Term)
    (typing : GlobalIR.ContextualGlobalRuntimeIntegerOptionalCall globals assignment
      definitions slotTypes functionSources program context operation left right)
    (result : PolyIR.Value)
    (success : GlobalIR.evaluateIntegerOptionalCall program store operation (fuel + 1)
      environment left right = .ok result) :
    ∃ dividend divisor,
      GlobalIR.evaluateIntegerOptionalCall program store operation (fuel + 1)
        environment left right = .ok
          (IntegerOptionValue.evaluate operation.toPrimitive dividend divisor).toRuntimeValue ∧
      PolyIR.ValueTyped globals result (.option .integer) := by
  obtain ⟨dividend, divisor, leftEvaluates, rightEvaluates, _resultValue⟩ :=
    (GlobalIR.evaluateIntegerOptionalCall_success_iff program store operation fuel environment
      left right result).mp success
  obtain ⟨sharedResult, _sharedTyped⟩ := evaluateIntegerOptionalCall_matches_shared
    globals program store operation fuel environment left right dividend divisor
    leftEvaluates rightEvaluates
  obtain ⟨resultTyped, _operands⟩ :=
    GlobalIR.evaluate_contextualGlobalRuntimeIntegerOptionalCall_preserves_type
      globals assignment definitions slotTypes functionSources program programTyped store context
      (fuel + 1) environment environmentTyped operation left right typing storeLayout storeTyped
      result success
  exact ⟨dividend, divisor, sharedResult, resultTyped⟩

/-- A contextually typed integer call is type safe at the evaluator boundary:
it either propagates an evaluator fault or returns a value of Option Integer
type. -/
theorem evaluateIntegerOptionalCall_type_safe
    (globals : List Surface.Signature) (program : List GlobalIR.Definition)
    (store : GlobalIR.Store) (fuel : Nat) (environment : List PolyIR.Value)
    (operation : GlobalIR.IntegerOptionalOperation) (left right : PolyIR.Term) :
    (∃ fault, GlobalIR.evaluateIntegerOptionalCall program store operation (fuel + 1)
      environment left right = .error fault) ∨
    (∃ value, GlobalIR.evaluateIntegerOptionalCall program store operation (fuel + 1)
      environment left right = .ok value ∧
      PolyIR.ValueTyped globals value (.option .integer)) := by
    cases result : GlobalIR.evaluateIntegerOptionalCall program store operation (fuel + 1)
      environment left right with
  | error fault => exact Or.inl ⟨fault, rfl⟩
  | ok value =>
      have successful := (GlobalIR.evaluateIntegerOptionalCall_success_iff program store
        operation fuel environment left right value).mp result
      obtain ⟨dividend, divisor, leftEvaluates, rightEvaluates, valueEq⟩ := successful
      exact Or.inr ⟨GlobalIR.integerOptionalRuntimeValue operation.toPrimitive dividend divisor,
        by simpa [valueEq] using result,
        GlobalIR.integerOptionalRuntimeValue_typed globals operation.toPrimitive dividend divisor⟩

/-- A contextually typed divisor expression that evaluates to integer zero
reaches the Option operation's ordinary `none` result. The zero-divisor
case therefore composes with arbitrary evaluated integer operands instead
of being restricted to literal arguments. -/
theorem evaluateContextualIntegerOptionalCall_zero_divisor
    (globals : List Surface.Signature) (assignment : Nat → Surface.Ty)
    (program : List GlobalIR.Definition) (store : GlobalIR.Store)
    (context : List Surface.Ty) (fuel : Nat) (environment : List PolyIR.Value)
    (environmentTyped : PolyIR.ValuesTyped globals environment
      (Surface.interpretTypes assignment context))
    (operation : GlobalIR.IntegerOptionalOperation) (left right : PolyIR.Term)
    (leftTyped : GlobalIR.ContextualArithmeticTerm globals assignment context left .integer)
    (rightTyped : GlobalIR.ContextualArithmeticTerm globals assignment context right .integer)
    (leftValue rightValue : PolyIR.Value)
    (leftEvaluates : GlobalIR.evaluate program store fuel environment left = .ok leftValue)
    (rightEvaluates : GlobalIR.evaluate program store fuel environment right = .ok rightValue)
    (rightIsZero : rightValue = .int 0) :
    GlobalIR.evaluateIntegerOptionalCall program store operation (fuel + 1)
      environment left right = .ok .none ∧
    PolyIR.ValueTyped globals .none (.option .integer) := by
  obtain ⟨_dividend, divisor, _leftValueEq, rightValueEq, evaluated, _typed⟩ :=
    evaluateIntegerOptionalCall_of_contextual_integer_operands globals assignment
      program store context fuel environment environmentTyped operation left right
      leftTyped rightTyped leftValue rightValue leftEvaluates rightEvaluates
  have divisorZero : divisor = 0 := by
    have valuesAgree := rightValueEq.symm.trans rightIsZero
    cases valuesAgree
    rfl
  constructor
  · simpa [IntegerOptionValue.evaluate, IntegerOptionValue.toRuntimeValue,
      GlobalIR.IntegerOptionalOperation.toPrimitive, TypedExpansion.integerOptional,
      divisorZero] using evaluated
  · exact .none

/-- The arithmetic specification remains valid when quotient and remainder
operands are arbitrary contextually typed GlobalIR integer terms.  Each term
is evaluated by the ordinary evaluator first; the resulting integer values
then feed both Option calls, with the same reconstruction, magnitude, and
sign guarantees as the literal-operand theorem. -/
theorem evaluateContextualIntegerOptionalCall_division_equation
    (globals : List Surface.Signature) (assignment : Nat → Surface.Ty)
    (program : List GlobalIR.Definition) (store : GlobalIR.Store)
    (context : List Surface.Ty) (fuel : Nat) (environment : List PolyIR.Value)
    (environmentTyped : PolyIR.ValuesTyped globals environment
      (Surface.interpretTypes assignment context))
    (left right : PolyIR.Term)
    (leftTyped : GlobalIR.ContextualArithmeticTerm globals assignment context left .integer)
    (rightTyped : GlobalIR.ContextualArithmeticTerm globals assignment context right .integer)
    (leftValue rightValue : PolyIR.Value)
    (leftEvaluates : GlobalIR.evaluate program store (fuel + 1) environment left =
      .ok leftValue)
    (rightEvaluates : GlobalIR.evaluate program store (fuel + 1) environment right =
      .ok rightValue)
    (nonzero : ∀ divisor, rightValue = .int divisor → divisor ≠ 0) :
    ∃ dividend divisor quotient remainder,
      leftValue = .int dividend ∧ rightValue = .int divisor ∧
      GlobalIR.evaluateIntegerOptionalCall program store .quotient (fuel + 2)
        environment left right = .ok (.some (.int quotient)) ∧
      GlobalIR.evaluateIntegerOptionalCall program store .remainder (fuel + 2)
        environment left right = .ok (.some (.int remainder)) ∧
      dividend = quotient * divisor + remainder ∧
      quotient.natAbs = dividend.natAbs / divisor.natAbs ∧
      (if (dividend < 0) = (divisor < 0) then 0 ≤ quotient else quotient ≤ 0) ∧
      remainder.natAbs < divisor.natAbs ∧
      (dividend < 0 → remainder ≤ 0) ∧ (0 ≤ dividend → 0 ≤ remainder) ∧
      PolyIR.ValueTyped globals (.some (.int quotient)) (.option .integer) ∧
      PolyIR.ValueTyped globals (.some (.int remainder)) (.option .integer) := by
  obtain ⟨dividend, divisor, leftValueEq, rightValueEq, _quotientModel, _quotientTyped⟩ :=
    evaluateIntegerOptionalCall_of_contextual_integer_operands globals assignment program store
      context (fuel + 1) environment environmentTyped .quotient left right
      leftTyped rightTyped leftValue rightValue leftEvaluates rightEvaluates
  subst leftValue
  subst rightValue
  have quotientNonzero := nonzero divisor rfl
  obtain ⟨quotient, remainder, quotientSpec, remainderSpec, reconstructs⟩ :=
    TypedExpansion.integerOptional_division_equation dividend divisor quotientNonzero
  have quotientSpec' : some (TypedExpansion.truncQuotient dividend divisor) = some quotient := by
    simpa [TypedExpansion.integerOptional, quotientNonzero] using quotientSpec
  have quotientEq : quotient = TypedExpansion.truncQuotient dividend divisor :=
    (Option.some.inj quotientSpec').symm
  have remainderSpec' : some
      (dividend - TypedExpansion.truncQuotient dividend divisor * divisor) = some remainder := by
    simpa [TypedExpansion.integerOptional, quotientNonzero] using remainderSpec
  have remainderEq : remainder =
      dividend - TypedExpansion.truncQuotient dividend divisor * divisor :=
    (Option.some.inj remainderSpec').symm
  have ⟨remainderModel, _remainderTyped⟩ := evaluateIntegerOptionalCall_matches_shared
    globals program store .remainder (fuel + 1) environment left right dividend divisor
    leftEvaluates rightEvaluates
  have quotientRuntime :
      GlobalIR.evaluateIntegerOptionalCall program store .quotient (fuel + 2)
        environment left right = .ok (.some (.int quotient)) := by
    simpa [IntegerOptionValue.evaluate, IntegerOptionValue.toRuntimeValue,
      GlobalIR.IntegerOptionalOperation.toPrimitive, TypedExpansion.integerOptional,
      Nat.add_assoc, quotientNonzero, quotientEq] using _quotientModel
  have remainderRuntime :
      GlobalIR.evaluateIntegerOptionalCall program store .remainder (fuel + 2)
        environment left right = .ok (.some (.int remainder)) := by
    simpa [IntegerOptionValue.evaluate, IntegerOptionValue.toRuntimeValue,
      GlobalIR.IntegerOptionalOperation.toPrimitive, TypedExpansion.integerOptional,
      Nat.add_assoc, quotientNonzero, remainderEq] using remainderModel
  have quotientMagnitude : quotient.natAbs = dividend.natAbs / divisor.natAbs := by
    rw [quotientEq]
    exact TypedExpansion.truncQuotient_natAbs dividend divisor
  have quotientSign :
      (if (dividend < 0) = (divisor < 0) then 0 ≤ quotient else quotient ≤ 0) := by
    by_cases sameSign : (dividend < 0) = (divisor < 0)
    · simp only [if_pos sameSign]
      rw [quotientEq]
      exact TypedExpansion.truncQuotient_nonneg_of_same_sign dividend divisor sameSign
    · simp only [if_neg sameSign]
      rw [quotientEq]
      exact TypedExpansion.truncQuotient_nonpos_of_opposite_sign dividend divisor sameSign
  have remainderMagnitude : remainder.natAbs < divisor.natAbs := by
    rw [remainderEq]
    exact TypedExpansion.truncRemainder_natAbs_lt dividend divisor quotientNonzero
  have remainderSign : (dividend < 0 → remainder ≤ 0) ∧
      (0 ≤ dividend → 0 ≤ remainder) := by
    rw [remainderEq]
    exact TypedExpansion.truncRemainder_sign dividend divisor
  exact ⟨dividend, divisor, quotient, remainder, rfl, rfl, quotientRuntime,
    remainderRuntime, reconstructs, quotientMagnitude, quotientSign, remainderMagnitude,
    remainderSign.1, remainderSign.2, .some .int, .some .int⟩


end NLisp
