import NLisp.CBindingWalk
import NLisp.GlobalIR
import NLisp.IntegerOptionalCorrespondence

namespace NLisp

/-- Names used by the C builtin table for the two integer operations whose
result is optional. -/
def integerOptionalBuiltinName : GlobalIR.IntegerOptionalOperation → String
  | .quotient => "quotient"
  | .remainder => "remainder"

/-- The C registration, curried primitive signature, GlobalIR native call,
and Option Integer result typing agree for quotient and remainder. A zero
divisor is covered by the same equation and evaluates successfully to none. -/
theorem cBuiltin_integerOptional_GlobalIR_semantics
    (globals : List Surface.Signature) (program : List GlobalIR.Definition)
    (store : GlobalIR.Store) (environment : List PolyIR.Value) (fuel : Nat)
    (operation : GlobalIR.IntegerOptionalOperation) (left right : PolyIR.Term)
    (dividend divisor : Int)
    (leftEvaluates : GlobalIR.evaluate program store fuel environment left =
      .ok (.int dividend))
    (rightEvaluates : GlobalIR.evaluate program store fuel environment right =
      .ok (.int divisor)) :
    CBindingWalk.builtinPrimitive (integerOptionalBuiltinName operation) =
        some operation.toPrimitive ∧
      TypedExpansion.Primitive.type operation.toPrimitive =
        .fn .integer (.fn .integer (.option .integer)) ∧
      GlobalIR.evaluateIntegerOptionalCall program store operation (fuel + 1)
        environment left right =
        .ok (IntegerOptionValue.evaluate operation.toPrimitive dividend divisor).toRuntimeValue ∧
      PolyIR.ValueTyped globals
        (IntegerOptionValue.evaluate operation.toPrimitive dividend divisor).toRuntimeValue
        (.option .integer) := by
  have mapping : CBindingWalk.builtinPrimitive (integerOptionalBuiltinName operation) =
      some operation.toPrimitive := by
    cases operation <;> rfl
  have signature : TypedExpansion.Primitive.type operation.toPrimitive =
      .fn .integer (.fn .integer (.option .integer)) := by
    cases operation <;> rfl
  obtain ⟨evaluation, typed⟩ :=
    evaluateIntegerOptionalCall_matches_shared globals program store operation fuel
      environment left right dividend divisor leftEvaluates rightEvaluates
  exact ⟨mapping, signature, evaluation, typed⟩

/-- Even when operand terms are arbitrary, every successful C quotient or
remainder call in GlobalIR returns a value of the registered Option Integer
result type. Operand faults and wrong-shape faults remain evaluator errors and
therefore do not weaken this success-preservation statement. -/
theorem cBuiltin_integerOptional_success_preserves_type
    (globals : List Surface.Signature) (program : List GlobalIR.Definition)
    (store : GlobalIR.Store) (environment : List PolyIR.Value) (fuel : Nat)
    (operation : GlobalIR.IntegerOptionalOperation) (left right : PolyIR.Term)
    (result : PolyIR.Value)
    (success : GlobalIR.evaluateIntegerOptionalCall program store operation fuel
      environment left right = .ok result) :
    CBindingWalk.builtinPrimitive (integerOptionalBuiltinName operation) =
        some operation.toPrimitive ∧
      TypedExpansion.Primitive.type operation.toPrimitive =
        .fn .integer (.fn .integer (.option .integer)) ∧
      PolyIR.ValueTyped globals result (.option .integer) := by
  have mapping : CBindingWalk.builtinPrimitive (integerOptionalBuiltinName operation) =
      some operation.toPrimitive := by
    cases operation <;> rfl
  have signature : TypedExpansion.Primitive.type operation.toPrimitive =
      .fn .integer (.fn .integer (.option .integer)) := by
    cases operation <;> rfl
  exact ⟨mapping, signature,
    GlobalIR.evaluateIntegerOptionalCall_preserves_type globals program store operation
      fuel environment left right result success⟩

/-- The Option-valued C builtins preserve the GlobalIR helper's precise fault
order: left operand first, right operand second, then wrong-shape checking.
This packages the C builtin identity with the error classification theorem. -/
theorem cBuiltin_integerOptional_fault_order
    (program : List GlobalIR.Definition) (store : GlobalIR.Store)
    (operation : GlobalIR.IntegerOptionalOperation) (fuel : Nat)
    (environment : List PolyIR.Value) (left right : PolyIR.Term)
    (fault : GlobalIR.Fault) :
    CBindingWalk.builtinPrimitive (integerOptionalBuiltinName operation) =
        some operation.toPrimitive ∧
      (GlobalIR.evaluateIntegerOptionalCall program store operation (fuel + 1)
          environment left right = .error fault ↔
        (∃ leftFault,
          GlobalIR.evaluate program store fuel environment left = .error leftFault ∧
          fault = leftFault) ∨
        (∃ leftValue rightFault,
          GlobalIR.evaluate program store fuel environment left = .ok leftValue ∧
          GlobalIR.evaluate program store fuel environment right = .error rightFault ∧
          fault = rightFault) ∨
        (∃ leftValue rightValue,
          GlobalIR.evaluate program store fuel environment left = .ok leftValue ∧
          GlobalIR.evaluate program store fuel environment right = .ok rightValue ∧
          (¬ ∃ x y, leftValue = .int x ∧ rightValue = .int y) ∧
          fault = .core .wrongShape)) := by
  have mapping : CBindingWalk.builtinPrimitive (integerOptionalBuiltinName operation) =
      some operation.toPrimitive := by
    cases operation <;> rfl
  exact ⟨mapping, GlobalIR.evaluateIntegerOptionalCall_error_iff program store operation
    fuel environment left right fault⟩

/-- The `to-float` registry identity, unary signature, GlobalIR native-call
result, and runtime Float typing agree. Exact bitwise equivalence with C's
`integer_to_float` rounding helper remains a separate refinement theorem. -/
theorem cBuiltin_toFloat_GlobalIR_semantics
    (globals : List Surface.Signature) (program : List GlobalIR.Definition)
    (store : GlobalIR.Store) (environment : List PolyIR.Value) (fuel : Nat)
    (operand : PolyIR.Term) (integer : Int)
    (operandEvaluates : GlobalIR.evaluate program store fuel environment operand =
      .ok (.int integer)) :
    CBindingWalk.builtinPrimitive "to-float" = some .toFloat ∧
      TypedExpansion.Primitive.type .toFloat = .fn .integer .floating ∧
      GlobalIR.evaluateIntegerToFloatCall program store (fuel + 1) environment operand =
        .ok (.float (Float.ofInt integer)) ∧
      PolyIR.ValueTyped globals (.float (Float.ofInt integer)) .float := by
  have mapping : CBindingWalk.builtinPrimitive "to-float" = some .toFloat := by rfl
  have signature : TypedExpansion.Primitive.type .toFloat = .fn .integer .floating := by rfl
  obtain ⟨evaluation, typed⟩ := GlobalIR.evaluateIntegerToFloatCall_of_integer_child
    globals program store fuel environment operand integer operandEvaluates
  exact ⟨mapping, signature, by simpa [GlobalIR.integerToFloatRuntimeValue] using evaluation,
    by simpa [GlobalIR.integerToFloatRuntimeValue] using typed⟩

/-- The `float-truncate` builtin identity and unary Option Integer signature
agree with the raw-binary64 GlobalIR result model for every encoding. The
bridge from an evaluator `Float` value to its exact C binary64 bits is not
assumed here. -/
theorem cBuiltin_floatTruncate_GlobalIR_bit_model
    (globals : List Surface.Signature) (bits : UInt64) :
    CBindingWalk.builtinPrimitive "float-truncate" = some .truncate ∧
      TypedExpansion.Primitive.type .truncate = .fn .floating (.option .integer) ∧
      GlobalIR.floatTruncateRuntimeValue bits =
        (match TypedExpansion.binary64Truncate bits with
         | none => .none
         | some integer => .some (.int integer)) ∧
      (GlobalIR.floatTruncateRuntimeValue bits = .none ↔
        TypedExpansion.binary64Truncate bits = none) ∧
      PolyIR.ValueTyped globals (GlobalIR.floatTruncateRuntimeValue bits)
        (.option .integer) := by
  have mapping : CBindingWalk.builtinPrimitive "float-truncate" = some .truncate := by rfl
  have signature : TypedExpansion.Primitive.type .truncate =
      .fn .floating (.option .integer) := by rfl
  have valueModel : GlobalIR.floatTruncateRuntimeValue bits =
      (match TypedExpansion.binary64Truncate bits with
       | none => PolyIR.Value.none
       | some integer => PolyIR.Value.some (.int integer)) := by
    rfl
  have rejectedIffNonfinite : GlobalIR.floatTruncateRuntimeValue bits = .none ↔
      TypedExpansion.binary64Truncate bits = none := by
    cases truncation : TypedExpansion.binary64Truncate bits <;>
      simp [GlobalIR.floatTruncateRuntimeValue, truncation]
  exact ⟨mapping, signature, valueModel, rejectedIffNonfinite,
    GlobalIR.floatTruncateRuntimeValue_typed globals bits⟩

/-- Boolean equality registration, primitive signature, GlobalIR result, and
result typing agree after both Boolean operands evaluate. -/
theorem cBuiltin_booleanEquality_GlobalIR_semantics
    (globals : List Surface.Signature) (program : List GlobalIR.Definition)
    (store : GlobalIR.Store) (environment : List PolyIR.Value) (fuel : Nat)
    (left right : PolyIR.Term) (x y : Bool)
    (leftEvaluates : GlobalIR.evaluate program store fuel environment left = .ok (.bool x))
    (rightEvaluates : GlobalIR.evaluate program store fuel environment right = .ok (.bool y)) :
    CBindingWalk.builtinPrimitive "boolean=" = some .boolEq ∧
      TypedExpansion.Primitive.type .boolEq =
        .fn .boolean (.fn .boolean .boolean) ∧
      GlobalIR.evaluateBooleanEqualityCall program store (fuel + 1) environment left right =
        .ok (.bool (x == y)) ∧
      PolyIR.ValueTyped globals (.bool (x == y)) .boolean := by
  have mapping : CBindingWalk.builtinPrimitive "boolean=" = some .boolEq := by rfl
  have signature : TypedExpansion.Primitive.type .boolEq =
      .fn .boolean (.fn .boolean .boolean) := by rfl
  obtain ⟨evaluation, typed⟩ := GlobalIR.evaluateBooleanEqualityCall_of_boolean_children
    globals program store fuel environment left right x y leftEvaluates rightEvaluates
  exact ⟨mapping, signature, by simpa [GlobalIR.evaluateBooleanEqualityValue] using evaluation,
    by simpa [GlobalIR.evaluateBooleanEqualityValue] using typed⟩

/-- Boolean negation registration, primitive signature, GlobalIR result, and
result typing agree after its operand evaluates. -/
theorem cBuiltin_booleanNot_GlobalIR_semantics
    (globals : List Surface.Signature) (program : List GlobalIR.Definition)
    (store : GlobalIR.Store) (environment : List PolyIR.Value) (fuel : Nat)
    (operand : PolyIR.Term) (value : Bool)
    (operandEvaluates : GlobalIR.evaluate program store fuel environment operand =
      .ok (.bool value)) :
    CBindingWalk.builtinPrimitive "not" = some .not ∧
      TypedExpansion.Primitive.type .not = .fn .boolean .boolean ∧
      GlobalIR.evaluateBooleanNotCall program store (fuel + 1) environment operand =
        .ok (.bool (!value)) ∧
      PolyIR.ValueTyped globals (.bool (!value)) .boolean := by
  have mapping : CBindingWalk.builtinPrimitive "not" = some .not := by rfl
  have signature : TypedExpansion.Primitive.type .not = .fn .boolean .boolean := by rfl
  obtain ⟨evaluation, typed⟩ := GlobalIR.evaluateBooleanNotCall_of_boolean_child
    globals program store fuel environment operand value operandEvaluates
  exact ⟨mapping, signature, evaluation, typed⟩

def floatComparisonBuiltinName : GlobalIR.FloatComparisonOperation → String
  | .lt => "float<"
  | .le => "float<="
  | .gt => "float>"
  | .ge => "float>="
  | .eq => "float="

/-- The five registered Float comparisons share the curried signature and
produce Boolean values with the C ordered-NaN behavior in the GlobalIR model. -/
theorem cBuiltin_floatComparison_GlobalIR_semantics
    (globals : List Surface.Signature) (program : List GlobalIR.Definition)
    (store : GlobalIR.Store) (environment : List PolyIR.Value) (fuel : Nat)
    (operation : GlobalIR.FloatComparisonOperation) (left right : PolyIR.Term)
    (x y : Float)
    (leftEvaluates : GlobalIR.evaluate program store fuel environment left = .ok (.float x))
    (rightEvaluates : GlobalIR.evaluate program store fuel environment right = .ok (.float y)) :
    CBindingWalk.builtinPrimitive (floatComparisonBuiltinName operation) =
        some operation.toPrimitive ∧
      TypedExpansion.Primitive.type operation.toPrimitive =
        .fn .floating (.fn .floating .boolean) ∧
      GlobalIR.evaluateFloatComparisonCall program store operation (fuel + 1)
        environment left right =
        .ok (GlobalIR.floatComparisonRuntimeValue operation x y) ∧
      PolyIR.ValueTyped globals
        (GlobalIR.floatComparisonRuntimeValue operation x y) .boolean := by
  have mapping : CBindingWalk.builtinPrimitive (floatComparisonBuiltinName operation) =
      some operation.toPrimitive := by
    cases operation <;> rfl
  have signature : TypedExpansion.Primitive.type operation.toPrimitive =
      .fn .floating (.fn .floating .boolean) := by
    cases operation <;> rfl
  obtain ⟨evaluation, typed⟩ := GlobalIR.evaluateFloatComparisonCall_of_float_children
    globals program store operation fuel environment left right x y leftEvaluates rightEvaluates
  exact ⟨mapping, signature, evaluation, typed⟩

/-- The C Float comparison registrations and GlobalIR helper share left-to-right
operand fault propagation and reject wrong-shaped values after both operands. -/
theorem cBuiltin_floatComparison_fault_order
    (program : List GlobalIR.Definition) (store : GlobalIR.Store)
    (operation : GlobalIR.FloatComparisonOperation) (fuel : Nat)
    (environment : List PolyIR.Value) (left right : PolyIR.Term)
    (fault : GlobalIR.Fault) :
    CBindingWalk.builtinPrimitive (floatComparisonBuiltinName operation) =
        some operation.toPrimitive ∧
      (GlobalIR.evaluateFloatComparisonCall program store operation (fuel + 1)
          environment left right = .error fault ↔
        (∃ leftFault,
          GlobalIR.evaluate program store fuel environment left = .error leftFault ∧
          fault = leftFault) ∨
        (∃ leftValue rightFault,
          GlobalIR.evaluate program store fuel environment left = .ok leftValue ∧
          GlobalIR.evaluate program store fuel environment right = .error rightFault ∧
          fault = rightFault) ∨
        (∃ leftValue rightValue,
          GlobalIR.evaluate program store fuel environment left = .ok leftValue ∧
          GlobalIR.evaluate program store fuel environment right = .ok rightValue ∧
          (¬ ∃ x y, leftValue = .float x ∧ rightValue = .float y) ∧
          fault = .core .wrongShape)) := by
  have mapping : CBindingWalk.builtinPrimitive (floatComparisonBuiltinName operation) =
      some operation.toPrimitive := by
    cases operation <;> rfl
  exact ⟨mapping, GlobalIR.evaluateFloatComparisonCall_error_iff program store operation
    fuel environment left right fault⟩

/-- Every successful registered Float comparison call returns a value of its
Boolean result type, regardless of the operand terms' shapes. -/
theorem cBuiltin_floatComparison_success_preserves_type
    (globals : List Surface.Signature) (program : List GlobalIR.Definition)
    (store : GlobalIR.Store) (environment : List PolyIR.Value) (fuel : Nat)
    (operation : GlobalIR.FloatComparisonOperation) (left right : PolyIR.Term)
    (result : PolyIR.Value)
    (success : GlobalIR.evaluateFloatComparisonCall program store operation fuel
      environment left right = .ok result) :
    CBindingWalk.builtinPrimitive (floatComparisonBuiltinName operation) =
        some operation.toPrimitive ∧
      TypedExpansion.Primitive.type operation.toPrimitive =
        .fn .floating (.fn .floating .boolean) ∧
      PolyIR.ValueTyped globals result .boolean := by
  have mapping : CBindingWalk.builtinPrimitive (floatComparisonBuiltinName operation) =
      some operation.toPrimitive := by
    cases operation <;> rfl
  have signature : TypedExpansion.Primitive.type operation.toPrimitive =
      .fn .floating (.fn .floating .boolean) := by
    cases operation <;> rfl
  exact ⟨mapping, signature,
    GlobalIR.evaluateFloatComparisonCall_preserves_type globals program store operation
      fuel environment left right result success⟩

/-- The registered Float comparison contract also composes with the typed
GlobalIR runtime fragment: operands may contain generated getter reads, and
their successful Float shapes are derived from the contextual typing proof. -/
theorem cBuiltin_floatComparison_contextual_runtime_type_safety
    (globals : List Surface.Signature) (assignment : Nat → Surface.Ty)
    (definitions : Surface.Definitions) (slotTypes : List Surface.Ty)
    (functionSources : List (Nat × Nat)) (program : List GlobalIR.Definition)
    (programTyped : GlobalIR.GlobalProgramTyped globals definitions slotTypes functionSources program)
    (store : GlobalIR.Store) (storeLayout : store.length = slotTypes.length)
    (storeTyped : GlobalIR.StoreWellTyped globals slotTypes store)
    (context : List Surface.Ty) (environment : List PolyIR.Value)
    (environmentTyped : PolyIR.ValuesTyped globals environment
      (Surface.interpretTypes assignment context))
    (operation : GlobalIR.FloatComparisonOperation) (fuel : Nat)
    (left right : PolyIR.Term)
    (typing : GlobalIR.ContextualGlobalRuntimeFloatComparisonCall globals assignment
      definitions slotTypes functionSources program context operation left right)
    (result : PolyIR.Value)
    (success : GlobalIR.evaluateFloatComparisonCall program store operation fuel
      environment left right = .ok result) :
    CBindingWalk.builtinPrimitive (floatComparisonBuiltinName operation) =
        some operation.toPrimitive ∧
      TypedExpansion.Primitive.type operation.toPrimitive =
        .fn .floating (.fn .floating .boolean) ∧
      (PolyIR.ValueTyped globals result .boolean ∧
        ∃ leftValue rightValue,
          GlobalIR.evaluate program store (fuel - 1) environment left = .ok leftValue ∧
          GlobalIR.evaluate program store (fuel - 1) environment right = .ok rightValue ∧
          PolyIR.ValueTyped globals leftValue .float ∧
          PolyIR.ValueTyped globals rightValue .float) := by
  have mapping : CBindingWalk.builtinPrimitive (floatComparisonBuiltinName operation) =
      some operation.toPrimitive := by
    cases operation <;> rfl
  have signature : TypedExpansion.Primitive.type operation.toPrimitive =
      .fn .floating (.fn .floating .boolean) := by
    cases operation <;> rfl
  have runtime := GlobalIR.evaluate_contextualGlobalRuntimeFloatComparisonCall_preserves_type
    globals assignment definitions slotTypes functionSources program programTyped store context
    fuel environment environmentTyped operation left right typing storeLayout storeTyped result
    success
  exact ⟨mapping, signature, runtime⟩

/-- Name and primitive identities for the four curried C floating arithmetic
builtins, in the order used by the C operation table. -/
def floatBinBuiltinName : Surface.FloatBinOp → String
  | .add => "float+"
  | .sub => "float-"
  | .mul => "float*"
  | .div => "float/"

def floatBinPrimitive : Surface.FloatBinOp → TypedExpansion.Primitive
  | .add => .fadd
  | .sub => .fsub
  | .mul => .fmul
  | .div => .fdiv

/-- C builtin registration, Lean primitive typing, and GlobalIR FloatBinOp
evaluation agree for every floating arithmetic operation. The result is
preserved at runtime as a Float value. -/
theorem cBuiltin_floatBin_GlobalIR_semantics
    (globals : List Surface.Signature) (program : List GlobalIR.Definition)
    (store : GlobalIR.Store) (environment : List PolyIR.Value) (fuel : Nat)
    (operation : Surface.FloatBinOp) (left right : PolyIR.Term) (x y : Float)
    (leftEvaluates : GlobalIR.evaluate program store fuel environment left = .ok (.float x))
    (rightEvaluates : GlobalIR.evaluate program store fuel environment right = .ok (.float y)) :
    CBindingWalk.builtinPrimitive (floatBinBuiltinName operation) =
      some (floatBinPrimitive operation) ∧
      TypedExpansion.Primitive.type (floatBinPrimitive operation) =
        .fn .floating (.fn .floating .floating) ∧
      GlobalIR.evaluate program store (fuel + 1) environment
        (.floatBin operation left right) =
          .ok (.float (GlobalIR.floatBinValue operation x y)) ∧
      PolyIR.ValueTyped globals (.float (GlobalIR.floatBinValue operation x y)) .float := by
  have mapped : CBindingWalk.builtinPrimitive (floatBinBuiltinName operation) =
      some (floatBinPrimitive operation) := by
    cases operation <;> rfl
  have primitiveType : TypedExpansion.Primitive.type (floatBinPrimitive operation) =
      .fn .floating (.fn .floating .floating) := by
    cases operation <;> rfl
  obtain ⟨evaluated, typed⟩ := GlobalIR.evaluate_floatBin_typed_of_children globals
    program store environment fuel operation left right x y leftEvaluates rightEvaluates
  exact ⟨mapped, primitiveType, evaluated, typed⟩

/-- C floating arithmetic registration and its curried type compose with the
getter-aware runtime typing proof for the actual GlobalIR FloatBin term. -/
theorem cBuiltin_floatBin_contextual_runtime_type_safety
    (globals : List Surface.Signature) (assignment : Nat → Surface.Ty)
    (definitions : Surface.Definitions) (slotTypes : List Surface.Ty)
    (functionSources : List (Nat × Nat)) (program : List GlobalIR.Definition)
    (programTyped : GlobalIR.GlobalProgramTyped globals definitions slotTypes functionSources program)
    (store : GlobalIR.Store) (storeLayout : store.length = slotTypes.length)
    (storeTyped : GlobalIR.StoreWellTyped globals slotTypes store)
    (context : List Surface.Ty) (environment : List PolyIR.Value)
    (environmentTyped : PolyIR.ValuesTyped globals environment
      (Surface.interpretTypes assignment context))
    (operation : Surface.FloatBinOp) (fuel : Nat) (left right : PolyIR.Term)
    (typing : GlobalIR.ContextualGlobalRuntimeFloatBinCall globals assignment definitions
      slotTypes functionSources program context operation left right)
    (result : PolyIR.Value)
    (success : GlobalIR.evaluate program store fuel environment
      (.floatBin operation left right) = .ok result) :
    CBindingWalk.builtinPrimitive (floatBinBuiltinName operation) =
        some (floatBinPrimitive operation) ∧
      TypedExpansion.Primitive.type (floatBinPrimitive operation) =
        .fn .floating (.fn .floating .floating) ∧
      (PolyIR.ValueTyped globals result .float ∧
        ∃ leftValue rightValue,
          GlobalIR.evaluate program store (fuel - 1) environment left = .ok leftValue ∧
          GlobalIR.evaluate program store (fuel - 1) environment right = .ok rightValue ∧
          PolyIR.ValueTyped globals leftValue .float ∧
          PolyIR.ValueTyped globals rightValue .float) := by
  have mapped : CBindingWalk.builtinPrimitive (floatBinBuiltinName operation) =
      some (floatBinPrimitive operation) := by
    cases operation <;> rfl
  have primitiveType : TypedExpansion.Primitive.type (floatBinPrimitive operation) =
      .fn .floating (.fn .floating .floating) := by
    cases operation <;> rfl
  have runtime := GlobalIR.evaluate_contextualGlobalRuntimeFloatBinCall_preserves_type
    globals assignment definitions slotTypes functionSources program programTyped store context
    fuel environment environmentTyped operation left right typing storeLayout storeTyped result
    success
  exact ⟨mapped, primitiveType, runtime⟩

/-- The C floating arithmetic registrations have the same operand-fault order
and wrong-shape classification as GlobalIR's binary Float rules. -/
theorem cBuiltin_floatBin_fault_order
    (program : List GlobalIR.Definition) (store : GlobalIR.Store)
    (operation : Surface.FloatBinOp) (fuel : Nat) (environment : List PolyIR.Value)
    (left right : PolyIR.Term) (fault : GlobalIR.Fault) :
    CBindingWalk.builtinPrimitive (floatBinBuiltinName operation) =
        some (floatBinPrimitive operation) ∧
      (GlobalIR.evaluate program store (fuel + 1) environment
        (.floatBin operation left right) = .error fault ↔
        (∃ leftFault,
          GlobalIR.evaluate program store fuel environment left = .error leftFault ∧
          fault = leftFault) ∨
        (∃ leftValue rightFault,
          GlobalIR.evaluate program store fuel environment left = .ok leftValue ∧
          GlobalIR.evaluate program store fuel environment right = .error rightFault ∧
          fault = rightFault) ∨
        (∃ leftValue rightValue,
          GlobalIR.evaluate program store fuel environment left = .ok leftValue ∧
          GlobalIR.evaluate program store fuel environment right = .ok rightValue ∧
          (¬ ∃ x y, leftValue = .float x ∧ rightValue = .float y) ∧
          fault = .core .wrongShape)) := by
  have mapped : CBindingWalk.builtinPrimitive (floatBinBuiltinName operation) =
      some (floatBinPrimitive operation) := by
    cases operation <;> rfl
  exact ⟨mapped, GlobalIR.evaluate_floatBin_error_iff program store operation fuel
    environment left right fault⟩

/-- The registered C `+` builtin, its curried primitive signature, and the
GlobalIR integer addition rule share one result equation and type guarantee.
The source checker separately pins the C operation row to `mpz_add`. -/
theorem cBuiltin_add_GlobalIR_semantics
    (globals : List Surface.Signature) (program : List GlobalIR.Definition)
    (store : GlobalIR.Store) (environment : List PolyIR.Value) (fuel : Nat)
    (left right : PolyIR.Term) (x y : Int)
    (leftEvaluates : GlobalIR.evaluate program store fuel environment left = .ok (.int x))
    (rightEvaluates : GlobalIR.evaluate program store fuel environment right = .ok (.int y)) :
    CBindingWalk.builtinPrimitive "+" = some .add ∧
      TypedExpansion.Primitive.type .add = .fn .integer (.fn .integer .integer) ∧
      GlobalIR.evaluate program store (fuel + 1) environment (.add left right) =
        .ok (.int (x + y)) ∧
      PolyIR.ValueTyped globals (.int (x + y)) .integer := by
  exact ⟨rfl, rfl, (GlobalIR.evaluate_add_typed_of_children globals program store
    environment fuel left right x y leftEvaluates rightEvaluates).1,
    (GlobalIR.evaluate_add_typed_of_children globals program store
      environment fuel left right x y leftEvaluates rightEvaluates).2⟩

/-- Registered C subtraction and GlobalIR subtraction have the same typed
integer result. -/
theorem cBuiltin_sub_GlobalIR_semantics
    (globals : List Surface.Signature) (program : List GlobalIR.Definition)
    (store : GlobalIR.Store) (environment : List PolyIR.Value) (fuel : Nat)
    (left right : PolyIR.Term) (x y : Int)
    (leftEvaluates : GlobalIR.evaluate program store fuel environment left = .ok (.int x))
    (rightEvaluates : GlobalIR.evaluate program store fuel environment right = .ok (.int y)) :
    CBindingWalk.builtinPrimitive "-" = some .sub ∧
      TypedExpansion.Primitive.type .sub = .fn .integer (.fn .integer .integer) ∧
      GlobalIR.evaluate program store (fuel + 1) environment (.sub left right) =
        .ok (.int (x - y)) ∧
      PolyIR.ValueTyped globals (.int (x - y)) .integer := by
  exact ⟨rfl, rfl, (GlobalIR.evaluate_sub_typed_of_children globals program store
    environment fuel left right x y leftEvaluates rightEvaluates).1,
    (GlobalIR.evaluate_sub_typed_of_children globals program store
      environment fuel left right x y leftEvaluates rightEvaluates).2⟩

/-- Registered C multiplication and GlobalIR multiplication have the same
typed integer result. -/
theorem cBuiltin_mul_GlobalIR_semantics
    (globals : List Surface.Signature) (program : List GlobalIR.Definition)
    (store : GlobalIR.Store) (environment : List PolyIR.Value) (fuel : Nat)
    (left right : PolyIR.Term) (x y : Int)
    (leftEvaluates : GlobalIR.evaluate program store fuel environment left = .ok (.int x))
    (rightEvaluates : GlobalIR.evaluate program store fuel environment right = .ok (.int y)) :
    CBindingWalk.builtinPrimitive "*" = some .mul ∧
      TypedExpansion.Primitive.type .mul = .fn .integer (.fn .integer .integer) ∧
      GlobalIR.evaluate program store (fuel + 1) environment (.mul left right) =
        .ok (.int (x * y)) ∧
      PolyIR.ValueTyped globals (.int (x * y)) .integer := by
  exact ⟨rfl, rfl, (GlobalIR.evaluate_mul_typed_of_children globals program store
    environment fuel left right x y leftEvaluates rightEvaluates).1,
    (GlobalIR.evaluate_mul_typed_of_children globals program store
      environment fuel left right x y leftEvaluates rightEvaluates).2⟩

/-- Registered C `<=` agrees with GlobalIR's integer comparison rule. -/
theorem cBuiltin_le_GlobalIR_semantics
    (globals : List Surface.Signature) (program : List GlobalIR.Definition)
    (store : GlobalIR.Store) (environment : List PolyIR.Value) (fuel : Nat)
    (left right : PolyIR.Term) (x y : Int)
    (leftEvaluates : GlobalIR.evaluate program store fuel environment left = .ok (.int x))
    (rightEvaluates : GlobalIR.evaluate program store fuel environment right = .ok (.int y)) :
    CBindingWalk.builtinPrimitive "<=" = some .le ∧
      TypedExpansion.Primitive.type .le = .fn .integer (.fn .integer .boolean) ∧
      GlobalIR.evaluate program store (fuel + 1) environment (.le left right) =
        .ok (.bool (decide (x ≤ y))) ∧
      PolyIR.ValueTyped globals (.bool (decide (x ≤ y))) .boolean := by
  exact ⟨rfl, rfl, (GlobalIR.evaluate_le_typed_of_children globals program store
    environment fuel left right x y leftEvaluates rightEvaluates).1,
    (GlobalIR.evaluate_le_typed_of_children globals program store
      environment fuel left right x y leftEvaluates rightEvaluates).2⟩

/-- Registered C integer equality agrees with GlobalIR's integer equality
rule and returns a typed Boolean. -/
theorem cBuiltin_intEq_GlobalIR_semantics
    (globals : List Surface.Signature) (program : List GlobalIR.Definition)
    (store : GlobalIR.Store) (environment : List PolyIR.Value) (fuel : Nat)
    (left right : PolyIR.Term) (x y : Int)
    (leftEvaluates : GlobalIR.evaluate program store fuel environment left = .ok (.int x))
    (rightEvaluates : GlobalIR.evaluate program store fuel environment right = .ok (.int y)) :
    CBindingWalk.builtinPrimitive "integer=" = some .intEq ∧
      TypedExpansion.Primitive.type .intEq = .fn .integer (.fn .integer .boolean) ∧
      GlobalIR.evaluate program store (fuel + 1) environment (.intEq left right) =
        .ok (.bool (x == y)) ∧
      PolyIR.ValueTyped globals (.bool (x == y)) .boolean := by
  exact ⟨rfl, rfl, (GlobalIR.evaluate_intEq_typed_of_children globals program store
    environment fuel left right x y leftEvaluates rightEvaluates).1,
    (GlobalIR.evaluate_intEq_typed_of_children globals program store
      environment fuel left right x y leftEvaluates rightEvaluates).2⟩

/-- The integer relational builtins not represented by dedicated GlobalIR
term constructors are modeled by this evaluator boundary. Their operand
evaluation order and wrong-shape behavior match the C dispatcher. -/
inductive IntegerComparisonOperation where
  | lt | le | gt | ge
  deriving DecidableEq, Repr

def IntegerComparisonOperation.name : IntegerComparisonOperation → String
  | .lt => "<"
  | .le => "<="
  | .gt => ">"
  | .ge => ">="

def IntegerComparisonOperation.primitive : IntegerComparisonOperation →
    TypedExpansion.Primitive
  | .lt => .lt
  | .le => .le
  | .gt => .gt
  | .ge => .ge

def IntegerComparisonOperation.evaluate (operation : IntegerComparisonOperation)
    (left right : Int) : Bool :=
  match operation with
  | .lt => decide (left < right)
  | .le => decide (left ≤ right)
  | .gt => decide (left > right)
  | .ge => decide (left ≥ right)

def evaluateIntegerComparisonCall (program : List GlobalIR.Definition)
    (store : GlobalIR.Store) (operation : IntegerComparisonOperation) :
    Nat → List PolyIR.Value → PolyIR.Term → PolyIR.Term →
      Except GlobalIR.Fault PolyIR.Value
  | 0, _, _, _ => .error (.core .outOfFuel)
  | fuel + 1, environment, left, right => do
      let leftValue ← GlobalIR.evaluate program store fuel environment left
      let rightValue ← GlobalIR.evaluate program store fuel environment right
      match leftValue, rightValue with
      | .int leftInteger, .int rightInteger =>
          .ok (.bool (operation.evaluate leftInteger rightInteger))
      | _, _ => .error (.core .wrongShape)

theorem evaluateIntegerComparisonCall_error_iff
    (program : List GlobalIR.Definition) (store : GlobalIR.Store)
    (operation : IntegerComparisonOperation) (fuel : Nat)
    (environment : List PolyIR.Value) (left right : PolyIR.Term)
    (fault : GlobalIR.Fault) :
    evaluateIntegerComparisonCall program store operation (fuel + 1) environment left right =
        .error fault ↔
      (∃ leftFault,
        GlobalIR.evaluate program store fuel environment left = .error leftFault ∧
        fault = leftFault) ∨
      (∃ leftValue rightFault,
        GlobalIR.evaluate program store fuel environment left = .ok leftValue ∧
        GlobalIR.evaluate program store fuel environment right = .error rightFault ∧
        fault = rightFault) ∨
      (∃ leftValue rightValue,
        GlobalIR.evaluate program store fuel environment left = .ok leftValue ∧
        GlobalIR.evaluate program store fuel environment right = .ok rightValue ∧
        (¬ ∃ x y, leftValue = .int x ∧ rightValue = .int y) ∧
        fault = .core .wrongShape) := by
  simp only [evaluateIntegerComparisonCall, bind, Except.bind, pure, Except.pure]
  cases leftResult : GlobalIR.evaluate program store fuel environment left with
  | error leftFault => simp [leftResult, eq_comm]
  | ok leftValue =>
      cases rightResult : GlobalIR.evaluate program store fuel environment right with
      | error rightFault => simp [leftResult, rightResult, eq_comm]
      | ok rightValue =>
          cases leftValue <;> cases rightValue <;>
            simp [leftResult, rightResult, eq_comm]

theorem evaluateIntegerComparisonCall_of_integer_children
    (globals : List Surface.Signature) (program : List GlobalIR.Definition)
    (store : GlobalIR.Store) (operation : IntegerComparisonOperation) (fuel : Nat)
    (environment : List PolyIR.Value) (left right : PolyIR.Term) (x y : Int)
    (leftEvaluates : GlobalIR.evaluate program store fuel environment left = .ok (.int x))
    (rightEvaluates : GlobalIR.evaluate program store fuel environment right = .ok (.int y)) :
    evaluateIntegerComparisonCall program store operation (fuel + 1) environment left right =
      .ok (.bool (operation.evaluate x y)) ∧
    PolyIR.ValueTyped globals (.bool (operation.evaluate x y)) .boolean := by
  constructor
  · simp [evaluateIntegerComparisonCall, leftEvaluates, rightEvaluates,
      bind, Except.bind, pure, Except.pure]
  · exact .bool

theorem evaluateIntegerComparisonCall_success_preserves_type
    (globals : List Surface.Signature) (program : List GlobalIR.Definition)
    (store : GlobalIR.Store) (operation : IntegerComparisonOperation) (fuel : Nat)
    (environment : List PolyIR.Value) (left right : PolyIR.Term) (result : PolyIR.Value)
    (success : evaluateIntegerComparisonCall program store operation fuel environment left right =
      .ok result) : PolyIR.ValueTyped globals result .boolean := by
  cases fuel with
  | zero => simp [evaluateIntegerComparisonCall] at success
  | succ remaining =>
      simp only [evaluateIntegerComparisonCall, bind, Except.bind, pure, Except.pure] at success
      cases leftResult : GlobalIR.evaluate program store remaining environment left with
      | error fault => simp [leftResult] at success
      | ok leftValue =>
          cases rightResult : GlobalIR.evaluate program store remaining environment right with
          | error fault => simp [leftResult, rightResult] at success
          | ok rightValue =>
              cases leftValue <;> cases rightValue <;>
                simp [leftResult, rightResult, IntegerComparisonOperation.evaluate] at success
              cases success
              exact .bool

/-- All four registered integer order comparisons have the declared curried
type and return the corresponding Boolean for integer operands. This covers
`<`, `>`, and `>=` in addition to the dedicated GlobalIR `<=` rule. -/
theorem cBuiltin_integerComparison_semantics
    (globals : List Surface.Signature) (program : List GlobalIR.Definition)
    (store : GlobalIR.Store) (environment : List PolyIR.Value) (fuel : Nat)
    (operation : IntegerComparisonOperation) (left right : PolyIR.Term) (x y : Int)
    (leftEvaluates : GlobalIR.evaluate program store fuel environment left = .ok (.int x))
    (rightEvaluates : GlobalIR.evaluate program store fuel environment right = .ok (.int y)) :
    CBindingWalk.builtinPrimitive operation.name = some operation.primitive ∧
    TypedExpansion.Primitive.type operation.primitive =
      .fn .integer (.fn .integer .boolean) ∧
    evaluateIntegerComparisonCall program store operation (fuel + 1) environment left right =
      .ok (.bool (operation.evaluate x y)) ∧
    PolyIR.ValueTyped globals (.bool (operation.evaluate x y)) .boolean := by
  have mapping : CBindingWalk.builtinPrimitive operation.name = some operation.primitive := by
    cases operation <;> rfl
  have signature : TypedExpansion.Primitive.type operation.primitive =
      .fn .integer (.fn .integer .boolean) := by
    cases operation <;> rfl
  obtain ⟨evaluated, typed⟩ := evaluateIntegerComparisonCall_of_integer_children
    globals program store operation fuel environment left right x y leftEvaluates rightEvaluates
  exact ⟨mapping, signature, evaluated, typed⟩

/-- The String builtins currently have an explicit evaluator boundary because
GlobalIR terms do not encode native builtin closures directly. -/
inductive StringBuiltinOperation where
  | equal
  | append
  deriving DecidableEq, Repr

def StringBuiltinOperation.name : StringBuiltinOperation → String
  | .equal => "string="
  | .append => "string-append"

def StringBuiltinOperation.primitive : StringBuiltinOperation → TypedExpansion.Primitive
  | .equal => .stringEq
  | .append => .append

def StringBuiltinOperation.resultType : StringBuiltinOperation → Surface.Ty
  | .equal => .boolean
  | .append => .string

def StringBuiltinOperation.primitiveResultType : StringBuiltinOperation → TypedExpansion.Ty
  | .equal => .boolean
  | .append => .string

def StringBuiltinOperation.result (operation : StringBuiltinOperation)
    (left right : String) : PolyIR.Value :=
  match operation with
  | .equal => .bool (decide (left = right))
  | .append => .string (left ++ right)

/-- Evaluate the two registered C String builtins after evaluating both
arguments from left to right. Their String values have explicit byte-buffer
semantics in `Lexical.CTextModel`. -/
def evaluateStringBuiltin (program : List GlobalIR.Definition) (store : GlobalIR.Store)
    (operation : StringBuiltinOperation) : Nat → List PolyIR.Value → PolyIR.Term →
      PolyIR.Term → Except GlobalIR.Fault PolyIR.Value
  | 0, _, _, _ => .error (.core .outOfFuel)
  | fuel + 1, environment, left, right => do
      let leftValue ← GlobalIR.evaluate program store fuel environment left
      let rightValue ← GlobalIR.evaluate program store fuel environment right
      match leftValue, rightValue with
      | .string leftText, .string rightText => .ok (operation.result leftText rightText)
      | _, _ => .error (.core .wrongShape)

/-- Exact fault order for String calls: left operand, right operand, then
runtime shape validation. -/
theorem evaluateStringBuiltin_error_iff
    (program : List GlobalIR.Definition) (store : GlobalIR.Store)
    (operation : StringBuiltinOperation) (fuel : Nat) (environment : List PolyIR.Value)
    (left right : PolyIR.Term) (fault : GlobalIR.Fault) :
    evaluateStringBuiltin program store operation (fuel + 1) environment left right =
        .error fault ↔
      (∃ leftFault,
        GlobalIR.evaluate program store fuel environment left = .error leftFault ∧
        fault = leftFault) ∨
      (∃ leftValue rightFault,
        GlobalIR.evaluate program store fuel environment left = .ok leftValue ∧
        GlobalIR.evaluate program store fuel environment right = .error rightFault ∧
        fault = rightFault) ∨
      (∃ leftValue rightValue,
        GlobalIR.evaluate program store fuel environment left = .ok leftValue ∧
        GlobalIR.evaluate program store fuel environment right = .ok rightValue ∧
        (¬ ∃ leftText rightText,
          leftValue = .string leftText ∧ rightValue = .string rightText) ∧
        fault = .core .wrongShape) := by
  simp only [evaluateStringBuiltin, bind, Except.bind, pure, Except.pure]
  cases leftResult : GlobalIR.evaluate program store fuel environment left with
  | error leftFault => simp [leftResult, eq_comm]
  | ok leftValue =>
      cases rightResult : GlobalIR.evaluate program store fuel environment right with
      | error rightFault => simp [leftResult, rightResult, eq_comm]
      | ok rightValue =>
          cases leftValue <;> cases rightValue <;>
            simp [leftResult, rightResult, eq_comm]

/-- Exact successful-result characterization for the String helper. It
evaluates both operands left-to-right and succeeds precisely on two String
values, returning the operation's declared result. -/
theorem evaluateStringBuiltin_success_iff
    (program : List GlobalIR.Definition) (store : GlobalIR.Store)
    (operation : StringBuiltinOperation) (fuel : Nat) (environment : List PolyIR.Value)
    (left right : PolyIR.Term) (result : PolyIR.Value) :
    evaluateStringBuiltin program store operation (fuel + 1) environment left right =
        .ok result ↔
      ∃ leftText rightText,
        GlobalIR.evaluate program store fuel environment left = .ok (.string leftText) ∧
        GlobalIR.evaluate program store fuel environment right = .ok (.string rightText) ∧
        result = operation.result leftText rightText := by
  simp only [evaluateStringBuiltin, bind, Except.bind, pure, Except.pure]
  cases leftResult : GlobalIR.evaluate program store fuel environment left with
  | error fault => simp [leftResult]
  | ok leftValue =>
      cases rightResult : GlobalIR.evaluate program store fuel environment right with
      | error fault => simp [leftResult, rightResult]
      | ok rightValue =>
          cases leftValue <;> cases rightValue <;>
            simp [leftResult, rightResult, StringBuiltinOperation.result, eq_comm]

theorem evaluateStringBuiltin_success_preserves_type
    (globals : List Surface.Signature) (program : List GlobalIR.Definition)
    (store : GlobalIR.Store) (operation : StringBuiltinOperation) (fuel : Nat)
    (environment : List PolyIR.Value) (left right : PolyIR.Term) (result : PolyIR.Value)
    (success : evaluateStringBuiltin program store operation fuel environment left right =
      .ok result) :
    PolyIR.ValueTyped globals result operation.resultType := by
  cases operation with
  | equal =>
      change PolyIR.ValueTyped globals result .boolean
      cases fuel with
      | zero => simp [evaluateStringBuiltin] at success
      | succ fuel =>
          simp only [evaluateStringBuiltin, bind, Except.bind, pure, Except.pure] at success
          cases leftResult : GlobalIR.evaluate program store fuel environment left with
          | error fault => simp [leftResult] at success
          | ok leftValue =>
              cases rightResult : GlobalIR.evaluate program store fuel environment right with
              | error fault => simp [leftResult, rightResult] at success
              | ok rightValue =>
                  cases leftValue <;> cases rightValue <;>
                    simp [leftResult, rightResult, StringBuiltinOperation.result] at success
                  cases success
                  exact .bool
  | append =>
      change PolyIR.ValueTyped globals result .string
      cases fuel with
      | zero => simp [evaluateStringBuiltin] at success
      | succ fuel =>
          simp only [evaluateStringBuiltin, bind, Except.bind, pure, Except.pure] at success
          cases leftResult : GlobalIR.evaluate program store fuel environment left with
          | error fault => simp [leftResult] at success
          | ok leftValue =>
              cases rightResult : GlobalIR.evaluate program store fuel environment right with
              | error fault => simp [leftResult, rightResult] at success
              | ok rightValue =>
                  cases leftValue <;> cases rightValue <;>
                    simp [leftResult, rightResult, StringBuiltinOperation.result] at success
                  cases success
                  exact .string

/-- The registered C name, curried primitive signature, and native
GlobalIR-helper success typing agree for each String operation. -/
theorem cBuiltin_string_success_preserves_type
    (globals : List Surface.Signature) (program : List GlobalIR.Definition)
    (store : GlobalIR.Store) (operation : StringBuiltinOperation) (fuel : Nat)
    (environment : List PolyIR.Value) (left right : PolyIR.Term) (result : PolyIR.Value)
    (success : evaluateStringBuiltin program store operation fuel environment left right =
      .ok result) :
    CBindingWalk.builtinPrimitive operation.name = some operation.primitive ∧
      TypedExpansion.Primitive.type operation.primitive =
        .fn .string (.fn .string operation.primitiveResultType) ∧
      PolyIR.ValueTyped globals result operation.resultType := by
  cases operation with
  | equal =>
      exact ⟨rfl, rfl, evaluateStringBuiltin_success_preserves_type globals program store
        .equal fuel environment left right result success⟩
  | append =>
      exact ⟨rfl, rfl, evaluateStringBuiltin_success_preserves_type globals program store
        .append fuel environment left right result success⟩

/-- The native String helper implements byte equality and concatenation on
canonical C Text values, including embedded NUL bytes. -/
theorem evaluateStringBuiltin_CText_semantics
    (operation : StringBuiltinOperation) (left right : String) :
    Lexical.CTextModel.stringEqual (Lexical.CTextModel.ofString left)
        (Lexical.CTextModel.ofString right) = decide (left = right) ∧
      Lexical.CTextModel.stringAppend (Lexical.CTextModel.ofString left)
        (Lexical.CTextModel.ofString right) = Lexical.CTextModel.ofString (left ++ right) ∧
      (match operation with
        | .equal => operation.result left right = .bool (decide (left = right))
        | .append => operation.result left right = .string (left ++ right)) := by
  refine ⟨Lexical.CTextModel.stringEqual_ofString_iff left right,
    Lexical.CTextModel.stringAppend_ofString left right, ?_⟩
  cases operation <;> rfl

/-- Evaluate the registered character equality builtin after its two operands
have been evaluated from left to right. C's stored scalar equality is modeled
by Lean `Char` equality. -/
def evaluateCharacterEquality (program : List GlobalIR.Definition) (store : GlobalIR.Store) :
    Nat → List PolyIR.Value → PolyIR.Term → PolyIR.Term → Except GlobalIR.Fault PolyIR.Value
  | 0, _, _, _ => .error (.core .outOfFuel)
  | fuel + 1, environment, left, right => do
      let leftValue ← GlobalIR.evaluate program store fuel environment left
      let rightValue ← GlobalIR.evaluate program store fuel environment right
      match leftValue, rightValue with
      | .character leftCharacter, .character rightCharacter =>
          .ok (.bool (decide (leftCharacter = rightCharacter)))
      | _, _ => .error (.core .wrongShape)

theorem evaluateCharacterEquality_error_iff
    (program : List GlobalIR.Definition) (store : GlobalIR.Store) (fuel : Nat)
    (environment : List PolyIR.Value) (left right : PolyIR.Term) (fault : GlobalIR.Fault) :
    evaluateCharacterEquality program store (fuel + 1) environment left right = .error fault ↔
      (∃ leftFault,
        GlobalIR.evaluate program store fuel environment left = .error leftFault ∧
        fault = leftFault) ∨
      (∃ leftValue rightFault,
        GlobalIR.evaluate program store fuel environment left = .ok leftValue ∧
        GlobalIR.evaluate program store fuel environment right = .error rightFault ∧
        fault = rightFault) ∨
      (∃ leftValue rightValue,
        GlobalIR.evaluate program store fuel environment left = .ok leftValue ∧
        GlobalIR.evaluate program store fuel environment right = .ok rightValue ∧
        (¬ ∃ leftCharacter rightCharacter,
          leftValue = .character leftCharacter ∧ rightValue = .character rightCharacter) ∧
        fault = .core .wrongShape) := by
  simp only [evaluateCharacterEquality, bind, Except.bind, pure, Except.pure]
  cases leftResult : GlobalIR.evaluate program store fuel environment left with
  | error leftFault => simp [leftResult, eq_comm]
  | ok leftValue =>
      cases rightResult : GlobalIR.evaluate program store fuel environment right with
      | error rightFault => simp [leftResult, rightResult, eq_comm]
      | ok rightValue =>
          cases leftValue <;> cases rightValue <;>
            simp [leftResult, rightResult, eq_comm]

/-- Exact successful-result characterization for C `character=`. -/
theorem evaluateCharacterEquality_success_iff
    (program : List GlobalIR.Definition) (store : GlobalIR.Store) (fuel : Nat)
    (environment : List PolyIR.Value) (left right : PolyIR.Term) (result : PolyIR.Value) :
    evaluateCharacterEquality program store (fuel + 1) environment left right = .ok result ↔
      ∃ leftCharacter rightCharacter,
        GlobalIR.evaluate program store fuel environment left = .ok (.character leftCharacter) ∧
        GlobalIR.evaluate program store fuel environment right = .ok (.character rightCharacter) ∧
        result = .bool (decide (leftCharacter = rightCharacter)) := by
  simp only [evaluateCharacterEquality, bind, Except.bind, pure, Except.pure]
  cases leftResult : GlobalIR.evaluate program store fuel environment left with
  | error fault => simp [leftResult]
  | ok leftValue =>
      cases rightResult : GlobalIR.evaluate program store fuel environment right with
      | error fault => simp [leftResult, rightResult]
      | ok rightValue =>
          cases leftValue <;> cases rightValue <;>
            simp [leftResult, rightResult, eq_comm]

theorem cBuiltin_characterEquality_success_preserves_type
    (globals : List Surface.Signature) (program : List GlobalIR.Definition)
    (store : GlobalIR.Store) (fuel : Nat) (environment : List PolyIR.Value)
    (left right : PolyIR.Term) (result : PolyIR.Value)
    (success : evaluateCharacterEquality program store fuel environment left right =
      .ok result) :
    CBindingWalk.builtinPrimitive "character=" = some .charEq ∧
      TypedExpansion.Primitive.type .charEq =
        .fn .character (.fn .character .boolean) ∧
      PolyIR.ValueTyped globals result .boolean := by
  have resultTyped : PolyIR.ValueTyped globals result .boolean := by
    cases fuel with
    | zero => simp [evaluateCharacterEquality] at success
    | succ fuel =>
        simp only [evaluateCharacterEquality, bind, Except.bind, pure, Except.pure] at success
        cases leftResult : GlobalIR.evaluate program store fuel environment left with
        | error fault => simp [leftResult] at success
        | ok leftValue =>
            cases rightResult : GlobalIR.evaluate program store fuel environment right with
            | error fault => simp [leftResult, rightResult] at success
            | ok rightValue =>
                cases leftValue <;> cases rightValue <;>
                  simp [leftResult, rightResult] at success
                cases success
                exact .bool
  exact ⟨rfl, rfl, resultTyped⟩

/-- For successful Character operands, the GlobalIR helper returns exactly
the Boolean produced by C's comparison of the stored Unicode scalar values. -/
theorem cBuiltin_characterEquality_GlobalIR_semantics
    (globals : List Surface.Signature) (program : List GlobalIR.Definition)
    (store : GlobalIR.Store) (fuel : Nat) (environment : List PolyIR.Value)
    (left right : PolyIR.Term) (leftCharacter rightCharacter : Char)
    (leftEvaluates : GlobalIR.evaluate program store fuel environment left =
      .ok (.character leftCharacter))
    (rightEvaluates : GlobalIR.evaluate program store fuel environment right =
      .ok (.character rightCharacter)) :
    CBindingWalk.builtinPrimitive "character=" = some .charEq ∧
      TypedExpansion.Primitive.type .charEq =
        .fn .character (.fn .character .boolean) ∧
      evaluateCharacterEquality program store (fuel + 1) environment left right =
        .ok (.bool (leftCharacter.toNat == rightCharacter.toNat)) ∧
      PolyIR.ValueTyped globals (.bool (leftCharacter.toNat == rightCharacter.toNat))
        .boolean := by
  have cEquality := CBindingWalk.builtinCharacterEquality_semantics leftCharacter rightCharacter
  have evaluated : evaluateCharacterEquality program store (fuel + 1) environment left right =
      .ok (.bool (leftCharacter.toNat == rightCharacter.toNat)) := by
    simp [evaluateCharacterEquality, leftEvaluates, rightEvaluates, bind, Except.bind,
      pure, Except.pure, cEquality.2.2]
  exact ⟨rfl, rfl, evaluated, .bool⟩

end NLisp
