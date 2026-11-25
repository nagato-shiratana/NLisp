import NLisp.GlobalIR
import NLisp.ErasureExecution

namespace NLisp

def wrapCoreFault {α : Type} (result : Except PolyIR.Fault α) :
    Except GlobalIR.Fault α :=
  match result with
  | .error fault => .error (.core fault)
  | .ok value => .ok value

@[simp] theorem wrapCoreFault_bind {α β : Type} (result : Except PolyIR.Fault α)
    (next : α → Except PolyIR.Fault β) :
    wrapCoreFault (result >>= next) =
      (wrapCoreFault result >>= fun value => wrapCoreFault (next value)) := by
  cases result <;> rfl

theorem wrapCoreFault_error_iff (result : Except PolyIR.Fault α) (fault : PolyIR.Fault) :
    wrapCoreFault result = .error (.core fault) ↔ result = .error fault := by
  cases result with
  | error actual => simp [wrapCoreFault]
  | ok value => simp [wrapCoreFault]

theorem wrapCoreFault_ok_iff (result : Except PolyIR.Fault α) (value : α) :
    wrapCoreFault result = .ok value ↔ result = .ok value := by
  cases result with
  | error actual => simp [wrapCoreFault]
  | ok actual => simp [wrapCoreFault]

theorem functionTable_map_lookup (definitions : List PolyIR.RuntimeDefinition) (index : Nat) :
    (definitions.map GlobalIR.Definition.function)[index]? =
      (definitions[index]?).map GlobalIR.Definition.function := by
  induction definitions generalizing index with
  | nil => cases index <;> rfl
  | cons head tail ih => cases index <;> simp [ih]

/-- Leaf terms have the same operational behavior in a function-only
GlobalIR table and PolyIR, including wrapped errors and arbitrary fuel. -/
inductive FunctionTableLeaf : PolyIR.Term → Prop where
  | var (index : Nat) : FunctionTableLeaf (.var index)
  | global (index : Nat) : FunctionTableLeaf (.global index)
  | bool (value : Bool) : FunctionTableLeaf (.bool value)
  | int (value : Int) : FunctionTableLeaf (.int value)
  | float (value : Float) : FunctionTableLeaf (.float value)
  | string (value : String) : FunctionTableLeaf (.string value)
  | character (value : Char) : FunctionTableLeaf (.character value)
  | unit : FunctionTableLeaf .unit
  | lam (arity : Nat) (body : PolyIR.Term) : FunctionTableLeaf (.lam arity body)
  | nil : FunctionTableLeaf .nil
  | none : FunctionTableLeaf .none

theorem functionTable_globalIR_leaf_commutes
    (definitions : List PolyIR.RuntimeDefinition) (store : GlobalIR.Store)
    {term : PolyIR.Term} (leaf : FunctionTableLeaf term) :
    ∀ fuel environment,
      GlobalIR.evaluate (definitions.map GlobalIR.Definition.function) store fuel environment term =
        wrapCoreFault (PolyIR.evaluate definitions fuel environment term) := by
  induction leaf with
  | var index =>
      intro fuel environment
      cases fuel with
      | zero => simp [GlobalIR.evaluate, PolyIR.evaluate, wrapCoreFault]
      | succ fuel =>
          cases lookup : environment[index]? <;>
            simp [GlobalIR.evaluate, PolyIR.evaluate, wrapCoreFault, lookup,
              Except.pure, Pure.pure, pure]
  | global index =>
      intro fuel environment
      cases fuel with
      | zero => simp [GlobalIR.evaluate, PolyIR.evaluate, wrapCoreFault]
      | succ fuel =>
          simp only [GlobalIR.evaluate, PolyIR.evaluate, wrapCoreFault]
          rw [functionTable_map_lookup]
          cases lookup : definitions[index]? <;>
            simp [lookup, Except.pure, Pure.pure, pure]
  | bool value =>
      intro fuel environment
      cases fuel <;> simp [GlobalIR.evaluate, PolyIR.evaluate, wrapCoreFault,
        Except.pure, Pure.pure, pure]

  | int value =>
      intro fuel environment
      cases fuel <;> simp [GlobalIR.evaluate, PolyIR.evaluate, wrapCoreFault,
        Except.pure, Pure.pure, pure]
  | float value =>
      intro fuel environment
      cases fuel <;> simp [GlobalIR.evaluate, PolyIR.evaluate, wrapCoreFault,
        Except.pure, Pure.pure, pure]
  | string value =>
      intro fuel environment
      cases fuel <;> simp [GlobalIR.evaluate, PolyIR.evaluate, wrapCoreFault,
        Except.pure, Pure.pure, pure]
  | character value =>
      intro fuel environment
      cases fuel <;> simp [GlobalIR.evaluate, PolyIR.evaluate, wrapCoreFault,
        Except.pure, Pure.pure, pure]
  | unit =>
      intro fuel environment
      cases fuel <;> simp [GlobalIR.evaluate, PolyIR.evaluate, wrapCoreFault,
        Except.pure, Pure.pure, pure]
  | lam arity body =>
      intro fuel environment
      cases fuel <;> simp [GlobalIR.evaluate, PolyIR.evaluate, wrapCoreFault,
        Except.pure, Pure.pure, pure]
  | nil =>
      intro fuel environment
      cases fuel <;> simp [GlobalIR.evaluate, PolyIR.evaluate, wrapCoreFault,
        Except.pure, Pure.pure, pure]
  | none =>
      intro fuel environment
      cases fuel <;> simp [GlobalIR.evaluate, PolyIR.evaluate, wrapCoreFault,
        Except.pure, Pure.pure, pure]

/-- Once expression evaluation commutes pointwise, evaluating a list of
arguments also commutes. This separates the structural list induction from
the expression-specific simulation. -/
theorem functionTable_globalIR_arguments_commutes_of_pointwise
    (definitions : List PolyIR.RuntimeDefinition) (store : GlobalIR.Store)
    (terms : List PolyIR.Term) (fuel : Nat) (environment : List PolyIR.Value)
    (pointwise : ∀ evaluationFuel term, term ∈ terms →
      GlobalIR.evaluate (definitions.map GlobalIR.Definition.function) store evaluationFuel
          environment term = wrapCoreFault (PolyIR.evaluate definitions evaluationFuel environment term)) :
    GlobalIR.evaluateArgs (definitions.map GlobalIR.Definition.function) store fuel environment terms =
      wrapCoreFault (PolyIR.evaluateArgs definitions fuel environment terms) := by
  revert fuel environment pointwise
  induction terms with
  | nil =>
      intro fuel environment pointwise
      cases fuel <;> simp [GlobalIR.evaluateArgs, PolyIR.evaluateArgs, wrapCoreFault,
        Except.pure, Pure.pure, pure]
  | cons head tail ih =>
      intro fuel environment pointwise
      cases fuel with
      | zero => simp [GlobalIR.evaluateArgs, PolyIR.evaluateArgs, wrapCoreFault]
      | succ fuel =>
          have headCommutes := pointwise fuel head (by simp)
          have tailCommutes := ih fuel environment (by
            intro evaluationFuel term member
            exact pointwise evaluationFuel term (by simp [member]))
          simp only [GlobalIR.evaluateArgs, PolyIR.evaluateArgs]
          rw [headCommutes]
          rw [tailCommutes]
          cases hhead : PolyIR.evaluate definitions fuel environment head <;>
            cases htail : PolyIR.evaluateArgs definitions fuel environment tail <;> rfl

/-- Sequence evaluation commutes when each expression evaluation commutes.
The accumulator value is passed through unchanged and only the evaluated
expressions require the pointwise simulation premise. -/
theorem functionTable_globalIR_sequence_commutes_of_pointwise
    (definitions : List PolyIR.RuntimeDefinition) (store : GlobalIR.Store)
    (terms : List PolyIR.Term) (fuel : Nat) (environment : List PolyIR.Value)
    (previous : PolyIR.Value)
    (pointwise : ∀ evaluationFuel term, term ∈ terms →
      GlobalIR.evaluate (definitions.map GlobalIR.Definition.function) store evaluationFuel
          environment term = wrapCoreFault (PolyIR.evaluate definitions evaluationFuel environment term)) :
    GlobalIR.evaluateSequence (definitions.map GlobalIR.Definition.function) store
        fuel environment previous terms =
      wrapCoreFault (PolyIR.evaluateSequence definitions fuel environment previous terms) := by
  revert fuel environment previous pointwise
  induction terms with
  | nil =>
      intro fuel environment previous pointwise
      cases fuel <;> simp [GlobalIR.evaluateSequence, PolyIR.evaluateSequence, wrapCoreFault,
        Except.pure, Pure.pure, pure]
  | cons head tail ih =>
      intro fuel environment previous pointwise
      cases fuel with
      | zero => simp [GlobalIR.evaluateSequence, PolyIR.evaluateSequence, wrapCoreFault]
      | succ fuel =>
          have headCommutes := pointwise fuel head (by simp)
          simp only [GlobalIR.evaluateSequence, PolyIR.evaluateSequence]
          rw [headCommutes]
          cases hhead : PolyIR.evaluate definitions fuel environment head with
          | error fault => rfl
          | ok value =>
              have tailCommutes := ih fuel environment value (by
                intro evaluationFuel term member
                exact pointwise evaluationFuel term (by simp [member]))
              change GlobalIR.evaluateSequence (definitions.map GlobalIR.Definition.function)
                store fuel environment value tail =
                  wrapCoreFault (PolyIR.evaluateSequence definitions fuel environment value tail)
              rw [tailCommutes]

/-- The expression-level `.begin` evaluator commutes when its first
expression and every sequence expression commute pointwise. -/
theorem functionTable_globalIR_begin_commutes_of_pointwise
    (definitions : List PolyIR.RuntimeDefinition) (store : GlobalIR.Store)
    (first : PolyIR.Term) (rest : List PolyIR.Term) (fuel : Nat)
    (environment : List PolyIR.Value)
    (pointwise : ∀ evaluationFuel term, term ∈ first :: rest →
      GlobalIR.evaluate (definitions.map GlobalIR.Definition.function) store evaluationFuel
          environment term = wrapCoreFault (PolyIR.evaluate definitions evaluationFuel environment term)) :
    GlobalIR.evaluate (definitions.map GlobalIR.Definition.function) store fuel environment
        (.begin first rest) =
      wrapCoreFault (PolyIR.evaluate definitions fuel environment (.begin first rest)) := by
  cases fuel with
  | zero => simp [GlobalIR.evaluate, PolyIR.evaluate, wrapCoreFault]
  | succ fuel =>
      have firstCommutes := pointwise fuel first (by simp)
      simp only [GlobalIR.evaluate, PolyIR.evaluate]
      rw [firstCommutes]
      cases hfirst : PolyIR.evaluate definitions fuel environment first with
      | error fault => rfl
      | ok value =>
          have restCommutes := functionTable_globalIR_sequence_commutes_of_pointwise
            definitions store rest fuel environment value (by
              intro evaluationFuel term member
              exact pointwise evaluationFuel term (by simp [member]))
          change GlobalIR.evaluateSequence (definitions.map GlobalIR.Definition.function)
            store fuel environment value rest =
              wrapCoreFault (PolyIR.evaluateSequence definitions fuel environment value rest)
          exact restCommutes

/-- Conditional evaluation commutes from pointwise correspondence for the
condition and both branches. Only the selected branch is evaluated. -/
theorem functionTable_globalIR_ite_commutes_of_pointwise
    (definitions : List PolyIR.RuntimeDefinition) (store : GlobalIR.Store)
    (condition yes no : PolyIR.Term) (fuel : Nat) (environment : List PolyIR.Value)
    (pointwise : ∀ evaluationFuel term, term ∈ [condition, yes, no] →
      GlobalIR.evaluate (definitions.map GlobalIR.Definition.function) store evaluationFuel environment term =
        wrapCoreFault (PolyIR.evaluate definitions evaluationFuel environment term)) :
    GlobalIR.evaluate (definitions.map GlobalIR.Definition.function) store fuel environment
        (.ite condition yes no) =
      wrapCoreFault (PolyIR.evaluate definitions fuel environment (.ite condition yes no)) := by
  cases fuel with
  | zero => simp [GlobalIR.evaluate, PolyIR.evaluate, wrapCoreFault]
  | succ fuel =>
      have conditionCommutes := pointwise fuel condition (by simp)
      simp only [GlobalIR.evaluate, PolyIR.evaluate]
      rw [conditionCommutes]
      cases hcondition : PolyIR.evaluate definitions fuel environment condition with
      | error fault => rfl
      | ok value =>
          cases value with
          | bool decision =>
              cases decision with
              | false => exact pointwise fuel no (by simp)
              | true => exact pointwise fuel yes (by simp)
          | int value => rfl
          | float value => rfl
          | string value => rfl
          | character value => rfl
          | unit => rfl
          | closure arity body captured => rfl
          | nil => rfl
          | cons head tail => rfl
          | none => rfl
          | some value => rfl
          | global index => rfl

/-- Integer addition commutes from pointwise correspondence of both
operands; both successful values and wrong-shape failures are included. -/
theorem functionTable_globalIR_add_commutes_of_pointwise
    (definitions : List PolyIR.RuntimeDefinition) (store : GlobalIR.Store)
    (left right : PolyIR.Term) (fuel : Nat) (environment : List PolyIR.Value)
    (pointwise : ∀ evaluationFuel term, term ∈ [left, right] →
      GlobalIR.evaluate (definitions.map GlobalIR.Definition.function) store evaluationFuel environment term =
        wrapCoreFault (PolyIR.evaluate definitions evaluationFuel environment term)) :
    GlobalIR.evaluate (definitions.map GlobalIR.Definition.function) store fuel environment
        (.add left right) =
      wrapCoreFault (PolyIR.evaluate definitions fuel environment (.add left right)) := by
  cases fuel with
  | zero => simp [GlobalIR.evaluate, PolyIR.evaluate, wrapCoreFault]
  | succ fuel =>
      have leftCommutes := pointwise fuel left (by simp)
      have rightCommutes := pointwise fuel right (by simp)
      simp only [GlobalIR.evaluate, PolyIR.evaluate]
      rw [leftCommutes]
      cases hleft : PolyIR.evaluate definitions fuel environment left with
      | error fault => rfl
      | ok leftValue =>
          rw [rightCommutes]
          cases hright : PolyIR.evaluate definitions fuel environment right with
          | error fault => rfl
          | ok rightValue =>
              cases leftValue <;> cases rightValue <;> rfl

inductive FunctionTableIntegerBinary where
  | add | sub | mul | le | intEq
  deriving DecidableEq

def FunctionTableIntegerBinary.term (operation : FunctionTableIntegerBinary)
    (left right : PolyIR.Term) : PolyIR.Term :=
  match operation with
  | .add => .add left right
  | .sub => .sub left right
  | .mul => .mul left right
  | .le => .le left right
  | .intEq => .intEq left right

/-- Integer binary operators share the same compositional simulation shape.
For each operation, correspondence of the two child evaluations implies
correspondence of the complete function-table GlobalIR and PolyIR evaluation,
including child errors and wrong-shape errors. -/
theorem functionTable_globalIR_integerBinary_commutes_of_pointwise
    (definitions : List PolyIR.RuntimeDefinition) (store : GlobalIR.Store)
    (operation : FunctionTableIntegerBinary) (left right : PolyIR.Term)
    (fuel : Nat) (environment : List PolyIR.Value)
    (pointwise : ∀ evaluationFuel term, term ∈ [left, right] →
      GlobalIR.evaluate (definitions.map GlobalIR.Definition.function) store evaluationFuel environment term =
        wrapCoreFault (PolyIR.evaluate definitions evaluationFuel environment term)) :
    GlobalIR.evaluate (definitions.map GlobalIR.Definition.function) store fuel environment
        (operation.term left right) =
      wrapCoreFault (PolyIR.evaluate definitions fuel environment (operation.term left right)) := by
  cases operation with
  | add =>
      simpa [FunctionTableIntegerBinary.term] using
        functionTable_globalIR_add_commutes_of_pointwise definitions store left right fuel environment pointwise
  | sub =>
      cases fuel with
      | zero => simp [FunctionTableIntegerBinary.term, GlobalIR.evaluate, PolyIR.evaluate, wrapCoreFault]
      | succ fuel =>
          have leftCommutes := pointwise fuel left (by simp)
          have rightCommutes := pointwise fuel right (by simp)
          simp only [FunctionTableIntegerBinary.term, GlobalIR.evaluate, PolyIR.evaluate]
          rw [leftCommutes]
          cases hleft : PolyIR.evaluate definitions fuel environment left with
          | error fault => rfl
          | ok leftValue =>
              rw [rightCommutes]
              cases hright : PolyIR.evaluate definitions fuel environment right with
              | error fault => rfl
              | ok rightValue => cases leftValue <;> cases rightValue <;> rfl
  | mul =>
      cases fuel with
      | zero => simp [FunctionTableIntegerBinary.term, GlobalIR.evaluate, PolyIR.evaluate, wrapCoreFault]
      | succ fuel =>
          have leftCommutes := pointwise fuel left (by simp)
          have rightCommutes := pointwise fuel right (by simp)
          simp only [FunctionTableIntegerBinary.term, GlobalIR.evaluate, PolyIR.evaluate]
          rw [leftCommutes]
          cases hleft : PolyIR.evaluate definitions fuel environment left with
          | error fault => rfl
          | ok leftValue =>
              rw [rightCommutes]
              cases hright : PolyIR.evaluate definitions fuel environment right with
              | error fault => rfl
              | ok rightValue => cases leftValue <;> cases rightValue <;> rfl
  | le =>
      cases fuel with
      | zero => simp [FunctionTableIntegerBinary.term, GlobalIR.evaluate, PolyIR.evaluate, wrapCoreFault]
      | succ fuel =>
          have leftCommutes := pointwise fuel left (by simp)
          have rightCommutes := pointwise fuel right (by simp)
          simp only [FunctionTableIntegerBinary.term, GlobalIR.evaluate, PolyIR.evaluate]
          rw [leftCommutes]
          cases hleft : PolyIR.evaluate definitions fuel environment left with
          | error fault => rfl
          | ok leftValue =>
              rw [rightCommutes]
              cases hright : PolyIR.evaluate definitions fuel environment right with
              | error fault => rfl
              | ok rightValue => cases leftValue <;> cases rightValue <;> rfl
  | intEq =>
      cases fuel with
      | zero => simp [FunctionTableIntegerBinary.term, GlobalIR.evaluate, PolyIR.evaluate, wrapCoreFault]
      | succ fuel =>
          have leftCommutes := pointwise fuel left (by simp)
          have rightCommutes := pointwise fuel right (by simp)
          simp only [FunctionTableIntegerBinary.term, GlobalIR.evaluate, PolyIR.evaluate]
          rw [leftCommutes]
          cases hleft : PolyIR.evaluate definitions fuel environment left with
          | error fault => rfl
          | ok leftValue =>
              rw [rightCommutes]
              cases hright : PolyIR.evaluate definitions fuel environment right with
              | error fault => rfl
              | ok rightValue => cases leftValue <;> cases rightValue <;> rfl

/-- Float addition, subtraction, multiplication, and division have the same
function-table simulation rule. The child correspondence is sufficient even
for NaN, infinities, signed zero, and subnormal values because the two formal
evaluators invoke the same Lean Float operation. This theorem does not assert
agreement with an external C binary64 implementation. -/
theorem functionTable_globalIR_floatBin_commutes_of_pointwise
    (definitions : List PolyIR.RuntimeDefinition) (store : GlobalIR.Store)
    (operation : Surface.FloatBinOp) (left right : PolyIR.Term)
    (fuel : Nat) (environment : List PolyIR.Value)
    (pointwise : ∀ evaluationFuel term, term ∈ [left, right] →
      GlobalIR.evaluate (definitions.map GlobalIR.Definition.function) store evaluationFuel environment term =
        wrapCoreFault (PolyIR.evaluate definitions evaluationFuel environment term)) :
    GlobalIR.evaluate (definitions.map GlobalIR.Definition.function) store fuel environment
        (.floatBin operation left right) =
      wrapCoreFault (PolyIR.evaluate definitions fuel environment (.floatBin operation left right)) := by
  cases fuel with
  | zero => simp [GlobalIR.evaluate, PolyIR.evaluate, wrapCoreFault]
  | succ fuel =>
      have leftCommutes := pointwise fuel left (by simp)
      have rightCommutes := pointwise fuel right (by simp)
      simp only [GlobalIR.evaluate, PolyIR.evaluate]
      rw [leftCommutes]
      cases hleft : PolyIR.evaluate definitions fuel environment left with
      | error fault => rfl
      | ok leftValue =>
          rw [rightCommutes]
          cases hright : PolyIR.evaluate definitions fuel environment right with
          | error fault => rfl
          | ok rightValue =>
              cases leftValue <;> cases rightValue <;> cases operation <;> rfl

theorem eraseValues_lookup_none (values : List Surface.Value) (index : Nat)
    (missing : values[index]? = none) :
    (PolyIR.eraseValues values)[index]? = none := by
  induction values generalizing index with
  | nil => cases index <;> rfl
  | cons head tail ih =>
      cases index with
      | zero => simp [PolyIR.eraseValues] at missing ⊢
      | succ index =>
          have tailMissing : tail[index]? = none := by simpa using missing
          have tailErased := ih index tailMissing
          simpa [PolyIR.eraseValues] using tailErased

/-- An unbound local-variable error has the same source fault in the Surface
evaluator and the corresponding wrapped core fault in GlobalIR, after the
standard value erasure of the environment. -/
theorem unbound_variable_fault_corresponds_to_globalIR
    (sourceProgram : Surface.Definitions) (runtimeProgram : List GlobalIR.Definition)
    (store : GlobalIR.Store) (fuel index : Nat) (environment : List Surface.Value)
    (missing : environment[index]? = none) :
    Surface.evaluate sourceProgram (fuel + 1) environment (.var index) =
        .error .unbound ↔
      GlobalIR.evaluate runtimeProgram store (fuel + 1) (PolyIR.eraseValues environment)
        (.var index) = .error (.core .unbound) := by
  have erasedMissing : (PolyIR.eraseValues environment)[index]? = none :=
    eraseValues_lookup_none environment index missing
  simp [Surface.evaluate, GlobalIR.evaluate, missing, erasedMissing]

/-- A source global reference and its erased GlobalIR index agree on the
unbound case when both declaration tables lack that index. This covers the
global lookup fault independently of the distinct top-level value getter
lowering. -/
theorem unbound_global_reference_fault_corresponds_to_globalIR
    (sourceProgram : Surface.Definitions) (runtimeProgram : List GlobalIR.Definition)
    (store : GlobalIR.Store) (fuel index : Nat) (environment : List Surface.Value)
    (typeArguments : List Surface.Ty)
    (sourceMissing : sourceProgram[index]? = none)
    (runtimeMissing : runtimeProgram[index]? = none) :
    Surface.evaluate sourceProgram (fuel + 1) environment
        (.global index typeArguments) = .error .unbound ↔
      GlobalIR.evaluate runtimeProgram store (fuel + 1) (PolyIR.eraseValues environment)
        (.global index) = .error (.core .unbound) := by
  simp [Surface.evaluate, GlobalIR.evaluate, sourceMissing, runtimeMissing]

/-- Integer addition reports the corresponding wrong-shape fault when its
successfully evaluated operands are not both integers. The four child-result
hypotheses expose the evaluator correspondence needed by a compositional
source-to-GlobalIR proof. -/
theorem add_wrong_shape_fault_corresponds_to_globalIR
    (sourceProgram : Surface.Definitions) (runtimeProgram : List GlobalIR.Definition)
    (store : GlobalIR.Store) (fuel : Nat) (environment : List Surface.Value)
    (left right : Surface.Expr) (leftValue rightValue : Surface.Value)
    (sourceLeft : Surface.evaluate sourceProgram fuel environment left = .ok leftValue)
    (sourceRight : Surface.evaluate sourceProgram fuel environment right = .ok rightValue)
    (runtimeLeft : GlobalIR.evaluate runtimeProgram store fuel (PolyIR.eraseValues environment)
      (PolyIR.erase left) = .ok (PolyIR.eraseValue leftValue))
    (runtimeRight : GlobalIR.evaluate runtimeProgram store fuel (PolyIR.eraseValues environment)
      (PolyIR.erase right) = .ok (PolyIR.eraseValue rightValue))
    (notBothIntegers : ¬ ∃ leftInt rightInt,
      leftValue = .int leftInt ∧ rightValue = .int rightInt) :
    Surface.evaluate sourceProgram (fuel + 1) environment (.add left right) =
        .error .wrongShape ↔
      GlobalIR.evaluate runtimeProgram store (fuel + 1) (PolyIR.eraseValues environment)
        (.add (PolyIR.erase left) (PolyIR.erase right)) = .error (.core .wrongShape) := by
  have sourceFault : Surface.evaluate sourceProgram (fuel + 1) environment
      (.add left right) = .error .wrongShape := by
    change (do
      let leftResult ← Surface.evaluate sourceProgram fuel environment left
      let rightResult ← Surface.evaluate sourceProgram fuel environment right
      match leftResult, rightResult with
      | .int x, .int y => pure (Surface.Value.int (x + y))
      | _, _ => .error .wrongShape) = .error .wrongShape
    rw [sourceLeft, sourceRight]
    cases leftValue <;> cases rightValue <;> first
      | rfl
      | exact False.elim (notBothIntegers ⟨_, _, rfl, rfl⟩)
  have runtimeFault : GlobalIR.evaluate runtimeProgram store (fuel + 1)
      (PolyIR.eraseValues environment) (.add (PolyIR.erase left) (PolyIR.erase right)) =
        .error (.core .wrongShape) := by
    change Except.bind
      (GlobalIR.evaluate runtimeProgram store fuel (PolyIR.eraseValues environment)
        (PolyIR.erase left)) (fun leftResult =>
      Except.bind
        (GlobalIR.evaluate runtimeProgram store fuel (PolyIR.eraseValues environment)
          (PolyIR.erase right)) (fun rightResult =>
      match leftResult, rightResult with
      | .int x, .int y => Except.ok (PolyIR.Value.int (x + y))
      | _, _ => Except.error (.core .wrongShape))) = .error (.core .wrongShape)
    rw [runtimeLeft, runtimeRight]
    cases leftValue <;> cases rightValue <;>
      simp_all [PolyIR.eraseValue, Except.bind, Except.pure]
  exact ⟨fun _ => runtimeFault, fun _ => sourceFault⟩

/-- Integer subtraction reports the corresponding wrong-shape fault when its
successfully evaluated operands are not both integers. -/
theorem sub_wrong_shape_fault_corresponds_to_globalIR
    (sourceProgram : Surface.Definitions) (runtimeProgram : List GlobalIR.Definition)
    (store : GlobalIR.Store) (fuel : Nat) (environment : List Surface.Value)
    (left right : Surface.Expr) (leftValue rightValue : Surface.Value)
    (sourceLeft : Surface.evaluate sourceProgram fuel environment left = .ok leftValue)
    (sourceRight : Surface.evaluate sourceProgram fuel environment right = .ok rightValue)
    (runtimeLeft : GlobalIR.evaluate runtimeProgram store fuel (PolyIR.eraseValues environment)
      (PolyIR.erase left) = .ok (PolyIR.eraseValue leftValue))
    (runtimeRight : GlobalIR.evaluate runtimeProgram store fuel (PolyIR.eraseValues environment)
      (PolyIR.erase right) = .ok (PolyIR.eraseValue rightValue))
    (notBothIntegers : ¬ ∃ leftInt rightInt,
      leftValue = .int leftInt ∧ rightValue = .int rightInt) :
    Surface.evaluate sourceProgram (fuel + 1) environment (.sub left right) =
        .error .wrongShape ↔
      GlobalIR.evaluate runtimeProgram store (fuel + 1) (PolyIR.eraseValues environment)
        (.sub (PolyIR.erase left) (PolyIR.erase right)) = .error (.core .wrongShape) := by
  have sourceFault : Surface.evaluate sourceProgram (fuel + 1) environment
      (.sub left right) = .error .wrongShape := by
    change (do
      let leftResult ← Surface.evaluate sourceProgram fuel environment left
      let rightResult ← Surface.evaluate sourceProgram fuel environment right
      match leftResult, rightResult with
      | .int x, .int y => pure (Surface.Value.int (x - y))
      | _, _ => .error .wrongShape) = .error .wrongShape
    rw [sourceLeft, sourceRight]
    cases leftValue <;> cases rightValue <;> first
      | rfl
      | exact False.elim (notBothIntegers ⟨_, _, rfl, rfl⟩)
  have runtimeFault : GlobalIR.evaluate runtimeProgram store (fuel + 1)
      (PolyIR.eraseValues environment) (.sub (PolyIR.erase left) (PolyIR.erase right)) =
        .error (.core .wrongShape) := by
    change Except.bind
      (GlobalIR.evaluate runtimeProgram store fuel (PolyIR.eraseValues environment)
        (PolyIR.erase left)) (fun leftResult =>
      Except.bind
        (GlobalIR.evaluate runtimeProgram store fuel (PolyIR.eraseValues environment)
          (PolyIR.erase right)) (fun rightResult =>
      match leftResult, rightResult with
      | .int x, .int y => Except.ok (PolyIR.Value.int (x - y))
      | _, _ => Except.error (.core .wrongShape))) = .error (.core .wrongShape)
    rw [runtimeLeft, runtimeRight]
    cases leftValue <;> cases rightValue <;>
      simp_all [PolyIR.eraseValue, Except.bind, Except.pure]
  exact ⟨fun _ => runtimeFault, fun _ => sourceFault⟩

/-- Integer multiplication reports the corresponding wrong-shape fault when
its successfully evaluated operands are not both integers. -/
theorem mul_wrong_shape_fault_corresponds_to_globalIR
    (sourceProgram : Surface.Definitions) (runtimeProgram : List GlobalIR.Definition)
    (store : GlobalIR.Store) (fuel : Nat) (environment : List Surface.Value)
    (left right : Surface.Expr) (leftValue rightValue : Surface.Value)
    (sourceLeft : Surface.evaluate sourceProgram fuel environment left = .ok leftValue)
    (sourceRight : Surface.evaluate sourceProgram fuel environment right = .ok rightValue)
    (runtimeLeft : GlobalIR.evaluate runtimeProgram store fuel (PolyIR.eraseValues environment)
      (PolyIR.erase left) = .ok (PolyIR.eraseValue leftValue))
    (runtimeRight : GlobalIR.evaluate runtimeProgram store fuel (PolyIR.eraseValues environment)
      (PolyIR.erase right) = .ok (PolyIR.eraseValue rightValue))
    (notBothIntegers : ¬ ∃ leftInt rightInt,
      leftValue = .int leftInt ∧ rightValue = .int rightInt) :
    Surface.evaluate sourceProgram (fuel + 1) environment (.mul left right) =
        .error .wrongShape ↔
      GlobalIR.evaluate runtimeProgram store (fuel + 1) (PolyIR.eraseValues environment)
        (.mul (PolyIR.erase left) (PolyIR.erase right)) = .error (.core .wrongShape) := by
  have sourceFault : Surface.evaluate sourceProgram (fuel + 1) environment
      (.mul left right) = .error .wrongShape := by
    change (do
      let leftResult ← Surface.evaluate sourceProgram fuel environment left
      let rightResult ← Surface.evaluate sourceProgram fuel environment right
      match leftResult, rightResult with
      | .int x, .int y => pure (Surface.Value.int (x * y))
      | _, _ => .error .wrongShape) = .error .wrongShape
    rw [sourceLeft, sourceRight]
    cases leftValue <;> cases rightValue <;> first
      | rfl
      | exact False.elim (notBothIntegers ⟨_, _, rfl, rfl⟩)
  have runtimeFault : GlobalIR.evaluate runtimeProgram store (fuel + 1)
      (PolyIR.eraseValues environment) (.mul (PolyIR.erase left) (PolyIR.erase right)) =
        .error (.core .wrongShape) := by
    change Except.bind
      (GlobalIR.evaluate runtimeProgram store fuel (PolyIR.eraseValues environment)
        (PolyIR.erase left)) (fun leftResult =>
      Except.bind
        (GlobalIR.evaluate runtimeProgram store fuel (PolyIR.eraseValues environment)
          (PolyIR.erase right)) (fun rightResult =>
      match leftResult, rightResult with
      | .int x, .int y => Except.ok (PolyIR.Value.int (x * y))
      | _, _ => Except.error (.core .wrongShape))) = .error (.core .wrongShape)
    rw [runtimeLeft, runtimeRight]
    cases leftValue <;> cases rightValue <;>
      simp_all [PolyIR.eraseValue, Except.bind, Except.pure]
  exact ⟨fun _ => runtimeFault, fun _ => sourceFault⟩

/-- Integer comparison reports the corresponding wrong-shape fault when its
successfully evaluated operands are not both integers. -/
theorem le_wrong_shape_fault_corresponds_to_globalIR
    (sourceProgram : Surface.Definitions) (runtimeProgram : List GlobalIR.Definition)
    (store : GlobalIR.Store) (fuel : Nat) (environment : List Surface.Value)
    (left right : Surface.Expr) (leftValue rightValue : Surface.Value)
    (sourceLeft : Surface.evaluate sourceProgram fuel environment left = .ok leftValue)
    (sourceRight : Surface.evaluate sourceProgram fuel environment right = .ok rightValue)
    (runtimeLeft : GlobalIR.evaluate runtimeProgram store fuel (PolyIR.eraseValues environment)
      (PolyIR.erase left) = .ok (PolyIR.eraseValue leftValue))
    (runtimeRight : GlobalIR.evaluate runtimeProgram store fuel (PolyIR.eraseValues environment)
      (PolyIR.erase right) = .ok (PolyIR.eraseValue rightValue))
    (notBothIntegers : ¬ ∃ leftInt rightInt,
      leftValue = .int leftInt ∧ rightValue = .int rightInt) :
    Surface.evaluate sourceProgram (fuel + 1) environment (.le left right) =
        .error .wrongShape ↔
      GlobalIR.evaluate runtimeProgram store (fuel + 1) (PolyIR.eraseValues environment)
        (.le (PolyIR.erase left) (PolyIR.erase right)) = .error (.core .wrongShape) := by
  have sourceFault : Surface.evaluate sourceProgram (fuel + 1) environment
      (.le left right) = .error .wrongShape := by
    change (do
      let leftResult ← Surface.evaluate sourceProgram fuel environment left
      let rightResult ← Surface.evaluate sourceProgram fuel environment right
      match leftResult, rightResult with
      | .int x, .int y => pure (Surface.Value.bool (x ≤ y))
      | _, _ => .error .wrongShape) = .error .wrongShape
    rw [sourceLeft, sourceRight]
    cases leftValue <;> cases rightValue <;> first
      | rfl
      | exact False.elim (notBothIntegers ⟨_, _, rfl, rfl⟩)
  have runtimeFault : GlobalIR.evaluate runtimeProgram store (fuel + 1)
      (PolyIR.eraseValues environment) (.le (PolyIR.erase left) (PolyIR.erase right)) =
        .error (.core .wrongShape) := by
    change Except.bind
      (GlobalIR.evaluate runtimeProgram store fuel (PolyIR.eraseValues environment)
        (PolyIR.erase left)) (fun leftResult =>
      Except.bind
        (GlobalIR.evaluate runtimeProgram store fuel (PolyIR.eraseValues environment)
          (PolyIR.erase right)) (fun rightResult =>
      match leftResult, rightResult with
      | .int x, .int y => Except.ok (PolyIR.Value.bool (x ≤ y))
      | _, _ => Except.error (.core .wrongShape))) = .error (.core .wrongShape)
    rw [runtimeLeft, runtimeRight]
    cases leftValue <;> cases rightValue <;>
      simp_all [PolyIR.eraseValue, Except.bind, Except.pure]
  exact ⟨fun _ => runtimeFault, fun _ => sourceFault⟩

/-- Integer equality reports the corresponding wrong-shape fault when its
successfully evaluated operands are not both integers. -/
theorem intEq_wrong_shape_fault_corresponds_to_globalIR
    (sourceProgram : Surface.Definitions) (runtimeProgram : List GlobalIR.Definition)
    (store : GlobalIR.Store) (fuel : Nat) (environment : List Surface.Value)
    (left right : Surface.Expr) (leftValue rightValue : Surface.Value)
    (sourceLeft : Surface.evaluate sourceProgram fuel environment left = .ok leftValue)
    (sourceRight : Surface.evaluate sourceProgram fuel environment right = .ok rightValue)
    (runtimeLeft : GlobalIR.evaluate runtimeProgram store fuel (PolyIR.eraseValues environment)
      (PolyIR.erase left) = .ok (PolyIR.eraseValue leftValue))
    (runtimeRight : GlobalIR.evaluate runtimeProgram store fuel (PolyIR.eraseValues environment)
      (PolyIR.erase right) = .ok (PolyIR.eraseValue rightValue))
    (notBothIntegers : ¬ ∃ leftInt rightInt,
      leftValue = .int leftInt ∧ rightValue = .int rightInt) :
    Surface.evaluate sourceProgram (fuel + 1) environment (.intEq left right) =
        .error .wrongShape ↔
      GlobalIR.evaluate runtimeProgram store (fuel + 1) (PolyIR.eraseValues environment)
        (.intEq (PolyIR.erase left) (PolyIR.erase right)) = .error (.core .wrongShape) := by
  have sourceFault : Surface.evaluate sourceProgram (fuel + 1) environment
      (.intEq left right) = .error .wrongShape := by
    change (do
      let leftResult ← Surface.evaluate sourceProgram fuel environment left
      let rightResult ← Surface.evaluate sourceProgram fuel environment right
      match leftResult, rightResult with
      | .int x, .int y => pure (Surface.Value.bool (x == y))
      | _, _ => .error .wrongShape) = .error .wrongShape
    rw [sourceLeft, sourceRight]
    cases leftValue <;> cases rightValue <;> first
      | rfl
      | exact False.elim (notBothIntegers ⟨_, _, rfl, rfl⟩)
  have runtimeFault : GlobalIR.evaluate runtimeProgram store (fuel + 1)
      (PolyIR.eraseValues environment) (.intEq (PolyIR.erase left) (PolyIR.erase right)) =
        .error (.core .wrongShape) := by
    change Except.bind
      (GlobalIR.evaluate runtimeProgram store fuel (PolyIR.eraseValues environment)
        (PolyIR.erase left)) (fun leftResult =>
      Except.bind
        (GlobalIR.evaluate runtimeProgram store fuel (PolyIR.eraseValues environment)
          (PolyIR.erase right)) (fun rightResult =>
      match leftResult, rightResult with
      | .int x, .int y => Except.ok (PolyIR.Value.bool (x == y))
      | _, _ => Except.error (.core .wrongShape))) = .error (.core .wrongShape)
    rw [runtimeLeft, runtimeRight]
    cases leftValue <;> cases rightValue <;>
      simp_all [PolyIR.eraseValue, Except.bind, Except.pure]
  exact ⟨fun _ => runtimeFault, fun _ => sourceFault⟩

/-- Float arithmetic reports the same wrong-shape fault in Surface and
GlobalIR when child evaluations correspond and the source operands are not
both Floats. -/
theorem floatBin_wrong_shape_fault_corresponds_to_globalIR
    (sourceProgram : Surface.Definitions) (runtimeProgram : List GlobalIR.Definition)
    (store : GlobalIR.Store) (fuel : Nat) (environment : List Surface.Value)
    (operation : Surface.FloatBinOp) (left right : Surface.Expr)
    (leftValue rightValue : Surface.Value)
    (sourceLeft : Surface.evaluate sourceProgram fuel environment left = .ok leftValue)
    (sourceRight : Surface.evaluate sourceProgram fuel environment right = .ok rightValue)
    (runtimeLeft : GlobalIR.evaluate runtimeProgram store fuel (PolyIR.eraseValues environment)
      (PolyIR.erase left) = .ok (PolyIR.eraseValue leftValue))
    (runtimeRight : GlobalIR.evaluate runtimeProgram store fuel (PolyIR.eraseValues environment)
      (PolyIR.erase right) = .ok (PolyIR.eraseValue rightValue))
    (notBothFloats : ¬ ∃ x y, leftValue = .float x ∧ rightValue = .float y) :
    Surface.evaluate sourceProgram (fuel + 1) environment
        (.floatBin operation left right) = .error .wrongShape ↔
      GlobalIR.evaluate runtimeProgram store (fuel + 1) (PolyIR.eraseValues environment)
        (.floatBin operation (PolyIR.erase left) (PolyIR.erase right)) =
          .error (.core .wrongShape) := by
  have sourceFault : Surface.evaluate sourceProgram (fuel + 1) environment
      (.floatBin operation left right) = .error .wrongShape := by
    change (do
      let leftResult ← Surface.evaluate sourceProgram fuel environment left
      let rightResult ← Surface.evaluate sourceProgram fuel environment right
      match leftResult, rightResult with
      | .float x, .float y => pure (Surface.Value.float (GlobalIR.floatBinValue operation x y))
      | _, _ => .error .wrongShape) = .error .wrongShape
    rw [sourceLeft, sourceRight]
    cases leftValue <;> cases rightValue <;> first
      | exact False.elim (notBothFloats ⟨_, _, rfl, rfl⟩)
      | rfl
  have runtimeFault : GlobalIR.evaluate runtimeProgram store (fuel + 1)
      (PolyIR.eraseValues environment)
      (.floatBin operation (PolyIR.erase left) (PolyIR.erase right)) =
        .error (.core .wrongShape) := by
    change Except.bind
      (GlobalIR.evaluate runtimeProgram store fuel (PolyIR.eraseValues environment)
        (PolyIR.erase left)) (fun leftResult =>
      Except.bind
        (GlobalIR.evaluate runtimeProgram store fuel (PolyIR.eraseValues environment)
          (PolyIR.erase right)) (fun rightResult =>
        match leftResult, rightResult with
        | .float x, .float y =>
            Except.ok (PolyIR.Value.float (GlobalIR.floatBinValue operation x y))
        | _, _ => Except.error (.core .wrongShape))) = .error (.core .wrongShape)
    rw [runtimeLeft, runtimeRight]
    cases leftValue <;> cases rightValue <;>
      simp_all [PolyIR.eraseValue, Except.bind, Except.pure]
  exact ⟨fun _ => runtimeFault, fun _ => sourceFault⟩

/-- A closure application with a mismatched argument count reports the
same source/runtime arity fault when function and argument evaluation results
correspond under value erasure. -/
theorem closure_wrong_arity_fault_corresponds_to_globalIR
    (sourceProgram : Surface.Definitions) (runtimeProgram : List GlobalIR.Definition)
    (store : GlobalIR.Store) (fuel : Nat) (environment : List Surface.Value)
    (arguments : List Surface.Expr)
    (parameters : List Surface.Ty) (resultType : Surface.Ty) (body : Surface.Expr)
    (captured values : List Surface.Value)
    (sourceFunction : Surface.evaluate sourceProgram fuel environment function =
      .ok (.closure parameters resultType body captured))
    (sourceArguments : Surface.evaluateArgs sourceProgram fuel environment arguments =
      .ok values)
    (runtimeFunction : GlobalIR.evaluate runtimeProgram store fuel
      (PolyIR.eraseValues environment) (PolyIR.erase function) =
      .ok (.closure parameters.length (PolyIR.erase body) (PolyIR.eraseValues captured)))
    (runtimeArguments : GlobalIR.evaluateArgs runtimeProgram store fuel
      (PolyIR.eraseValues environment) (PolyIR.eraseList arguments) =
      .ok (PolyIR.eraseValues values))
    (arityMismatch : values.length ≠ parameters.length) :
    Surface.evaluate sourceProgram (fuel + 1) environment (.app function arguments) =
        .error .wrongArity ↔
      GlobalIR.evaluate runtimeProgram store (fuel + 1) (PolyIR.eraseValues environment)
        (.app (PolyIR.erase function) (PolyIR.eraseList arguments)) =
          .error (.core .wrongArity) := by
  have sourceFault : Surface.evaluate sourceProgram (fuel + 1) environment
      (.app function arguments) = .error .wrongArity := by
    change (do
      let functionValue ← Surface.evaluate sourceProgram fuel environment function
      let argumentValues ← Surface.evaluateArgs sourceProgram fuel environment arguments
      match functionValue with
      | .closure closureParameters _ closureBody capturedEnvironment =>
        if argumentValues.length = closureParameters.length then
          Surface.evaluate sourceProgram fuel (argumentValues ++ capturedEnvironment) closureBody
        else .error .wrongArity
      | .global index _ =>
        match sourceProgram[index]? with
        | none => .error .unbound
        | some definition =>
          if argumentValues.length = definition.1.parameters.length then
            Surface.evaluate sourceProgram fuel argumentValues definition.2
          else .error .wrongArity
      | _ => .error .wrongShape) = .error .wrongArity
    rw [sourceFunction, sourceArguments]
    simp [Except.bind, Except.pure, Pure.pure, bind, pure, arityMismatch]
  have runtimeFault : GlobalIR.evaluate runtimeProgram store (fuel + 1)
      (PolyIR.eraseValues environment)
      (.app (PolyIR.erase function) (PolyIR.eraseList arguments)) =
        .error (.core .wrongArity) := by
    change (do
      let functionValue ← GlobalIR.evaluate runtimeProgram store fuel
        (PolyIR.eraseValues environment) (PolyIR.erase function)
      let argumentValues ← GlobalIR.evaluateArgs runtimeProgram store fuel
        (PolyIR.eraseValues environment) (PolyIR.eraseList arguments)
      match functionValue with
      | .closure closureArity closureBody capturedEnvironment =>
        if argumentValues.length = closureArity then
          GlobalIR.evaluate runtimeProgram store fuel (argumentValues ++ capturedEnvironment)
            closureBody
        else .error (.core .wrongArity)
      | .global index =>
        match runtimeProgram[index]? with
        | none => .error (.core .unbound)
        | some (.function definition) =>
          if argumentValues.length = definition.arity then
            GlobalIR.evaluate runtimeProgram store fuel argumentValues definition.body
          else .error (.core .wrongArity)
        | some (.getter slot) =>
          if argumentValues.isEmpty then GlobalIR.readGlobal store slot
          else .error (.core .wrongArity)
      | _ => .error (.core .wrongShape)) = .error (.core .wrongArity)
    rw [runtimeFunction, runtimeArguments]
    simp [Except.bind, Except.pure, Pure.pure, bind, pure, arityMismatch]
  exact ⟨fun _ => runtimeFault, fun _ => sourceFault⟩

/-- Calling the same source and runtime global function with too few or too
many successfully evaluated arguments reports the same arity fault. The
declaration lookup and arity agreement expose the layout correspondence used
by mixed GlobalIR programs. -/
theorem global_function_wrong_arity_fault_corresponds_to_globalIR
    (sourceProgram : Surface.Definitions) (runtimeProgram : List GlobalIR.Definition)
    (store : GlobalIR.Store) (fuel index : Nat) (environment : List Surface.Value)
    (arguments : List Surface.Expr)
    (typeArguments : List Surface.Ty) (signature : Surface.Signature)
    (sourceBody : Surface.Expr) (runtimeDefinition : PolyIR.RuntimeDefinition)
    (values : List Surface.Value)
    (sourceFunctionEval : Surface.evaluate sourceProgram fuel environment
      (.global index typeArguments) = .ok (.global index typeArguments))
    (runtimeFunctionEval : GlobalIR.evaluate runtimeProgram store fuel
      (PolyIR.eraseValues environment) (.global index) = .ok (.global index))
    (sourceLookup : sourceProgram[index]? = some (signature, sourceBody))
    (runtimeLookup : runtimeProgram[index]? = some (.function runtimeDefinition))
    (arityAgreement : runtimeDefinition.arity = signature.parameters.length)
    (sourceArguments : Surface.evaluateArgs sourceProgram fuel environment arguments = .ok values)
    (runtimeArguments : GlobalIR.evaluateArgs runtimeProgram store fuel
      (PolyIR.eraseValues environment) (PolyIR.eraseList arguments) =
        .ok (PolyIR.eraseValues values))
    (arityMismatch : values.length ≠ signature.parameters.length) :
    Surface.evaluate sourceProgram (fuel + 1) environment
        (.app (.global index typeArguments) arguments) =
        .error .wrongArity ↔
      GlobalIR.evaluate runtimeProgram store (fuel + 1) (PolyIR.eraseValues environment)
        (.app (.global index) (PolyIR.eraseList arguments)) =
          .error (.core .wrongArity) := by
  have runtimeArityMismatch : values.length ≠ runtimeDefinition.arity := by
    rw [arityAgreement]
    exact arityMismatch
  have sourceFault : Surface.evaluate sourceProgram (fuel + 1) environment
      (.app (.global index typeArguments) arguments) = .error .wrongArity := by
    change (do
      let functionValue ← Surface.evaluate sourceProgram fuel environment
        (.global index typeArguments)
      let argumentValues ← Surface.evaluateArgs sourceProgram fuel environment arguments
      match functionValue with
      | .closure parameters _ body captured =>
          if argumentValues.length = parameters.length then
            Surface.evaluate sourceProgram fuel (argumentValues ++ captured) body
          else .error .wrongArity
      | .global found _ =>
          match sourceProgram[found]? with
          | none => .error .unbound
          | some definition =>
              if argumentValues.length = definition.1.parameters.length then
                Surface.evaluate sourceProgram fuel argumentValues definition.2
              else .error .wrongArity
      | _ => .error .wrongShape) = .error .wrongArity
    rw [sourceFunctionEval, sourceArguments]
    simp [Except.bind, Except.pure, Pure.pure, bind, pure, sourceLookup, arityMismatch]
  have runtimeFault : GlobalIR.evaluate runtimeProgram store (fuel + 1)
      (PolyIR.eraseValues environment)
      (.app (.global index) (PolyIR.eraseList arguments)) =
        .error (.core .wrongArity) := by
    change (do
      let functionValue ← GlobalIR.evaluate runtimeProgram store fuel
        (PolyIR.eraseValues environment) (.global index)
      let argumentValues ← GlobalIR.evaluateArgs runtimeProgram store fuel
        (PolyIR.eraseValues environment) (PolyIR.eraseList arguments)
      match functionValue with
      | .closure arity body captured =>
          if argumentValues.length = arity then
            GlobalIR.evaluate runtimeProgram store fuel (argumentValues ++ captured) body
          else .error (.core .wrongArity)
      | .global found =>
          match runtimeProgram[found]? with
          | none => .error (.core .unbound)
          | some (.function definition) =>
              if argumentValues.length = definition.arity then
                GlobalIR.evaluate runtimeProgram store fuel argumentValues definition.body
              else .error (.core .wrongArity)
          | some (.getter slot) =>
              if argumentValues.isEmpty then GlobalIR.readGlobal store slot
              else .error (.core .wrongArity)
      | _ => .error (.core .wrongShape)) = .error (.core .wrongArity)
    rw [runtimeFunctionEval, runtimeArguments]
    simp only [Except.bind, Except.pure, Pure.pure, bind, pure, runtimeLookup]
    by_cases arityOk : values.length = runtimeDefinition.arity
    · exact False.elim (runtimeArityMismatch arityOk)
    · simp [arityOk]
  exact ⟨fun _ => runtimeFault, fun _ => sourceFault⟩

/-- Application propagates a corresponding fault from function evaluation
before attempting to evaluate any argument. -/
theorem application_function_fault_propagates_to_globalIR
    (sourceProgram : Surface.Definitions) (runtimeProgram : List GlobalIR.Definition)
    (store : GlobalIR.Store) (fuel : Nat) (environment : List Surface.Value)
    (function : Surface.Expr) (arguments : List Surface.Expr) (fault : PolyIR.Fault)
    (sourceFunction : Surface.evaluate sourceProgram fuel environment function = .error fault)
    (runtimeFunction : GlobalIR.evaluate runtimeProgram store fuel
      (PolyIR.eraseValues environment) (PolyIR.erase function) = .error (.core fault)) :
    Surface.evaluate sourceProgram (fuel + 1) environment (.app function arguments) =
        .error fault ↔
      GlobalIR.evaluate runtimeProgram store (fuel + 1) (PolyIR.eraseValues environment)
        (.app (PolyIR.erase function) (PolyIR.eraseList arguments)) = .error (.core fault) := by
  have sourceFault : Surface.evaluate sourceProgram (fuel + 1) environment
      (.app function arguments) = .error fault := by
    change (do
      let functionValue ← Surface.evaluate sourceProgram fuel environment function
      let argumentValues ← Surface.evaluateArgs sourceProgram fuel environment arguments
      match functionValue with
      | .closure parameters _ body captured =>
          if argumentValues.length = parameters.length then
            Surface.evaluate sourceProgram fuel (argumentValues ++ captured) body
          else .error .wrongArity
      | .global index _ =>
          match sourceProgram[index]? with
          | none => .error .unbound
          | some definition =>
              if argumentValues.length = definition.1.parameters.length then
                Surface.evaluate sourceProgram fuel argumentValues definition.2
              else .error .wrongArity
      | _ => .error .wrongShape) = .error fault
    rw [sourceFunction]
    simp [Except.bind, Except.pure, Pure.pure, bind, pure]
  have runtimeFault : GlobalIR.evaluate runtimeProgram store (fuel + 1)
      (PolyIR.eraseValues environment)
      (.app (PolyIR.erase function) (PolyIR.eraseList arguments)) = .error (.core fault) := by
    change (do
      let functionValue ← GlobalIR.evaluate runtimeProgram store fuel
        (PolyIR.eraseValues environment) (PolyIR.erase function)
      let argumentValues ← GlobalIR.evaluateArgs runtimeProgram store fuel
        (PolyIR.eraseValues environment) (PolyIR.eraseList arguments)
      match functionValue with
      | .closure arity body captured =>
          if argumentValues.length = arity then
            GlobalIR.evaluate runtimeProgram store fuel (argumentValues ++ captured) body
          else .error (.core .wrongArity)
      | .global index =>
          match runtimeProgram[index]? with
          | none => .error (.core .unbound)
          | some (.function definition) =>
              if argumentValues.length = definition.arity then
                GlobalIR.evaluate runtimeProgram store fuel argumentValues definition.body
              else .error (.core .wrongArity)
          | some (.getter slot) =>
              if argumentValues.isEmpty then GlobalIR.readGlobal store slot
              else .error (.core .wrongArity)
      | _ => .error (.core .wrongShape)) = .error (.core fault)
    rw [runtimeFunction]
    simp [Except.bind, Except.pure, Pure.pure, bind, pure]
  exact ⟨fun _ => runtimeFault, fun _ => sourceFault⟩

/-- Once function evaluation succeeds, application propagates a corresponding
fault from its left-to-right argument evaluation on both evaluators. -/
theorem application_arguments_fault_propagates_to_globalIR
    (sourceProgram : Surface.Definitions) (runtimeProgram : List GlobalIR.Definition)
    (store : GlobalIR.Store) (fuel : Nat) (environment : List Surface.Value)
    (function : Surface.Expr) (arguments : List Surface.Expr)
    (sourceValue : Surface.Value) (runtimeValue : PolyIR.Value) (fault : PolyIR.Fault)
    (sourceFunction : Surface.evaluate sourceProgram fuel environment function = .ok sourceValue)
    (runtimeFunction : GlobalIR.evaluate runtimeProgram store fuel
      (PolyIR.eraseValues environment) (PolyIR.erase function) = .ok runtimeValue)
    (sourceArguments : Surface.evaluateArgs sourceProgram fuel environment arguments =
      .error fault)
    (runtimeArguments : GlobalIR.evaluateArgs runtimeProgram store fuel
      (PolyIR.eraseValues environment) (PolyIR.eraseList arguments) = .error (.core fault)) :
    Surface.evaluate sourceProgram (fuel + 1) environment (.app function arguments) =
        .error fault ↔
      GlobalIR.evaluate runtimeProgram store (fuel + 1) (PolyIR.eraseValues environment)
        (.app (PolyIR.erase function) (PolyIR.eraseList arguments)) = .error (.core fault) := by
  have sourceFault : Surface.evaluate sourceProgram (fuel + 1) environment
      (.app function arguments) = .error fault := by
    change (do
      let functionValue ← Surface.evaluate sourceProgram fuel environment function
      let argumentValues ← Surface.evaluateArgs sourceProgram fuel environment arguments
      match functionValue with
      | .closure parameters _ body captured =>
          if argumentValues.length = parameters.length then
            Surface.evaluate sourceProgram fuel (argumentValues ++ captured) body
          else .error .wrongArity
      | .global index _ =>
          match sourceProgram[index]? with
          | none => .error .unbound
          | some definition =>
              if argumentValues.length = definition.1.parameters.length then
                Surface.evaluate sourceProgram fuel argumentValues definition.2
              else .error .wrongArity
      | _ => .error .wrongShape) = .error fault
    rw [sourceFunction, sourceArguments]
    simp [Except.bind, Except.pure, Pure.pure, bind, pure]
  have runtimeFault : GlobalIR.evaluate runtimeProgram store (fuel + 1)
      (PolyIR.eraseValues environment)
      (.app (PolyIR.erase function) (PolyIR.eraseList arguments)) = .error (.core fault) := by
    change (do
      let functionValue ← GlobalIR.evaluate runtimeProgram store fuel
        (PolyIR.eraseValues environment) (PolyIR.erase function)
      let argumentValues ← GlobalIR.evaluateArgs runtimeProgram store fuel
        (PolyIR.eraseValues environment) (PolyIR.eraseList arguments)
      match functionValue with
      | .closure arity body captured =>
          if argumentValues.length = arity then
            GlobalIR.evaluate runtimeProgram store fuel (argumentValues ++ captured) body
          else .error (.core .wrongArity)
      | .global index =>
          match runtimeProgram[index]? with
          | none => .error (.core .unbound)
          | some (.function definition) =>
              if argumentValues.length = definition.arity then
                GlobalIR.evaluate runtimeProgram store fuel argumentValues definition.body
              else .error (.core .wrongArity)
          | some (.getter slot) =>
              if argumentValues.isEmpty then GlobalIR.readGlobal store slot
              else .error (.core .wrongArity)
      | _ => .error (.core .wrongShape)) = .error (.core fault)
    rw [runtimeFunction, runtimeArguments]
    simp [Except.bind, Except.pure, Pure.pure, bind, pure]
  exact ⟨fun _ => runtimeFault, fun _ => sourceFault⟩

end NLisp
