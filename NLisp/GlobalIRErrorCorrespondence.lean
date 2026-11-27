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

/-- Parallel `letMany` evaluation commutes for any initializer count. A fault
in the left-to-right initializer walk propagates unchanged; after successful
initialization the body runs in the same extended environment on both IRs. -/
theorem functionTable_globalIR_letMany_commutes_of_pointwise
    (definitions : List PolyIR.RuntimeDefinition) (store : GlobalIR.Store)
    (initializers : List PolyIR.Term) (body : PolyIR.Term) (fuel : Nat)
    (environment : List PolyIR.Value)
    (initializersCommute : ∀ evaluationFuel term, term ∈ initializers →
      GlobalIR.evaluate (definitions.map GlobalIR.Definition.function) store evaluationFuel
          environment term =
        wrapCoreFault (PolyIR.evaluate definitions evaluationFuel environment term))
    (bodyCommutes : ∀ evaluationFuel localEnvironment,
      GlobalIR.evaluate (definitions.map GlobalIR.Definition.function) store evaluationFuel
          localEnvironment body =
        wrapCoreFault (PolyIR.evaluate definitions evaluationFuel localEnvironment body)) :
    GlobalIR.evaluate (definitions.map GlobalIR.Definition.function) store fuel environment
        (.letMany initializers body) =
      wrapCoreFault (PolyIR.evaluate definitions fuel environment (.letMany initializers body)) := by
  cases fuel with
  | zero => simp [GlobalIR.evaluate, PolyIR.evaluate, wrapCoreFault]
  | succ fuel =>
      have initializersResult := functionTable_globalIR_arguments_commutes_of_pointwise
        definitions store initializers fuel environment (by
          intro evaluationFuel term member
          exact initializersCommute evaluationFuel term member)
      simp only [GlobalIR.evaluate, PolyIR.evaluate]
      rw [initializersResult]
      cases evaluated : PolyIR.evaluateArgs definitions fuel environment initializers with
      | error fault => rfl
      | ok values => exact bodyCommutes fuel (values ++ environment)

/-- PolyIR-side store initialization, used to compare the same left-to-right
initializer protocol with a function-only GlobalIR table. The store is shared
by type so the correspondence can expose each committed value. -/
def initializeValuesCore (definitions : List PolyIR.RuntimeDefinition) :
    Nat → GlobalIR.Store → Nat → List PolyIR.Term → Except GlobalIR.Fault GlobalIR.Store
  | 0, _, _, _ => .error (.core .outOfFuel)
  | _ + 1, store, _, [] => .ok store
  | fuel + 1, store, slot, head :: tail => do
      let value ← wrapCoreFault (PolyIR.evaluate definitions fuel [] head)
      initializeValuesCore definitions fuel (store.set slot (some value)) (slot + 1) tail

/-- Initializer evaluation commutes for an arbitrary list when each expression
commutes at the store state and decreasing fuel where it is actually run.
This includes faults and the store writes performed by successful prefixes. -/
theorem functionTable_globalIR_initializeValues_commutes_of_pointwise
    (definitions : List PolyIR.RuntimeDefinition) (store : GlobalIR.Store)
    (slot fuel : Nat) (initializers : List PolyIR.Term)
    (pointwise : ∀ currentStore evaluationFuel term, term ∈ initializers →
      GlobalIR.evaluate (definitions.map GlobalIR.Definition.function) currentStore
          evaluationFuel [] term =
        wrapCoreFault (PolyIR.evaluate definitions evaluationFuel [] term)) :
    GlobalIR.initializeValues (definitions.map GlobalIR.Definition.function)
        fuel store slot initializers =
      initializeValuesCore definitions fuel store slot initializers := by
  induction fuel generalizing store slot initializers with
  | zero => simp [GlobalIR.initializeValues, initializeValuesCore]
  | succ fuel ih =>
      cases initializers with
      | nil => simp [GlobalIR.initializeValues, initializeValuesCore, pure, Except.pure]
      | cons head tail =>
          simp only [GlobalIR.initializeValues, initializeValuesCore]
          rw [pointwise store fuel head (by simp)]
          cases evaluated : PolyIR.evaluate definitions fuel [] head with
          | error fault => rfl
          | ok value =>
              exact ih (store.set slot (some value)) (slot + 1) tail (by
                intro currentStore evaluationFuel term member
                exact pointwise currentStore evaluationFuel term (by simp [member]))

/-- A fault produced by the PolyIR-side model of a top-level initializer list
is the observable result of running the corresponding function-only GlobalIR
program. This carries initializer faults through the program entry boundary. -/
theorem functionTable_globalIR_run_reports_initializer_fault
    (definitions : List PolyIR.RuntimeDefinition) (initializers : List PolyIR.Term)
    (entry fuel : Nat) (fault : GlobalIR.Fault)
    (pointwise : ∀ currentStore evaluationFuel term, term ∈ initializers →
      GlobalIR.evaluate (definitions.map GlobalIR.Definition.function) currentStore
          evaluationFuel [] term =
        wrapCoreFault (PolyIR.evaluate definitions evaluationFuel [] term))
    (initializerFault : initializeValuesCore definitions fuel
      (List.replicate initializers.length none) 0 initializers = .error fault) :
    GlobalIR.run ⟨definitions.map GlobalIR.Definition.function, initializers, entry⟩ fuel =
      .error fault := by
  apply GlobalIR.run_reports_initializer_fault
  rw [functionTable_globalIR_initializeValues_commutes_of_pointwise
    definitions (List.replicate initializers.length none) 0 fuel initializers pointwise]
  exact initializerFault

/-- A PolyIR initializer fault after a successful PolyIR prefix is preserved
through the function-table GlobalIR simulation and the observable program
entry. -/
theorem functionTable_globalIR_run_reports_initializer_fault_after_prefix
    (definitions : List PolyIR.RuntimeDefinition) (initializersBefore : List PolyIR.Term)
    (head : PolyIR.Term) (tail : List PolyIR.Term) (entry fuel : Nat)
    (after : GlobalIR.Store) (coreFault : PolyIR.Fault)
    (pointwise : ∀ currentStore evaluationFuel term,
      GlobalIR.evaluate (definitions.map GlobalIR.Definition.function) currentStore
          evaluationFuel [] term =
        wrapCoreFault (PolyIR.evaluate definitions evaluationFuel [] term))
    (prefixSuccess : initializeValuesCore definitions
      (fuel + initializersBefore.length + 2)
      (List.replicate (initializersBefore ++ head :: tail).length none) 0
      initializersBefore = .ok after)
    (faultStep : PolyIR.evaluate definitions (fuel + 1) [] head = .error coreFault) :
    GlobalIR.run ⟨definitions.map GlobalIR.Definition.function,
      initializersBefore ++ head :: tail, entry⟩ (fuel + initializersBefore.length + 2) =
      .error (.core coreFault) := by
  have pointwisePrefix : ∀ currentStore evaluationFuel term, term ∈ initializersBefore →
      GlobalIR.evaluate (definitions.map GlobalIR.Definition.function) currentStore
          evaluationFuel [] term =
        wrapCoreFault (PolyIR.evaluate definitions evaluationFuel [] term) := by
    intro currentStore evaluationFuel term member
    exact pointwise currentStore evaluationFuel term
  have globalPrefix : GlobalIR.initializeValues
      (definitions.map GlobalIR.Definition.function)
      (fuel + initializersBefore.length + 2)
      (List.replicate (initializersBefore ++ head :: tail).length none) 0
      initializersBefore = .ok after := by
    rw [functionTable_globalIR_initializeValues_commutes_of_pointwise definitions
      (List.replicate (initializersBefore ++ head :: tail).length none) 0
      (fuel + initializersBefore.length + 2) initializersBefore pointwisePrefix]
    exact prefixSuccess
  have globalFault : GlobalIR.evaluate
      (definitions.map GlobalIR.Definition.function) after (fuel + 1) [] head =
      .error (.core coreFault) := by
    have corresponding := pointwise after (fuel + 1) head
    rw [faultStep] at corresponding
    exact corresponding
  exact GlobalIR.run_reports_initializer_fault_after_prefix
    ⟨definitions.map GlobalIR.Definition.function,
      initializersBefore ++ head :: tail, entry⟩ fuel
    initializersBefore head tail after (.core coreFault) rfl globalPrefix globalFault

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

/-- Some construction commutes from child-evaluation correspondence, including
propagation of a child fault. -/
theorem functionTable_globalIR_some_commutes_of_pointwise
    (definitions : List PolyIR.RuntimeDefinition) (store : GlobalIR.Store)
    (value : PolyIR.Term) (fuel : Nat) (environment : List PolyIR.Value)
    (pointwise : ∀ evaluationFuel term, term ∈ [value] →
      GlobalIR.evaluate (definitions.map GlobalIR.Definition.function) store
          evaluationFuel environment term =
        wrapCoreFault (PolyIR.evaluate definitions evaluationFuel environment term)) :
    GlobalIR.evaluate (definitions.map GlobalIR.Definition.function) store fuel environment
        (.some value) =
      wrapCoreFault (PolyIR.evaluate definitions fuel environment (.some value)) := by
  cases fuel with
  | zero => simp [GlobalIR.evaluate, PolyIR.evaluate, wrapCoreFault]
  | succ fuel =>
      have valueCommutes := pointwise fuel value (by simp)
      simp only [GlobalIR.evaluate, PolyIR.evaluate]
      rw [valueCommutes]
      cases hvalue : PolyIR.evaluate definitions fuel environment value <;> rfl

/-- Cons construction evaluates its head and tail left to right. Pointwise
correspondence of both children gives correspondence for values and faults. -/
theorem functionTable_globalIR_cons_commutes_of_pointwise
    (definitions : List PolyIR.RuntimeDefinition) (store : GlobalIR.Store)
    (head tail : PolyIR.Term) (fuel : Nat) (environment : List PolyIR.Value)
    (pointwise : ∀ evaluationFuel term, term ∈ [head, tail] →
      GlobalIR.evaluate (definitions.map GlobalIR.Definition.function) store
          evaluationFuel environment term =
        wrapCoreFault (PolyIR.evaluate definitions evaluationFuel environment term)) :
    GlobalIR.evaluate (definitions.map GlobalIR.Definition.function) store fuel environment
        (.cons head tail) =
      wrapCoreFault (PolyIR.evaluate definitions fuel environment (.cons head tail)) := by
  cases fuel with
  | zero => simp [GlobalIR.evaluate, PolyIR.evaluate, wrapCoreFault]
  | succ fuel =>
      have headCommutes := pointwise fuel head (by simp)
      have tailCommutes := pointwise fuel tail (by simp)
      simp only [GlobalIR.evaluate, PolyIR.evaluate]
      rw [headCommutes]
      cases hhead : PolyIR.evaluate definitions fuel environment head with
      | error fault => rfl
      | ok headValue =>
          rw [tailCommutes]
          cases htail : PolyIR.evaluate definitions fuel environment tail with
          | error fault => rfl
          | ok tailValue => rfl

/-- List matching commutes when its target and branches commute pointwise.
The cons branch extends both environments with head then tail, matching the
two evaluators' binder order. -/
theorem functionTable_globalIR_matchList_commutes_of_pointwise
    (definitions : List PolyIR.RuntimeDefinition) (store : GlobalIR.Store)
    (target empty full : PolyIR.Term) (fuel : Nat) (environment : List PolyIR.Value)
    (pointwise : ∀ evaluationFuel branchEnvironment term,
      term ∈ [target, empty, full] →
      GlobalIR.evaluate (definitions.map GlobalIR.Definition.function) store
          evaluationFuel branchEnvironment term =
        wrapCoreFault (PolyIR.evaluate definitions evaluationFuel branchEnvironment term)) :
    GlobalIR.evaluate (definitions.map GlobalIR.Definition.function) store fuel environment
        (.matchList target empty full) =
      wrapCoreFault (PolyIR.evaluate definitions fuel environment (.matchList target empty full)) := by
  cases fuel with
  | zero => simp [GlobalIR.evaluate, PolyIR.evaluate, wrapCoreFault]
  | succ fuel =>
      have targetCommutes := pointwise fuel environment target (by simp)
      simp only [GlobalIR.evaluate, PolyIR.evaluate]
      rw [targetCommutes]
      cases targetResult : PolyIR.evaluate definitions fuel environment target with
      | error fault => rfl
      | ok targetValue =>
          cases targetValue with
          | nil => exact pointwise fuel environment empty (by simp)
          | cons head tail => exact pointwise fuel (head :: tail :: environment) full (by simp)
          | bool value => rfl
          | int value => rfl
          | float value => rfl
          | string value => rfl
          | character value => rfl
          | unit => rfl
          | closure arity body captured => rfl
          | none => rfl
          | some value => rfl
          | global index => rfl

/-- Option matching commutes pointwise. The Some branch extends the evaluator
environment with the unwrapped value at index zero. -/
theorem functionTable_globalIR_matchOption_commutes_of_pointwise
    (definitions : List PolyIR.RuntimeDefinition) (store : GlobalIR.Store)
    (target empty full : PolyIR.Term) (fuel : Nat) (environment : List PolyIR.Value)
    (pointwise : ∀ evaluationFuel branchEnvironment term,
      term ∈ [target, empty, full] →
      GlobalIR.evaluate (definitions.map GlobalIR.Definition.function) store
          evaluationFuel branchEnvironment term =
        wrapCoreFault (PolyIR.evaluate definitions evaluationFuel branchEnvironment term)) :
    GlobalIR.evaluate (definitions.map GlobalIR.Definition.function) store fuel environment
        (.matchOption target empty full) =
      wrapCoreFault (PolyIR.evaluate definitions fuel environment (.matchOption target empty full)) := by
  cases fuel with
  | zero => simp [GlobalIR.evaluate, PolyIR.evaluate, wrapCoreFault]
  | succ fuel =>
      have targetCommutes := pointwise fuel environment target (by simp)
      simp only [GlobalIR.evaluate, PolyIR.evaluate]
      rw [targetCommutes]
      cases targetResult : PolyIR.evaluate definitions fuel environment target with
      | error fault => rfl
      | ok targetValue =>
          cases targetValue with
          | none => exact pointwise fuel environment empty (by simp)
          | some value => exact pointwise fuel (value :: environment) full (by simp)
          | bool value => rfl
          | int value => rfl
          | float value => rfl
          | string value => rfl
          | character value => rfl
          | unit => rfl
          | closure arity body captured => rfl
          | nil => rfl
          | cons head tail => rfl
          | global index => rfl

/-- Compositional data fragment for function-table evaluation. Leaves are
included directly; Some/Cons and List/Option matches may nest recursively. -/
inductive FunctionTableDataFragment : PolyIR.Term → Prop where
  | leaf {term : PolyIR.Term} : FunctionTableLeaf term → FunctionTableDataFragment term
  | some (value : PolyIR.Term) : FunctionTableDataFragment value →
      FunctionTableDataFragment (.some value)
  | cons (head tail : PolyIR.Term) : FunctionTableDataFragment head →
      FunctionTableDataFragment tail → FunctionTableDataFragment (.cons head tail)
  | integerBinary (operation : FunctionTableIntegerBinary) (left right : PolyIR.Term) :
      FunctionTableDataFragment left → FunctionTableDataFragment right →
      FunctionTableDataFragment (operation.term left right)
  | floatBin (operation : Surface.FloatBinOp) (left right : PolyIR.Term) :
      FunctionTableDataFragment left → FunctionTableDataFragment right →
      FunctionTableDataFragment (.floatBin operation left right)
  | ite (condition yes no : PolyIR.Term) : FunctionTableDataFragment condition →
      FunctionTableDataFragment yes → FunctionTableDataFragment no →
      FunctionTableDataFragment (.ite condition yes no)
  | beginOne (first second : PolyIR.Term) : FunctionTableDataFragment first →
      FunctionTableDataFragment second → FunctionTableDataFragment (.begin first [second])
  | beginRows (first : PolyIR.Term) (rest : List PolyIR.Term) :
      FunctionTableDataFragment first →
      (∀ term, term ∈ rest → FunctionTableDataFragment term) →
      FunctionTableDataFragment (.begin first rest)
  | letManyOne (initializer body : PolyIR.Term) : FunctionTableDataFragment initializer →
      FunctionTableDataFragment body → FunctionTableDataFragment (.letMany [initializer] body)
  | letManyRows (initializers : List PolyIR.Term) (body : PolyIR.Term) :
      (∀ initializer, initializer ∈ initializers → FunctionTableDataFragment initializer) →
      FunctionTableDataFragment body →
      FunctionTableDataFragment (.letMany initializers body)
  | matchList (target empty full : PolyIR.Term) :
      FunctionTableDataFragment target → FunctionTableDataFragment empty →
      FunctionTableDataFragment full →
      FunctionTableDataFragment (.matchList target empty full)
  | matchOption (target empty full : PolyIR.Term) :
      FunctionTableDataFragment target → FunctionTableDataFragment empty →
      FunctionTableDataFragment full →
      FunctionTableDataFragment (.matchOption target empty full)

/-- Arbitrary-length expression lists whose members belong to the data
fragment. This is used for begin sequences and parallel-let initializers. -/
inductive FunctionTableDataTerms : List PolyIR.Term → Prop where
  | nil : FunctionTableDataTerms []
  | cons (head : PolyIR.Term) (tail : List PolyIR.Term) :
      FunctionTableDataFragment head → FunctionTableDataTerms tail →
      FunctionTableDataTerms (head :: tail)

/-- Evaluation correspondence for the compositional data fragment. Child
faults, constructor results, selected branches, and binder environment order
are inherited from the pointwise constructor lemmas above. -/
theorem functionTable_globalIR_dataFragment_commutes
    (definitions : List PolyIR.RuntimeDefinition) (store : GlobalIR.Store)
    {term : PolyIR.Term} (fragment : FunctionTableDataFragment term) :
    ∀ fuel environment,
      GlobalIR.evaluate (definitions.map GlobalIR.Definition.function) store fuel environment term =
        wrapCoreFault (PolyIR.evaluate definitions fuel environment term) := by
  induction fragment with
  | leaf leaf => exact functionTable_globalIR_leaf_commutes definitions store leaf
  | some value valueProof valueIH =>
      intro fuel environment
      apply functionTable_globalIR_some_commutes_of_pointwise definitions store value fuel environment
      intro evaluationFuel term member
      have termEq : term = value := by simpa using member
      subst term
      exact valueIH evaluationFuel environment
  | cons head tail headFragment tailFragment headIH tailIH =>
      intro fuel environment
      apply functionTable_globalIR_cons_commutes_of_pointwise definitions store head tail fuel
        environment
      intro evaluationFuel term member
      simp [List.mem_cons] at member
      rcases member with headEq | tailEq
      · subst term
        exact headIH evaluationFuel environment
      · subst term
        exact tailIH evaluationFuel environment
  | integerBinary operation left right leftProof rightProof leftIH rightIH =>
      intro fuel environment
      apply functionTable_globalIR_integerBinary_commutes_of_pointwise definitions store
        operation left right fuel environment
      intro evaluationFuel term member
      simp [List.mem_cons] at member
      rcases member with leftEq | rightEq
      · subst term
        exact leftIH evaluationFuel environment
      · subst term
        exact rightIH evaluationFuel environment
  | floatBin operation left right leftProof rightProof leftIH rightIH =>
      intro fuel environment
      apply functionTable_globalIR_floatBin_commutes_of_pointwise definitions store
        operation left right fuel environment
      intro evaluationFuel term member
      simp [List.mem_cons] at member
      rcases member with leftEq | rightEq
      · subst term
        exact leftIH evaluationFuel environment
      · subst term
        exact rightIH evaluationFuel environment
  | ite condition yes no conditionProof yesProof noProof conditionIH yesIH noIH =>
      intro fuel environment
      apply functionTable_globalIR_ite_commutes_of_pointwise definitions store
        condition yes no fuel environment
      intro evaluationFuel term member
      simp [List.mem_cons] at member
      rcases member with conditionEq | yesEq | noEq
      · subst term
        exact conditionIH evaluationFuel environment
      · subst term
        exact yesIH evaluationFuel environment
      · subst term
        exact noIH evaluationFuel environment
  | beginOne first second firstProof secondProof firstIH secondIH =>
      intro fuel environment
      apply functionTable_globalIR_begin_commutes_of_pointwise definitions store first [second]
        fuel environment
      intro evaluationFuel term member
      simp [List.mem_cons] at member
      rcases member with firstEq | secondEq
      · subst term
        exact firstIH evaluationFuel environment
      · have secondIsTerm : term = second := secondEq
        clear secondEq
        subst term
        exact secondIH evaluationFuel environment
  | beginRows first rest firstFragment restFragments firstIH restIH =>
      intro fuel environment
      apply functionTable_globalIR_begin_commutes_of_pointwise definitions store first rest
        fuel environment
      intro evaluationFuel term member
      simp [List.mem_cons] at member
      rcases member with firstEq | restMember
      · subst term
        exact firstIH evaluationFuel environment
      · exact restIH term restMember evaluationFuel environment
  | letManyOne initializer body initializerProof bodyProof initializerIH bodyIH =>
      intro fuel environment
      apply functionTable_globalIR_letMany_commutes_of_pointwise definitions store
        [initializer] body fuel environment
      · intro evaluationFuel term member
        have termEq : term = initializer := by simpa using member
        subst term
        exact initializerIH evaluationFuel environment
      · intro evaluationFuel localEnvironment
        exact bodyIH evaluationFuel localEnvironment
  | letManyRows initializers body initializerFragments bodyFragment initializerIH bodyIH =>
      intro fuel environment
      apply functionTable_globalIR_letMany_commutes_of_pointwise definitions store
        initializers body fuel environment
      · intro evaluationFuel term member
        exact initializerIH term member evaluationFuel environment
      · intro evaluationFuel localEnvironment
        exact bodyIH evaluationFuel localEnvironment
  | matchList target empty full targetFragment emptyFragment fullFragment
      targetIH emptyIH fullIH =>
      intro fuel environment
      apply functionTable_globalIR_matchList_commutes_of_pointwise definitions store
        target empty full fuel environment
      intro evaluationFuel branchEnvironment term member
      simp [List.mem_cons] at member
      rcases member with targetEq | emptyEq | fullEq
      · subst term
        exact targetIH evaluationFuel branchEnvironment
      · subst term
        exact emptyIH evaluationFuel branchEnvironment
      · subst term
        exact fullIH evaluationFuel branchEnvironment
  | matchOption target empty full targetFragment emptyFragment fullFragment
      targetIH emptyIH fullIH =>
      intro fuel environment
      apply functionTable_globalIR_matchOption_commutes_of_pointwise definitions store
        target empty full fuel environment
      intro evaluationFuel branchEnvironment term member
      simp [List.mem_cons] at member
      rcases member with targetEq | emptyEq | fullEq
      · subst term
        exact targetIH evaluationFuel branchEnvironment
      · subst term
        exact emptyIH evaluationFuel branchEnvironment
      · subst term
        exact fullIH evaluationFuel branchEnvironment

/-- Every member of a data-fragment term list commutes at every fuel and
environment. -/
theorem functionTable_globalIR_dataTerms_pointwise
    (definitions : List PolyIR.RuntimeDefinition) (store : GlobalIR.Store)
    {terms : List PolyIR.Term} (fragments : FunctionTableDataTerms terms) :
    ∀ evaluationFuel environment term, term ∈ terms →
      GlobalIR.evaluate (definitions.map GlobalIR.Definition.function) store
          evaluationFuel environment term =
        wrapCoreFault (PolyIR.evaluate definitions evaluationFuel environment term) := by
  induction fragments with
  | nil => simp
  | cons head tail headFragment tailFragments tailIH =>
      intro evaluationFuel environment term member
      simp [List.mem_cons] at member
      rcases member with headEq | tailMember
      · subst term
        exact functionTable_globalIR_dataFragment_commutes definitions store headFragment
          evaluationFuel environment
      · exact tailIH evaluationFuel environment term tailMember

private theorem dataTerms_mem_append_left {α : Type} (left right : List α)
    {item : α} (member : item ∈ left) : item ∈ left ++ right := by
  induction left with
  | nil => simp at member
  | cons head tail ih =>
      simp only [List.cons_append, List.mem_cons]
      simp only [List.mem_cons] at member
      rcases member with same | member
      · exact Or.inl same
      · exact Or.inr (ih member)

private theorem dataTerms_mem_append_right {α : Type} (left right : List α)
    {item : α} (member : item ∈ right) : item ∈ left ++ right := by
  induction left with
  | nil => simpa using member
  | cons head tail ih =>
      simp only [List.cons_append, List.mem_cons]
      exact Or.inr ih

/-- Any initializer fault in a list of recursively composed data-fragment
terms reaches the function-table GlobalIR program entry. Evaluation
correspondence is derived from the syntax evidence instead of being supplied
as a separate pointwise assumption. -/
theorem functionTable_dataTerms_run_reports_initializer_fault
    (definitions : List PolyIR.RuntimeDefinition) (initializers : List PolyIR.Term)
    (entry fuel : Nat) (fault : GlobalIR.Fault)
    (fragments : FunctionTableDataTerms initializers)
    (initializerFault : initializeValuesCore definitions fuel
      (List.replicate initializers.length none) 0 initializers = .error fault) :
    GlobalIR.run ⟨definitions.map GlobalIR.Definition.function, initializers, entry⟩ fuel =
      .error fault := by
  apply functionTable_globalIR_run_reports_initializer_fault definitions initializers
    entry fuel fault
  · intro currentStore evaluationFuel term member
    exact functionTable_globalIR_dataTerms_pointwise definitions currentStore fragments
      evaluationFuel [] term member
  · exact initializerFault

/-- The same composition carries a fault after any successful initializer
prefix, preserving both the committed store and the original core fault. -/
theorem functionTable_dataTerms_run_reports_initializer_fault_after_prefix
    (definitions : List PolyIR.RuntimeDefinition) (initializersBefore : List PolyIR.Term)
    (head : PolyIR.Term) (tail : List PolyIR.Term) (entry fuel : Nat)
    (after : GlobalIR.Store) (coreFault : PolyIR.Fault)
    (fragments : FunctionTableDataTerms (initializersBefore ++ head :: tail))
    (prefixSuccess : initializeValuesCore definitions
      (fuel + initializersBefore.length + 2)
      (List.replicate (initializersBefore ++ head :: tail).length none) 0
      initializersBefore = .ok after)
    (faultStep : PolyIR.evaluate definitions (fuel + 1) [] head = .error coreFault) :
    GlobalIR.run ⟨definitions.map GlobalIR.Definition.function,
      initializersBefore ++ head :: tail, entry⟩
      (fuel + initializersBefore.length + 2) = .error (.core coreFault) := by
  have pointwisePrefix : ∀ currentStore evaluationFuel term,
      term ∈ initializersBefore →
        GlobalIR.evaluate (definitions.map GlobalIR.Definition.function) currentStore
            evaluationFuel [] term =
          wrapCoreFault (PolyIR.evaluate definitions evaluationFuel [] term) := by
    intro currentStore evaluationFuel term member
    have memberAll : term ∈ initializersBefore ++ head :: tail := by
      exact dataTerms_mem_append_left initializersBefore (head :: tail) member
    exact functionTable_globalIR_dataTerms_pointwise definitions currentStore fragments
      evaluationFuel [] term memberAll
  have globalPrefix : GlobalIR.initializeValues
      (definitions.map GlobalIR.Definition.function)
      (fuel + initializersBefore.length + 2)
      (List.replicate (initializersBefore ++ head :: tail).length none)
      0 initializersBefore = .ok after := by
    rw [functionTable_globalIR_initializeValues_commutes_of_pointwise definitions
      (List.replicate (initializersBefore ++ head :: tail).length none) 0
      (fuel + initializersBefore.length + 2) initializersBefore pointwisePrefix]
    exact prefixSuccess
  have globalFault : GlobalIR.evaluate
      (definitions.map GlobalIR.Definition.function) after (fuel + 1) [] head =
      .error (.core coreFault) := by
    have memberHead : head ∈ initializersBefore ++ head :: tail := by
      exact dataTerms_mem_append_right initializersBefore (head :: tail) (by simp)
    have corresponding := functionTable_globalIR_dataTerms_pointwise definitions after fragments
      (fuel + 1) [] head memberHead
    rw [faultStep] at corresponding
    exact corresponding
  exact GlobalIR.run_reports_initializer_fault_after_prefix
    ⟨definitions.map GlobalIR.Definition.function,
      initializersBefore ++ head :: tail, entry⟩ fuel
    initializersBefore head tail after (.core coreFault) rfl globalPrefix globalFault

/-- A Surface initializer fault reaches the program entry after erasure when
the initializer list is in the recursively composed data fragment. -/
theorem functionTable_dataTerms_sourceFault_run_reports_initializer_fault_after_prefix
    (sourceProgram : Surface.Definitions) (initializersBefore tail : List PolyIR.Term)
    (expression : Surface.Expr) (entry fuel : Nat) (after : GlobalIR.Store)
    (fault : PolyIR.Fault)
    (fragments : FunctionTableDataTerms
      (initializersBefore ++ PolyIR.erase expression :: tail))
    (prefixSuccess : initializeValuesCore (PolyIR.eraseDefinitions sourceProgram)
      (fuel + initializersBefore.length + 2)
      (List.replicate (initializersBefore ++ PolyIR.erase expression :: tail).length none)
      0 initializersBefore = .ok after)
    (sourceFault : Surface.evaluate sourceProgram (fuel + 1) [] expression = .error fault) :
    GlobalIR.run
      ⟨(PolyIR.eraseDefinitions sourceProgram).map GlobalIR.Definition.function,
        initializersBefore ++ PolyIR.erase expression :: tail, entry⟩
      (fuel + initializersBefore.length + 2) = .error (.core fault) := by
  have erasedFault := PolyIR.execution_error_iff.mpr sourceFault
  exact functionTable_dataTerms_run_reports_initializer_fault_after_prefix
    (PolyIR.eraseDefinitions sourceProgram) initializersBefore (PolyIR.erase expression)
    tail entry fuel after fault fragments prefixSuccess erasedFault

/-- A source initializer fault reaches the entry when the already committed
prefix is supplied directly as a GlobalIR store. This avoids requiring the
caller to reconstruct how that store was initialized. -/
theorem functionTable_dataTerms_sourceFault_run_reports_initializer_fault_after_global_prefix
    (sourceProgram : Surface.Definitions) (initializersBefore tail : List PolyIR.Term)
    (expression : Surface.Expr) (entry fuel : Nat) (after : GlobalIR.Store)
    (fault : PolyIR.Fault)
    (fragments : FunctionTableDataTerms
      (initializersBefore ++ PolyIR.erase expression :: tail))
    (prefixSuccess : GlobalIR.initializeValues
      ((PolyIR.eraseDefinitions sourceProgram).map GlobalIR.Definition.function)
      (fuel + initializersBefore.length + 2)
      (List.replicate (initializersBefore ++ PolyIR.erase expression :: tail).length none)
      0 initializersBefore = .ok after)
    (sourceFault : Surface.evaluate sourceProgram (fuel + 1) [] expression = .error fault) :
    GlobalIR.run
      ⟨(PolyIR.eraseDefinitions sourceProgram).map GlobalIR.Definition.function,
        initializersBefore ++ PolyIR.erase expression :: tail, entry⟩
      (fuel + initializersBefore.length + 2) = .error (.core fault) := by
  have erasedFault := PolyIR.execution_error_iff.mpr sourceFault
  have erasedFault' : PolyIR.evaluate (PolyIR.eraseDefinitions sourceProgram)
      (fuel + 1) [] (PolyIR.erase expression) = .error fault := by
    simpa using erasedFault
  have faultStep : GlobalIR.evaluate
      ((PolyIR.eraseDefinitions sourceProgram).map GlobalIR.Definition.function)
      after (fuel + 1) [] (PolyIR.erase expression) = .error (.core fault) := by
    have member : PolyIR.erase expression ∈
        initializersBefore ++ PolyIR.erase expression :: tail := by
      exact dataTerms_mem_append_right initializersBefore
        (PolyIR.erase expression :: tail) (by simp)
    have corresponding := functionTable_globalIR_dataTerms_pointwise
      (PolyIR.eraseDefinitions sourceProgram) after fragments (fuel + 1) []
      (PolyIR.erase expression) member
    rw [erasedFault'] at corresponding
    simpa [wrapCoreFault] using corresponding
  exact GlobalIR.run_reports_initializer_fault_after_prefix
    ⟨(PolyIR.eraseDefinitions sourceProgram).map GlobalIR.Definition.function,
      initializersBefore ++ PolyIR.erase expression :: tail, entry⟩ fuel
    initializersBefore (PolyIR.erase expression) tail after (.core fault) rfl
    prefixSuccess faultStep

/-- Arbitrary-length begin sequences whose entries belong to the compositional
data fragment preserve values and faults. -/
theorem functionTable_globalIR_dataBegin_commutes
    (definitions : List PolyIR.RuntimeDefinition) (store : GlobalIR.Store)
    (first : PolyIR.Term) (rest : List PolyIR.Term)
    (firstFragment : FunctionTableDataFragment first)
    (restFragments : FunctionTableDataTerms rest) (fuel : Nat)
    (environment : List PolyIR.Value) :
    GlobalIR.evaluate (definitions.map GlobalIR.Definition.function) store fuel environment
        (.begin first rest) =
      wrapCoreFault (PolyIR.evaluate definitions fuel environment (.begin first rest)) := by
  apply functionTable_globalIR_begin_commutes_of_pointwise definitions store first rest fuel
    environment
  intro evaluationFuel term member
  simp [List.mem_cons] at member
  rcases member with firstEq | restMember
  · subst term
    exact functionTable_globalIR_dataFragment_commutes definitions store firstFragment
      evaluationFuel environment
  · exact functionTable_globalIR_dataTerms_pointwise definitions store restFragments
      evaluationFuel environment term restMember

/-- Arbitrary-length parallel-let initializers may contain any term from the
data fragment. They are checked in the original environment, then the body is
checked in the environment extended with all values. -/
theorem functionTable_globalIR_dataLetMany_commutes
    (definitions : List PolyIR.RuntimeDefinition) (store : GlobalIR.Store)
    (initializers : List PolyIR.Term) (body : PolyIR.Term)
    (initializerFragments : FunctionTableDataTerms initializers)
    (bodyFragment : FunctionTableDataFragment body) (fuel : Nat)
    (environment : List PolyIR.Value) :
    GlobalIR.evaluate (definitions.map GlobalIR.Definition.function) store fuel environment
        (.letMany initializers body) =
      wrapCoreFault (PolyIR.evaluate definitions fuel environment (.letMany initializers body)) := by
  apply functionTable_globalIR_letMany_commutes_of_pointwise definitions store initializers body
    fuel environment
  · intro evaluationFuel term member
    exact functionTable_globalIR_dataTerms_pointwise definitions store initializerFragments
      evaluationFuel environment term member
  · intro evaluationFuel localEnvironment
    exact functionTable_globalIR_dataFragment_commutes definitions store bodyFragment
      evaluationFuel localEnvironment

/-- A direct function-table global application commutes whenever its argument
terms and selected function body commute pointwise. -/
theorem functionTable_globalIR_globalFunctionCall_commutes_of_pointwise
    (definitions : List PolyIR.RuntimeDefinition) (store : GlobalIR.Store)
    (index : Nat) (arguments : List PolyIR.Term) (arity : Nat) (body : PolyIR.Term)
    (definitionFound : definitions[index]? = some ⟨arity, body⟩)
    (argumentsPointwise : ∀ fuel environment term, term ∈ arguments →
      GlobalIR.evaluate (definitions.map GlobalIR.Definition.function) store fuel environment term =
        wrapCoreFault (PolyIR.evaluate definitions fuel environment term))
    (bodyPointwise : ∀ fuel environment,
      GlobalIR.evaluate (definitions.map GlobalIR.Definition.function) store fuel environment body =
        wrapCoreFault (PolyIR.evaluate definitions fuel environment body))
    (fuel : Nat) (environment : List PolyIR.Value) :
    GlobalIR.evaluate (definitions.map GlobalIR.Definition.function) store (fuel + 1) environment
        (.app (.global index) arguments) =
      wrapCoreFault (PolyIR.evaluate definitions (fuel + 1) environment
        (.app (.global index) arguments)) := by
  have globalCommutes := functionTable_globalIR_leaf_commutes definitions store
    (FunctionTableLeaf.global index) fuel environment
  have argumentsCommute := functionTable_globalIR_arguments_commutes_of_pointwise
    definitions store arguments fuel environment
    (fun evaluationFuel term member => argumentsPointwise evaluationFuel environment term member)
  change (do
    let functionValue ← GlobalIR.evaluate (definitions.map GlobalIR.Definition.function) store
      fuel environment (.global index)
    let argumentValues ← GlobalIR.evaluateArgs (definitions.map GlobalIR.Definition.function) store
      fuel environment arguments
    match functionValue with
    | .closure functionArity functionBody captured =>
        if argumentValues.length = functionArity then
          GlobalIR.evaluate (definitions.map GlobalIR.Definition.function) store fuel
            (argumentValues ++ captured) functionBody
        else .error (.core .wrongArity)
    | .global found =>
        match (definitions.map GlobalIR.Definition.function)[found]? with
        | none => .error (.core .unbound)
        | some (.function definition) =>
            if argumentValues.length = definition.arity then
              GlobalIR.evaluate (definitions.map GlobalIR.Definition.function) store fuel
                argumentValues definition.body
            else .error (.core .wrongArity)
        | some (.getter slot) =>
            if argumentValues.isEmpty then GlobalIR.readGlobal store slot
            else .error (.core .wrongArity)
    | _ => .error (.core .wrongShape)) =
    wrapCoreFault (do
      let functionValue ← PolyIR.evaluate definitions fuel environment (.global index)
      let argumentValues ← PolyIR.evaluateArgs definitions fuel environment arguments
      match functionValue with
      | .closure functionArity functionBody captured =>
          if argumentValues.length = functionArity then
            PolyIR.evaluate definitions fuel (argumentValues ++ captured) functionBody
          else .error .wrongArity
      | .global found =>
          match definitions[found]? with
          | none => .error .unbound
          | some definition =>
              if argumentValues.length = definition.arity then
                PolyIR.evaluate definitions fuel argumentValues definition.body
              else .error .wrongArity
      | _ => .error .wrongShape)
  rw [globalCommutes, argumentsCommute]
  cases functionResult : PolyIR.evaluate definitions fuel environment (.global index) with
  | error fault =>
    simp [functionResult, wrapCoreFault, Except.bind, Except.pure, Pure.pure, bind, pure]
  | ok functionValue =>
    have functionValueEq : functionValue = .global index := by
      cases fuel with
      | zero => simp [PolyIR.evaluate] at functionResult
      | succ fuel =>
          have evaluatedGlobal : (Except.ok (.global index) : Except PolyIR.Fault PolyIR.Value) =
              .ok functionValue := by
            simpa [PolyIR.evaluate, definitionFound, Except.pure, Pure.pure] using functionResult
          exact (Except.ok.inj evaluatedGlobal).symm
    subst functionValue
    cases argumentsResult : PolyIR.evaluateArgs definitions fuel environment arguments with
    | error fault =>
      simp [functionResult, argumentsResult, wrapCoreFault, Except.bind,
        Except.pure, Pure.pure, bind, pure]
    | ok values =>
      by_cases arityCheck : values.length = arity
      · simp [functionResult, argumentsResult, functionTable_map_lookup,
          definitionFound, arityCheck, wrapCoreFault, Except.bind, Except.pure,
          Pure.pure, bind, pure]
        exact bodyPointwise fuel values
      · simp [functionResult, argumentsResult, functionTable_map_lookup,
          definitionFound, arityCheck, wrapCoreFault, Except.bind, Except.pure,
          Pure.pure, bind, pure]

/-- Applications of a literal lambda preserve results and faults when their
argument evaluations and body evaluation correspond pointwise. -/
theorem functionTable_globalIR_lambdaCall_commutes_of_pointwise
    (definitions : List PolyIR.RuntimeDefinition) (store : GlobalIR.Store)
    (arity : Nat) (body : PolyIR.Term) (arguments : List PolyIR.Term)
    (argumentsPointwise : ∀ fuel environment term, term ∈ arguments →
      GlobalIR.evaluate (definitions.map GlobalIR.Definition.function) store fuel environment term =
        wrapCoreFault (PolyIR.evaluate definitions fuel environment term))
    (bodyPointwise : ∀ fuel environment,
      GlobalIR.evaluate (definitions.map GlobalIR.Definition.function) store fuel environment body =
        wrapCoreFault (PolyIR.evaluate definitions fuel environment body))
    (fuel : Nat) (environment : List PolyIR.Value) :
    GlobalIR.evaluate (definitions.map GlobalIR.Definition.function) store (fuel + 1) environment
        (.app (.lam arity body) arguments) =
      wrapCoreFault (PolyIR.evaluate definitions (fuel + 1) environment
        (.app (.lam arity body) arguments)) := by
  have functionCommutes := functionTable_globalIR_leaf_commutes definitions store
    (FunctionTableLeaf.lam arity body) fuel environment
  have argumentsCommute := functionTable_globalIR_arguments_commutes_of_pointwise
    definitions store arguments fuel environment
    (fun evaluationFuel term member => argumentsPointwise evaluationFuel environment term member)
  change (do
    let functionValue ← GlobalIR.evaluate (definitions.map GlobalIR.Definition.function) store
      fuel environment (.lam arity body)
    let argumentValues ← GlobalIR.evaluateArgs (definitions.map GlobalIR.Definition.function) store
      fuel environment arguments
    match functionValue with
    | .closure functionArity functionBody captured =>
        if argumentValues.length = functionArity then
          GlobalIR.evaluate (definitions.map GlobalIR.Definition.function) store fuel
            (argumentValues ++ captured) functionBody
        else .error (.core .wrongArity)
    | .global found =>
        match (definitions.map GlobalIR.Definition.function)[found]? with
        | none => .error (.core .unbound)
        | some (.function definition) =>
            if argumentValues.length = definition.arity then
              GlobalIR.evaluate (definitions.map GlobalIR.Definition.function) store fuel
                argumentValues definition.body
            else .error (.core .wrongArity)
        | some (.getter slot) =>
            if argumentValues.isEmpty then GlobalIR.readGlobal store slot
            else .error (.core .wrongArity)
    | _ => .error (.core .wrongShape)) =
    wrapCoreFault (do
      let functionValue ← PolyIR.evaluate definitions fuel environment (.lam arity body)
      let argumentValues ← PolyIR.evaluateArgs definitions fuel environment arguments
      match functionValue with
      | .closure functionArity functionBody captured =>
          if argumentValues.length = functionArity then
            PolyIR.evaluate definitions fuel (argumentValues ++ captured) functionBody
          else .error .wrongArity
      | .global found =>
          match definitions[found]? with
          | none => .error .unbound
          | some definition =>
              if argumentValues.length = definition.arity then
                PolyIR.evaluate definitions fuel argumentValues definition.body
              else .error .wrongArity
      | _ => .error .wrongShape)
  rw [functionCommutes, argumentsCommute]
  cases functionResult : PolyIR.evaluate definitions fuel environment (.lam arity body) with
  | error fault =>
    simp [functionResult, wrapCoreFault, Except.bind, Except.pure, Pure.pure, bind, pure]
  | ok functionValue =>
    have functionValueEq : functionValue = .closure arity body environment := by
      cases fuel with
      | zero => simp [PolyIR.evaluate] at functionResult
      | succ fuel =>
          have evaluatedLambda :
              (Except.ok (.closure arity body environment) : Except PolyIR.Fault PolyIR.Value) =
                .ok functionValue := by
            simpa [PolyIR.evaluate, Except.pure, Pure.pure] using functionResult
          exact (Except.ok.inj evaluatedLambda).symm
    subst functionValue
    cases argumentsResult : PolyIR.evaluateArgs definitions fuel environment arguments with
    | error fault =>
      simp [functionResult, argumentsResult, wrapCoreFault, Except.bind,
        Except.pure, Pure.pure, bind, pure]
    | ok values =>
      by_cases arityCheck : values.length = arity
      · simp [functionResult, argumentsResult, arityCheck, wrapCoreFault,
          Except.bind, Except.pure, Pure.pure, bind, pure]
        exact bodyPointwise fuel (values ++ environment)
      · simp [functionResult, argumentsResult, arityCheck, wrapCoreFault,
          Except.bind, Except.pure, Pure.pure, bind, pure]

/-- Fault-inclusive global-call correspondence for terms in the recursive
data fragment, including arbitrary argument counts. -/
theorem functionTable_globalIR_dataGlobalCall_commutes
    (definitions : List PolyIR.RuntimeDefinition) (store : GlobalIR.Store)
    (index : Nat) (arguments : List PolyIR.Term) (arity : Nat) (body : PolyIR.Term)
    (definitionFound : definitions[index]? = some ⟨arity, body⟩)
    (argumentsFragments : FunctionTableDataTerms arguments)
    (bodyFragment : FunctionTableDataFragment body) (fuel : Nat)
    (environment : List PolyIR.Value) :
    GlobalIR.evaluate (definitions.map GlobalIR.Definition.function) store (fuel + 1)
        environment (.app (.global index) arguments) =
      wrapCoreFault (PolyIR.evaluate definitions (fuel + 1) environment
        (.app (.global index) arguments)) := by
  apply functionTable_globalIR_globalFunctionCall_commutes_of_pointwise
    definitions store index arguments arity body definitionFound
  · intro evaluationFuel argumentEnvironment term member
    exact functionTable_globalIR_dataTerms_pointwise definitions store argumentsFragments
      evaluationFuel argumentEnvironment term member
  · intro evaluationFuel bodyEnvironment
    exact functionTable_globalIR_dataFragment_commutes definitions store bodyFragment
      evaluationFuel bodyEnvironment

mutual
  inductive FunctionTableCallFragment (definitions : List PolyIR.RuntimeDefinition) :
      PolyIR.Term → Prop where
    | data {term : PolyIR.Term} : FunctionTableDataFragment term →
        FunctionTableCallFragment definitions term
    | globalCall (index : Nat) (arguments : List PolyIR.Term) (arity : Nat)
        (body : PolyIR.Term)
        (definitionFound : definitions[index]? = some ⟨arity, body⟩)
        (argumentsFragments : FunctionTableCallTerms definitions arguments)
        (bodyFragment : FunctionTableCallFragment definitions body) :
        FunctionTableCallFragment definitions (.app (.global index) arguments)
    | lambdaCall (arity : Nat) (body : PolyIR.Term) (arguments : List PolyIR.Term)
        (argumentsFragments : FunctionTableCallTerms definitions arguments)
        (bodyFragment : FunctionTableCallFragment definitions body) :
        FunctionTableCallFragment definitions (.app (.lam arity body) arguments)
    | beginRows (first : PolyIR.Term) (rest : List PolyIR.Term)
        (firstFragment : FunctionTableCallFragment definitions first)
        (restFragments : FunctionTableCallTerms definitions rest) :
        FunctionTableCallFragment definitions (.begin first rest)
    | letManyRows (initializers : List PolyIR.Term) (body : PolyIR.Term)
        (initializerFragments : FunctionTableCallTerms definitions initializers)
        (bodyFragment : FunctionTableCallFragment definitions body) :
        FunctionTableCallFragment definitions (.letMany initializers body)

  inductive FunctionTableCallTerms (definitions : List PolyIR.RuntimeDefinition) :
      List PolyIR.Term → Prop where
    | nil : FunctionTableCallTerms definitions []
    | cons (head : PolyIR.Term) (tail : List PolyIR.Term) :
        FunctionTableCallFragment definitions head →
        FunctionTableCallTerms definitions tail →
        FunctionTableCallTerms definitions (head :: tail)
end

/-- Fault-inclusive evaluation correspondence for recursively nested direct
global calls in `FunctionTableCallFragment`. -/
theorem functionTable_globalIR_callFragment_commutes
    (definitions : List PolyIR.RuntimeDefinition) (store : GlobalIR.Store)
    {term : PolyIR.Term} (fragment : FunctionTableCallFragment definitions term) :
    ∀ fuel environment,
      GlobalIR.evaluate (definitions.map GlobalIR.Definition.function) store fuel environment term =
        wrapCoreFault (PolyIR.evaluate definitions fuel environment term) := by
  exact FunctionTableCallFragment.rec
    (motive_1 := fun expression _ => ∀ fuel environment,
      GlobalIR.evaluate (definitions.map GlobalIR.Definition.function) store fuel environment expression =
        wrapCoreFault (PolyIR.evaluate definitions fuel environment expression))
    (motive_2 := fun terms _ => ∀ fuel environment term, term ∈ terms →
      GlobalIR.evaluate (definitions.map GlobalIR.Definition.function) store fuel environment term =
        wrapCoreFault (PolyIR.evaluate definitions fuel environment term))
    (fun {expression} dataFragment =>
      functionTable_globalIR_dataFragment_commutes definitions store dataFragment)
    (fun index arguments arity body definitionFound _argumentsFragments bodyFragment
        argumentsIH bodyIH => by
      intro fuel environment
      cases fuel with
      | zero => simp [GlobalIR.evaluate, PolyIR.evaluate, wrapCoreFault]
      | succ fuel =>
          exact functionTable_globalIR_globalFunctionCall_commutes_of_pointwise
            definitions store index arguments arity body definitionFound
            (fun evaluationFuel argumentEnvironment argument member =>
              argumentsIH evaluationFuel argumentEnvironment argument member)
            (fun evaluationFuel bodyEnvironment => bodyIH evaluationFuel bodyEnvironment)
            fuel environment)
    (fun arity body arguments _argumentsFragments bodyFragment argumentsIH bodyIH => by
      intro fuel environment
      cases fuel with
      | zero => simp [GlobalIR.evaluate, PolyIR.evaluate, wrapCoreFault]
      | succ fuel =>
          exact functionTable_globalIR_lambdaCall_commutes_of_pointwise
            definitions store arity body arguments
            (fun evaluationFuel argumentEnvironment argument member =>
              argumentsIH evaluationFuel argumentEnvironment argument member)
            (fun evaluationFuel bodyEnvironment => bodyIH evaluationFuel bodyEnvironment)
            fuel environment)
    (fun first rest _firstFragment _restFragments firstIH restIH => by
      intro fuel environment
      apply functionTable_globalIR_begin_commutes_of_pointwise definitions store first rest
        fuel environment
      intro evaluationFuel term member
      simp [List.mem_cons] at member
      rcases member with firstEq | restMember
      · subst term
        exact firstIH evaluationFuel environment
      · exact restIH evaluationFuel environment term restMember)
    (fun initializers body _initializerFragments _bodyFragment initializerIH bodyIH => by
      intro fuel environment
      apply functionTable_globalIR_letMany_commutes_of_pointwise definitions store
        initializers body fuel environment
      · intro evaluationFuel term member
        exact initializerIH evaluationFuel environment term member
      · intro evaluationFuel bodyEnvironment
        exact bodyIH evaluationFuel bodyEnvironment)
    (by simp)
    (fun head tail _headFragment _tailFragments headIH tailIH => by
      intro fuel environment term member
      simp [List.mem_cons] at member
      rcases member with headEq | tailMember
      · subst term
        exact headIH fuel environment
      · exact tailIH fuel environment term tailMember)
    fragment

/-- On the recursively composed direct-call fragment, GlobalIR's fuel
exhaustion definition of divergence is exactly PolyIR fuel exhaustion.
Finite runtime faults are kept distinct on both sides by the wrapped error. -/
theorem functionTable_globalIR_callFragment_diverges_iff
    (definitions : List PolyIR.RuntimeDefinition) (store : GlobalIR.Store)
    {term : PolyIR.Term} (fragment : FunctionTableCallFragment definitions term)
    (environment : List PolyIR.Value) :
    GlobalIR.Diverges (definitions.map GlobalIR.Definition.function) store environment term ↔
      ∀ fuel, 0 < fuel →
        PolyIR.evaluate definitions fuel environment term = .error .outOfFuel := by
  constructor
  · intro globalDiverges fuel positive
    have corresponding := functionTable_globalIR_callFragment_commutes
      definitions store fragment fuel environment
    have exhausted := globalDiverges fuel positive
    rw [corresponding] at exhausted
    exact (wrapCoreFault_error_iff _ .outOfFuel).mp exhausted
  · intro polyDiverges fuel positive
    have corresponding := functionTable_globalIR_callFragment_commutes
      definitions store fragment fuel environment
    rw [polyDiverges fuel positive] at corresponding
    exact corresponding

/-- Surface fuel divergence is reflected to and from GlobalIR for any
surface expression whose erased term is in the recursive call fragment.
This composes the executable Surface-to-PolyIR diagram with the
fault-inclusive PolyIR-to-GlobalIR diagram. -/
theorem functionTable_surface_globalIR_callFragment_diverges_iff
    (sourceProgram : Surface.Definitions) (store : GlobalIR.Store)
    (expression : Surface.Expr)
    (fragment : FunctionTableCallFragment (PolyIR.eraseDefinitions sourceProgram)
      (PolyIR.erase expression)) (environment : List Surface.Value) :
    GlobalIR.Diverges
      ((PolyIR.eraseDefinitions sourceProgram).map GlobalIR.Definition.function)
      store (PolyIR.eraseValues environment) (PolyIR.erase expression) ↔
      ∀ fuel, 0 < fuel →
        Surface.evaluate sourceProgram fuel environment expression = .error .outOfFuel := by
  rw [functionTable_globalIR_callFragment_diverges_iff
    (PolyIR.eraseDefinitions sourceProgram) store fragment (PolyIR.eraseValues environment)]
  constructor
  · intro polyFuel fuel positive
    have allPolyFuel : ∀ budget,
        PolyIR.evaluate (PolyIR.eraseDefinitions sourceProgram) budget
          (PolyIR.eraseValues environment) (PolyIR.erase expression) = .error .outOfFuel := by
      intro budget
      cases budget with
      | zero => simp [PolyIR.evaluate]
      | succ budget => exact polyFuel (budget + 1) (by omega)
    exact (PolyIR.fuel_divergence_iff sourceProgram environment expression).mp
      allPolyFuel fuel
  · intro sourceFuel fuel positive
    have allSourceFuel : ∀ budget,
        Surface.evaluate sourceProgram budget environment expression = .error .outOfFuel := by
      intro budget
      cases budget with
      | zero => simp [Surface.evaluate]
      | succ budget => exact sourceFuel (budget + 1) (by omega)
    exact (PolyIR.fuel_divergence_iff sourceProgram environment expression).mpr
      allSourceFuel fuel

/-- For a closed well-typed Surface expression in the recursive call
fragment, absence of a finite source big-step derivation is equivalent to
GlobalIR fuel divergence. Typing rules out finite runtime faults, while the
fragment provides the evaluator correspondence at every fuel depth. -/
theorem functionTable_typed_source_globalIR_callFragment_diverges_iff
    (sourceProgram : Surface.Definitions) (globals : List Surface.Signature)
    (programTyped : PolyIR.ProgramTyped globals sourceProgram)
    (store : GlobalIR.Store) (expression : Surface.Expr) (type : Surface.Ty)
    (expressionTyped : Surface.HasType globals 0 [] expression type)
    (fragment : FunctionTableCallFragment (PolyIR.eraseDefinitions sourceProgram)
      (PolyIR.erase expression)) :
    (¬ ∃ value, Surface.Evaluates sourceProgram [] expression value) ↔
      GlobalIR.Diverges
        ((PolyIR.eraseDefinitions sourceProgram).map GlobalIR.Definition.function)
        store [] (PolyIR.erase expression) := by
  have typedFuel := PolyIR.typed_closed_divergence_iff_fuel_exhaustion sourceProgram globals
    programTyped expression type expressionTyped
  have positiveFuel :
      (¬ ∃ value, Surface.Evaluates sourceProgram [] expression value) ↔
        ∀ fuel, 0 < fuel →
          Surface.evaluate sourceProgram fuel [] expression = .error .outOfFuel := by
    constructor
    · intro noFinite fuel positive
      exact typedFuel.mp noFinite fuel
    · intro allPositive
      apply typedFuel.mpr
      intro fuel
      cases fuel with
      | zero => simp [Surface.evaluate]
      | succ fuel => exact allPositive (fuel + 1) (by omega)
  exact positiveFuel.trans
    (functionTable_surface_globalIR_callFragment_diverges_iff sourceProgram store
      expression fragment []).symm

/-- A typed, nonterminating Surface initializer at any position in a
function-only GlobalIR program makes `run` exhaust its depth fuel after the
successful initializer prefix has committed. -/
theorem functionTable_typed_source_initializer_diverges_after_prefix
    (sourceProgram : Surface.Definitions) (globals : List Surface.Signature)
    (programTyped : PolyIR.ProgramTyped globals sourceProgram)
    (initializersBefore tail : List PolyIR.Term) (expression : Surface.Expr)
    (type : Surface.Ty)
    (expressionTyped : Surface.HasType globals 0 [] expression type)
    (fragment : FunctionTableCallFragment (PolyIR.eraseDefinitions sourceProgram)
      (PolyIR.erase expression)) (entry fuel : Nat) (after : GlobalIR.Store)
    (sourceDiverges : ¬ ∃ value, Surface.Evaluates sourceProgram [] expression value)
    (prefixSuccess : GlobalIR.initializeValues
      ((PolyIR.eraseDefinitions sourceProgram).map GlobalIR.Definition.function)
      (fuel + initializersBefore.length + 2)
      (List.replicate (initializersBefore ++ PolyIR.erase expression :: tail).length none)
      0 initializersBefore = .ok after) :
    GlobalIR.run ⟨
      (PolyIR.eraseDefinitions sourceProgram).map GlobalIR.Definition.function,
      initializersBefore ++ PolyIR.erase expression :: tail, entry⟩
      (fuel + initializersBefore.length + 2) = .error (.core .outOfFuel) := by
  have diverges := functionTable_typed_source_globalIR_callFragment_diverges_iff
    sourceProgram globals programTyped after expression type expressionTyped fragment
  have globalDiverges := diverges.mp sourceDiverges
  exact GlobalIR.run_reports_initializer_diverges_after_prefix
    ⟨(PolyIR.eraseDefinitions sourceProgram).map GlobalIR.Definition.function,
      initializersBefore ++ PolyIR.erase expression :: tail, entry⟩
    fuel initializersBefore (PolyIR.erase expression) tail after rfl prefixSuccess
    globalDiverges

/-- Pointwise evaluation correspondence for every member of a recursively
composed call argument list. -/
theorem functionTable_globalIR_callTerms_pointwise
    (definitions : List PolyIR.RuntimeDefinition) (store : GlobalIR.Store)
    {terms : List PolyIR.Term} (fragments : FunctionTableCallTerms definitions terms) :
    ∀ fuel environment term, term ∈ terms →
      GlobalIR.evaluate (definitions.map GlobalIR.Definition.function) store fuel environment term =
        wrapCoreFault (PolyIR.evaluate definitions fuel environment term) := by
  exact FunctionTableCallTerms.rec
    (motive_1 := fun _ _ => True)
    (motive_2 := fun expressions _ => ∀ fuel environment term, term ∈ expressions →
      GlobalIR.evaluate (definitions.map GlobalIR.Definition.function) store fuel environment term =
        wrapCoreFault (PolyIR.evaluate definitions fuel environment term))
    (fun {_} _ => True.intro)
    (fun _ _ _ _ _ _ _ _ _ => True.intro)
    (fun _ _ _ _ _ _ _ => True.intro)
    (fun _ _ _ _ _ _ => True.intro)
    (fun _ _ _ _ _ _ => True.intro)
    (by simp)
    (fun head tail _headFragment _tailFragments _headIH tailIH => by
      intro fuel environment term member
      simp [List.mem_cons] at member
      rcases member with headEq | tailMember
      · subst term
        exact functionTable_globalIR_callFragment_commutes definitions store _headFragment
          fuel environment
      · exact tailIH fuel environment term tailMember)
    fragments

/-- Initializer execution for any recursively composed direct-call fragments
commutes all the way through the mutable GlobalIR store. The recursive
fragment certificate discharges the expression premise at every slot, so
successful prefixes, the final store, and the first fault are compared in
one theorem. -/
theorem functionTable_callTerms_initializeValues_commutes
    (definitions : List PolyIR.RuntimeDefinition) (initializers : List PolyIR.Term)
    (fragments : FunctionTableCallTerms definitions initializers)
    (fuel slot : Nat) (store : GlobalIR.Store) :
    GlobalIR.initializeValues (definitions.map GlobalIR.Definition.function)
        fuel store slot initializers =
      initializeValuesCore definitions fuel store slot initializers := by
  apply functionTable_globalIR_initializeValues_commutes_of_pointwise
  intro currentStore evaluationFuel term member
  exact functionTable_globalIR_callTerms_pointwise definitions currentStore fragments
    evaluationFuel [] term member

/-- Derive the successful GlobalIR prefix from the PolyIR initializer walk,
then report divergence of a typed Surface initializer at the next slot. The
fragment certificate covers both the prefix terms and the divergent term. -/
theorem functionTable_typed_source_initializer_diverges_after_core_prefix
    (sourceProgram : Surface.Definitions) (globals : List Surface.Signature)
    (programTyped : PolyIR.ProgramTyped globals sourceProgram)
    (initializersBefore tail : List PolyIR.Term) (expression : Surface.Expr)
    (type : Surface.Ty)
    (expressionTyped : Surface.HasType globals 0 [] expression type)
    (prefixFragments : FunctionTableCallTerms (PolyIR.eraseDefinitions sourceProgram)
      initializersBefore)
    (headFragment : FunctionTableCallFragment (PolyIR.eraseDefinitions sourceProgram)
      (PolyIR.erase expression))
    (entry fuel : Nat) (after : GlobalIR.Store)
    (sourceDiverges : ¬ ∃ value, Surface.Evaluates sourceProgram [] expression value)
    (prefixSuccess : initializeValuesCore (PolyIR.eraseDefinitions sourceProgram)
      (fuel + initializersBefore.length + 2)
      (List.replicate (initializersBefore ++ PolyIR.erase expression :: tail).length none)
      0 initializersBefore = .ok after) :
    GlobalIR.run ⟨
      (PolyIR.eraseDefinitions sourceProgram).map GlobalIR.Definition.function,
      initializersBefore ++ PolyIR.erase expression :: tail, entry⟩
      (fuel + initializersBefore.length + 2) = .error (.core .outOfFuel) := by
  have pointwisePrefix : ∀ currentStore evaluationFuel term,
      term ∈ initializersBefore →
        GlobalIR.evaluate
          ((PolyIR.eraseDefinitions sourceProgram).map GlobalIR.Definition.function)
          currentStore evaluationFuel [] term =
          wrapCoreFault (PolyIR.evaluate (PolyIR.eraseDefinitions sourceProgram)
            evaluationFuel [] term) := by
    intro currentStore evaluationFuel term member
    exact functionTable_globalIR_callTerms_pointwise
      (PolyIR.eraseDefinitions sourceProgram) currentStore prefixFragments
      evaluationFuel [] term member
  have globalPrefix : GlobalIR.initializeValues
      ((PolyIR.eraseDefinitions sourceProgram).map GlobalIR.Definition.function)
      (fuel + initializersBefore.length + 2)
      (List.replicate (initializersBefore ++ PolyIR.erase expression :: tail).length none)
      0 initializersBefore = .ok after := by
    rw [functionTable_globalIR_initializeValues_commutes_of_pointwise
      (PolyIR.eraseDefinitions sourceProgram)
      (List.replicate (initializersBefore ++ PolyIR.erase expression :: tail).length none)
      0 (fuel + initializersBefore.length + 2) initializersBefore pointwisePrefix]
    exact prefixSuccess
  exact functionTable_typed_source_initializer_diverges_after_prefix sourceProgram globals
    programTyped initializersBefore tail expression type expressionTyped
    headFragment
    entry fuel after sourceDiverges globalPrefix

/-- Surface faults pass through erasure and the recursive call fragment into
function-only GlobalIR, including the core-fault wrapper. -/
theorem functionTable_globalIR_callFragment_source_fault
    (sourceProgram : Surface.Definitions) (store : GlobalIR.Store)
    (expression : Surface.Expr)
    (fragment : FunctionTableCallFragment (PolyIR.eraseDefinitions sourceProgram)
      (PolyIR.erase expression))
    (fuel : Nat) (environment : List Surface.Value) (fault : PolyIR.Fault)
    (sourceFault : Surface.evaluate sourceProgram fuel environment expression = .error fault) :
    GlobalIR.evaluate ((PolyIR.eraseDefinitions sourceProgram).map GlobalIR.Definition.function)
        store fuel (PolyIR.eraseValues environment) (PolyIR.erase expression) =
      .error (.core fault) := by
  have erasedFault := PolyIR.execution_error_iff.mpr sourceFault
  have correspondence := functionTable_globalIR_callFragment_commutes
    (PolyIR.eraseDefinitions sourceProgram) store fragment fuel (PolyIR.eraseValues environment)
  rw [erasedFault] at correspondence
  exact correspondence

/-- A top-level initializer fault is observable through `GlobalIR.run` when
each initializer belongs to the recursively composed call fragment. -/
theorem functionTable_callTerms_run_reports_initializer_fault
    (definitions : List PolyIR.RuntimeDefinition) (initializers : List PolyIR.Term)
    (entry fuel : Nat) (fault : GlobalIR.Fault)
    (fragments : FunctionTableCallTerms definitions initializers)
    (initializerFault : initializeValuesCore definitions fuel
      (List.replicate initializers.length none) 0 initializers = .error fault) :
    GlobalIR.run ⟨definitions.map GlobalIR.Definition.function, initializers, entry⟩ fuel =
      .error fault := by
  apply functionTable_globalIR_run_reports_initializer_fault definitions initializers
    entry fuel fault
  · intro currentStore evaluationFuel term member
    exact functionTable_globalIR_callTerms_pointwise definitions currentStore fragments
      evaluationFuel [] term member
  · exact initializerFault

private theorem globalIR_mem_append_left {α : Type} (left right : List α)
    {item : α} (member : item ∈ left) : item ∈ left ++ right := by
  induction left with
  | nil => simp at member
  | cons head tail ih =>
      simp only [List.cons_append, List.mem_cons]
      simp only [List.mem_cons] at member
      rcases member with headEq | tailMember
      · exact Or.inl headEq
      · exact Or.inr (ih tailMember)

private theorem globalIR_mem_append_right {α : Type} (left right : List α)
    {item : α} (member : item ∈ right) : item ∈ left ++ right := by
  induction left with
  | nil => simpa using member
  | cons head tail ih =>
      simp only [List.cons_append, List.mem_cons]
      exact Or.inr ih

/-- A fault after any successful initializer prefix is observable through
`GlobalIR.run` when the complete initializer sequence has call-fragment
evidence. The prefix correspondence is derived only for its own elements. -/
theorem functionTable_callTerms_run_reports_initializer_fault_after_prefix
    (definitions : List PolyIR.RuntimeDefinition) (initializersBefore : List PolyIR.Term)
    (head : PolyIR.Term) (tail : List PolyIR.Term) (entry fuel : Nat)
    (after : GlobalIR.Store) (coreFault : PolyIR.Fault)
    (fragments : FunctionTableCallTerms definitions (initializersBefore ++ head :: tail))
    (prefixSuccess : initializeValuesCore definitions
      (fuel + initializersBefore.length + 2)
      (List.replicate (initializersBefore ++ head :: tail).length none) 0
      initializersBefore = .ok after)
    (faultStep : PolyIR.evaluate definitions (fuel + 1) [] head = .error coreFault) :
    GlobalIR.run ⟨definitions.map GlobalIR.Definition.function,
      initializersBefore ++ head :: tail, entry⟩ (fuel + initializersBefore.length + 2) =
      .error (.core coreFault) := by
  have pointwisePrefix : ∀ currentStore evaluationFuel term, term ∈ initializersBefore →
      GlobalIR.evaluate (definitions.map GlobalIR.Definition.function) currentStore
          evaluationFuel [] term =
        wrapCoreFault (PolyIR.evaluate definitions evaluationFuel [] term) := by
    intro currentStore evaluationFuel term member
    have memberAll : term ∈ initializersBefore ++ head :: tail := by
      exact globalIR_mem_append_left initializersBefore (head :: tail) member
    exact functionTable_globalIR_callTerms_pointwise definitions currentStore fragments
      evaluationFuel [] term memberAll
  have globalPrefix : GlobalIR.initializeValues
      (definitions.map GlobalIR.Definition.function)
      (fuel + initializersBefore.length + 2)
      (List.replicate (initializersBefore ++ head :: tail).length none) 0
      initializersBefore = .ok after := by
    rw [functionTable_globalIR_initializeValues_commutes_of_pointwise definitions
      (List.replicate (initializersBefore ++ head :: tail).length none) 0
      (fuel + initializersBefore.length + 2) initializersBefore pointwisePrefix]
    exact prefixSuccess
  have globalFault : GlobalIR.evaluate
      (definitions.map GlobalIR.Definition.function) after (fuel + 1) [] head =
      .error (.core coreFault) := by
    have memberHead : head ∈ initializersBefore ++ head :: tail :=
      globalIR_mem_append_right initializersBefore (head :: tail)
        (List.mem_cons_self head tail)
    have corresponding := functionTable_globalIR_callTerms_pointwise definitions after fragments
      (fuel + 1) [] head memberHead
    rw [faultStep] at corresponding
    exact corresponding
  exact GlobalIR.run_reports_initializer_fault_after_prefix
    ⟨definitions.map GlobalIR.Definition.function,
      initializersBefore ++ head :: tail, entry⟩ fuel initializersBefore head tail after
    (.core coreFault) rfl globalPrefix globalFault

/-- A source initializer fault in the call fragment propagates through the
function-table GlobalIR initializer prefix and program entry. -/
theorem functionTable_sourceFault_run_reports_initializer_fault_after_prefix
    (sourceProgram : Surface.Definitions) (initializersBefore tail : List PolyIR.Term)
    (expression : Surface.Expr) (entry fuel : Nat) (after : GlobalIR.Store)
    (fault : PolyIR.Fault)
    (fragments : FunctionTableCallTerms (PolyIR.eraseDefinitions sourceProgram)
      (initializersBefore ++ PolyIR.erase expression :: tail))
    (prefixSuccess : initializeValuesCore (PolyIR.eraseDefinitions sourceProgram)
      (fuel + initializersBefore.length + 2)
      (List.replicate (initializersBefore ++ PolyIR.erase expression :: tail).length none)
      0 initializersBefore = .ok after)
    (sourceFault : Surface.evaluate sourceProgram (fuel + 1) [] expression = .error fault) :
    GlobalIR.run
      ⟨(PolyIR.eraseDefinitions sourceProgram).map GlobalIR.Definition.function,
        initializersBefore ++ PolyIR.erase expression :: tail, entry⟩
      (fuel + initializersBefore.length + 2) = .error (.core fault) := by
  have erasedFault := PolyIR.execution_error_iff.mpr sourceFault
  exact functionTable_callTerms_run_reports_initializer_fault_after_prefix
    (PolyIR.eraseDefinitions sourceProgram) initializersBefore (PolyIR.erase expression)
    tail entry fuel after fault fragments prefixSuccess erasedFault

/-- Compose a Surface initializer fault with an already established GlobalIR
initializer prefix. The faulting slot is evaluated against the committed
store, and the resulting core fault is reported by the top-level run. -/
theorem functionTable_sourceFault_run_reports_initializer_fault_after_global_prefix
    (sourceProgram : Surface.Definitions) (initializersBefore tail : List PolyIR.Term)
    (expression : Surface.Expr) (entry fuel : Nat) (after : GlobalIR.Store)
    (fault : PolyIR.Fault)
    (fragments : FunctionTableCallTerms (PolyIR.eraseDefinitions sourceProgram)
      (initializersBefore ++ PolyIR.erase expression :: tail))
    (prefixSuccess : GlobalIR.initializeValues
      ((PolyIR.eraseDefinitions sourceProgram).map GlobalIR.Definition.function)
      (fuel + initializersBefore.length + 2)
      (List.replicate (initializersBefore ++ PolyIR.erase expression :: tail).length none)
      0 initializersBefore = .ok after)
    (sourceFault : Surface.evaluate sourceProgram (fuel + 1) [] expression = .error fault) :
    GlobalIR.run
      ⟨(PolyIR.eraseDefinitions sourceProgram).map GlobalIR.Definition.function,
        initializersBefore ++ PolyIR.erase expression :: tail, entry⟩
      (fuel + initializersBefore.length + 2) = .error (.core fault) := by
  have erasedFault := PolyIR.execution_error_iff.mpr sourceFault
  have faultStep : GlobalIR.evaluate
      ((PolyIR.eraseDefinitions sourceProgram).map GlobalIR.Definition.function)
      after (fuel + 1) [] (PolyIR.erase expression) = .error (.core fault) := by
    have correspondence := functionTable_globalIR_callTerms_pointwise
      (PolyIR.eraseDefinitions sourceProgram) after fragments (fuel + 1) []
      (PolyIR.erase expression)
      (globalIR_mem_append_right initializersBefore
        (PolyIR.erase expression :: tail) (by simp))
    have wrappedFault := (wrapCoreFault_error_iff
      (PolyIR.evaluate (PolyIR.eraseDefinitions sourceProgram)
        (fuel + 1) [] (PolyIR.erase expression)) fault).2 erasedFault
    exact correspondence.trans wrappedFault
  exact GlobalIR.run_reports_initializer_fault_after_prefix
    ⟨(PolyIR.eraseDefinitions sourceProgram).map GlobalIR.Definition.function,
      initializersBefore ++ PolyIR.erase expression :: tail, entry⟩
    fuel initializersBefore (PolyIR.erase expression) tail after (.core fault) rfl
    prefixSuccess faultStep

/-- With one unit of fuel an application cannot reach its argument list: its
callee evaluation receives zero fuel and reports out-of-fuel in both IRs. -/
theorem functionTable_globalIR_application_one_fuel_outOfFuel
    (definitions : List PolyIR.RuntimeDefinition) (store : GlobalIR.Store)
    (callee : PolyIR.Term) (arguments : List PolyIR.Term)
    (environment : List PolyIR.Value) :
    GlobalIR.evaluate (definitions.map GlobalIR.Definition.function) store 1 environment
        (.app callee arguments) = .error (.core .outOfFuel) ∧
    PolyIR.evaluate definitions 1 environment (.app callee arguments) = .error .outOfFuel := by
  simp [GlobalIR.evaluate, PolyIR.evaluate, wrapCoreFault,
    Except.bind, Except.pure, Pure.pure, bind, pure]

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

/-- A conditional propagates the same fault from condition evaluation before
it inspects the condition's value or selects a branch. -/
theorem conditional_condition_fault_propagates_to_globalIR
    (sourceProgram : Surface.Definitions) (runtimeProgram : List GlobalIR.Definition)
    (store : GlobalIR.Store) (fuel : Nat) (environment : List Surface.Value)
    (condition yes no : Surface.Expr) (fault : PolyIR.Fault)
    (sourceCondition : Surface.evaluate sourceProgram fuel environment condition = .error fault)
    (runtimeCondition : GlobalIR.evaluate runtimeProgram store fuel
      (PolyIR.eraseValues environment) (PolyIR.erase condition) = .error (.core fault)) :
    Surface.evaluate sourceProgram (fuel + 1) environment (.ite condition yes no) = .error fault ↔
      GlobalIR.evaluate runtimeProgram store (fuel + 1) (PolyIR.eraseValues environment)
        (.ite (PolyIR.erase condition) (PolyIR.erase yes) (PolyIR.erase no)) =
          .error (.core fault) := by
  have sourceFault : Surface.evaluate sourceProgram (fuel + 1) environment
      (.ite condition yes no) = .error fault := by
    change (do
      match ← Surface.evaluate sourceProgram fuel environment condition with
      | .bool true => Surface.evaluate sourceProgram fuel environment yes
      | .bool false => Surface.evaluate sourceProgram fuel environment no
      | _ => .error .wrongShape) = .error fault
    rw [sourceCondition]
    simp [Except.bind, Except.pure, Pure.pure, bind, pure]
  have runtimeFault : GlobalIR.evaluate runtimeProgram store (fuel + 1)
      (PolyIR.eraseValues environment)
      (.ite (PolyIR.erase condition) (PolyIR.erase yes) (PolyIR.erase no)) =
        .error (.core fault) := by
    change (do
      match ← GlobalIR.evaluate runtimeProgram store fuel
        (PolyIR.eraseValues environment) (PolyIR.erase condition) with
      | .bool true => (GlobalIR.evaluate runtimeProgram store fuel (PolyIR.eraseValues environment) (PolyIR.erase yes))
      | .bool false => (GlobalIR.evaluate runtimeProgram store fuel (PolyIR.eraseValues environment) (PolyIR.erase no))
      | _ => .error (.core .wrongShape)) = .error (.core fault)
    rw [runtimeCondition]
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

/-- The polymorphic `Some` constructor preserves a child evaluation fault in
both Surface and erased GlobalIR evaluation. -/
theorem some_child_fault_propagates_to_globalIR
    (sourceProgram : Surface.Definitions) (runtimeProgram : List GlobalIR.Definition)
    (store : GlobalIR.Store) (fuel : Nat) (environment : List Surface.Value)
    (elementType : Surface.Ty) (expression : Surface.Expr) (fault : PolyIR.Fault)
    (sourceChild : Surface.evaluate sourceProgram fuel environment expression = .error fault)
    (runtimeChild : GlobalIR.evaluate runtimeProgram store fuel
      (PolyIR.eraseValues environment) (PolyIR.erase expression) = .error (.core fault)) :
    Surface.evaluate sourceProgram (fuel + 1) environment
        (.some elementType expression) = .error fault ↔
      GlobalIR.evaluate runtimeProgram store (fuel + 1) (PolyIR.eraseValues environment)
        (.some (PolyIR.erase expression)) = .error (.core fault) := by
  have sourceFault : Surface.evaluate sourceProgram (fuel + 1) environment
      (.some elementType expression) = .error fault := by
    change (do
      let value ← Surface.evaluate sourceProgram fuel environment expression
      pure (Surface.Value.some value)) = .error fault
    rw [sourceChild]
    simp [Except.bind, Except.pure, Pure.pure, bind, pure]
  have runtimeFault : GlobalIR.evaluate runtimeProgram store (fuel + 1)
      (PolyIR.eraseValues environment) (.some (PolyIR.erase expression)) =
        .error (.core fault) := by
    change (do
      pure (PolyIR.Value.some (← GlobalIR.evaluate runtimeProgram store fuel
        (PolyIR.eraseValues environment) (PolyIR.erase expression)))) = .error (.core fault)
    rw [runtimeChild]
    simp [Except.bind, Except.pure, Pure.pure, bind, pure]
  exact ⟨fun _ => runtimeFault, fun _ => sourceFault⟩

/-- `Cons` evaluates its head before its tail and preserves a head fault in
both the source evaluator and the erased GlobalIR evaluator. -/
theorem cons_head_fault_propagates_to_globalIR
    (sourceProgram : Surface.Definitions) (runtimeProgram : List GlobalIR.Definition)
    (store : GlobalIR.Store) (fuel : Nat) (environment : List Surface.Value)
    (elementType : Surface.Ty) (head tail : Surface.Expr) (fault : PolyIR.Fault)
    (sourceHead : Surface.evaluate sourceProgram fuel environment head = .error fault)
    (runtimeHead : GlobalIR.evaluate runtimeProgram store fuel
      (PolyIR.eraseValues environment) (PolyIR.erase head) = .error (.core fault)) :
    Surface.evaluate sourceProgram (fuel + 1) environment
        (.cons elementType head tail) = .error fault ↔
      GlobalIR.evaluate runtimeProgram store (fuel + 1) (PolyIR.eraseValues environment)
        (.cons (PolyIR.erase head) (PolyIR.erase tail)) = .error (.core fault) := by
  have sourceFault : Surface.evaluate sourceProgram (fuel + 1) environment
      (.cons elementType head tail) = .error fault := by
    change (do
      let headValue ← Surface.evaluate sourceProgram fuel environment head
      let tailValue ← Surface.evaluate sourceProgram fuel environment tail
      pure (Surface.Value.cons headValue tailValue)) = .error fault
    rw [sourceHead]
    simp [Except.bind, Except.pure, Pure.pure, bind, pure]
  have runtimeFault : GlobalIR.evaluate runtimeProgram store (fuel + 1)
      (PolyIR.eraseValues environment) (.cons (PolyIR.erase head) (PolyIR.erase tail)) =
        .error (.core fault) := by
    change (do
      let headValue ← GlobalIR.evaluate runtimeProgram store fuel
        (PolyIR.eraseValues environment) (PolyIR.erase head)
      let tailValue ← GlobalIR.evaluate runtimeProgram store fuel
        (PolyIR.eraseValues environment) (PolyIR.erase tail)
      pure (PolyIR.Value.cons headValue tailValue)) = .error (.core fault)
    rw [runtimeHead]
    simp [Except.bind, Except.pure, Pure.pure, bind, pure]
  exact ⟨fun _ => runtimeFault, fun _ => sourceFault⟩

/-- After `Cons`'s head succeeds, its tail fault is propagated unchanged by
both evaluators, preserving the constructor's left-to-right order. -/
theorem cons_tail_fault_propagates_to_globalIR
    (sourceProgram : Surface.Definitions) (runtimeProgram : List GlobalIR.Definition)
    (store : GlobalIR.Store) (fuel : Nat) (environment : List Surface.Value)
    (elementType : Surface.Ty) (head tail : Surface.Expr) (headValue : Surface.Value)
    (fault : PolyIR.Fault)
    (sourceHead : Surface.evaluate sourceProgram fuel environment head = .ok headValue)
    (runtimeHead : GlobalIR.evaluate runtimeProgram store fuel
      (PolyIR.eraseValues environment) (PolyIR.erase head) =
        .ok (PolyIR.eraseValue headValue))
    (sourceTail : Surface.evaluate sourceProgram fuel environment tail = .error fault)
    (runtimeTail : GlobalIR.evaluate runtimeProgram store fuel
      (PolyIR.eraseValues environment) (PolyIR.erase tail) = .error (.core fault)) :
    Surface.evaluate sourceProgram (fuel + 1) environment
        (.cons elementType head tail) = .error fault ↔
      GlobalIR.evaluate runtimeProgram store (fuel + 1) (PolyIR.eraseValues environment)
        (.cons (PolyIR.erase head) (PolyIR.erase tail)) = .error (.core fault) := by
  have sourceFault : Surface.evaluate sourceProgram (fuel + 1) environment
      (.cons elementType head tail) = .error fault := by
    change (do
      let headResult ← Surface.evaluate sourceProgram fuel environment head
      let tailResult ← Surface.evaluate sourceProgram fuel environment tail
      pure (Surface.Value.cons headResult tailResult)) = .error fault
    rw [sourceHead, sourceTail]
    simp [Except.bind, Except.pure, Pure.pure, bind, pure]
  have runtimeFault : GlobalIR.evaluate runtimeProgram store (fuel + 1)
      (PolyIR.eraseValues environment) (.cons (PolyIR.erase head) (PolyIR.erase tail)) =
        .error (.core fault) := by
    change (do
      let headResult ← GlobalIR.evaluate runtimeProgram store fuel
        (PolyIR.eraseValues environment) (PolyIR.erase head)
      let tailResult ← GlobalIR.evaluate runtimeProgram store fuel
        (PolyIR.eraseValues environment) (PolyIR.erase tail)
      pure (PolyIR.Value.cons headResult tailResult)) = .error (.core fault)
    rw [runtimeHead, runtimeTail]
    simp [Except.bind, Except.pure, Pure.pure, bind, pure]
  exact ⟨fun _ => runtimeFault, fun _ => sourceFault⟩

/-- A Float binary operation propagates a left-operand fault before evaluating
its right operand in both Surface and GlobalIR. -/
theorem floatBin_left_fault_propagates_to_globalIR
    (sourceProgram : Surface.Definitions) (runtimeProgram : List GlobalIR.Definition)
    (store : GlobalIR.Store) (fuel : Nat) (environment : List Surface.Value)
    (operation : Surface.FloatBinOp) (left right : Surface.Expr) (fault : PolyIR.Fault)
    (sourceLeft : Surface.evaluate sourceProgram fuel environment left = .error fault)
    (runtimeLeft : GlobalIR.evaluate runtimeProgram store fuel
      (PolyIR.eraseValues environment) (PolyIR.erase left) = .error (.core fault)) :
    Surface.evaluate sourceProgram (fuel + 1) environment
        (.floatBin operation left right) = .error fault ↔
      GlobalIR.evaluate runtimeProgram store (fuel + 1) (PolyIR.eraseValues environment)
        (.floatBin operation (PolyIR.erase left) (PolyIR.erase right)) =
          .error (.core fault) := by
  have sourceFault : Surface.evaluate sourceProgram (fuel + 1) environment
      (.floatBin operation left right) = .error fault := by
    change (do
      let leftValue ← Surface.evaluate sourceProgram fuel environment left
      let rightValue ← Surface.evaluate sourceProgram fuel environment right
      match leftValue, rightValue with
      | .float x, .float y => pure (Surface.Value.float (match operation with
          | .add => Float.add x y
          | .sub => Float.sub x y
          | .mul => Float.mul x y
          | .div => Float.div x y))
      | _, _ => .error .wrongShape) = .error fault
    rw [sourceLeft]
    simp [Except.bind, Except.pure, Pure.pure, bind, pure]
  have runtimeFault : GlobalIR.evaluate runtimeProgram store (fuel + 1)
      (PolyIR.eraseValues environment)
      (.floatBin operation (PolyIR.erase left) (PolyIR.erase right)) = .error (.core fault) := by
    change (do
      let leftValue ← GlobalIR.evaluate runtimeProgram store fuel
        (PolyIR.eraseValues environment) (PolyIR.erase left)
      let rightValue ← GlobalIR.evaluate runtimeProgram store fuel
        (PolyIR.eraseValues environment) (PolyIR.erase right)
      match leftValue, rightValue with
      | .float x, .float y => pure (PolyIR.Value.float (GlobalIR.floatBinValue operation x y))
      | _, _ => .error (.core .wrongShape)) = .error (.core fault)
    rw [runtimeLeft]
    simp [Except.bind, Except.pure, Pure.pure, bind, pure]
  exact ⟨fun _ => runtimeFault, fun _ => sourceFault⟩

/-- Once the left Float operand succeeds, a right-operand fault is preserved
in order by both Surface and GlobalIR binary Float evaluation. -/
theorem floatBin_right_fault_propagates_to_globalIR
    (sourceProgram : Surface.Definitions) (runtimeProgram : List GlobalIR.Definition)
    (store : GlobalIR.Store) (fuel : Nat) (environment : List Surface.Value)
    (operation : Surface.FloatBinOp) (left right : Surface.Expr)
    (leftValue : Surface.Value) (leftFloat : Float) (fault : PolyIR.Fault)
    (sourceLeft : Surface.evaluate sourceProgram fuel environment left = .ok leftValue)
    (runtimeLeft : GlobalIR.evaluate runtimeProgram store fuel
      (PolyIR.eraseValues environment) (PolyIR.erase left) =
        .ok (PolyIR.eraseValue leftValue))
    (sourceLeftFloat : leftValue = .float leftFloat)
    (sourceRight : Surface.evaluate sourceProgram fuel environment right = .error fault)
    (runtimeRight : GlobalIR.evaluate runtimeProgram store fuel
      (PolyIR.eraseValues environment) (PolyIR.erase right) = .error (.core fault)) :
    Surface.evaluate sourceProgram (fuel + 1) environment
        (.floatBin operation left right) = .error fault ↔
      GlobalIR.evaluate runtimeProgram store (fuel + 1) (PolyIR.eraseValues environment)
        (.floatBin operation (PolyIR.erase left) (PolyIR.erase right)) =
          .error (.core fault) := by
  subst leftValue
  have sourceFault : Surface.evaluate sourceProgram (fuel + 1) environment
      (.floatBin operation left right) = .error fault := by
    change (do
      let leftResult ← Surface.evaluate sourceProgram fuel environment left
      let rightResult ← Surface.evaluate sourceProgram fuel environment right
      match leftResult, rightResult with
      | .float x, .float y => pure (Surface.Value.float (match operation with
          | .add => Float.add x y
          | .sub => Float.sub x y
          | .mul => Float.mul x y
          | .div => Float.div x y))
      | _, _ => .error .wrongShape) = .error fault
    rw [sourceLeft, sourceRight]
    simp [Except.bind, Except.pure, Pure.pure, bind, pure]
  have runtimeFault : GlobalIR.evaluate runtimeProgram store (fuel + 1)
      (PolyIR.eraseValues environment)
      (.floatBin operation (PolyIR.erase left) (PolyIR.erase right)) = .error (.core fault) := by
    change (do
      let leftResult ← GlobalIR.evaluate runtimeProgram store fuel
        (PolyIR.eraseValues environment) (PolyIR.erase left)
      let rightResult ← GlobalIR.evaluate runtimeProgram store fuel
        (PolyIR.eraseValues environment) (PolyIR.erase right)
      match leftResult, rightResult with
      | .float x, .float y => pure (PolyIR.Value.float (GlobalIR.floatBinValue operation x y))
      | _, _ => .error (.core .wrongShape)) = .error (.core fault)
    rw [runtimeLeft, runtimeRight]
    simp [Except.bind, Except.pure, Pure.pure, bind, pure]
  exact ⟨fun _ => runtimeFault, fun _ => sourceFault⟩

/-- After an `if` condition produces a Boolean, only the selected branch is
evaluated; a fault in that branch agrees between Surface and GlobalIR. -/
theorem conditional_selected_branch_fault_propagates_to_globalIR
    (sourceProgram : Surface.Definitions) (runtimeProgram : List GlobalIR.Definition)
    (store : GlobalIR.Store) (fuel : Nat) (environment : List Surface.Value)
    (condition yes no : Surface.Expr) (selected : Bool) (fault : PolyIR.Fault)
    (sourceCondition : Surface.evaluate sourceProgram fuel environment condition =
      .ok (.bool selected))
    (runtimeCondition : GlobalIR.evaluate runtimeProgram store fuel
      (PolyIR.eraseValues environment) (PolyIR.erase condition) =
        .ok (.bool selected))
    (sourceBranch : Surface.evaluate sourceProgram fuel environment
      (if selected then yes else no) = .error fault)
    (runtimeBranch : GlobalIR.evaluate runtimeProgram store fuel
      (PolyIR.eraseValues environment) (PolyIR.erase (if selected then yes else no)) =
        .error (.core fault)) :
    Surface.evaluate sourceProgram (fuel + 1) environment (.ite condition yes no) =
        .error fault ↔
      GlobalIR.evaluate runtimeProgram store (fuel + 1) (PolyIR.eraseValues environment)
        (.ite (PolyIR.erase condition) (PolyIR.erase yes) (PolyIR.erase no)) =
          .error (.core fault) := by
  have sourceFault : Surface.evaluate sourceProgram (fuel + 1) environment
      (.ite condition yes no) = .error fault := by
    change (do
      match ← Surface.evaluate sourceProgram fuel environment condition with
      | .bool true => Surface.evaluate sourceProgram fuel environment yes
      | .bool false => Surface.evaluate sourceProgram fuel environment no
      | _ => .error .wrongShape) = .error fault
    rw [sourceCondition]
    cases selected <;> simpa [sourceBranch]
  have runtimeFault : GlobalIR.evaluate runtimeProgram store (fuel + 1)
      (PolyIR.eraseValues environment)
      (.ite (PolyIR.erase condition) (PolyIR.erase yes) (PolyIR.erase no)) =
        .error (.core fault) := by
    change (do
      match ← GlobalIR.evaluate runtimeProgram store fuel
        (PolyIR.eraseValues environment) (PolyIR.erase condition) with
      | .bool true => (GlobalIR.evaluate runtimeProgram store fuel
          (PolyIR.eraseValues environment) (PolyIR.erase yes))
      | .bool false => (GlobalIR.evaluate runtimeProgram store fuel
          (PolyIR.eraseValues environment) (PolyIR.erase no))
      | _ => .error (.core .wrongShape)) = .error (.core fault)
    rw [runtimeCondition]
    cases selected <;> simpa [runtimeBranch]
  exact ⟨fun _ => runtimeFault, fun _ => sourceFault⟩

/-- A list match propagates a fault from its scrutinee before inspecting the
list shape or entering either branch. -/
theorem matchList_scrutinee_fault_propagates_to_globalIR
    (sourceProgram : Surface.Definitions) (runtimeProgram : List GlobalIR.Definition)
    (store : GlobalIR.Store) (fuel : Nat) (environment : List Surface.Value)
    (target empty full : Surface.Expr) (fault : PolyIR.Fault)
    (sourceTarget : Surface.evaluate sourceProgram fuel environment target = .error fault)
    (runtimeTarget : GlobalIR.evaluate runtimeProgram store fuel
      (PolyIR.eraseValues environment) (PolyIR.erase target) = .error (.core fault)) :
    Surface.evaluate sourceProgram (fuel + 1) environment
        (.matchList target empty full) = .error fault ↔
      GlobalIR.evaluate runtimeProgram store (fuel + 1) (PolyIR.eraseValues environment)
        (.matchList (PolyIR.erase target) (PolyIR.erase empty) (PolyIR.erase full)) =
          .error (.core fault) := by
  have sourceFault : Surface.evaluate sourceProgram (fuel + 1) environment
      (.matchList target empty full) = .error fault := by
    change (do
      match ← Surface.evaluate sourceProgram fuel environment target with
      | .nil => Surface.evaluate sourceProgram fuel environment empty
      | .cons head tail => Surface.evaluate sourceProgram fuel (head :: tail :: environment) full
      | _ => .error .wrongShape) = .error fault
    rw [sourceTarget]
    simp [Except.bind, Except.pure, Pure.pure, bind, pure]
  have runtimeFault : GlobalIR.evaluate runtimeProgram store (fuel + 1)
      (PolyIR.eraseValues environment)
      (.matchList (PolyIR.erase target) (PolyIR.erase empty) (PolyIR.erase full)) =
        .error (.core fault) := by
    change (do
      match ← GlobalIR.evaluate runtimeProgram store fuel
        (PolyIR.eraseValues environment) (PolyIR.erase target) with
      | .nil => (GlobalIR.evaluate runtimeProgram store fuel
          (PolyIR.eraseValues environment) (PolyIR.erase empty))
      | .cons head tail => (GlobalIR.evaluate runtimeProgram store fuel
          (head :: tail :: PolyIR.eraseValues environment) (PolyIR.erase full))
      | _ => .error (.core .wrongShape)) = .error (.core fault)
    rw [runtimeTarget]
    simp [Except.bind, Except.pure, Pure.pure, bind, pure]
  exact ⟨fun _ => runtimeFault, fun _ => sourceFault⟩

/-- An option match propagates a fault from its scrutinee before inspecting
whether the value is `None` or entering the `Some` branch. -/
theorem matchOption_scrutinee_fault_propagates_to_globalIR
    (sourceProgram : Surface.Definitions) (runtimeProgram : List GlobalIR.Definition)
    (store : GlobalIR.Store) (fuel : Nat) (environment : List Surface.Value)
    (target empty full : Surface.Expr) (fault : PolyIR.Fault)
    (sourceTarget : Surface.evaluate sourceProgram fuel environment target = .error fault)
    (runtimeTarget : GlobalIR.evaluate runtimeProgram store fuel
      (PolyIR.eraseValues environment) (PolyIR.erase target) = .error (.core fault)) :
    Surface.evaluate sourceProgram (fuel + 1) environment
        (.matchOption target empty full) = .error fault ↔
      GlobalIR.evaluate runtimeProgram store (fuel + 1) (PolyIR.eraseValues environment)
        (.matchOption (PolyIR.erase target) (PolyIR.erase empty) (PolyIR.erase full)) =
          .error (.core fault) := by
  have sourceFault : Surface.evaluate sourceProgram (fuel + 1) environment
      (.matchOption target empty full) = .error fault := by
    change (do
      match ← Surface.evaluate sourceProgram fuel environment target with
      | .none => Surface.evaluate sourceProgram fuel environment empty
      | .some value => Surface.evaluate sourceProgram fuel (value :: environment) full
      | _ => .error .wrongShape) = .error fault
    rw [sourceTarget]
    simp [Except.bind, Except.pure, Pure.pure, bind, pure]
  have runtimeFault : GlobalIR.evaluate runtimeProgram store (fuel + 1)
      (PolyIR.eraseValues environment)
      (.matchOption (PolyIR.erase target) (PolyIR.erase empty) (PolyIR.erase full)) =
        .error (.core fault) := by
    change (do
      match ← GlobalIR.evaluate runtimeProgram store fuel
        (PolyIR.eraseValues environment) (PolyIR.erase target) with
      | .none => (GlobalIR.evaluate runtimeProgram store fuel
          (PolyIR.eraseValues environment) (PolyIR.erase empty))
      | .some value => (GlobalIR.evaluate runtimeProgram store fuel
          (value :: PolyIR.eraseValues environment) (PolyIR.erase full))
      | _ => .error (.core .wrongShape)) = .error (.core fault)
    rw [runtimeTarget]
    simp [Except.bind, Except.pure, Pure.pure, bind, pure]
  exact ⟨fun _ => runtimeFault, fun _ => sourceFault⟩

end NLisp
