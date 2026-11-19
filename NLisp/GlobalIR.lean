import NLisp.PolyIR

namespace NLisp.GlobalIR
open PolyIR

/- A global read is represented by a zero-argument getter in the function
table. The current store is passed to evaluation, so a closure created during
initialization never freezes a missing global value in its local environment.
User functions still have one shared, erased body and their original arity. -/
inductive Definition where
  | function : RuntimeDefinition → Definition
  | getter : Nat → Definition

inductive Fault where
  | core : PolyIR.Fault → Fault
  | beforeInitialization : Nat → Fault
  deriving DecidableEq

abbrev Store := List (Option Value)

def readGlobal (store : Store) (slot : Nat) : Except Fault Value :=
  match store[slot]? with
  | some (some value) => .ok value
  | some none => .error (.beforeInitialization slot)
  | none => .error (.core .unbound)

mutual
def evaluate (program : List Definition) (store : Store) : Nat → List Value → Term → Except Fault Value
  | 0, _, _ => .error (.core .outOfFuel)
  | fuel + 1, env, term => do
    match term with
    | .var i => match env[i]? with | some value => pure value | none => .error (.core .unbound)
    | .global i => match program[i]? with | some _ => pure (.global i) | none => .error (.core .unbound)
    | .bool b => pure (.bool b)
    | .int n => pure (.int n)
    | .unit => pure .unit
    | .lam arity body => pure (.closure arity body env)
    | .app f args =>
      let function ← evaluate program store fuel env f
      let values ← evaluateArgs program store fuel env args
      match function with
      | .closure arity body captured =>
        if values.length = arity then evaluate program store fuel (values ++ captured) body
        else .error (.core .wrongArity)
      | .global i =>
        match program[i]? with
        | none => .error (.core .unbound)
        | some (.function definition) =>
          if values.length = definition.arity then evaluate program store fuel values definition.body
          else .error (.core .wrongArity)
        | some (.getter slot) =>
          if values.isEmpty then readGlobal store slot else .error (.core .wrongArity)
      | _ => .error (.core .wrongShape)
    | .ite c yes no =>
      match ← evaluate program store fuel env c with
      | .bool true => evaluate program store fuel env yes
      | .bool false => evaluate program store fuel env no
      | _ => .error (.core .wrongShape)
    | .add a b | .sub a b | .mul a b | .le a b | .intEq a b =>
      let left ← evaluate program store fuel env a
      let right ← evaluate program store fuel env b
      match left, right with
      | .int x, .int y =>
        match term with
        | .add _ _ => pure (.int (x + y))
        | .sub _ _ => pure (.int (x - y))
        | .mul _ _ => pure (.int (x * y))
        | .le _ _ => pure (.bool (decide (x ≤ y)))
        | _ => pure (.bool (x == y))
      | _, _ => .error (.core .wrongShape)
    | .letMany values body =>
      let bindings ← evaluateArgs program store fuel env values
      evaluate program store fuel (bindings ++ env) body
    | .begin first rest =>
      let value ← evaluate program store fuel env first
      evaluateSequence program store fuel env value rest
    | .nil => pure .nil
    | .cons head tail => return .cons (← evaluate program store fuel env head) (← evaluate program store fuel env tail)
    | .none => pure .none
    | .some value => return .some (← evaluate program store fuel env value)
    | .matchList target empty full =>
      match ← evaluate program store fuel env target with
      | .nil => evaluate program store fuel env empty
      | .cons head tail => evaluate program store fuel (head :: tail :: env) full
      | _ => .error (.core .wrongShape)
    | .matchOption target empty full =>
      match ← evaluate program store fuel env target with
      | .none => evaluate program store fuel env empty
      | .some value => evaluate program store fuel (value :: env) full
      | _ => .error (.core .wrongShape)

def evaluateArgs (program : List Definition) (store : Store) : Nat → List Value → List Term → Except Fault (List Value)
  | 0, _, _ => .error (.core .outOfFuel)
  | _ + 1, _, [] => pure []
  | fuel + 1, env, head :: tail => return (← evaluate program store fuel env head) ::
      (← evaluateArgs program store fuel env tail)

def evaluateSequence (program : List Definition) (store : Store) :
    Nat → List Value → Value → List Term → Except Fault Value
  | 0, _, _, _ => .error (.core .outOfFuel)
  | _ + 1, _, value, [] => pure value
  | fuel + 1, env, _, head :: tail => do
    let value ← evaluate program store fuel env head
    evaluateSequence program store fuel env value tail
end

def initializeValues (program : List Definition) : Nat → Store → Nat → List Term → Except Fault Store
  | 0, _, _, _ => .error (.core .outOfFuel)
  | _ + 1, store, _, [] => pure store
  | fuel + 1, store, slot, head :: tail => do
    let value ← evaluate program store fuel [] head
    initializeValues program fuel (store.set slot (some value)) (slot + 1) tail

structure Program where
  definitions : List Definition
  initializers : List Term
  entry : Nat

def run (program : Program) (fuel : Nat) : Except Fault Value := do
  let store ← initializeValues program.definitions fuel (List.replicate program.initializers.length none)
    0 program.initializers
  evaluate program.definitions store fuel [] (.app (.global program.entry) [])

theorem read_initialized {store : Store} {slot : Nat} {value : Value}
    (entry : store[slot]? = some (some value)) : readGlobal store slot = .ok value := by
  simp [readGlobal, entry]

theorem read_uninitialized {store : Store} {slot : Nat} (entry : store[slot]? = some none) :
    readGlobal store slot = .error (.beforeInitialization slot) := by simp [readGlobal, entry]

theorem initialization_length {fuel : Nat}
    (success : initializeValues program fuel store slot expressions = .ok result) : result.length = store.length := by
  induction fuel generalizing store slot expressions with
  | zero => simp [initializeValues] at success
  | succ fuel ih =>
    cases expressions with
    | nil =>
      have same : store = result := by simpa [initializeValues, pure, Except.pure] using success
      simp [same]
    | cons head tail =>
      cases step : evaluate program store fuel [] head with
      | error fault => simp [initializeValues, step, bind, Except.bind] at success
      | ok value =>
        have rest : initializeValues program fuel (store.set slot (some value)) (slot + 1) tail = .ok result := by
          simpa [initializeValues, step, bind, Except.bind] using success
        simpa using ih rest

theorem set_other_lookup (store : Store) (slot index : Nat) (value : Option Value) (different : index ≠ slot) :
    (store.set slot value)[index]? = store[index]? := by
  induction store generalizing slot index with
  | nil => simp [getElem?_def, Nat.not_lt_zero]
  | cons head tail ih =>
    cases slot <;> cases index
    · exact False.elim (different rfl)
    · simp [getElem?_def, Nat.succ_lt_succ_iff]
    · simp [getElem?_def]
    · simpa [getElem?_def, Nat.succ_lt_succ_iff] using ih _ _ (by omega)

theorem initialized_prefix_unchanged {fuel : Nat}
    (success : initializeValues program fuel store slot expressions = .ok result)
    (earlier : index < slot) : result[index]? = store[index]? := by
  induction fuel generalizing store slot expressions with
  | zero => simp [initializeValues] at success
  | succ fuel ih =>
    cases expressions with
    | nil =>
      have same : store = result := by simpa [initializeValues, pure, Except.pure] using success
      simp [same]
    | cons head tail =>
      cases step : evaluate program store fuel [] head with
      | error fault => simp [initializeValues, step, bind, Except.bind] at success
      | ok value =>
        have rest : initializeValues program fuel (store.set slot (some value)) (slot + 1) tail = .ok result := by
          simpa [initializeValues, step, bind, Except.bind] using success
        exact (ih rest (by omega)).trans (set_other_lookup store slot index (some value) (by omega))

theorem initialized_cells_present {fuel : Nat}
    (success : initializeValues program fuel store slot expressions = .ok result)
    (fits : slot + expressions.length ≤ store.length)
    (selected : slot ≤ index ∧ index < slot + expressions.length) :
    ∃ value, result[index]? = some (some value) := by
  induction fuel generalizing store slot expressions with
  | zero => simp [initializeValues] at success
  | succ fuel ih =>
    cases expressions with
    | nil => simp only [List.length_nil, Nat.add_zero] at selected; omega
    | cons head tail =>
      cases step : evaluate program store fuel [] head with
      | error fault => simp [initializeValues, step, bind, Except.bind] at success
      | ok value =>
        have rest : initializeValues program fuel (store.set slot (some value)) (slot + 1) tail = .ok result := by
          simpa [initializeValues, step, bind, Except.bind] using success
        simp only [List.length_cons] at fits selected
        by_cases current : index = slot
        · subst index
          have earlier := initialized_prefix_unchanged rest (index := slot) (by omega)
          refine ⟨value, earlier.trans ?_⟩
          have bound : slot < store.length := by omega
          simp only [getElem?_def, List.length_set, dif_pos bound, Option.some.injEq]
          exact List.get_set_eq store slot (some value) (by simpa using bound)
        · apply ih rest
          · simpa only [List.length_set] using (show slot + 1 + tail.length ≤ store.length by omega)
          · constructor <;> omega

end NLisp.GlobalIR
