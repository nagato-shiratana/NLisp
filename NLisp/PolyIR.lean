import NLisp.Surface

namespace NLisp.PolyIR
open Surface

/- The execution IR has no types or type applications. Its functions retain
their original arity: zero-argument functions are not encoded as Unit lambdas.
This initial backend uses a common tagged value representation. -/
inductive Term where
  | var : Nat → Term
  | global : Nat → Term
  | bool : Bool → Term
  | int : Int → Term
  | unit : Term
  | lam : Nat → Term → Term
  | app : Term → List Term → Term
  | ite : Term → Term → Term → Term
  | add : Term → Term → Term
  | sub : Term → Term → Term
  | mul : Term → Term → Term
  | le : Term → Term → Term
  | intEq : Term → Term → Term
  | letMany : List Term → Term → Term
  | begin : Term → List Term → Term
  | nil : Term
  | cons : Term → Term → Term
  | none : Term
  | some : Term → Term
  | matchList : Term → Term → Term → Term
  | matchOption : Term → Term → Term → Term
  deriving Repr

/- Count only recursive syntax nodes. The default sizeOf also counts the
numeric magnitude of integer literals; using that magnitude as the kernel's
termination measure can make checking a short literal prohibitively costly.
The nested recursors are used only in termination proofs, so their lack of
native code generation in Lean 4.8 does not affect executable erasure. -/
macro "source_nodes_using " recursor:term : term => `(
  $recursor (motive_1 := fun _ => Nat) (motive_2 := fun _ => Nat)
    (fun _ => 1) (fun _ _ => 1) (fun _ => 1) (fun _ => 1) 1
    (fun _ _ _ body => 1 + body)
    (fun _ _ f args => 1 + f + args)
    (fun _ _ _ c y n => 1 + c + y + n)
    (fun _ _ a b => 1 + a + b)
    (fun _ _ a b => 1 + a + b)
    (fun _ _ a b => 1 + a + b)
    (fun _ _ a b => 1 + a + b)
    (fun _ _ a b => 1 + a + b)
    (fun _ _ _ values body => 1 + values + body)
    (fun _ _ first rest => 1 + first + rest)
    (fun _ => 1) (fun _ _ _ head tail => 1 + head + tail)
    (fun _ => 1) (fun _ _ value => 1 + value)
    (fun _ _ _ target empty full => 1 + target + empty + full)
    (fun _ _ _ target empty full => 1 + target + empty + full)
    0 (fun _ _ head tail => 1 + head + tail))

noncomputable def sourceNodes (expression : Surface.Expr) : Nat :=
  (source_nodes_using Surface.Expr.rec) expression

noncomputable def sourceListNodes (expressions : List Surface.Expr) : Nat :=
  (source_nodes_using Surface.Expr.rec_1) expressions

mutual
def erase (expression : Surface.Expr) : Term :=
  match expression with
  | .var i => .var i
  | .global i _ => .global i
  | .bool b => .bool b
  | .int n => .int n
  | .unit => .unit
  | .lam args _ body => .lam args.length (erase body)
  | .app f args => .app (erase f) (eraseList args)
  | .ite c yes no => .ite (erase c) (erase yes) (erase no)
  | .add a b => .add (erase a) (erase b)
  | .sub a b => .sub (erase a) (erase b)
  | .mul a b => .mul (erase a) (erase b)
  | .le a b => .le (erase a) (erase b)
  | .intEq a b => .intEq (erase a) (erase b)
  | .letMany _ values body => .letMany (eraseList values) (erase body)
  | .begin first rest => .begin (erase first) (eraseList rest)
  | .nil _ => .nil
  | .cons _ head tail => .cons (erase head) (erase tail)
  | .none _ => .none
  | .some _ value => .some (erase value)
  | .matchList target empty full => .matchList (erase target) (erase empty) (erase full)
  | .matchOption target empty full => .matchOption (erase target) (erase empty) (erase full)
termination_by sourceNodes expression
decreasing_by all_goals simp_wf; simp only [sourceNodes, sourceListNodes]; omega

def eraseList (expressions : List Surface.Expr) : List Term :=
  match expressions with
  | [] => []
  | e :: es => erase e :: eraseList es
termination_by sourceListNodes expressions
decreasing_by all_goals simp_wf; simp only [sourceNodes, sourceListNodes]; omega
end

/- A proof-carrying IR node retains its full polymorphic source term. This
is a checked representation, not yet an inference/elaboration algorithm. -/
structure CheckedExpr (globals : List Signature) (typeCount : Nat) (context : List Ty) (type : Ty) where
  expression : Surface.Expr
  typing : HasType globals typeCount context expression type

structure Definition (globals : List Signature) (signature : Signature) where
  signature_valid : signature.wellFormed
  body : CheckedExpr globals signature.typeArity signature.parameters signature.result

structure Program where
  signatures : List Signature
  definitions : (index : Fin signatures.length) → Definition signatures signatures[index]

inductive Value where
  | bool : Bool → Value
  | int : Int → Value
  | unit : Value
  | closure : Nat → Term → List Value → Value
  | global : Nat → Value
  | nil : Value
  | cons : Value → Value → Value
  | none : Value
  | some : Value → Value
  deriving Repr

structure RuntimeDefinition where
  arity : Nat
  body : Term

def Program.erase (p : Program) : List RuntimeDefinition :=
  (List.range p.signatures.length).map (fun index =>
    if h : index < p.signatures.length then
      RuntimeDefinition.mk (p.signatures[index]).parameters.length
        (NLisp.PolyIR.erase (p.definitions ⟨index, h⟩).body.expression)
    else RuntimeDefinition.mk 0 .unit)

inductive Fault where
  | outOfFuel | unbound | wrongShape | wrongArity
  deriving DecidableEq, Repr

/- Fuel bounds derivation depth, not total execution steps. Exhaustion is
Unknown, never evidence of divergence. EvalArgs fixes left-to-right order;
parallel-let initializers all see the original environment. -/
mutual
  def evaluate (program : List RuntimeDefinition) : Nat → List Value → Term → Except Fault Value
    | 0, _, _ => .error .outOfFuel
    | fuel + 1, env, term => do
      match term with
      | .var i => match env[i]? with | some v => pure v | none => .error .unbound
      | .global i => match program[i]? with | some _ => pure (.global i) | none => .error .unbound
      | .bool b => pure (.bool b)
      | .int n => pure (.int n)
      | .unit => pure .unit
      | .lam arity body => pure (.closure arity body env)
      | .app f args =>
        let function ← evaluate program fuel env f
        let values ← evaluateArgs program fuel env args
        match function with
        | .closure arity body captured =>
          if values.length = arity then evaluate program fuel (values ++ captured) body
          else .error .wrongArity
        | .global i =>
          match program[i]? with
          | none => .error .unbound
          | some definition =>
            if values.length = definition.arity then evaluate program fuel values definition.body
            else .error .wrongArity
        | _ => .error .wrongShape
      | .ite c yes no =>
        match ← evaluate program fuel env c with
        | .bool true => evaluate program fuel env yes
        | .bool false => evaluate program fuel env no
        | _ => .error .wrongShape
      | .add a b | .sub a b | .mul a b | .le a b | .intEq a b =>
        let left ← evaluate program fuel env a
        let right ← evaluate program fuel env b
        match left, right with
        | .int x, .int y =>
          match term with
          | .add _ _ => pure (.int (x + y))
          | .sub _ _ => pure (.int (x - y))
          | .mul _ _ => pure (.int (x * y))
          | .le _ _ => pure (.bool (decide (x ≤ y)))
          | _ => pure (.bool (x == y))
        | _, _ => .error .wrongShape
      | .letMany values body =>
        let bindings ← evaluateArgs program fuel env values
        evaluate program fuel (bindings ++ env) body
      | .begin first rest =>
        let value ← evaluate program fuel env first
        evaluateSequence program fuel env value rest
      | .nil => pure .nil
      | .cons head tail =>
        let h ← evaluate program fuel env head
        let t ← evaluate program fuel env tail
        pure (.cons h t)
      | .none => pure .none
      | .some value => return .some (← evaluate program fuel env value)
      | .matchList target empty full =>
        match ← evaluate program fuel env target with
        | .nil => evaluate program fuel env empty
        | .cons head tail => evaluate program fuel (head :: tail :: env) full
        | _ => .error .wrongShape
      | .matchOption target empty full =>
        match ← evaluate program fuel env target with
        | .none => evaluate program fuel env empty
        | .some value => evaluate program fuel (value :: env) full
        | _ => .error .wrongShape
  def evaluateArgs (program : List RuntimeDefinition) : Nat → List Value → List Term → Except Fault (List Value)
    | 0, _, _ => .error .outOfFuel
    | _ + 1, _, [] => pure []
    | fuel + 1, env, head :: tail => do
      let value ← evaluate program fuel env head
      let values ← evaluateArgs program fuel env tail
      pure (value :: values)
  def evaluateSequence (program : List RuntimeDefinition) : Nat → List Value → Value → List Term → Except Fault Value
    | 0, _, _, _ => .error .outOfFuel
    | _ + 1, _, value, [] => pure value
    | fuel + 1, env, _, head :: tail => do
      let value ← evaluate program fuel env head
      evaluateSequence program fuel env value tail
end

theorem erase_type_arguments (index : Nat) (a b : List Ty) :
    erase (.global index a) = erase (.global index b) := by simp [erase]

theorem checked_expression_has_type (e : CheckedExpr globals n Γ t) :
    HasType globals n Γ e.expression t := e.typing

end NLisp.PolyIR
