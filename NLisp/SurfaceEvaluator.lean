import NLisp.SurfaceSemantics
import NLisp.PolyIR

namespace NLisp.Surface

/- Annotated source interpreter. Type arguments remain in global values;
   no type substitution or specialization is performed during execution. -/
mutual
  def evaluate (program : Definitions) : Nat → List Value → Expr → Except NLisp.PolyIR.Fault Value
    | 0, _, _ => .error .outOfFuel
    | fuel + 1, env, term => do
      match term with
      | .var i => match env[i]? with | some v => pure v | none => .error .unbound
      | .global i types => match program[i]? with | some _ => pure (.global i types) | none => .error .unbound
      | .bool b => pure (.bool b)
      | .int n => pure (.int n)
      | .float x => pure (.float x)
      | .string value => pure (.string value)
      | .character value => pure (.character value)
      | .floatBin op left right => do
        let leftValue ← evaluate program fuel env left
        let rightValue ← evaluate program fuel env right
        match leftValue, rightValue with
        | .float x, .float y =>
          pure (.float (match op with
            | .add => Float.add x y
            | .sub => Float.sub x y
            | .mul => Float.mul x y
            | .div => Float.div x y))
        | _, _ => .error .wrongShape
      | .unit => pure .unit
      | .lam parameters result body => pure (.closure parameters result body env)
      | .app f args =>
        let function ← evaluate program fuel env f
        let values ← evaluateArgs program fuel env args
        match function with
        | .closure parameters _ body captured =>
          if values.length = parameters.length then evaluate program fuel (values ++ captured) body
          else .error .wrongArity
        | .global i _ =>
          match program[i]? with
          | none => .error .unbound
          | some definition =>
            if values.length = definition.1.parameters.length then evaluate program fuel values definition.2
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
      | .letMany _ values body =>
        let bindings ← evaluateArgs program fuel env values
        evaluate program fuel (bindings ++ env) body
      | .begin first rest =>
        let value ← evaluate program fuel env first
        evaluateSequence program fuel env value rest
      | .nil _ => pure .nil
      | .cons _ head tail =>
        let h ← evaluate program fuel env head
        let t ← evaluate program fuel env tail
        pure (.cons h t)
      | .none _ => pure .none
      | .some _ value => return .some (← evaluate program fuel env value)
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
  def evaluateArgs (program : Definitions) : Nat → List Value → List Expr → Except NLisp.PolyIR.Fault (List Value)
    | 0, _, _ => .error .outOfFuel
    | _ + 1, _, [] => pure []
    | fuel + 1, env, head :: tail => do
      let value ← evaluate program fuel env head
      let values ← evaluateArgs program fuel env tail
      pure (value :: values)
  def evaluateSequence (program : Definitions) : Nat → List Value → Value → List Expr → Except NLisp.PolyIR.Fault Value
    | 0, _, _, _ => .error .outOfFuel
    | _ + 1, _, value, [] => pure value
    | fuel + 1, env, _, head :: tail => do
      let value ← evaluate program fuel env head
      evaluateSequence program fuel env value tail
end

end NLisp.Surface

