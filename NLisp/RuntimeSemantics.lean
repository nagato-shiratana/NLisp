import NLisp.PolyIR

namespace NLisp.PolyIR

/- Independent finite big-step semantics for erased execution terms. -/
mutual
  inductive Evaluates (program : (List RuntimeDefinition)) : List Value → Term → Value → Prop where
    | var : env[index]? = some value → Evaluates program env (.var index) value
    | global : program[index]? = some definition →
        Evaluates program env (.global index) (.global index)
    | bool : Evaluates program env (.bool b) (.bool b)
    | int : Evaluates program env (.int n) (.int n)
    | unit : Evaluates program env .unit .unit
    | lam : Evaluates program env (.lam arity body) (.closure arity body env)
    | appClosure : Evaluates program env f (.closure arity body captured) →
        ArgumentsEvaluate program env args values → values.length = arity →
        Evaluates program (values ++ captured) body value →
        Evaluates program env (.app f args) value
    | appGlobal : Evaluates program env f (.global index) →
        ArgumentsEvaluate program env args values → program[index]? = some definition →
        values.length = definition.arity →
        Evaluates program values definition.body value → Evaluates program env (.app f args) value
    | ifTrue : Evaluates program env c (.bool true) → Evaluates program env yes value →
        Evaluates program env (.ite c yes no) value
    | ifFalse : Evaluates program env c (.bool false) → Evaluates program env no value →
        Evaluates program env (.ite c yes no) value
    | add : Evaluates program env a (.int x) → Evaluates program env b (.int y) →
        Evaluates program env (.add a b) (.int (x + y))
    | sub : Evaluates program env a (.int x) → Evaluates program env b (.int y) →
        Evaluates program env (.sub a b) (.int (x - y))
    | mul : Evaluates program env a (.int x) → Evaluates program env b (.int y) →
        Evaluates program env (.mul a b) (.int (x * y))
    | le : Evaluates program env a (.int x) → Evaluates program env b (.int y) →
        Evaluates program env (.le a b) (.bool (decide (x ≤ y)))
    | intEq : Evaluates program env a (.int x) → Evaluates program env b (.int y) →
        Evaluates program env (.intEq a b) (.bool (x == y))
    | letMany : ArgumentsEvaluate program env initializers values →
        Evaluates program (values ++ env) body value →
        Evaluates program env (.letMany initializers body) value
    | begin : Evaluates program env first value → SequenceEvaluates program env rest value result →
        Evaluates program env (.begin first rest) result
    | nil : Evaluates program env .nil .nil
    | cons : Evaluates program env head h → Evaluates program env tail t →
        Evaluates program env (.cons head tail) (.cons h t)
    | none : Evaluates program env .none .none
    | some : Evaluates program env expression value → Evaluates program env (.some expression) (.some value)
    | matchNil : Evaluates program env target .nil → Evaluates program env empty value →
        Evaluates program env (.matchList target empty full) value
    | matchCons : Evaluates program env target (.cons head tail) →
        Evaluates program (head :: tail :: env) full value →
        Evaluates program env (.matchList target empty full) value
    | matchNone : Evaluates program env target .none → Evaluates program env empty value →
        Evaluates program env (.matchOption target empty full) value
    | matchSome : Evaluates program env target (.some item) →
        Evaluates program (item :: env) full value →
        Evaluates program env (.matchOption target empty full) value
  inductive ArgumentsEvaluate (program : (List RuntimeDefinition)) :
      List Value → List Term → List Value → Prop where
    | nil : ArgumentsEvaluate program env [] []
    | cons : Evaluates program env head value → ArgumentsEvaluate program env tail values →
        ArgumentsEvaluate program env (head :: tail) (value :: values)
  inductive SequenceEvaluates (program : (List RuntimeDefinition)) :
      List Value → List Term → Value → Value → Prop where
    | nil : SequenceEvaluates program env [] value value
    | cons : Evaluates program env head value → SequenceEvaluates program env tail value result →
        SequenceEvaluates program env (head :: tail) previous result
end


end NLisp.PolyIR

