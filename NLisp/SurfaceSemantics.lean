import NLisp.Surface

namespace NLisp.Surface

/- Source-level values retain annotated closures and explicit global type
arguments. This semantics is independent of the erased evaluator. -/
inductive Value where
  | bool : Bool → Value
  | int : Int → Value
  | float : Float → Value
  | string : String → Value
  | character : Char → Value
  | unit : Value
  | closure : List Ty → Ty → Expr → List Value → Value
  | global : Nat → List Ty → Value
  | nil : Value
  | cons : Value → Value → Value
  | none : Value
  | some : Value → Value

abbrev Definitions := List (Signature × Expr)

/- Finite big-step derivations describe terminating executions. Absence of
a derivation is not itself a proved divergence result. Evaluation of globals
shares the entire definition table, permitting self and mutual recursion. -/
mutual
  inductive Evaluates (program : Definitions) : List Value → Expr → Value → Prop where
    | var : env[index]? = some value → Evaluates program env (.var index) value
    | global : program[index]? = some definition →
        Evaluates program env (.global index types) (.global index types)
    | bool : Evaluates program env (.bool b) (.bool b)
    | int : Evaluates program env (.int n) (.int n)
    | float : Evaluates program env (.float x) (.float x)
    | string : Evaluates program env (.string value) (.string value)
    | character : Evaluates program env (.character value) (.character value)
    | floatBin : Evaluates program env left (.float x) →
        Evaluates program env right (.float y) →
        Evaluates program env (.floatBin op left right)
          (.float (match op with
            | .add => Float.add x y
            | .sub => Float.sub x y
            | .mul => Float.mul x y
            | .div => Float.div x y))
    | unit : Evaluates program env .unit .unit
    | lam : Evaluates program env (.lam ps result body) (.closure ps result body env)
    | appClosure : Evaluates program env f (.closure ps result body captured) →
        ArgumentsEvaluate program env args values → values.length = ps.length →
        Evaluates program (values ++ captured) body value →
        Evaluates program env (.app f args) value
    | appGlobal : Evaluates program env f (.global index types) →
        ArgumentsEvaluate program env args values → program[index]? = some (signature, body) →
        values.length = signature.parameters.length →
        Evaluates program values body value → Evaluates program env (.app f args) value
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
        Evaluates program env (.letMany types initializers body) value
    | begin : Evaluates program env first value → SequenceEvaluates program env rest value result →
        Evaluates program env (.begin first rest) result
    | nil : Evaluates program env (.nil t) .nil
    | cons : Evaluates program env head h → Evaluates program env tail t →
        Evaluates program env (.cons type head tail) (.cons h t)
    | none : Evaluates program env (.none t) .none
    | some : Evaluates program env expression value → Evaluates program env (.some t expression) (.some value)
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
  inductive ArgumentsEvaluate (program : Definitions) :
      List Value → List Expr → List Value → Prop where
    | nil : ArgumentsEvaluate program env [] []
    | cons : Evaluates program env head value → ArgumentsEvaluate program env tail values →
        ArgumentsEvaluate program env (head :: tail) (value :: values)
  inductive SequenceEvaluates (program : Definitions) :
      List Value → List Expr → Value → Value → Prop where
    | nil : SequenceEvaluates program env [] value value
    | cons : Evaluates program env head value → SequenceEvaluates program env tail value result →
        SequenceEvaluates program env (head :: tail) previous result
end

end NLisp.Surface
