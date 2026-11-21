import NLisp.RuntimeSemantics

namespace NLisp.Named

/- Operational source syntax retains binding identities. Type annotations and
type applications have no runtime effect, and are checked separately against
the original annotated C syntax by ExpansionLowering. -/
inductive Expr where
  | var : Nat → Expr
  | global : Nat → Expr
  | bool : Bool → Expr
  | int : Int → Expr
  | unit : Expr
  | lam : List Nat → Expr → Expr
  | app : Expr → List Expr → Expr
  | ite : Expr → Expr → Expr → Expr
  | add : Expr → Expr → Expr
  | sub : Expr → Expr → Expr
  | mul : Expr → Expr → Expr
  | le : Expr → Expr → Expr
  | intEq : Expr → Expr → Expr
  | letMany : List Nat → List Expr → Expr → Expr
  | begin : Expr → List Expr → Expr
  | nil : Expr
  | cons : Expr → Expr → Expr
  | none : Expr
  | some : Expr → Expr
  | matchList : Expr → Expr → Nat → Nat → Expr → Expr
  | matchOption : Expr → Expr → Nat → Expr → Expr
  deriving Repr

inductive Value where
  | bool : Bool → Value
  | int : Int → Value
  | unit : Value
  | closure : List Nat → Expr → List (Nat × Value) → Value
  | global : Nat → Value
  | nil : Value
  | cons : Value → Value → Value
  | none : Value
  | some : Value → Value

abbrev Environment := List (Nat × Value)
abbrev Definitions := List (List Nat × Expr)

def lookup (id : Nat) : Environment → Option Value
  | [] => none
  | (key, value) :: tail => if key = id then some value else lookup id tail

def bind (ids : List Nat) (values : List Value) : Environment := ids.zip values

mutual
inductive Evaluates (program : Definitions) : Environment → Expr → Value → Prop where
  | var : lookup binderId env = some value → Evaluates program env (.var binderId) value
  | global : program[index]? = some definition →
      Evaluates program env (.global index) (.global index)
  | bool : Evaluates program env (.bool b) (.bool b)
  | int : Evaluates program env (.int n) (.int n)
  | unit : Evaluates program env .unit .unit
  | lam : Evaluates program env (.lam ps body) (.closure ps body env)
  | appClosure : Evaluates program env f (.closure ps body captured) →
      ArgumentsEvaluate program env args values → values.length = ps.length →
      Evaluates program (bind ps values ++ captured) body value →
      Evaluates program env (.app f args) value
  | appGlobal : Evaluates program env f (.global index) →
      ArgumentsEvaluate program env args values → program[index]? = some (ps, body) →
      values.length = ps.length → Evaluates program (bind ps values) body value →
      Evaluates program env (.app f args) value
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
  | letMany : ArgumentsEvaluate program env initializers values → values.length = ids.length →
      Evaluates program (bind ids values ++ env) body value →
      Evaluates program env (.letMany ids initializers body) value
  | begin : Evaluates program env first value → SequenceEvaluates program env rest value result →
      Evaluates program env (.begin first rest) result
  | nil : Evaluates program env .nil .nil
  | cons : Evaluates program env head h → Evaluates program env tail t →
      Evaluates program env (.cons head tail) (.cons h t)
  | none : Evaluates program env .none .none
  | some : Evaluates program env expression value → Evaluates program env (.some expression) (.some value)
  | matchNil : Evaluates program env target .nil → Evaluates program env empty value →
      Evaluates program env (.matchList target empty h t full) value
  | matchCons : Evaluates program env target (.cons head tail) →
      Evaluates program ((h, head) :: (t, tail) :: env) full value →
      Evaluates program env (.matchList target empty h t full) value
  | matchNone : Evaluates program env target .none → Evaluates program env empty value →
      Evaluates program env (.matchOption target empty binderId full) value
  | matchSome : Evaluates program env target (.some item) →
      Evaluates program ((binderId, item) :: env) full value →
      Evaluates program env (.matchOption target empty binderId full) value
inductive ArgumentsEvaluate (program : Definitions) : Environment → List Expr → List Value → Prop where
  | nil : ArgumentsEvaluate program env [] []
  | cons : Evaluates program env head value → ArgumentsEvaluate program env tail values →
      ArgumentsEvaluate program env (head :: tail) (value :: values)
inductive SequenceEvaluates (program : Definitions) : Environment → List Expr → Value → Value → Prop where
  | nil : SequenceEvaluates program env [] value value
  | cons : Evaluates program env head value → SequenceEvaluates program env tail value result →
      SequenceEvaluates program env (head :: tail) previous result
end

end NLisp.Named
