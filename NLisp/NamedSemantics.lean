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
  | float : Float → Expr
  | string : String → Expr
  | character : Char → Expr
  | unit : Expr
  | lam : List Nat → Expr → Expr
  | app : Expr → List Expr → Expr
  | ite : Expr → Expr → Expr → Expr
  | add : Expr → Expr → Expr
  | sub : Expr → Expr → Expr
  | mul : Expr → Expr → Expr
  | le : Expr → Expr → Expr
  | intEq : Expr → Expr → Expr
  | floatBin : Surface.FloatBinOp → Expr → Expr → Expr
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
  | float : Float → Value
  | string : String → Value
  | character : Char → Value
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

/-- Named `letMany` binds exactly the shorter of the identifier and value
rows. Any semantic simulation that erases binder names must therefore carry
an alignment premise; otherwise the Named environment and IR stack differ in
length. -/
theorem bind_length_eq_min (ids : List Nat) (values : List Value) :
    (bind ids values).length = min ids.length values.length := by
  induction ids generalizing values with
  | nil => simp [bind]
  | cons head tail ih =>
      cases values with
      | nil => simp [bind]
      | cons value rest =>
          change Nat.succ (bind tail rest).length =
            min (Nat.succ tail.length) (Nat.succ rest.length)
          rw [ih]
          omega

/-- A `letMany` binding row has one Named environment entry per binder iff
the evaluated initializer/value row is at least as long as the binder row.
The common well-scoped case is equality, but spelling out this weaker iff
makes the truncation behavior of `List.zip` explicit. -/
theorem bind_length_eq_ids_iff (ids : List Nat) (values : List Value) :
    (bind ids values).length = ids.length ↔ ids.length ≤ values.length := by
  rw [bind_length_eq_min]
  omega

/-- An aligned binder/value row is not truncated by `List.zip`. -/
theorem bind_length_of_aligned (ids : List Nat) (values : List Value)
    (aligned : values.length = ids.length) :
    (bind ids values).length = ids.length := by
  induction ids generalizing values with
  | nil => simp [bind] at aligned ⊢
  | cons head tail ih =>
      cases values with
      | nil => simp at aligned
      | cons value rest =>
          simp only [List.length_cons] at aligned
          have tailAligned : rest.length = tail.length := by omega
          change Nat.succ (List.zip tail rest).length = Nat.succ tail.length
          exact congrArg Nat.succ (ih rest tailAligned)

/-- Extending a named environment with an aligned `letMany` binding row does
not change lookups for identities outside the binder list. The length premise
is the same invariant used by `Evaluates.letMany`; keeping it explicit avoids
silently relying on `List.zip` truncation in environment reasoning. -/
theorem lookup_bind_append_of_not_mem
    (identifier : Nat) (ids : List Nat) (values : List Value)
    (environment : Environment)
    (aligned : values.length = ids.length)
    (outside : identifier ∉ ids) :
    lookup identifier (bind ids values ++ environment) =
      lookup identifier environment := by
  induction ids generalizing values with
  | nil => simp [bind]
  | cons head tail ih =>
      cases values with
      | nil => simp at aligned
      | cons value rest =>
          have headNe : head ≠ identifier := by
            intro equal
            apply outside
            simp [equal]
          have tailOutside : identifier ∉ tail := by
            intro member
            apply outside
            simp [member]
          have tailAligned : rest.length = tail.length := by
            simp at aligned
            omega
          change lookup identifier ((head, value) :: (bind tail rest ++ environment)) =
            lookup identifier environment
          simp only [lookup, if_neg headNe]
          exact ih rest tailAligned tailOutside

/-- A lookup of a binder at a given aligned `letMany` row position returns
the value at the same position, provided no earlier binder shadows it. This
is the positional invariant needed to relate identity environments to the
IR's de Bruijn-style value lists. -/
theorem lookup_bind_append_of_get
    (identifier : Nat) (ids : List Nat) (values : List Value)
    (environment : Environment) (index : Nat)
    (aligned : values.length = ids.length)
    (found : ids.get? index = some identifier)
    (notEarlier : identifier ∉ ids.take index) :
    lookup identifier (bind ids values ++ environment) = values.get? index := by
  induction ids generalizing values index with
  | nil => simp at found
  | cons head tail ih =>
      cases values with
      | nil => simp at aligned
      | cons value rest =>
          cases index with
          | zero =>
              simp only [List.get?_cons_zero, Option.some.injEq] at found
              subst identifier
              simp [bind, lookup]
          | succ index =>
              have notHead : identifier ≠ head := by
                intro equal
                subst identifier
                exact notEarlier (by simp)
              have tailNotEarlier : identifier ∉ tail.take index := by
                intro member
                apply notEarlier
                simp [member]
              have tailAligned : rest.length = tail.length := by
                simp at aligned
                omega
              change lookup identifier ((head, value) :: (bind tail rest ++ environment)) =
                rest.get? index
              simp only [lookup, if_neg (Ne.symm notHead)]
              exact ih rest index tailAligned (by simpa using found) tailNotEarlier

mutual
inductive Evaluates (program : Definitions) : Environment → Expr → Value → Prop where
  | var : lookup binderId env = some value → Evaluates program env (.var binderId) value
  | global : program[index]? = some definition →
      Evaluates program env (.global index) (.global index)
  | bool : Evaluates program env (.bool b) (.bool b)
  | int : Evaluates program env (.int n) (.int n)
  | float : Evaluates program env (.float x) (.float x)
  | string : Evaluates program env (.string s) (.string s)
  | character : Evaluates program env (.character c) (.character c)
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
  | floatBin : Evaluates program env left (.float x) → Evaluates program env right (.float y) →
      Evaluates program env (.floatBin op left right) (.float (match op with
        | .add => x.add y | .sub => x.sub y | .mul => x.mul y | .div => x.div y))
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
