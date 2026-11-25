namespace NLisp.TypedExpansion

/-! An independent typing certificate language for all runtime NLisp types.
Float literals retain binary64 bits. This module establishes typing only;
it does not give floating point or string operations an evaluation semantics.
The separate NLisp.Core calculus supplies operational theorems for its subset.
-/

inductive Ty where
  | boolean | integer | unit | floating | string | character
  | fn (argument result : Ty)
  | list (element : Ty)
  | option (element : Ty)
  deriving DecidableEq, Repr

inductive Primitive where
  | add | sub | mul | quotient | remainder
  | lt | le | gt | ge | intEq
  | fadd | fsub | fmul | fdiv | flt | fle | fgt | fge | floatEq
  | boolEq | not | stringEq | charEq | append | toFloat | truncate
  deriving DecidableEq, Repr

def binary (input output : Ty) : Ty := .fn input (.fn input output)

def Primitive.type : Primitive → Ty
  | .add | .sub | .mul => binary .integer .integer
  | .quotient | .remainder => binary .integer (.option .integer)
  | .lt | .le | .gt | .ge | .intEq => binary .integer .boolean
  | .fadd | .fsub | .fmul | .fdiv => binary .floating .floating
  | .flt | .fle | .fgt | .fge | .floatEq => binary .floating .boolean
  | .boolEq => binary .boolean .boolean
  | .not => .fn .boolean .boolean
  | .stringEq => binary .string .boolean
  | .charEq => binary .character .boolean
  | .append => binary .string .string
  | .toFloat => .fn .integer .floating
  | .truncate => .fn .floating (.option .integer)

/-- Signed integer division used by the `quotient` builtin. The magnitude
division is Nat division and the sign is applied afterward, so negative
operands truncate toward zero as GMP's `mpz_tdiv_q` does. This function is
only observed through `integerOptional` when the divisor is nonzero. -/
def truncQuotient (left right : Int) : Int :=
  let magnitude := Int.ofNat (left.natAbs / right.natAbs)
  if (left < 0) = (right < 0) then magnitude else -magnitude

/-- Integer option-valued builtin semantics. Division by zero returns None;
remainder is defined from the same truncating quotient, matching `mpz_tdiv_r`
and fixing the remainder sign to the dividend. -/
def integerOptional (operation : Primitive) (left right : Int) : Option Int :=
  if right = 0 then none else
    match operation with
    | .quotient => some (truncQuotient left right)
    | .remainder => some (left - truncQuotient left right * right)
    | _ => none

theorem integerOptional_quotient_defined_iff (left right : Int) :
    (integerOptional .quotient left right).isSome = true ↔ right ≠ 0 := by
  by_cases h : right = 0 <;> simp [integerOptional, h]

theorem integerOptional_remainder_defined_iff (left right : Int) :
    (integerOptional .remainder left right).isSome = true ↔ right ≠ 0 := by
  by_cases h : right = 0 <;> simp [integerOptional, h]

theorem integerOptional_remainder_equation (left right : Int) (nonzero : right ≠ 0) :
    integerOptional .remainder left right =
      some (left - truncQuotient left right * right) := by
  simp [integerOptional, nonzero]

/-- For every nonzero divisor, quotient and remainder are both present and
reconstruct the dividend with the C/GMP truncation convention. -/
theorem integerOptional_division_equation (left right : Int) (nonzero : right ≠ 0) :
    ∃ quotient remainder,
      integerOptional .quotient left right = some quotient ∧
      integerOptional .remainder left right = some remainder ∧
      left = quotient * right + remainder := by
  refine ⟨truncQuotient left right, left - truncQuotient left right * right,
    ?_, ?_, ?_⟩
  · simp [integerOptional, nonzero]
  · exact integerOptional_remainder_equation left right nonzero
  · calc
      left = left - truncQuotient left right * right + truncQuotient left right * right :=
        (Int.sub_add_cancel left (truncQuotient left right * right)).symm
      _ = truncQuotient left right * right +
          (left - truncQuotient left right * right) := Int.add_comm _ _

inductive Member : List Ty → Nat → Ty → Prop where
  | zero : Member (t :: Γ) 0 t
  | succ : Member Γ n t → Member (u :: Γ) (n + 1) t

inductive Var : List Ty → Ty → Type where
  | zero : Var (t :: Γ) t
  | succ : Var Γ t → Var (u :: Γ) t

def Var.index : Var Γ t → Nat
  | .zero => 0
  | .succ v => v.index + 1

theorem Var.member (v : Var Γ t) : Member Γ v.index t := by
  induction v with
  | zero => exact .zero
  | succ _ ih => exact .succ ih

inductive Expr : List Ty → Ty → Type where
  | var : Var Γ t → Expr Γ t
  | bool : Bool → Expr Γ .boolean
  | int : Int → Expr Γ .integer
  | unit : Expr Γ .unit
  | floatBits : UInt64 → Expr Γ .floating
  | str : String → Expr Γ .string
  | char : Char → Expr Γ .character
  | builtin (operation : Primitive) : Expr Γ operation.type
  | lam : Expr (a :: Γ) b → Expr Γ (.fn a b)
  | app : Expr Γ (.fn a b) → Expr Γ a → Expr Γ b
  | ite : Expr Γ .boolean → Expr Γ t → Expr Γ t → Expr Γ t
  | nil : Expr Γ (.list a)
  | cons : Expr Γ a → Expr Γ (.list a) → Expr Γ (.list a)
  | matchList : Expr Γ (.list a) → Expr Γ r → Expr (a :: .list a :: Γ) r → Expr Γ r
  | none : Expr Γ (.option a)
  | some : Expr Γ a → Expr Γ (.option a)
  | matchOption : Expr Γ (.option a) → Expr Γ r → Expr (a :: Γ) r → Expr Γ r
  | fix : Expr (t :: Γ) t → Expr Γ t

abbrev Ren (Γ Δ : List Ty) := {t : Ty} → Var Γ t → Var Δ t
abbrev Sub (Γ Δ : List Ty) := {t : Ty} → Var Γ t → Expr Δ t

def liftRen (rename : Ren Γ Δ) : Ren (a :: Γ) (a :: Δ) :=
  fun v => match v with
    | .zero => .zero
    | .succ w => .succ (rename w)

def Expr.rename (rename : Ren Γ Δ) : Expr Γ t → Expr Δ t
  | .var v => .var (rename v)
  | .bool b => .bool b
  | .int n => .int n
  | .unit => .unit
  | .floatBits bits => .floatBits bits
  | .str s => .str s
  | .char c => .char c
  | .builtin operation => .builtin operation
  | .lam body => .lam (body.rename (liftRen rename))
  | .app f x => .app (f.rename rename) (x.rename rename)
  | .ite c yes no => .ite (c.rename rename) (yes.rename rename) (no.rename rename)
  | .nil => .nil
  | .cons head tail => .cons (head.rename rename) (tail.rename rename)
  | .matchList scrut empty full =>
      .matchList (scrut.rename rename) (empty.rename rename)
        (full.rename (liftRen (liftRen rename)))
  | .none => .none
  | .some value => .some (value.rename rename)
  | .matchOption scrut empty full =>
      .matchOption (scrut.rename rename) (empty.rename rename) (full.rename (liftRen rename))
  | .fix body => .fix (body.rename (liftRen rename))

def liftSub (substitution : Sub Γ Δ) : Sub (a :: Γ) (a :: Δ) :=
  fun v => match v with
    | .zero => .var .zero
    | .succ w => (substitution w).rename (fun x => .succ x)

def Expr.subst (substitution : Sub Γ Δ) : Expr Γ t → Expr Δ t
  | .var v => substitution v
  | .bool b => .bool b
  | .int n => .int n
  | .unit => .unit
  | .floatBits bits => .floatBits bits
  | .str s => .str s
  | .char c => .char c
  | .builtin operation => .builtin operation
  | .lam body => .lam (body.subst (liftSub substitution))
  | .app f x => .app (f.subst substitution) (x.subst substitution)
  | .ite c yes no => .ite (c.subst substitution) (yes.subst substitution) (no.subst substitution)
  | .nil => .nil
  | .cons head tail => .cons (head.subst substitution) (tail.subst substitution)
  | .matchList scrut empty full =>
      .matchList (scrut.subst substitution) (empty.subst substitution)
        (full.subst (liftSub (liftSub substitution)))
  | .none => .none
  | .some value => .some (value.subst substitution)
  | .matchOption scrut empty full =>
      .matchOption (scrut.subst substitution) (empty.subst substitution)
        (full.subst (liftSub substitution))
  | .fix body => .fix (body.subst (liftSub substitution))

def singleHoleSub (value : Expr Γ a) : Sub [a] Γ :=
  fun | .zero => value

def Expr.add (left right : Expr Γ .integer) : Expr Γ .integer :=
  .app (.app (.builtin .add) left) right

/- The erased term retains literal data and primitive identities, but its
type is not an index. HasType is an extrinsic typing derivation for it. -/
inductive Term where
  | var : Nat → Term
  | bool : Bool → Term
  | int : Int → Term
  | unit : Term
  | floatBits : UInt64 → Term
  | str : String → Term
  | char : Char → Term
  | builtin : Primitive → Term
  | lam : Term → Term
  | app : Term → Term → Term
  | ite : Term → Term → Term → Term
  | nil : Term
  | cons : Term → Term → Term
  | matchList : Term → Term → Term → Term
  | none : Term
  | some : Term → Term
  | matchOption : Term → Term → Term → Term
  | fix : Term → Term

inductive HasType : List Ty → Term → Ty → Prop where
  | var : Member Γ index t → HasType Γ (.var index) t
  | bool : HasType Γ (.bool b) .boolean
  | int : HasType Γ (.int n) .integer
  | unit : HasType Γ .unit .unit
  | floatBits : HasType Γ (.floatBits bits) .floating
  | str : HasType Γ (.str s) .string
  | char : HasType Γ (.char c) .character
  | builtin : HasType Γ (.builtin operation) operation.type
  | lam : HasType (a :: Γ) body b → HasType Γ (.lam body) (.fn a b)
  | app : HasType Γ f (.fn a b) → HasType Γ x a → HasType Γ (.app f x) b
  | ite : HasType Γ c .boolean → HasType Γ yes t → HasType Γ no t → HasType Γ (.ite c yes no) t
  | nil : HasType Γ .nil (.list a)
  | cons : HasType Γ head a → HasType Γ tail (.list a) → HasType Γ (.cons head tail) (.list a)
  | matchList : HasType Γ scrut (.list a) → HasType Γ empty r →
      HasType (a :: .list a :: Γ) full r → HasType Γ (.matchList scrut empty full) r
  | none : HasType Γ .none (.option a)
  | some : HasType Γ value a → HasType Γ (.some value) (.option a)
  | matchOption : HasType Γ scrut (.option a) → HasType Γ empty r →
      HasType (a :: Γ) full r → HasType Γ (.matchOption scrut empty full) r
  | fix : HasType (t :: Γ) body t → HasType Γ (.fix body) t

def Expr.erase : Expr Γ t → Term
  | .var v => .var v.index
  | .bool b => .bool b
  | .int n => .int n
  | .unit => .unit
  | .floatBits bits => .floatBits bits
  | .str s => .str s
  | .char c => .char c
  | .builtin operation => .builtin operation
  | .lam body => .lam body.erase
  | .app f x => .app f.erase x.erase
  | .ite c yes no => .ite c.erase yes.erase no.erase
  | .nil => .nil
  | .cons head tail => .cons head.erase tail.erase
  | .matchList scrut empty full => .matchList scrut.erase empty.erase full.erase
  | .none => .none
  | .some value => .some value.erase
  | .matchOption scrut empty full => .matchOption scrut.erase empty.erase full.erase
  | .fix body => .fix body.erase

theorem Expr.hasType (expression : Expr Γ t) : HasType Γ expression.erase t := by
  induction expression with
  | var v => exact .var v.member
  | bool => exact .bool
  | int => exact .int
  | unit => exact .unit
  | floatBits => exact .floatBits
  | str => exact .str
  | char => exact .char
  | builtin => exact .builtin
  | lam _ ih => exact .lam ih
  | app _ _ ihf ihx => exact .app ihf ihx
  | ite _ _ _ ihc ihy ihn => exact .ite ihc ihy ihn
  | nil => exact .nil
  | cons _ _ ihh iht => exact .cons ihh iht
  | matchList _ _ _ ihs ihe ihf => exact .matchList ihs ihe ihf
  | none => exact .none
  | some _ ih => exact .some ih
  | matchOption _ _ _ ihs ihe ihf => exact .matchOption ihs ihe ihf
  | fix _ ih => exact .fix ih

end NLisp.TypedExpansion
