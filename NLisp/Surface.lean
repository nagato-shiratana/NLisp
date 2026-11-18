import NLisp.TypedExpansion
import Lean

namespace NLisp.Surface

/- Expanded, name-resolved syntax. Term variables use de Bruijn indices;
type variables use indices local to the enclosing generic definition.
Parameter zero is the first source parameter, including parallel let. -/
inductive Ty where
  | boolean | integer | unit
  | var : Nat → Ty
  | fn : List Ty → Ty → Ty
  | list : Ty → Ty
  | option : Ty → Ty
  deriving Repr

def Ty.wellFormed (count : Nat) : Ty → Prop
  | .var i => i < count
  | .fn args result => (∀ t ∈ args, t.wellFormed count) ∧ result.wellFormed count
  | .list t | .option t => t.wellFormed count
  | _ => True

/- Substitution removes the definition's quantified prefix. Caller variables
remain rigid. Arity and well-formedness are checked before instantiation. -/
mutual
def Ty.instantiate (arguments : List Ty) (type : Ty) : Ty :=
  match type with
  | .var i => (arguments[i]?).getD (.var (i - arguments.length))
  | .fn args result => .fn (instantiateTypes arguments args) (result.instantiate arguments)
  | .list t => .list (t.instantiate arguments)
  | .option t => .option (t.instantiate arguments)
  | t => t
termination_by sizeOf type
decreasing_by all_goals simp_wf; omega

def instantiateTypes (arguments : List Ty) (types : List Ty) : List Ty :=
  match types with
  | [] => []
  | t :: ts => t.instantiate arguments :: instantiateTypes arguments ts
termination_by sizeOf types
decreasing_by all_goals simp_wf; omega
end

structure Signature where
  typeArity : Nat
  parameters : List Ty
  result : Ty
  deriving Repr

def Signature.wellFormed (s : Signature) : Prop :=
  (∀ t ∈ s.parameters, t.wellFormed s.typeArity) ∧ s.result.wellFormed s.typeArity

inductive Expr where
  | var : Nat → Expr
  | global : Nat → List Ty → Expr
  | bool : Bool → Expr
  | int : Int → Expr
  | unit : Expr
  | lam : List Ty → Ty → Expr → Expr
  | app : Expr → List Expr → Expr
  | ite : Expr → Expr → Expr → Expr
  | add : Expr → Expr → Expr
  | sub : Expr → Expr → Expr
  | mul : Expr → Expr → Expr
  | le : Expr → Expr → Expr
  | intEq : Expr → Expr → Expr
  | letMany : List Ty → List Expr → Expr → Expr
  | begin : Expr → List Expr → Expr
  | nil : Ty → Expr
  | cons : Ty → Expr → Expr → Expr
  | none : Ty → Expr
  | some : Ty → Expr → Expr
  | matchList : Expr → Expr → Expr → Expr
  | matchOption : Expr → Expr → Expr → Expr
  deriving Repr

/- Global function bodies are checked with only their parameters in the
local context; top-level captures must first become explicit global inputs.
All global signatures are available while checking recursive bodies. -/
mutual
  inductive HasType (globals : List Signature) (typeCount : Nat) : List Ty → Expr → Ty → Prop where
    | var : Γ[index]? = some t → HasType globals typeCount Γ (.var index) t
    | global : globals[index]? = some signature →
        arguments.length = signature.typeArity →
        (∀ t ∈ arguments, t.wellFormed typeCount) → signature.wellFormed →
        HasType globals typeCount Γ (.global index arguments)
          (.fn (signature.parameters.map (Ty.instantiate arguments))
            (signature.result.instantiate arguments))
    | bool : HasType globals typeCount Γ (.bool b) .boolean
    | int : HasType globals typeCount Γ (.int n) .integer
    | unit : HasType globals typeCount Γ .unit .unit
    | lam : (∀ t ∈ parameters, t.wellFormed typeCount) → result.wellFormed typeCount →
        HasType globals typeCount (parameters ++ Γ) body result →
        HasType globals typeCount Γ (.lam parameters result body) (.fn parameters result)
    | app : HasType globals typeCount Γ f (.fn parameters result) →
        ArgsHaveTypes globals typeCount Γ args parameters →
        HasType globals typeCount Γ (.app f args) result
    | ite : HasType globals typeCount Γ c .boolean → HasType globals typeCount Γ yes t →
        HasType globals typeCount Γ no t → HasType globals typeCount Γ (.ite c yes no) t
    | add : HasType globals typeCount Γ a .integer → HasType globals typeCount Γ b .integer →
        HasType globals typeCount Γ (.add a b) .integer
    | sub : HasType globals typeCount Γ a .integer → HasType globals typeCount Γ b .integer →
        HasType globals typeCount Γ (.sub a b) .integer
    | mul : HasType globals typeCount Γ a .integer → HasType globals typeCount Γ b .integer →
        HasType globals typeCount Γ (.mul a b) .integer
    | le : HasType globals typeCount Γ a .integer → HasType globals typeCount Γ b .integer →
        HasType globals typeCount Γ (.le a b) .boolean
    | intEq : HasType globals typeCount Γ a .integer → HasType globals typeCount Γ b .integer →
        HasType globals typeCount Γ (.intEq a b) .boolean
    | letMany : (∀ t ∈ types, t.wellFormed typeCount) →
        ArgsHaveTypes globals typeCount Γ initializers types →
        HasType globals typeCount (types ++ Γ) body result →
        HasType globals typeCount Γ (.letMany types initializers body) result
    | begin : HasType globals typeCount Γ first t →
        SequenceHasType globals typeCount Γ rest t result →
        HasType globals typeCount Γ (.begin first rest) result
    | nil : t.wellFormed typeCount → HasType globals typeCount Γ (.nil t) (.list t)
    | cons : t.wellFormed typeCount → HasType globals typeCount Γ head t →
        HasType globals typeCount Γ tail (.list t) →
        HasType globals typeCount Γ (.cons t head tail) (.list t)
    | none : t.wellFormed typeCount → HasType globals typeCount Γ (.none t) (.option t)
    | some : t.wellFormed typeCount → HasType globals typeCount Γ value t →
        HasType globals typeCount Γ (.some t value) (.option t)
    | matchList : HasType globals typeCount Γ target (.list t) →
        HasType globals typeCount Γ empty result →
        HasType globals typeCount (t :: .list t :: Γ) full result →
        HasType globals typeCount Γ (.matchList target empty full) result
    | matchOption : HasType globals typeCount Γ target (.option t) →
        HasType globals typeCount Γ empty result → HasType globals typeCount (t :: Γ) full result →
        HasType globals typeCount Γ (.matchOption target empty full) result
  inductive ArgsHaveTypes (globals : List Signature) (typeCount : Nat) :
      List Ty → List Expr → List Ty → Prop where
    | nil : ArgsHaveTypes globals typeCount Γ [] []
    | cons : HasType globals typeCount Γ e t → ArgsHaveTypes globals typeCount Γ es ts →
        ArgsHaveTypes globals typeCount Γ (e :: es) (t :: ts)
  inductive SequenceHasType (globals : List Signature) (typeCount : Nat) :
      List Ty → List Expr → Ty → Ty → Prop where
    | nil : SequenceHasType globals typeCount Γ [] t t
    | cons : HasType globals typeCount Γ e t → SequenceHasType globals typeCount Γ es t result →
        SequenceHasType globals typeCount Γ (e :: es) previous result
end

end NLisp.Surface
