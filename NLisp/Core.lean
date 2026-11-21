namespace NLisp

/-! # NLisp-Core

An intrinsically typed core calculus for NLisp 0.2.  The type index on
`Expr Γ t` makes ill-typed core terms unrepresentable.  `Step` relates only
terms with the same type index, so preservation is enforced by the Lean
kernel.  The `progress` theorem proves that every closed term is a value or
can take a step.
-/

inductive Ty where
  | boolean
  | integer
  | unit
  | fn (arg result : Ty)
  | list (element : Ty)
  | option (element : Ty)
  deriving DecidableEq, Repr

inductive Var : List Ty → Ty → Type where
  | zero : Var (t :: Γ) t
  | succ : Var Γ t → Var (u :: Γ) t

inductive Expr : List Ty → Ty → Type where
  | var : Var Γ t → Expr Γ t
  | bool : Bool → Expr Γ .boolean
  | int : Int → Expr Γ .integer
  | unit : Expr Γ .unit
  | lam : Expr (a :: Γ) b → Expr Γ (.fn a b)
  | app : Expr Γ (.fn a b) → Expr Γ a → Expr Γ b
  | ite : Expr Γ .boolean → Expr Γ t → Expr Γ t → Expr Γ t
  | add : Expr Γ .integer → Expr Γ .integer → Expr Γ .integer
  | sub : Expr Γ .integer → Expr Γ .integer → Expr Γ .integer
  | mul : Expr Γ .integer → Expr Γ .integer → Expr Γ .integer
  | eqInt : Expr Γ .integer → Expr Γ .integer → Expr Γ .boolean
  | leq : Expr Γ .integer → Expr Γ .integer → Expr Γ .boolean
  | nil : Expr Γ (.list a)
  | cons : Expr Γ a → Expr Γ (.list a) → Expr Γ (.list a)
  | matchList :
      Expr Γ (.list a) →
      Expr Γ r →
      Expr (a :: .list a :: Γ) r →
      Expr Γ r
  | none : Expr Γ (.option a)
  | some : Expr Γ a → Expr Γ (.option a)
  | matchOption :
      Expr Γ (.option a) →
      Expr Γ r →
      Expr (a :: Γ) r →
      Expr Γ r
  | fix : Expr (t :: Γ) t → Expr Γ t

abbrev Ren (Γ Δ : List Ty) := {t : Ty} → Var Γ t → Var Δ t
abbrev Sub (Γ Δ : List Ty) := {t : Ty} → Var Γ t → Expr Δ t

def liftRen (ρ : Ren Γ Δ) : Ren (a :: Γ) (a :: Δ) :=
  fun v =>
    match v with
    | .zero => .zero
    | .succ v => .succ (ρ v)

def Expr.rename (ρ : Ren Γ Δ) : Expr Γ t → Expr Δ t
  | .var v => .var (ρ v)
  | .bool b => .bool b
  | .int n => .int n
  | .unit => .unit
  | .lam body => .lam (body.rename (liftRen ρ))
  | .app f x => .app (f.rename ρ) (x.rename ρ)
  | .ite c yes no => .ite (c.rename ρ) (yes.rename ρ) (no.rename ρ)
  | .add left right => .add (left.rename ρ) (right.rename ρ)
  | .sub left right => .sub (left.rename ρ) (right.rename ρ)
  | .mul left right => .mul (left.rename ρ) (right.rename ρ)
  | .eqInt left right => .eqInt (left.rename ρ) (right.rename ρ)
  | .leq left right => .leq (left.rename ρ) (right.rename ρ)
  | .nil => .nil
  | .cons head tail => .cons (head.rename ρ) (tail.rename ρ)
  | .matchList scrut nilCase consCase =>
      .matchList
        (scrut.rename ρ)
        (nilCase.rename ρ)
        (consCase.rename (liftRen (liftRen ρ)))
  | .none => .none
  | .some value => .some (value.rename ρ)
  | .matchOption scrut noneCase someCase =>
      .matchOption
        (scrut.rename ρ)
        (noneCase.rename ρ)
        (someCase.rename (liftRen ρ))
  | .fix body => .fix (body.rename (liftRen ρ))

def liftSub (σ : Sub Γ Δ) : Sub (a :: Γ) (a :: Δ) :=
  fun v =>
    match v with
    | .zero => .var .zero
    | .succ v => (σ v).rename (fun w => .succ w)

theorem liftSub_keeps_bound (σ : Sub Γ Δ) :
    liftSub (a := a) σ .zero = (.var .zero : Expr (a :: Δ) a) := rfl

theorem liftSub_shifts_hole (σ : Sub Γ Δ) (v : Var Γ t) :
    liftSub (a := a) σ (.succ v) =
      (σ v).rename (fun w => .succ w) := rfl

def Expr.subst (σ : Sub Γ Δ) : Expr Γ t → Expr Δ t
  | .var v => σ v
  | .bool b => .bool b
  | .int n => .int n
  | .unit => .unit
  | .lam body => .lam (body.subst (liftSub σ))
  | .app f x => .app (f.subst σ) (x.subst σ)
  | .ite c yes no => .ite (c.subst σ) (yes.subst σ) (no.subst σ)
  | .add left right => .add (left.subst σ) (right.subst σ)
  | .sub left right => .sub (left.subst σ) (right.subst σ)
  | .mul left right => .mul (left.subst σ) (right.subst σ)
  | .eqInt left right => .eqInt (left.subst σ) (right.subst σ)
  | .leq left right => .leq (left.subst σ) (right.subst σ)
  | .nil => .nil
  | .cons head tail => .cons (head.subst σ) (tail.subst σ)
  | .matchList scrut nilCase consCase =>
      .matchList
        (scrut.subst σ)
        (nilCase.subst σ)
        (consCase.subst (liftSub (liftSub σ)))
  | .none => .none
  | .some value => .some (value.subst σ)
  | .matchOption scrut noneCase someCase =>
      .matchOption
        (scrut.subst σ)
        (noneCase.subst σ)
        (someCase.subst (liftSub σ))
  | .fix body => .fix (body.subst (liftSub σ))

theorem subst_under_lambda (σ : Sub Γ Δ) (body : Expr (a :: Γ) t) :
    Expr.subst σ (.lam body) = .lam (body.subst (liftSub σ)) := rfl

def oneSub (value : Expr Γ a) : Sub (a :: Γ) Γ :=
  fun v =>
    match v with
    | .zero => value
    | .succ v => .var v

def Expr.instantiate (body : Expr (a :: Γ) t) (value : Expr Γ a) : Expr Γ t :=
  body.subst (oneSub value)

def twoSub (head : Expr Γ a) (tail : Expr Γ (.list a)) :
    Sub (a :: .list a :: Γ) Γ :=
  fun v =>
    match v with
    | .zero => head
    | .succ .zero => tail
    | .succ (.succ v) => .var v

def Expr.instantiateCons
    (body : Expr (a :: .list a :: Γ) t)
    (head : Expr Γ a)
    (tail : Expr Γ (.list a)) : Expr Γ t :=
  body.subst (twoSub head tail)

/-! ## Typed macro expansion

   A macro template is represented by a core expression whose context lists
   its typed holes. Expansion substitutes call-site expressions for those
   holes. Since substitution renames under binders, holes remain hygienic in
   this nameless core representation. This models expansion after parsing and
   type checking; it does not formalize the surface syntax-rules parser. -/

def expandTemplate (template : Expr Γ t) (arguments : Sub Γ Δ) : Expr Δ t :=
  template.subst arguments

def singleHoleSub (value : Expr Γ a) : Sub [a] Γ :=
  fun
  | .zero => value

structure TypedMacro (holes : List Ty) (output : Ty) where
  template : Expr holes output

def TypedMacro.expand (definition : TypedMacro holes output)
    (arguments : Sub holes Γ) : Expr Γ output :=
  expandTemplate definition.template arguments

theorem TypedMacro.expand_preserves_type
    (definition : TypedMacro holes output) (arguments : Sub holes Γ) :
    ∃ expanded : Expr Γ output, expanded = definition.expand arguments :=
  ⟨definition.expand arguments, rfl⟩

theorem expandTemplate_preserves_type
    (template : Expr Γ t) (arguments : Sub Γ Δ) :
    ∃ expanded : Expr Δ t, expanded = expandTemplate template arguments :=
  ⟨expandTemplate template arguments, rfl⟩

def twiceTemplate : Expr [.integer] .integer :=
  .add (.var .zero) (.var .zero)

def twiceMacro : TypedMacro [.integer] .integer :=
  ⟨twiceTemplate⟩

def expandTwice (argument : Expr Γ .integer) : Expr Γ .integer :=
  twiceMacro.expand (singleHoleSub argument)

theorem expandTwice_eq (argument : Expr Γ .integer) :
    expandTwice argument = .add argument argument := rfl

/- The template introduces a lambda binder and refers to its argument hole
   from beneath that binder. Expansion must keep the hole distinct from the
   lambda's locally bound variable. -/
def lambdaHoleTemplate : Expr [.integer] (.fn .integer .integer) :=
  .lam (.add (.var (.succ .zero)) (.var .zero))

def lambdaHoleMacro : TypedMacro [.integer] (.fn .integer .integer) :=
  ⟨lambdaHoleTemplate⟩

def expandLambdaHole (argument : Expr Γ .integer) :
    Expr Γ (.fn .integer .integer) :=
  lambdaHoleMacro.expand (singleHoleSub argument)

theorem expandLambdaHole_hygienic (argument : Expr Γ .integer) :
    expandLambdaHole argument =
      .lam (.add (argument.rename (fun v => .succ v)) (.var .zero)) := rfl

theorem expandLambdaHole_open :
    expandLambdaHole (Γ := [.integer]) (.var .zero) =
      .lam (.add (.var (.succ .zero)) (.var .zero)) := rfl

theorem expandLambdaHole_closed :
    expandLambdaHole (Γ := []) (.int 41) =
      (.lam (.add (.int 41) (.var .zero)) : Expr [] (.fn .integer .integer)) := rfl

inductive Value : {t : Ty} → Expr [] t → Prop where
  | bool : Value (.bool b)
  | int : Value (.int n)
  | unit : Value .unit
  | lam : Value (.lam body)
  | nil : Value (.nil : Expr [] (.list a))
  | cons : Value head → Value tail → Value (.cons head tail)
  | none : Value (.none : Expr [] (.option a))
  | some : Value value → Value (.some value)

inductive Step : {t : Ty} → Expr [] t → Expr [] t → Prop where
  | appFn : Step f f' → Step (.app f x) (.app f' x)
  | appArg : Value f → Step x x' → Step (.app f x) (.app f x')
  | beta : Value x → Step (.app (.lam body) x) (body.instantiate x)
  | ifCond : Step c c' → Step (.ite c yes no) (.ite c' yes no)
  | ifTrue : Step (.ite (.bool true) yes no) yes
  | ifFalse : Step (.ite (.bool false) yes no) no
  | addLeft : Step left left' → Step (.add left right) (.add left' right)
  | addRight : Value left → Step right right' → Step (.add left right) (.add left right')
  | addInt : Step (.add (.int left) (.int right)) (.int (left + right))
  | subLeft : Step left left' → Step (.sub left right) (.sub left' right)
  | subRight : Value left → Step right right' → Step (.sub left right) (.sub left right')
  | subInt : Step (.sub (.int left) (.int right)) (.int (left - right))
  | mulLeft : Step left left' → Step (.mul left right) (.mul left' right)
  | mulRight : Value left → Step right right' → Step (.mul left right) (.mul left right')
  | mulInt : Step (.mul (.int left) (.int right)) (.int (left * right))
  | eqIntLeft : Step left left' → Step (.eqInt left right) (.eqInt left' right)
  | eqIntRight : Value left → Step right right' → Step (.eqInt left right) (.eqInt left right')
  | eqIntValue : Step (.eqInt (.int left) (.int right)) (.bool (decide (left = right)))
  | leqLeft : Step left left' → Step (.leq left right) (.leq left' right)
  | leqRight : Value left → Step right right' → Step (.leq left right) (.leq left right')
  | leqInt : Step (.leq (.int left) (.int right)) (.bool (decide (left ≤ right)))
  | consHead : Step head head' → Step (.cons head tail) (.cons head' tail)
  | consTail : Value head → Step tail tail' → Step (.cons head tail) (.cons head tail')
  | matchListScrut :
      Step scrut scrut' →
      Step (.matchList scrut nilCase consCase) (.matchList scrut' nilCase consCase)
  | matchNil : Step (.matchList (.nil : Expr [] (.list a)) nilCase consCase) nilCase
  | matchCons :
      Value head →
      Value tail →
      Step
        (.matchList (.cons head tail) nilCase consCase)
        (consCase.instantiateCons head tail)
  | someValue : Step value value' → Step (.some value) (.some value')
  | matchOptionScrut :
      Step scrut scrut' →
      Step (.matchOption scrut noneCase someCase) (.matchOption scrut' noneCase someCase)
  | matchNone : Step (.matchOption (.none : Expr [] (.option a)) noneCase someCase) noneCase
  | matchSome :
      Value value →
      Step (.matchOption (.some value) noneCase someCase) (someCase.instantiate value)
  | unfoldFix : Step (.fix body) (body.instantiate (.fix body))

theorem progress : (term : Expr [] t) → Value term ∨ ∃ next, Step term next
  | .var v => nomatch v
  | .bool _ => Or.inl .bool
  | .int _ => Or.inl .int
  | .unit => Or.inl .unit
  | .lam _ => Or.inl .lam
  | .app f x => by
      rcases progress f with hf | ⟨f', hf⟩
      · rcases progress x with hx | ⟨x', hx⟩
        · cases hf
          exact Or.inr ⟨_, .beta hx⟩
        · exact Or.inr ⟨_, .appArg hf hx⟩
      · exact Or.inr ⟨_, .appFn hf⟩
  | .ite c yes no => by
      rcases progress c with hc | ⟨c', hc⟩
      · cases hc with
        | bool =>
          rename_i b
          cases b
          · exact Or.inr ⟨_, .ifFalse⟩
          · exact Or.inr ⟨_, .ifTrue⟩
      · exact Or.inr ⟨_, .ifCond hc⟩
  | .add left right => by
      rcases progress left with hl | ⟨left', hl⟩
      · rcases progress right with hr | ⟨right', hr⟩
        · cases hl
          cases hr
          exact Or.inr ⟨_, .addInt⟩
        · exact Or.inr ⟨_, .addRight hl hr⟩
      · exact Or.inr ⟨_, .addLeft hl⟩
  | .sub left right => by
      rcases progress left with hl | ⟨left', hl⟩
      · rcases progress right with hr | ⟨right', hr⟩
        · cases hl
          cases hr
          exact Or.inr ⟨_, .subInt⟩
        · exact Or.inr ⟨_, .subRight hl hr⟩
      · exact Or.inr ⟨_, .subLeft hl⟩
  | .mul left right => by
      rcases progress left with hl | ⟨left', hl⟩
      · rcases progress right with hr | ⟨right', hr⟩
        · cases hl
          cases hr
          exact Or.inr ⟨_, .mulInt⟩
        · exact Or.inr ⟨_, .mulRight hl hr⟩
      · exact Or.inr ⟨_, .mulLeft hl⟩
  | .eqInt left right => by
      rcases progress left with hl | ⟨left', hl⟩
      · rcases progress right with hr | ⟨right', hr⟩
        · cases hl
          cases hr
          exact Or.inr ⟨_, .eqIntValue⟩
        · exact Or.inr ⟨_, .eqIntRight hl hr⟩
      · exact Or.inr ⟨_, .eqIntLeft hl⟩
  | .leq left right => by
      rcases progress left with hl | ⟨left', hl⟩
      · rcases progress right with hr | ⟨right', hr⟩
        · cases hl
          cases hr
          exact Or.inr ⟨_, .leqInt⟩
        · exact Or.inr ⟨_, .leqRight hl hr⟩
      · exact Or.inr ⟨_, .leqLeft hl⟩
  | .nil => Or.inl .nil
  | .cons head tail => by
      rcases progress head with hh | ⟨head', hh⟩
      · rcases progress tail with ht | ⟨tail', ht⟩
        · exact Or.inl (.cons hh ht)
        · exact Or.inr ⟨_, .consTail hh ht⟩
      · exact Or.inr ⟨_, .consHead hh⟩
  | .matchList scrut nilCase consCase => by
      rcases progress scrut with hs | ⟨scrut', hs⟩
      · cases hs with
        | nil => exact Or.inr ⟨_, .matchNil⟩
        | cons hh ht => exact Or.inr ⟨_, .matchCons hh ht⟩
      · exact Or.inr ⟨_, .matchListScrut hs⟩
  | .none => Or.inl .none
  | .some value => by
      rcases progress value with hv | ⟨value', hv⟩
      · exact Or.inl (.some hv)
      · exact Or.inr ⟨_, .someValue hv⟩
  | .matchOption scrut noneCase someCase => by
      rcases progress scrut with hs | ⟨scrut', hs⟩
      · cases hs with
        | none => exact Or.inr ⟨_, .matchNone⟩
        | some hv => exact Or.inr ⟨_, .matchSome hv⟩
      · exact Or.inr ⟨_, .matchOptionScrut hs⟩
  | .fix _ => Or.inr ⟨_, .unfoldFix⟩

/- `Step` is indexed by one `t` on both sides.  Lean therefore rejects any
   reduction rule that changes the type.  This theorem exposes that kernel
   guarantee as a reusable result. -/
theorem preservation {term next : Expr [] t} (_ : Step term next) :
    ∃ preserved : Expr [] t, preserved = next :=
  ⟨next, rfl⟩

theorem valueCannotStep {term next : Expr [] t} (isValue : Value term) :
    ¬ Step term next := by
  intro steps
  induction isValue with
  | bool => cases steps
  | int => cases steps
  | unit => cases steps
  | lam => cases steps
  | nil => cases steps
  | cons _ _ headNormal tailNormal =>
      cases steps with
      | consHead headSteps => exact headNormal headSteps
      | consTail _ tailSteps => exact tailNormal tailSteps
  | none => cases steps
  | some _ valueNormal =>
      cases steps with
      | someValue valueSteps => exact valueNormal valueSteps

theorem notStuck (term : Expr [] t) :
    Value term ∨ ∃ next : Expr [] t, Step term next :=
  progress term

end NLisp
