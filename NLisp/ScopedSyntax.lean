import NLisp.TypedExpansion

namespace NLisp.ScopedSyntax

abbrev Ty := NLisp.TypedExpansion.Ty
abbrev Var := NLisp.TypedExpansion.Var
abbrev Expr := NLisp.TypedExpansion.Expr
abbrev Ren := NLisp.TypedExpansion.Ren
abbrev Sub := NLisp.TypedExpansion.Sub
abbrev singleHoleSub := @NLisp.TypedExpansion.singleHoleSub

/-! Scope-indexed syntax for all runtime types. Binding identity is
independent of its type or printed name. Definition-site and call-site
contexts enter expansion through separate identity-preserving embeddings.
This module does not prove C name resolution correct. -/

structure Binding where
  identity : Nat
  type : Ty
  deriving DecidableEq, Repr

abbrev Scope := List Binding

def types (scope : Scope) : List Ty := scope.map Binding.type
def uniqueIds : Scope → Bool
  | [] => true
  | b :: tail => tail.all (fun other => b.identity != other.identity) && uniqueIds tail

def Valid (scope : Scope) : Prop := uniqueIds scope = true

instance (scope : Scope) : Decidable (Valid scope) :=
  inferInstanceAs (Decidable (uniqueIds scope = true))

def bindingId (scope : Scope) : Var (types scope) t → Nat :=
  match scope with
  | [] => fun v => nomatch v
  | b :: tail => fun v =>
      match v with
      | .zero => b.identity
      | .succ w => bindingId tail w

structure Embedding (source target : Scope) where
  source_valid : Valid source
  target_valid : Valid target
  rename : Ren (types source) (types target)
  preserves : ∀ {t} (v : Var (types source) t),
    bindingId target (rename v) = bindingId source v

structure Syntax (scope : Scope) (result : Ty) where
  valid : Valid scope
  term : Expr (types scope) result

def Syntax.transport (embedding : Embedding source target)
    (value : Syntax source t) : Syntax target t :=
  ⟨embedding.target_valid, value.term.rename embedding.rename⟩

theorem transport_var (embedding : Embedding source target)
    (v : Var (types source) t) :
    (Syntax.transport embedding ⟨embedding.source_valid, .var v⟩).term =
      .var (embedding.rename v) := rfl

theorem transport_string (embedding : Embedding source target) (value : String) :
    (Syntax.transport embedding ⟨embedding.source_valid, .str value⟩).term =
      .str value := rfl

theorem transport_float_bits (embedding : Embedding source target) (bits : UInt64) :
    (Syntax.transport embedding ⟨embedding.source_valid, .floatBits bits⟩).term =
      .floatBits bits := rfl

theorem transport_builtin (embedding : Embedding source target)
    (operation : NLisp.TypedExpansion.Primitive) :
    (Syntax.transport embedding ⟨embedding.source_valid, .builtin operation⟩).term =
      .builtin operation := rfl

theorem distinct_origins_remain_distinct
    (definition : Embedding definitionScope output)
    (caller : Embedding callScope output)
    (captured : Var (types definitionScope) t)
    (argument : Var (types callScope) t)
    (different : bindingId definitionScope captured ≠ bindingId callScope argument) :
    definition.rename captured ≠ caller.rename argument := by
  intro equal
  apply different
  calc
    bindingId definitionScope captured = bindingId output (definition.rename captured) :=
      (definition.preserves captured).symm
    _ = bindingId output (caller.rename argument) := congrArg (bindingId output) equal
    _ = bindingId callScope argument := caller.preserves argument

def Embedding.weaken (embedding : Embedding source target) (fresh : Binding)
    (valid : Valid (fresh :: target)) : Embedding source (fresh :: target) where
  source_valid := embedding.source_valid
  target_valid := valid
  rename := fun v => .succ (embedding.rename v)
  preserves := fun v => embedding.preserves v

def holeVar : Var holes t → Var (holes ++ definition) t
  | .zero => .zero
  | .succ v => .succ (holeVar v)

def definitionVar (holes : List Ty) (v : Var definition t) : Var (holes ++ definition) t :=
  match holes with
  | [] => v
  | _ :: tail => .succ (definitionVar tail v)

def appendSub : (holes : List Ty) → Sub holes output → Sub definition output →
    Sub (holes ++ definition) output
  | [], _, captures => captures
  | _ :: tail, arguments, captures => fun v =>
      match v with
      | .zero => arguments .zero
      | .succ w => appendSub tail (fun z => arguments (.succ z)) captures w

theorem appendSub_hole (arguments : Sub holes output) (captures : Sub definition output)
    (v : Var holes t) :
    appendSub holes arguments captures (holeVar v) = arguments v := by
  induction v with
  | zero => rfl
  | succ _ ih => exact ih (fun w => arguments (.succ w))

theorem appendSub_definition (holes : List Ty) (arguments : Sub holes output)
    (captures : Sub definition output) (v : Var definition t) :
    appendSub holes arguments captures (definitionVar holes v) = captures v := by
  induction holes with
  | nil => rfl
  | cons _ tail ih => exact ih (fun w => arguments (.succ w))

structure Macro (definitionScope : Scope) (holes : List Ty) (result : Ty) where
  valid : Valid definitionScope
  template : Expr (holes ++ types definitionScope) result

structure Arguments (callScope : Scope) (holes : List Ty) where
  valid : Valid callScope
  values : Sub holes (types callScope)

def Macro.expand (definition : Macro definitionScope holes result)
    (arguments : Arguments callScope holes)
    (definitionInto : Embedding definitionScope output)
    (callerInto : Embedding callScope output) : Syntax output result :=
  ⟨definitionInto.target_valid,
    definition.template.subst (appendSub holes
      (fun v => (arguments.values v).rename callerInto.rename)
      (fun v => .var (definitionInto.rename v)))⟩

theorem expand_hole (arguments : Arguments callScope holes)
    (definitionInto : Embedding definitionScope output)
    (callerInto : Embedding callScope output) (v : Var holes t) :
    (Macro.expand ⟨definitionInto.source_valid, .var (holeVar v)⟩
      arguments definitionInto callerInto).term =
        (arguments.values v).rename callerInto.rename := by
  exact appendSub_hole _ _ v

theorem expand_capture (arguments : Arguments callScope holes)
    (definitionInto : Embedding definitionScope output)
    (callerInto : Embedding callScope output) (v : Var (types definitionScope) t) :
    (Macro.expand ⟨definitionInto.source_valid, .var (definitionVar holes v)⟩
      arguments definitionInto callerInto).term = .var (definitionInto.rename v) := by
  exact appendSub_definition holes _ _ v

namespace Examples

-- Both external bindings may be printed as "offset" and have the same type.
-- Their identities, 10 and 20, remain different throughout expansion.
def definitionScope : Scope := [⟨10, .integer⟩]
def callScope : Scope := [⟨20, .integer⟩, ⟨10, .integer⟩]

def definitionInto : Embedding definitionScope callScope where
  source_valid := by decide
  target_valid := by decide
  rename := fun | .zero => .succ .zero
  preserves := by
    intro t v
    cases v with
    | zero => rfl
    | succ w => nomatch w

def callerInto : Embedding callScope callScope where
  source_valid := by decide
  target_valid := by decide
  rename := fun v => v
  preserves := fun _ => rfl

def addCaptured : Macro definitionScope [.integer] .integer where
  valid := by decide
  template := .add (.var (.succ .zero)) (.var .zero)

def argument : Arguments callScope [.integer] where
  valid := by decide
  values := singleHoleSub (.var .zero)

theorem shadowing_preserves_both_origins :
    (addCaptured.expand argument definitionInto callerInto).term =
      .add (.var (.succ .zero)) (.var .zero) := rfl

theorem wrong_same_typed_binding_rejected :
    bindingId callScope (.zero : Var (types callScope) .integer) ≠
      bindingId definitionScope (.zero : Var (types definitionScope) .integer) := by decide

def withLambda : Macro definitionScope [.integer] (.fn .integer .integer) where
  valid := by decide
  template := .lam (.add (.var (.succ (.succ .zero))) (.var (.succ .zero)))

theorem introduced_lambda_captures_neither_origin :
    (withLambda.expand argument definitionInto callerInto).term =
      .lam (.add (.var (.succ (.succ .zero))) (.var (.succ .zero))) := rfl

theorem fresh_scope_shifts_both_origins :
    (addCaptured.expand argument
      (definitionInto.weaken ⟨30, .integer⟩ (by decide))
      (callerInto.weaken ⟨30, .integer⟩ (by decide))).term =
        .add (.var (.succ (.succ .zero))) (.var (.succ .zero)) := rfl

theorem duplicate_binding_identity_invalid :
    ¬ Valid [⟨10, .integer⟩, ⟨10, .integer⟩] := by decide

end Examples

end NLisp.ScopedSyntax
