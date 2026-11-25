import NLisp.SurfaceTypeEquality
import NLisp.PolyIR

namespace NLisp.Surface

/- A successful check carries its own kernel-checked typing derivation.
The depth budget bounds the checker, not the NLisp program's execution.
None means rejection or budget exhaustion; it is never a proof of invalidity. -/
mutual
def checkWF : Nat → (count : Nat) → (t : Ty) → Option (PLift (t.wellFormed count))
  | 0, _, _ => none
  | fuel + 1, count, t =>
    match t with
    | .boolean | .integer | .float | .string | .character | .unit => some ⟨True.intro⟩
    | .var i => if h : i < count then some ⟨by simpa [Ty.wellFormed] using h⟩ else none
    | .fn args result => do
      let a ← checkTypesWF fuel count args
      let r ← checkWF fuel count result
      pure ⟨by simpa [Ty.wellFormed] using And.intro a.down r.down⟩
    | .list t | .option t => do
      let h ← checkWF fuel count t
      pure ⟨by simpa [Ty.wellFormed] using h.down⟩

def checkTypesWF : Nat → (count : Nat) → (ts : List Ty) →
    Option (PLift (∀ t ∈ ts, t.wellFormed count))
  | 0, _, _ => none
  | fuel + 1, count, ts =>
    match ts with
    | [] => some ⟨by simp⟩
    | t :: rest => do
      let h ← checkWF fuel count t
      let hs ← checkTypesWF fuel count rest
      pure ⟨by simpa using And.intro h.down hs.down⟩
end

structure Inferred (globals : List Signature) (count : Nat) (context : List Ty) (e : Expr) where
  type : Ty
  typing : HasType globals count context e type

def Inferred.expect (value : Inferred globals count context e) (expected : Ty) :
    Option (PLift (HasType globals count context e expected)) :=
  if same : value.type = expected then some ⟨same ▸ value.typing⟩ else none

structure InferredArgs (globals : List Signature) (count : Nat) (context : List Ty) (es : List Expr) where
  types : List Ty
  typing : ArgsHaveTypes globals count context es types

structure InferredSequence (globals : List Signature) (count : Nat) (context : List Ty)
    (es : List Expr) (previous : Ty) where
  type : Ty
  typing : SequenceHasType globals count context es previous type

mutual
def infer : Nat → (globals : List Signature) → (count : Nat) → (context : List Ty) →
    (e : Expr) → Option (Inferred globals count context e)
  | 0, _, _, _, _ => none
  | fuel + 1, globals, count, context, e =>
    match e with
    | .var index =>
      match h : context[index]? with
      | none => none
      | some t => some ⟨t, .var h⟩
    | .global index arguments => do
      match h : globals[index]? with
      | none => none
      | some signature =>
        if arity : arguments.length = signature.typeArity then do
          let args ← checkTypesWF fuel count arguments
          let params ← checkTypesWF fuel signature.typeArity signature.parameters
          let result ← checkWF fuel signature.typeArity signature.result
          pure ⟨.fn (signature.parameters.map (Ty.instantiate arguments))
              (signature.result.instantiate arguments),
            .global h arity args.down ⟨params.down, result.down⟩⟩
        else none
    | .bool _ => some ⟨.boolean, .bool⟩
    | .int _ => some ⟨.integer, .int⟩
    | .float _ => some ⟨.float, .float⟩
    | .string _ => some ⟨.string, .string⟩
    | .character _ => some ⟨.character, .character⟩
    | .floatBin op left right => do
      let leftType ← infer fuel globals count context left
      let rightType ← infer fuel globals count context right
      let leftProof ← leftType.expect .float
      let rightProof ← rightType.expect .float
      pure ⟨.float, .floatBin leftProof.down rightProof.down⟩
    | .unit => some ⟨.unit, .unit⟩
    | .lam parameters result body => do
      let params ← checkTypesWF fuel count parameters
      let ret ← checkWF fuel count result
      let typed ← infer fuel globals count (parameters ++ context) body
      let checked ← typed.expect result
      pure ⟨.fn parameters result, .lam params.down ret.down checked.down⟩
    | .app f arguments => do
      let function ← infer fuel globals count context f
      let args ← inferArgs fuel globals count context arguments
      match function with
      | ⟨.fn parameters result, functionProof⟩ =>
        if same : args.types = parameters then
          pure ⟨result, .app functionProof (same ▸ args.typing)⟩
        else none
      | _ => none
    | .ite condition yes no => do
      let c ← infer fuel globals count context condition
      let hc ← c.expect .boolean
      let y ← infer fuel globals count context yes
      let n ← infer fuel globals count context no
      let hn ← n.expect y.type
      pure ⟨y.type, .ite hc.down y.typing hn.down⟩
    | .add a b => do
      let a ← infer fuel globals count context a
      let b ← infer fuel globals count context b
      let ha ← a.expect .integer
      let hb ← b.expect .integer
      pure ⟨.integer, .add ha.down hb.down⟩
    | .sub a b => do
      let a ← infer fuel globals count context a
      let b ← infer fuel globals count context b
      let ha ← a.expect .integer
      let hb ← b.expect .integer
      pure ⟨.integer, .sub ha.down hb.down⟩
    | .mul a b => do
      let a ← infer fuel globals count context a
      let b ← infer fuel globals count context b
      let ha ← a.expect .integer
      let hb ← b.expect .integer
      pure ⟨.integer, .mul ha.down hb.down⟩
    | .le a b => do
      let a ← infer fuel globals count context a
      let b ← infer fuel globals count context b
      let ha ← a.expect .integer
      let hb ← b.expect .integer
      pure ⟨.boolean, .le ha.down hb.down⟩
    | .intEq a b => do
      let a ← infer fuel globals count context a
      let b ← infer fuel globals count context b
      let ha ← a.expect .integer
      let hb ← b.expect .integer
      pure ⟨.boolean, .intEq ha.down hb.down⟩
    | .letMany types initializers body => do
      let valid ← checkTypesWF fuel count types
      let values ← inferArgs fuel globals count context initializers
      if same : values.types = types then do
        let result ← infer fuel globals count (types ++ context) body
        pure ⟨result.type, .letMany valid.down (same ▸ values.typing) result.typing⟩
      else none
    | .begin first rest => do
      let first ← infer fuel globals count context first
      let rest ← inferSequence fuel globals count context rest first.type
      pure ⟨rest.type, .begin first.typing rest.typing⟩
    | .nil t => do
      let valid ← checkWF fuel count t
      pure ⟨.list t, .nil valid.down⟩
    | .cons t head tail => do
      let valid ← checkWF fuel count t
      let head ← infer fuel globals count context head
      let tail ← infer fuel globals count context tail
      let h ← head.expect t
      let ts ← tail.expect (.list t)
      pure ⟨.list t, .cons valid.down h.down ts.down⟩
    | .none t => do
      let valid ← checkWF fuel count t
      pure ⟨.option t, .none valid.down⟩
    | .some t value => do
      let valid ← checkWF fuel count t
      let value ← infer fuel globals count context value
      let h ← value.expect t
      pure ⟨.option t, .some valid.down h.down⟩
    | .matchList target empty full => do
      let target ← infer fuel globals count context target
      match target with
      | ⟨.list t, targetProof⟩ =>
        let empty ← infer fuel globals count context empty
        let full ← infer fuel globals count (t :: .list t :: context) full
        let same ← full.expect empty.type
        pure ⟨empty.type, .matchList targetProof empty.typing same.down⟩
      | _ => none
    | .matchOption target empty full => do
      let target ← infer fuel globals count context target
      match target with
      | ⟨.option t, targetProof⟩ =>
        let empty ← infer fuel globals count context empty
        let full ← infer fuel globals count (t :: context) full
        let same ← full.expect empty.type
        pure ⟨empty.type, .matchOption targetProof empty.typing same.down⟩
      | _ => none

def inferArgs : Nat → (globals : List Signature) → (count : Nat) → (context : List Ty) →
    (es : List Expr) → Option (InferredArgs globals count context es)
  | 0, _, _, _, _ => none
  | fuel + 1, globals, count, context, es =>
    match es with
    | [] => some ⟨[], .nil⟩
    | e :: es => do
      let head ← infer fuel globals count context e
      let tail ← inferArgs fuel globals count context es
      pure ⟨head.type :: tail.types, .cons head.typing tail.typing⟩

def inferSequence : Nat → (globals : List Signature) → (count : Nat) → (context : List Ty) →
    (es : List Expr) → (previous : Ty) → Option (InferredSequence globals count context es previous)
  | 0, _, _, _, _, _ => none
  | fuel + 1, globals, count, context, es, previous =>
    match es with
    | [] => some ⟨previous, .nil⟩
    | e :: es => do
      let head ← infer fuel globals count context e
      let tail ← inferSequence fuel globals count context es head.type
      pure ⟨tail.type, .cons head.typing tail.typing⟩
end

def elaborate (fuel : Nat) (globals : List Signature) (count : Nat) (context : List Ty)
    (expression : Expr) (expected : Ty) :
    Option (PolyIR.CheckedExpr globals count context expected) := do
  let result ← infer fuel globals count context expression
  let proof ← result.expect expected
  pure ⟨expression, proof.down⟩


theorem infer_sound (result : Inferred globals count context expression) :
    HasType globals count context expression result.type := result.typing

def elaborateDefinition (fuel : Nat) (globals : List Signature) (signature : Signature)
    (body : Expr) : Option (PolyIR.Definition globals signature) := do
  let params ← checkTypesWF fuel signature.typeArity signature.parameters
  let result ← checkWF fuel signature.typeArity signature.result
  let checked ← elaborate fuel globals signature.typeArity signature.parameters body signature.result
  pure ⟨⟨params.down, result.down⟩, checked⟩

def elaborateDefinitions (fuel : Nat) (globals : List Signature) : (signatures : List Signature) →
    List Expr → Option ((index : Fin signatures.length) → PolyIR.Definition globals signatures[index])
  | [], [] => some (fun index => Fin.elim0 index)
  | signature :: signatures, body :: bodies => do
    let head ← elaborateDefinition fuel globals signature body
    let tail ← elaborateDefinitions fuel globals signatures bodies
    pure (fun index => by
      rcases index with ⟨index, bound⟩
      cases index with
      | zero => exact head
      | succ index => exact tail ⟨index, by simp only [List.length_cons] at bound; omega⟩)
  | _, _ => none

def elaborateProgram (fuel : Nat) (signatures : List Signature) (bodies : List Expr) :
    Option PolyIR.Program := do
  let definitions ← elaborateDefinitions fuel signatures signatures bodies
  pure ⟨signatures, definitions⟩

end NLisp.Surface
