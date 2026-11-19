import NLisp.ExpansionLowering
import NLisp.NameLowering

namespace NLisp.Named
open CBindingWalk ExpansionLowering

/- Decode operational source syntax independently of the proposed IR. Binder
and reference identities are retained. Types are checked on the original
nodes by ExpansionLowering and have no operational effect in this model. -/
def globalIndex (identity : Nat) : List Header → Option Nat
  | [] => none
  | h :: tail => if h.identity = identity then some 0 else (globalIndex identity tail).map Nat.succ

def parameterIds : List Node → Option (List Nat)
  | [] => some []
  | .list [id, _] :: tail => return (← binder id) :: (← parameterIds tail)
  | _ => none

def letParts : List Node → Option (List Nat × List Node)
  | [] => some ([], [])
  | .list [.list [id, _], value] :: tail => do
    let id ← binder id
    let (ids, values) ← letParts tail
    pure (id :: ids, value :: values)
  | _ => none

def readPrimitive : Nat → Option Expr
  | 3 => some (.lam [0, 1] (.add (.var 0) (.var 1)))
  | 6 => some (.lam [0, 1] (.sub (.var 0) (.var 1)))
  | 9 => some (.lam [0, 1] (.mul (.var 0) (.var 1)))
  | 15 => some (.lam [0, 1] (.le (.var 0) (.var 1)))
  | 24 => some (.lam [0, 1] (.intEq (.var 0) (.var 1)))
  | _ => none

mutual
def decodeExpr : Nat → List Header → Node → Option Expr
  | 0, _, _ => none
  | fuel + 1, headers, node =>
    match node with
    | .atom a selected =>
      if a.name = "true" then if selected = 0 then some (.bool true) else none
      else if a.name = "false" then if selected = 0 then some (.bool false) else none
      else if a.name = "unit" then if selected = 0 then some .unit else none
      else if Lexical.integerLiteral a.name.toList then
        if selected = 0 then a.name.toInt?.map Expr.int else none
      else if Lexical.identifier a.name then
        match globalIndex selected headers with
        | some index => some (.global index)
        | none => match readPrimitive selected with
          | some primitive => some primitive
          | none => some (.var selected)
      else none
    | .list (head :: tail) =>
      if name head = some "lambda" then
        match tail with
        | [.list params, _, body] => return .lam (← parameterIds params) (← decodeExpr fuel headers body)
        | _ => none
      else if name head = some "if" then
        match tail with
        | [c, y, n] => do
          let c ← decodeExpr fuel headers c
          let y ← decodeExpr fuel headers y
          let n ← decodeExpr fuel headers n
          pure (.ite c y n)
        | _ => none
      else if name head = some "let" then
        match tail with
        | [.list bindings, body] => do
          let (ids, values) ← letParts bindings
          return .letMany ids (← decodeExprs fuel headers values) (← decodeExpr fuel headers body)
        | _ => none
      else if name head = some "begin" then
        match tail with
        | first :: rest => return .begin (← decodeExpr fuel headers first) (← decodeExprs fuel headers rest)
        | [] => none
      else if name head = some "type-app" then
        match tail with
        | fn :: _ => decodeExpr fuel headers fn
        | [] => none
      else if name head = some "Nil" then
        match tail with | [_] => some .nil | _ => none
      else if name head = some "None" then
        match tail with | [_] => some .none | _ => none
      else if name head = some "Cons" then
        match tail with
        | [_, h, t] => return .cons (← decodeExpr fuel headers h) (← decodeExpr fuel headers t)
        | _ => none
      else if name head = some "Some" then
        match tail with
        | [_, value] => return .some (← decodeExpr fuel headers value)
        | _ => none
      else if name head = some "match" then
        match tail with
        | target :: cases => do
          let target ← decodeExpr fuel headers target
          match casesParts "Nil" "Cons" cases with
          | some (empty, [h, t], full) => do
            let empty ← decodeExpr fuel headers empty
            let h ← binder h
            let t ← binder t
            let full ← decodeExpr fuel headers full
            pure (.matchList target empty h t full)
          | _ =>
            let (empty, [v], full) ← casesParts "None" "Some" cases | none
            return .matchOption target (← decodeExpr fuel headers empty)
              (← binder v) (← decodeExpr fuel headers full)
        | [] => none
      else return .app (← decodeExpr fuel headers head) (← decodeExprs fuel headers tail)
    | .list [] => none

def decodeExprs : Nat → List Header → List Node → Option (List Expr)
  | 0, _, _ => none
  | fuel + 1, headers, nodes =>
    match nodes with
    | [] => some []
    | node :: tail => return (← decodeExpr fuel headers node) :: (← decodeExprs fuel headers tail)
end

def decodeFunctions (fuel : Nat) (headers : List Header) : List Header → Option Definitions
  | [] => some []
  | h :: tail => do
    let body ← decodeExpr fuel headers h.body
    let rest ← decodeFunctions fuel headers tail
    pure ((h.parameters.map Prod.fst, body) :: rest)

def decodeProgram (fuel : Nat) (forms : List Node) : Option Definitions := do
  let headers ← forms.mapM (readHeader fuel)
  decodeFunctions fuel headers headers

end NLisp.Named
