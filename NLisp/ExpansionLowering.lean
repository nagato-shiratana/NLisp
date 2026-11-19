import NLisp.CBindingWalk
import NLisp.SurfaceChecker

namespace NLisp.ExpansionLowering
open CBindingWalk Surface

/- This checker consumes the *same annotated nodes* checked by CBindingWalk.
It checks a proposed lowering, without trusting the Python converter. Its
fuel bounds checking depth; false can also mean insufficient fuel. -/
def name : Node → Option String
  | .atom a _ => some a.name
  | _ => none

def binder : Node → Option Nat
  | .atom a _ => if Lexical.identifier a.name then some a.token else none
  | _ => none

def indexOf (value : String) : List String → Option Nat
  | [] => none
  | head :: tail => if value = head then some 0 else (indexOf value tail).map Nat.succ

mutual
def readType : Nat → List String → Node → Option Ty
  | 0, _, _ => none
  | fuel + 1, variables, node =>
    match node with
    | .atom a _ =>
      match indexOf a.name variables with
      | some i => some (.var i)
      | none => match a.name with
        | "Integer" => some .integer
        | "Boolean" => some .boolean
        | "Unit" => some .unit
        | _ => none
    | .list [head, t] => do
      let t ← readType fuel variables t
      if name head = some "List" then pure (.list t)
      else if name head = some "Option" then pure (.option t)
      else none
    | .list [head, .list args, result] => do
      if name head ≠ some "Function" then none else
      return .fn (← readTypes fuel variables args) (← readType fuel variables result)
    | _ => none

def readTypes : Nat → List String → List Node → Option (List Ty)
  | 0, _, _ => none
  | fuel + 1, variables, nodes =>
    match nodes with
    | [] => some []
    | head :: tail => return (← readType fuel variables head) :: (← readTypes fuel variables tail)
end

def readParameters (fuel : Nat) (variables : List String) :
    List Node → Option (List (Nat × Ty))
  | [] => some []
  | .list [id, t] :: tail => return (← binder id, ← readType fuel variables t) ::
      (← readParameters fuel variables tail)
  | _ => none

structure Header where
  identity : Nat
  variables : List String
  parameters : List (Nat × Ty)
  result : Ty
  body : Node

def Header.signature (h : Header) : Signature :=
  ⟨h.variables.length, h.parameters.map Prod.snd, h.result⟩

def readHeader (fuel : Nat) : Node → Option Header
  | .list [head, id, .list parameters, result, body] => do
    if name head ≠ some "defun" then none else
    return ⟨← binder id, [], ← readParameters fuel [] parameters, ← readType fuel [] result, body⟩
  | .list [head, id, .list [quantifier, .list variables, .list parameters, result], body] => do
    if name head ≠ some "defun" ∨ name quantifier ≠ some "forall" then none else
    let variables ← variables.mapM name
    if !Lexical.distinctNames variables then none else
    return ⟨← binder id, variables, ← readParameters fuel variables parameters,
      ← readType fuel variables result, body⟩
  | _ => none

mutual
def occurs : Nat → Nat → Ty → Bool
  | 0, _, _ => false
  | fuel + 1, typeIndex, t => match t with
    | .var i => i == typeIndex
    | .fn args result => occursMany fuel typeIndex args || occurs fuel typeIndex result
    | .list t | .option t => occurs fuel typeIndex t
    | _ => false
def occursMany : Nat → Nat → List Ty → Bool
  | 0, _, _ => false
  | fuel + 1, typeIndex, ts => match ts with
    | [] => false
    | t :: ts => occurs fuel typeIndex t || occursMany fuel typeIndex ts
end

def inferrable (fuel : Nat) (h : Header) : Bool :=
  (List.range h.variables.length).all (fun i => occursMany fuel i (h.parameters.map Prod.snd))

def checkGlobal (fuel : Nat) (headers : List Header) (allowInference : Bool)
    (selected index : Nat) (arguments : List Ty) : Bool :=
  match headers[index]? with
  | none => false
  | some h => selected == h.identity && arguments.length == h.variables.length &&
      (h.variables.isEmpty || (allowInference && inferrable fuel h))

def primitive : Nat → Option Expr
  | 3 => some (.lam [.integer, .integer] .integer (.add (.var 0) (.var 1)))
  | 6 => some (.lam [.integer, .integer] .integer (.sub (.var 0) (.var 1)))
  | 9 => some (.lam [.integer, .integer] .integer (.mul (.var 0) (.var 1)))
  | 15 => some (.lam [.integer, .integer] .boolean (.le (.var 0) (.var 1)))
  | 24 => some (.lam [.integer, .integer] .boolean (.intEq (.var 0) (.var 1)))
  | _ => none

/- A restricted structural comparison avoids invoking the converter or the
type checker to recognize a primitive's fixed lambda representation. -/
def checkPrimitive (selected : Nat) : Expr → Bool
  | .lam parameters result body =>
    decide (parameters = [.integer, .integer]) &&
      match selected, result, body with
      | 3, .integer, .add (.var 0) (.var 1)
      | 6, .integer, .sub (.var 0) (.var 1)
      | 9, .integer, .mul (.var 0) (.var 1)
      | 15, .boolean, .le (.var 0) (.var 1)
      | 24, .boolean, .intEq (.var 0) (.var 1) => true
      | _, _, _ => false
  | _ => false

def caseParts (tag : String) : Node → Option (List Node × Node)
  | .list [.list (head :: bindings), body] =>
    if name head = some tag then some (bindings, body) else none
  | _ => none

def casesParts (empty full : String) (cases : List Node) :
    Option (Node × List Node × Node) := do
  let [a, b] := cases | none
  match caseParts empty a, caseParts full b with
  | some ([], e), some (bindings, f) => pure (e, bindings, f)
  | _, _ =>
    let ([], e) ← caseParts empty b | none
    let (bindings, f) ← caseParts full a
    pure (e, bindings, f)

mutual
def checkExpr : Nat → List Header → List String → List Nat → Bool → Node → Expr → Bool
  | 0, _, _, _, _, _, _ => false
  | fuel + 1, headers, variables, locals, allowInference, node, expression =>
    match node with
    | .atom a selected =>
      match expression with
      | .var index => decide (locals[index]? = some selected)
      | .global index arguments => checkGlobal fuel headers allowInference selected index arguments
      | .int n => selected == 0 && Lexical.integerLiteral a.name.toList && a.name.toInt? == some n
      | .bool b => selected == 0 && a.name == (if b then "true" else "false")
      | .unit => selected == 0 && a.name == "unit"
      | e => checkPrimitive selected e
    | .list (head :: tail) =>
      if name head = some "lambda" then
        match tail, expression with
        | [.list params, result, body], .lam types ret output =>
          match readParameters fuel variables params, readType fuel variables result with
          | some parsed, some r => decide (parsed.map Prod.snd = types ∧ r = ret) &&
              checkExpr fuel headers variables (parsed.map Prod.fst ++ locals) false body output
          | _, _ => false
        | _, _ => false
      else if name head = some "if" then
        match tail, expression with
        | [c, y, n], .ite c' y' n' =>
          checkExpr fuel headers variables locals false c c' &&
          checkExpr fuel headers variables locals false y y' &&
          checkExpr fuel headers variables locals false n n'
        | _, _ => false
      else if name head = some "let" then
        match tail, expression with
        | [.list bindings, body], .letMany types values output =>
          match readBindings fuel variables bindings with
          | some (parameters, inputs) =>
            decide (parameters.map Prod.snd = types) &&
              checkExprs fuel headers variables locals inputs values &&
              checkExpr fuel headers variables (parameters.map Prod.fst ++ locals) false body output
          | none => false
        | _, _ => false
      else if name head = some "begin" then
        match tail, expression with
        | first :: rest, .begin first' rest' =>
          checkExpr fuel headers variables locals false first first' &&
          checkExprs fuel headers variables locals rest rest'
        | _, _ => false
      else if name head = some "type-app" then
        match tail, expression with
        | .atom _ selected :: arguments, .global index types =>
          match headers[index]? with
          | some h => selected == h.identity && !h.variables.isEmpty &&
              decide (readTypes fuel variables arguments = some types) &&
              types.length == h.variables.length
          | none => false
        | _, _ => false
      else if name head = some "Nil" then
        match tail, expression with
        | [t], .nil t' => decide (readType fuel variables t = some t')
        | _, _ => false
      else if name head = some "None" then
        match tail, expression with
        | [t], .none t' => decide (readType fuel variables t = some t')
        | _, _ => false
      else if name head = some "Cons" then
        match tail, expression with
        | [t, h, ts], .cons t' h' ts' => decide (readType fuel variables t = some t') &&
            checkExpr fuel headers variables locals false h h' &&
            checkExpr fuel headers variables locals false ts ts'
        | _, _ => false
      else if name head = some "Some" then
        match tail, expression with
        | [t, v], .some t' v' => decide (readType fuel variables t = some t') &&
            checkExpr fuel headers variables locals false v v'
        | _, _ => false
      else if name head = some "match" then
        match tail, expression with
        | target :: cases, .matchList target' empty' full' =>
          match casesParts "Nil" "Cons" cases with
          | some (empty, [h, t], full) =>
            match binder h, binder t with
            | some h, some t => checkExpr fuel headers variables locals false target target' &&
                checkExpr fuel headers variables locals false empty empty' &&
                checkExpr fuel headers variables (h :: t :: locals) false full full'
            | _, _ => false
          | _ => false
        | target :: cases, .matchOption target' empty' full' =>
          match casesParts "None" "Some" cases with
          | some (empty, [v], full) =>
            match binder v with
            | some v => checkExpr fuel headers variables locals false target target' &&
                checkExpr fuel headers variables locals false empty empty' &&
                checkExpr fuel headers variables (v :: locals) false full full'
            | none => false
          | _ => false
        | _, _ => false
      else
        match expression with
        | .app f args => checkExpr fuel headers variables locals true head f &&
            checkExprs fuel headers variables locals tail args
        | _ => false
    | .list [] => false

def checkExprs : Nat → List Header → List String → List Nat → List Node → List Expr → Bool
  | 0, _, _, _, _, _ => false
  | fuel + 1, headers, variables, locals, inputs, outputs =>
    match inputs, outputs with
    | [], [] => true
    | input :: inputs, output :: outputs =>
      checkExpr fuel headers variables locals false input output &&
        checkExprs fuel headers variables locals inputs outputs
    | _, _ => false

def readBindings : Nat → List String → List Node → Option (List (Nat × Ty) × List Node)
  | 0, _, _ => none
  | fuel + 1, variables, bindings =>
    match bindings with
    | [] => some ([], [])
    | .list [.list [id, t], value] :: tail => do
      let id ← binder id
      let t ← readType fuel variables t
      let (rest, values) ← readBindings fuel variables tail
      pure ((id, t) :: rest, value :: values)
    | _ => none
end

def signatureMatches (header : Header) (signature : Signature) : Bool :=
  decide (header.variables.length = signature.typeArity ∧
    header.parameters.map Prod.snd = signature.parameters ∧ header.result = signature.result)

def checkFunctions (fuel : Nat) (all : List Header) :
    List Header → List Signature → List Expr → Bool
  | [], [], [] => true
  | h :: hs, s :: ss, body :: bodies =>
    signatureMatches h s && checkExpr fuel all h.variables (h.parameters.map Prod.fst) false h.body body &&
      checkFunctions fuel all hs ss bodies
  | _, _, _ => false

def checkProgram (fuel : Nat) (forms : List Node) (signatures : List Signature) (bodies : List Expr) : Bool :=
  match forms.mapM (readHeader fuel) with
  | none => false
  | some headers => checkFunctions fuel headers headers signatures bodies

def checkMain (fuel : Nat) (forms : List Node) (index : Nat) : Bool :=
  match forms[index]? with
  | some form@(.list (_ :: identifier :: _)) =>
    name identifier == some "main" &&
      match readHeader fuel form with
      | some h => signatureMatches h ⟨0, [], .integer⟩
      | none => false
  | _ => false

theorem local_reference_preserved (fuel : Nat) (a : CMacroCopy.Atom) (selected index : Nat)
    (accepted : checkExpr (fuel + 1) headers variables locals allowInference
      (.atom a selected) (.var index) = true) : locals[index]? = some selected := by
  exact of_decide_eq_true accepted

theorem signatures_preserved (accepted : signatureMatches header signature = true) :
    header.signature = signature := by
  have h := of_decide_eq_true accepted
  cases header
  cases signature
  simp_all [Header.signature]

end NLisp.ExpansionLowering
