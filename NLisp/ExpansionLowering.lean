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
        | "Float" => some .float
        | "String" => some .string
        | "Character" => some .character
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
  /- Original mixed top-level declaration position. Function-only readers use
  the default; `readProgramHeaders` records the actual position. -/
  order : Nat
  name : String

/- A top-level value keeps its annotated source identity and declaration
position. `order` is the position among all normalized top-level forms, so
initialization order survives when function declarations are interspersed. -/
structure GlobalHeader where
  identity : Nat
  type : Ty
  initializer : Node
  order : Nat
  name : String

def Header.signature (h : Header) : Signature :=
  ⟨h.variables.length, h.parameters.map Prod.snd, h.result⟩

def readHeader (fuel : Nat) : Node → Option Header
  | .list [head, id, .list parameters, result, body] => do
    if name head ≠ some "defun" then none else
    return ⟨← binder id, [], ← readParameters fuel [] parameters, ← readType fuel [] result, body,
      0, (← name id)⟩
  | .list [head, id, .list [quantifier, .list variables, .list parameters, result], body] => do
    if name head ≠ some "defun" ∨ name quantifier ≠ some "forall" then none else
    let variables ← variables.mapM name
    if !Lexical.distinctNames variables then none else
    return ⟨← binder id, variables, ← readParameters fuel variables parameters,
      ← readType fuel variables result, body, 0, (← name id)⟩
  | _ => none

def readGlobalHeader (fuel order : Nat) : Node → Option GlobalHeader
  | .list [head, .list [identifier, annotation], initializer] => do
      if name head ≠ some "define" then none else
      return ⟨← binder identifier, ← readType fuel [] annotation, initializer, order,
        (← name identifier)⟩
  | _ => none

def readGlobalHeaders (fuel : Nat) : Nat → List Node → Option (List GlobalHeader)
  | _, [] => some []
  | order, form :: tail => do
      match readGlobalHeader fuel order form with
      | some value => return value :: (← readGlobalHeaders fuel (order + 1) tail)
      | none =>
          if (readHeader fuel form).isSome then
            readGlobalHeaders fuel (order + 1) tail
          else none

inductive TopLevelDeclaration where
  | function (header : Header)
  | global (header : GlobalHeader)

def TopLevelDeclaration.identity : TopLevelDeclaration → Nat
  | .function header => header.identity
  | .global header => header.identity

def TopLevelDeclaration.name : TopLevelDeclaration → String
  | .function header => header.name
  | .global header => header.name

def TopLevelDeclaration.sourceOrder : TopLevelDeclaration → Nat
  | .function header => header.order
  | .global header => header.order

def TopLevelDeclaration.toNameEntry (declaration : TopLevelDeclaration) :
    CNameResolution.Entry :=
  ⟨declaration.name, declaration.identity, 0⟩

def TopLevelDeclaration.functions : List TopLevelDeclaration → List Header
  | [] => []
  | .function header :: rest => header :: functions rest
  | .global _ :: rest => functions rest

def TopLevelDeclaration.globals : List TopLevelDeclaration → List GlobalHeader
  | [] => []
  | .function _ :: rest => globals rest
  | .global header :: rest => header :: globals rest

structure ProgramHeaders where
  functions : List Header
  globals : List GlobalHeader
  declarations : List TopLevelDeclaration

def ProgramHeaders.namedEnvironment (headers : ProgramHeaders) : List CNameResolution.Entry :=
  headers.declarations.map TopLevelDeclaration.toNameEntry

theorem ProgramHeaders.findNameIndex_selects_declaration
    (headers : ProgramHeaders) (name : String) (binding : CNameResolution.Entry)
    (found : CNameResolution.findName headers.namedEnvironment name = some binding) :
    ∃ index declaration,
      CNameResolution.findNameIndex headers.namedEnvironment name = some index ∧
      headers.declarations.get? index = some declaration ∧
      declaration.identity = binding.identity := by
  obtain ⟨index, indexFound, namedAt⟩ :=
    CNameResolution.findNameIndex_complete headers.namedEnvironment name binding found
  cases declarationAt : headers.declarations.get? index with
  | none =>
      have namedNone : headers.namedEnvironment.get? index = none := by
        simp [ProgramHeaders.namedEnvironment, List.get?_map, declarationAt]
      rw [namedAt] at namedNone
      contradiction
  | some declaration =>
      have selectedEntry : TopLevelDeclaration.toNameEntry declaration = binding := by
        have mapped : (headers.declarations.get? index).map
            TopLevelDeclaration.toNameEntry = some binding := by
          simpa [ProgramHeaders.namedEnvironment, List.get?_map] using namedAt
        have mapped' := mapped
        rw [declarationAt] at mapped'
        exact Option.some.inj (by simpa using mapped')
      have identityAgreement : declaration.identity = binding.identity := by
        have entryIdentity := congrArg CNameResolution.Entry.identity selectedEntry
        simpa [TopLevelDeclaration.toNameEntry] using entryIdentity
      exact ⟨index, declaration, indexFound, declarationAt, identityAgreement⟩

/- Read mixed top-level declarations in one pass. Each output list preserves
its source order, and every define retains its original form position. -/
def readProgramHeaders (fuel : Nat) : Nat → List Node → Option ProgramHeaders
  | _, [] => some ⟨[], [], []⟩
  | order, form :: tail => do
      let rest ← readProgramHeaders fuel (order + 1) tail
      match readHeader fuel form with
      | some function =>
          let ordered := { function with order := order }
          pure ⟨ordered :: rest.functions, rest.globals,
            TopLevelDeclaration.function ordered :: rest.declarations⟩
      | none => do
          let global ← readGlobalHeader fuel order form
          pure ⟨rest.functions, global :: rest.globals,
            TopLevelDeclaration.global global :: rest.declarations⟩

/-- A function found at the head of a mixed top-level source list keeps that
source position in its Header while the recursive tail remains in source
order. -/
theorem readProgramHeaders_cons_function (fuel start : Nat) (form : Node)
    (tail : List Node) (header : Header) (rest : ProgramHeaders)
    (headRead : readHeader fuel form = some header)
    (tailRead : readProgramHeaders fuel (start + 1) tail = some rest) :
    readProgramHeaders fuel start (form :: tail) =
      some ⟨{ header with order := start } :: rest.functions, rest.globals,
        TopLevelDeclaration.function { header with order := start } :: rest.declarations⟩ := by
  simp [readProgramHeaders, headRead, tailRead]

/-- A value found at the head of a mixed top-level source list retains its
source position, and remains ahead of later values in the globals list. -/
theorem readProgramHeaders_cons_global (fuel start : Nat) (form : Node)
    (tail : List Node) (global : GlobalHeader) (rest : ProgramHeaders)
    (headNotFunction : readHeader fuel form = none)
    (headRead : readGlobalHeader fuel start form = some global)
    (tailRead : readProgramHeaders fuel (start + 1) tail = some rest) :
    readProgramHeaders fuel start (form :: tail) =
      some ⟨rest.functions, global :: rest.globals,
        TopLevelDeclaration.global global :: rest.declarations⟩ := by
  simp [readProgramHeaders, headNotFunction, headRead, tailRead]

theorem readProgramHeaders_declarations_project (fuel start : Nat)
    (forms : List Node) (headers : ProgramHeaders)
    (decoded : readProgramHeaders fuel start forms = some headers) :
    TopLevelDeclaration.functions headers.declarations = headers.functions ∧
      TopLevelDeclaration.globals headers.declarations = headers.globals := by
  induction forms generalizing start headers with
  | nil =>
      simp [readProgramHeaders] at decoded
      cases decoded
      simp [TopLevelDeclaration.functions, TopLevelDeclaration.globals]
  | cons form tail ih =>
      unfold readProgramHeaders at decoded
      cases tailRead : readProgramHeaders fuel (start + 1) tail with
      | none => simp [tailRead] at decoded
      | some rest =>
          cases functionRead : readHeader fuel form with
          | some function =>
              simp [tailRead, functionRead] at decoded
              cases decoded
              obtain ⟨functions, globals⟩ := ih (start + 1) rest tailRead
              simp [TopLevelDeclaration.functions, TopLevelDeclaration.globals,
                functions, globals]
          | none =>
              cases globalRead : readGlobalHeader fuel start form with
              | none => simp [tailRead, functionRead, globalRead] at decoded
              | some global =>
                  simp [tailRead, functionRead, globalRead] at decoded
                  cases decoded
                  obtain ⟨functions, globals⟩ := ih (start + 1) rest tailRead
                  simp [TopLevelDeclaration.functions, TopLevelDeclaration.globals,
                    functions, globals]

/- Global values use their position among value declarations for store slots;
the source token remains the key used to resolve references. `order` on the
header is reserved for initialization order and is not a slot number. -/
def globalValueIndex (identity : Nat) : List GlobalHeader → Option Nat
  | [] => none
  | header :: tail =>
      if header.identity = identity then some 0
      else (globalValueIndex identity tail).map Nat.succ

private theorem getElem?_some_lt_length {α : Type} (items : List α)
    (index : Nat) (item : α) (found : items[index]? = some item) :
    index < items.length := by
  simp only [getElem?_def] at found
  split at found
  · assumption
  · contradiction

theorem globalValueIndex_lookup_sound (identity : Nat) (headers : List GlobalHeader)
    (slot : Nat) (resolved : globalValueIndex identity headers = some slot) :
    ∃ header, headers[slot]? = some header ∧ header.identity = identity := by
  induction headers generalizing slot with
  | nil => simp [globalValueIndex, getElem?_def] at resolved
  | cons head tail ih =>
      by_cases same : head.identity = identity
      · simp [globalValueIndex, same] at resolved
        subst slot
        exact ⟨head, by simp [getElem?_def], same⟩
      · cases tailResult : globalValueIndex identity tail with
        | none => simp [globalValueIndex, same, tailResult] at resolved
        | some tailSlot =>
            have slotEq : tailSlot + 1 = slot := by
              simpa [globalValueIndex, same, tailResult] using resolved
            subst slot
            obtain ⟨header, headerEntry, identityEq⟩ := ih tailSlot tailResult
            have tailFound : tail[tailSlot]? = some header := headerEntry
            have tailBound := getElem?_some_lt_length tail tailSlot header tailFound
            have headerEntry' : (head :: tail)[tailSlot + 1]? = some header := by
              have valueEquality : tail[tailSlot] = header := by
                simp only [getElem?_def] at tailFound
                split at tailFound
                · exact Option.some.inj tailFound
                · contradiction
              have headBound : tailSlot + 1 < (head :: tail).length := by
                simpa only [Nat.add_one, List.length_cons] using
                  Nat.succ_lt_succ tailBound
              simp only [List.length_cons, Nat.add_one] at headBound ⊢
              change (if h : tailSlot.succ < tail.length.succ then
                some ((head :: tail)[tailSlot.succ]) else none) = some header
              rw [dif_pos headBound]
              simpa using valueEquality
            exact ⟨header, headerEntry', identityEq⟩

def globalValueReferenceIndex (functionCount identity : Nat)
    (headers : List GlobalHeader) : Option Nat :=
  (globalValueIndex identity headers).map (functionCount + ·)

theorem globalValueReferenceIndex_sound (functionCount identity index : Nat)
    (headers : List GlobalHeader)
    (resolved : globalValueReferenceIndex functionCount identity headers = some index) :
    ∃ slot header, index = functionCount + slot ∧ headers[slot]? = some header ∧
      header.identity = identity := by
  cases valueIndex : globalValueIndex identity headers with
  | none => simp [globalValueReferenceIndex, valueIndex] at resolved
  | some slot =>
      have indexEq : functionCount + slot = index := by
        simpa [globalValueReferenceIndex, valueIndex] using resolved
      obtain ⟨header, headerEntry, identityEq⟩ :=
        globalValueIndex_lookup_sound identity headers slot valueIndex
      exact ⟨slot, header, indexEq.symm, headerEntry, identityEq⟩

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
    (if selected == 39 || selected == 42 || selected == 45 || selected == 48 then
      decide (parameters = [.float, .float])
     else if selected == 33 then decide (parameters = [.boolean, .boolean])
     else if selected == 36 then decide (parameters = [.boolean])
     else decide (parameters = [.integer, .integer])) &&
      match selected, result, body with
      | 3, .integer, .add (.var 0) (.var 1)
      | 6, .integer, .sub (.var 0) (.var 1)
      | 9, .integer, .mul (.var 0) (.var 1)
      | 15, .boolean, .le (.var 0) (.var 1)
      | 12, .boolean, .ite (.le (.var 1) (.var 0)) (.bool false) (.bool true)
      | 18, .boolean, .ite (.le (.var 0) (.var 1)) (.bool false) (.bool true)
      | 21, .boolean, .le (.var 1) (.var 0)
      | 24, .boolean, .intEq (.var 0) (.var 1) => true
      | 33, .boolean, .ite (.var 0) (.var 1)
          (.ite (.var 1) (.bool false) (.bool true)) => true
      | 36, .boolean, .ite (.var 0) (.bool false) (.bool true) => true
      | 39, .float, .floatBin .add (.var 0) (.var 1)
      | 42, .float, .floatBin .sub (.var 0) (.var 1)
      | 45, .float, .floatBin .mul (.var 0) (.var 1)
      | 48, .float, .floatBin .div (.var 0) (.var 1) => true
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
      | .float x => selected == 0 && Lexical.readFloatLiteral a.name == some x
      | .string value => selected == 0 && Lexical.readStringLiteral a.name == some value
      | .character value => selected == 0 && Lexical.readCharacterLiteral a.name == some value
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
