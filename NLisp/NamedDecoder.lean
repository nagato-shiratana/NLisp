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

theorem letParts_lengths {bindings : List Node} {ids : List Nat} {values : List Node}
    (decoded : letParts bindings = some (ids, values)) : ids.length = values.length := by
  induction bindings generalizing ids values with
  | nil =>
      simp [letParts] at decoded
      cases decoded.1
      cases decoded.2
      rfl
  | cons head tail ih =>
      cases head with
      | atom atom selected => simp [letParts] at decoded
      | list items =>
          cases items with
          | nil => simp [letParts] at decoded
          | cons first rest =>
              cases rest with
              | nil => simp [letParts] at decoded
              | cons value extra =>
                  cases extra with
                  | cons extraHead extraTail => simp [letParts] at decoded
                  | nil =>
                      cases first with
                      | atom atom selected => simp [letParts] at decoded
                      | list pair =>
                          cases pair with
                          | nil => simp [letParts] at decoded
                          | cons id pairRest =>
                              cases pairRest with
                              | nil => simp [letParts] at decoded
                              | cons typ pairExtra =>
                                  cases pairExtra with
                                  | cons extraHead extraTail => simp [letParts] at decoded
                                  | nil =>
                                      cases hBinder : binder id with
                                      | none => simp [letParts, hBinder] at decoded
                                      | some binderId =>
                                          cases tailParts : letParts tail with
                                          | none => simp [letParts, hBinder, tailParts] at decoded
                                          | some parts =>
                                              rcases parts with ⟨tailIds, tailValues⟩
                                              have decodedParts :
                                                  some (binderId :: tailIds, value :: tailValues) =
                                                    some (ids, values) := by
                                                 simpa [letParts, hBinder, tailParts] using decoded
                                              have pairEq :
                                                  (binderId :: tailIds, value :: tailValues) =
                                                    (ids, values) := Option.some.inj decodedParts
                                              cases pairEq
                                              simp [ih tailParts]

def readPrimitive : Nat → Option Expr
  | 3 => some (.lam [0, 1] (.add (.var 0) (.var 1)))
  | 6 => some (.lam [0, 1] (.sub (.var 0) (.var 1)))
  | 9 => some (.lam [0, 1] (.mul (.var 0) (.var 1)))
  | 15 => some (.lam [0, 1] (.le (.var 0) (.var 1)))
  | 24 => some (.lam [0, 1] (.intEq (.var 0) (.var 1)))
  | _ => none

mutual
def decodeLetMany : Nat → List Header → List Node → Node → Option Expr
  | 0, _, _, _ => none
  | fuel + 1, headers, bindings, body => do
    let (ids, values) ← letParts bindings
    let initializers ← decodeExprs fuel headers values
    let body ← decodeExpr fuel headers body
    pure (.letMany ids initializers body)

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
        | [.list bindings, body] => decodeLetMany fuel headers bindings body
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

theorem decodeExprs_length {fuel : Nat} {headers : List Header} {nodes : List Node}
    {expressions : List Expr}
    (decoded : decodeExprs fuel headers nodes = some expressions) :
    expressions.length = nodes.length := by
  induction nodes generalizing fuel expressions with
  | nil =>
      cases fuel with
      | zero => simp [decodeExprs] at decoded
      | succ fuel => simp [decodeExprs] at decoded; subst expressions; rfl
  | cons node tail ih =>
      cases fuel with
      | zero => simp [decodeExprs] at decoded
      | succ fuel =>
          cases expressionResult : decodeExpr fuel headers node with
          | none => simp [decodeExprs, expressionResult] at decoded
          | some expression =>
              cases tailResult : decodeExprs fuel headers tail with
              | none => simp [decodeExprs, expressionResult, tailResult] at decoded
              | some tailExpressions =>
                  have decodedTail : decodeExprs fuel headers tail = some tailExpressions := tailResult
                  have lengthTail := ih decodedTail
                  have decodedEq : expressions = expression :: tailExpressions := by
                    simpa [decodeExprs, expressionResult, tailResult] using decoded.symm
                  subst expressions
                  simp [lengthTail]

theorem decodeLetMany_lengths {fuel : Nat} {headers : List Header}
    {bindings : List Node} {body : Node} {ids : List Nat}
    {initializers : List Expr} {decodedBody : Expr}
    (decoded : decodeLetMany fuel headers bindings body =
      some (Expr.letMany ids initializers decodedBody)) :
    ids.length = initializers.length := by
  cases fuel with
  | zero => simp [decodeLetMany] at decoded
  | succ fuel =>
      cases parts : letParts bindings with
      | none => simp [decodeLetMany, parts] at decoded
      | some pair =>
          rcases pair with ⟨partIds, values⟩
          cases expressions : decodeExprs fuel headers values with
          | none => simp [decodeLetMany, parts, expressions] at decoded
          | some partInitializers =>
              cases bodyResult : decodeExpr fuel headers body with
              | none => simp [decodeLetMany, parts, expressions, bodyResult] at decoded
              | some partBody =>
                  have resultEq :
                      Expr.letMany partIds partInitializers partBody =
                        Expr.letMany ids initializers decodedBody := by
                    simpa [decodeLetMany, parts, expressions, bodyResult] using decoded
                  cases resultEq
                  have idsLength := letParts_lengths parts
                  have initializersLength := decodeExprs_length expressions
                  omega

macro "let_layouts_aligned_using " recursor:term : term => `(
  $recursor
    (motive_1 := fun _ => Bool)
    (motive_2 := fun _ => Bool)
    (fun _ _ => true)
    (fun _ _ => true)
    (fun _ _ => true)
    (fun _ _ => true)
    (fun _ => true)
    (fun _ _ body _ => body)
    (fun _ _ function arguments _ => function && arguments)
    (fun _ _ _ condition yes no _ => condition && yes && no)
    (fun _ _ left right _ => left && right)
    (fun _ _ left right _ => left && right)
    (fun _ _ left right _ => left && right)
    (fun _ _ left right _ => left && right)
    (fun _ _ left right _ => left && right)
    (fun ids _ _ values body _ => decide (ids.length = values.length) && values && body)
    (fun _ _ first rest _ => first && rest)
    (fun _ => true)
    (fun _ _ head tail _ => head && tail)
    (fun _ => true)
    (fun _ value _ => value)
    (fun _ _ _ _ target empty full _ => target && empty && full)
    (fun _ _ _ _ target empty full _ => target && empty && full)
    (fun _ => true)
    (fun _ _ head tail _ => head && tail))

def letLayoutsAligned (expression : Expr) : Bool :=
  (let_layouts_aligned_using Expr.rec) expression

theorem letLayoutsAligned_letMany_lengths (ids : List Nat) (initializers : List Expr)
    (body : Expr)
    (aligned : letLayoutsAligned (.letMany ids initializers body) = true) :
    ids.length = initializers.length := by
  change (decide (ids.length = initializers.length) &&
    (let_layouts_aligned_using Expr.rec_1) initializers &&
    (let_layouts_aligned_using Expr.rec) body) = true at aligned
  have components := Bool.and_eq_true.mp aligned
  have arity := Bool.and_eq_true.mp components.1
  exact of_decide_eq_true arity.1

def decodeExprChecked (fuel : Nat) (headers : List Header) (node : Node) : Option Expr := do
  let expression ← decodeExpr fuel headers node
  if letLayoutsAligned expression then some expression else none

theorem decodeExprChecked_spec {fuel : Nat} {headers : List Header} {node : Node}
    {expression : Expr} (decoded : decodeExprChecked fuel headers node = some expression) :
    decodeExpr fuel headers node = some expression ∧ letLayoutsAligned expression = true := by
  unfold decodeExprChecked at decoded
  cases raw : decodeExpr fuel headers node with
  | none => simp [raw] at decoded
  | some result =>
      cases aligned : letLayoutsAligned result with
      | false => simp [raw, aligned] at decoded
      | true =>
          simp [raw, aligned] at decoded
          cases decoded
          exact ⟨raw, aligned⟩

theorem decodeExprChecked_letMany_lengths {fuel : Nat} {headers : List Header}
    {node : Node} {ids : List Nat} {initializers : List Expr} {body : Expr}
    (decoded : decodeExprChecked fuel headers node =
      some (.letMany ids initializers body)) :
    ids.length = initializers.length := by
  exact letLayoutsAligned_letMany_lengths ids initializers body
    (decodeExprChecked_spec decoded).2

theorem decodeExprChecked_letMany_evaluation_reflected
    {fuel : Nat} {headers : List Header} {node : Node}
    {ids : List Nat} {initializers : List Expr} {body : Expr}
    (decoded : decodeExprChecked fuel headers node =
      some (.letMany ids initializers body))
    (program : Definitions) (env : Environment)
    (argumentsReflected : ∀ {irValues},
      PolyIR.ArgumentsEvaluate (lowerDefinitions program) (lowerEnv env)
        (lowerMany (identities env) initializers) irValues →
      ∃ sourceValues, ArgumentsEvaluate program env initializers sourceValues ∧
        lowerValues sourceValues = irValues)
    (bodyReflected : ∀ (sourceValues : List Value) (irValues : List PolyIR.Value),
      sourceValues.length = ids.length → lowerValues sourceValues = irValues →
      ∀ {value},
        PolyIR.Evaluates (lowerDefinitions program) (irValues ++ lowerEnv env)
          (lower (ids ++ identities env) body) value →
        ∃ sourceValue, Evaluates program (bind ids sourceValues ++ env) body sourceValue ∧
          lowerValue sourceValue = value)
    (value : PolyIR.Value)
    (evaluated : PolyIR.Evaluates (lowerDefinitions program) (lowerEnv env)
      (lower (identities env) (.letMany ids initializers body)) value) :
    ∃ sourceValue, Evaluates program env (.letMany ids initializers body) sourceValue ∧
      lowerValue sourceValue = value := by
  exact letMany_evaluation_reflected program env ids initializers body
    (decodeExprChecked_letMany_lengths decoded) argumentsReflected bodyReflected
    value evaluated

def definitionsLetLayoutsAligned (definitions : Definitions) : Bool :=
  definitions.all (fun definition => letLayoutsAligned definition.2)

def decodeFunctions (fuel : Nat) (headers : List Header) : List Header → Option Definitions
  | [] => some []
  | h :: tail => do
    let body ← decodeExprChecked fuel headers h.body
    let rest ← decodeFunctions fuel headers tail
    pure ((h.parameters.map Prod.fst, body) :: rest)

/- For decoding only, an annotated top-level value is represented as a
zero-argument header. This puts value references after all function indices;
the header body is retained as the initializer node. -/
def GlobalHeader.decodeHeader (header : GlobalHeader) : Header :=
  ⟨header.identity, [], [], header.type, header.initializer⟩

def decodeHeadersWithGlobals (functions : List Header) (values : List GlobalHeader) :
    List Header :=
  functions ++ values.map GlobalHeader.decodeHeader

theorem globalIndex_mappedValues (identity : Nat) (values : List GlobalHeader) :
    globalIndex identity (values.map GlobalHeader.decodeHeader) =
      globalValueIndex identity values := by
  induction values with
  | nil => rfl
  | cons header tail ih =>
      by_cases same : header.identity = identity
      · simp [globalIndex, globalValueIndex, GlobalHeader.decodeHeader, same]
      · simp [globalIndex, globalValueIndex, GlobalHeader.decodeHeader, same, ih]

theorem globalIndex_append_of_none (identity : Nat) (prefix suffix : List Header)
    (prefixMissing : globalIndex identity prefix = none) :
    globalIndex identity (prefix ++ suffix) =
      (globalIndex identity suffix).map (prefix.length + ·) := by
  induction prefix with
  | nil => simp [globalIndex]
  | cons head tail ih =>
      by_cases same : head.identity = identity
      · simp [globalIndex, same] at prefixMissing
      · have tailMissing : globalIndex identity tail = none := by
          simpa [globalIndex, same] using prefixMissing
        cases suffixResult : globalIndex identity suffix with
        | none => simp [globalIndex, same, tailMissing, suffixResult]
        | some value =>
            have offsetEq : Nat.succ (tail.length + value) = (tail.length + 1) + value := by
              omega
            simp [globalIndex, same, tailMissing, ih tailMissing, suffixResult,
              List.length_cons, offsetEq]

theorem globalIndex_value_reference (identity slot : Nat) (functions : List Header)
    (values : List GlobalHeader)
    (functionMissing : globalIndex identity functions = none)
    (valueFound : globalValueIndex identity values = some slot) :
    globalIndex identity (decodeHeadersWithGlobals functions values) =
      some (functions.length + slot) := by
  rw [decodeHeadersWithGlobals, globalIndex_append_of_none identity functions
    (values.map GlobalHeader.decodeHeader) functionMissing, globalIndex_mappedValues]
  simp [valueFound]

def decodeGlobalInitializers (fuel : Nat) (functions : List Header)
    (values : List GlobalHeader) : Option (List Expr) :=
  decodeExprs fuel (decodeHeadersWithGlobals functions values)
    (values.map GlobalHeader.initializer)

theorem decodeGlobalInitializers_length {fuel : Nat} {functions : List Header}
    {values : List GlobalHeader} {initializers : List Expr}
    (decoded : decodeGlobalInitializers fuel functions values = some initializers) :
    initializers.length = values.length := by
  have expressionsDecoded :
      decodeExprs fuel (decodeHeadersWithGlobals functions values)
        (values.map GlobalHeader.initializer) = some initializers := by
    simpa [decodeGlobalInitializers] using decoded
  have length := decodeExprs_length expressionsDecoded
  simpa using length

def decodeProgramWithGlobals (fuel : Nat) (functions : List Header)
    (values : List GlobalHeader) :
    Option (Definitions × List Ty × List Expr) := do
  let headers := decodeHeadersWithGlobals functions values
  let definitions ← decodeFunctions fuel headers functions
  let initializers ← decodeGlobalInitializers fuel functions values
  return (definitions, values.map GlobalHeader.type, initializers)

def decodeTopLevelProgram (fuel : Nat) (forms : List Node) :
    Option (Definitions × List Surface.Ty × List Expr) := do
  let layout ← readProgramHeaders fuel 0 forms
  decodeProgramWithGlobals fuel layout.functions layout.globals

theorem decodeProgramWithGlobals_layout (fuel : Nat) (functions : List Header)
    (values : List GlobalHeader) (definitions : Definitions) (slotTypes : List Surface.Ty)
    (initializers : List Expr)
    (decoded : decodeProgramWithGlobals fuel functions values =
      some (definitions, slotTypes, initializers)) :
    slotTypes = values.map GlobalHeader.type ∧ slotTypes.length = initializers.length := by
  unfold decodeProgramWithGlobals at decoded
  cases functionResult : decodeFunctions fuel (decodeHeadersWithGlobals functions values) functions with
  | none => simp [functionResult] at decoded
  | some decodedDefinitions =>
      cases initializerResult : decodeGlobalInitializers fuel functions values with
      | none => simp [functionResult, initializerResult] at decoded
      | some decodedInitializers =>
          have resultEq :
              (decodedDefinitions, values.map GlobalHeader.type, decodedInitializers) =
                (definitions, slotTypes, initializers) := by
            simpa [functionResult, initializerResult] using decoded
          cases resultEq
          exact ⟨rfl, decodeGlobalInitializers_length initializerResult⟩

theorem decodeTopLevelProgram_layout (fuel : Nat) (forms : List Node)
    (definitions : Definitions) (slotTypes : List Surface.Ty) (initializers : List Expr)
    (decoded : decodeTopLevelProgram fuel forms =
      some (definitions, slotTypes, initializers)) :
    slotTypes.length = initializers.length := by
  unfold decodeTopLevelProgram at decoded
  cases layoutResult : readProgramHeaders fuel 0 forms with
  | none => simp [layoutResult] at decoded
  | some layout =>
      have innerDecoded :
          decodeProgramWithGlobals fuel layout.functions layout.globals =
            some (definitions, slotTypes, initializers) := by
        simpa [layoutResult] using decoded
      exact (decodeProgramWithGlobals_layout fuel layout.functions layout.globals
        definitions slotTypes initializers innerDecoded).2

theorem decodeFunctions_letLayoutsAligned (fuel : Nat) (headers : List Header)
    (functions : List Header) (definitions : Definitions)
    (decoded : decodeFunctions fuel headers functions = some definitions) :
    definitionsLetLayoutsAligned definitions = true := by
  induction functions generalizing definitions with
  | nil => simp [decodeFunctions, definitionsLetLayoutsAligned] at decoded ⊢
  | cons header tail ih =>
      cases bodyResult : decodeExprChecked fuel headers header.body with
      | none => simp [decodeFunctions, bodyResult] at decoded
      | some body =>
          cases restResult : decodeFunctions fuel headers tail with
          | none => simp [decodeFunctions, bodyResult, restResult] at decoded
          | some rest =>
              have tailAligned : definitionsLetLayoutsAligned rest = true :=
                ih restResult
              have bodyAligned := (decodeExprChecked_spec bodyResult).2
              simp [decodeFunctions, bodyResult, restResult,
                definitionsLetLayoutsAligned, bodyAligned, tailAligned]

def decodeProgram (fuel : Nat) (forms : List Node) : Option Definitions := do
  let headers ← forms.mapM (readHeader fuel)
  decodeFunctions fuel headers headers

theorem decodeProgram_letLayoutsAligned (fuel : Nat) (forms : List Node)
    (definitions : Definitions)
    (decoded : decodeProgram fuel forms = some definitions) :
    definitionsLetLayoutsAligned definitions = true := by
  unfold decodeProgram at decoded
  cases headersResult : forms.mapM (readHeader fuel) with
  | none => simp [headersResult] at decoded
  | some headers =>
      have functionsDecoded : decodeFunctions fuel headers headers = some definitions := by
        simpa [headersResult] using decoded
      exact decodeFunctions_letLayoutsAligned fuel headers headers definitions functionsDecoded

theorem definitionsLetLayoutsAligned_mem (definitions : Definitions)
    (aligned : definitionsLetLayoutsAligned definitions = true)
    (definition : List Nat × Expr) (member : definition ∈ definitions) :
    letLayoutsAligned definition.2 = true := by
  unfold definitionsLetLayoutsAligned at aligned
  exact List.all_eq_true.mp aligned definition member

theorem decodeProgram_member_letMany_lengths (fuel : Nat) (forms : List Node)
    (definitions : Definitions) (decoded : decodeProgram fuel forms = some definitions)
    (parameters ids : List Nat) (initializers : List Expr) (body : Expr)
    (member : (parameters, .letMany ids initializers body) ∈ definitions) :
    ids.length = initializers.length := by
  apply letLayoutsAligned_letMany_lengths ids initializers body
  exact definitionsLetLayoutsAligned_mem definitions
    (decodeProgram_letLayoutsAligned fuel forms definitions decoded)
    (parameters, .letMany ids initializers body) member

private theorem definition_mem_of_getElem? {definitions : Definitions} {index : Nat}
    {definition : List Nat × Expr} (found : definitions[index]? = some definition) :
    definition ∈ definitions := by
  induction definitions generalizing index with
  | nil =>
      have impossible : False := by
        have indexInvalid : ¬ index < 0 := by omega
        simp [getElem?_def, indexInvalid] at found
      exact False.elim impossible
  | cons head tail ih =>
      cases index with
      | zero =>
          have same : head = definition := by simpa [getElem?_def] using found
          subst definition
          simp
      | succ index =>
          have foundTail : tail[index]? = some definition := by
            simpa [getElem?_def, List.length_cons, Nat.succ_lt_succ_iff] using found
          exact List.mem_cons_of_mem _ (ih foundTail)

theorem decodeProgram_lookup_letMany_lengths (fuel : Nat) (forms : List Node)
    (definitions : Definitions) (decoded : decodeProgram fuel forms = some definitions)
    {index : Nat} {parameters ids : List Nat} {initializers : List Expr} {body : Expr}
    (found : definitions[index]? = some (parameters, .letMany ids initializers body)) :
    ids.length = initializers.length :=
  decodeProgram_member_letMany_lengths fuel forms definitions decoded parameters ids
    initializers body (definition_mem_of_getElem? found)

end NLisp.Named
