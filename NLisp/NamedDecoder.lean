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
  | 12 => some (.lam [0, 1]
      (.ite (.le (.var 1) (.var 0)) (.bool false) (.bool true)))
  | 18 => some (.lam [0, 1]
      (.ite (.le (.var 0) (.var 1)) (.bool false) (.bool true)))
  | 21 => some (.lam [0, 1] (.le (.var 1) (.var 0)))
  | 24 => some (.lam [0, 1] (.intEq (.var 0) (.var 1)))
  | 33 => some (.lam [0, 1]
      (.ite (.var 0) (.var 1) (.ite (.var 1) (.bool false) (.bool true))))
  | 36 => some (.lam [0] (.ite (.var 0) (.bool false) (.bool true)))
  | 39 => some (.lam [0, 1] (.floatBin .add (.var 0) (.var 1)))
  | 42 => some (.lam [0, 1] (.floatBin .sub (.var 0) (.var 1)))
  | 45 => some (.lam [0, 1] (.floatBin .mul (.var 0) (.var 1)))
  | 48 => some (.lam [0, 1] (.floatBin .div (.var 0) (.var 1)))
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
      else if a.name.startsWith "\"" then
        if selected = 0 then (Lexical.readStringLiteral a.name).map Expr.string else none
      else if a.name.startsWith "#\\" then
        if selected = 0 then (Lexical.readCharacterLiteral a.name).map Expr.character else none
      else if Lexical.floatLiteral a.name.toList then
        if selected = 0 then (Lexical.readFloatLiteral a.name).map Expr.float else none
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

mutual
def letLayoutsAligned : Expr → Bool
  | .var _ | .global _ | .bool _ | .int _ | .float _ | .string _ | .character _ | .unit | .nil | .none => true
  | .lam _ body | .some body => letLayoutsAligned body
  | .app function arguments => letLayoutsAligned function && letLayoutsAlignedList arguments
  | .ite condition yes no =>
      letLayoutsAligned condition && letLayoutsAligned yes && letLayoutsAligned no
  | .add left right | .sub left right | .mul left right | .le left right
  | .intEq left right | .floatBin _ left right | .cons left right =>
      letLayoutsAligned left && letLayoutsAligned right
  | .letMany ids initializers body =>
      decide (ids.length = initializers.length) &&
        letLayoutsAlignedList initializers && letLayoutsAligned body
  | .begin first rest => letLayoutsAligned first && letLayoutsAlignedList rest
  | .matchList target empty _ _ full =>
      letLayoutsAligned target && letLayoutsAligned empty && letLayoutsAligned full
  | .matchOption target empty _ full =>
      letLayoutsAligned target && letLayoutsAligned empty && letLayoutsAligned full

def letLayoutsAlignedList : List Expr → Bool
  | [] => true
  | head :: tail => letLayoutsAligned head && letLayoutsAlignedList tail
end

/-- Immediate source-expression children, excluding binder identifiers and
type annotations. This is the structural frontier traversed by evaluation. -/
def expressionChildren : Expr → List Expr
  | .var _ | .global _ | .bool _ | .int _ | .float _ | .string _ | .character _ | .unit | .nil | .none => []
  | .lam _ body | .some body => [body]
  | .app function arguments => function :: arguments
  | .ite condition yes no => [condition, yes, no]
  | .add left right | .sub left right | .mul left right | .le left right
  | .intEq left right | .floatBin _ left right | .cons left right => [left, right]
  | .letMany _ initializers body => body :: initializers
  | .begin first rest => first :: rest
  | .matchList target empty _ _ full | .matchOption target empty _ full =>
      [target, empty, full]

/-- Any expression selected from an aligned expression list is itself
well-scoped with respect to parallel-let binder/value arities. This is the
list-elimination fact needed by the mutual evaluation-reflection proof for
applications, initializers, and begin sequences. -/
theorem letLayoutsAlignedList_mem (expressions : List Expr)
    (aligned : letLayoutsAlignedList expressions = true) {expression : Expr}
    (member : expression ∈ expressions) :
    letLayoutsAligned expression = true := by
  induction expressions with
  | nil => simp at member
  | cons head tail ih =>
      simp only [letLayoutsAlignedList, Bool.and_eq_true] at aligned
      rcases List.mem_cons.mp member with same | rest
      · simpa [same] using aligned.1
      · exact ih aligned.2 rest

theorem letLayoutsAligned_app_parts (function : Expr) (arguments : List Expr)
    (aligned : letLayoutsAligned (.app function arguments) = true) :
    letLayoutsAligned function = true ∧ letLayoutsAlignedList arguments = true := by
  simpa [letLayoutsAligned, Bool.and_eq_true] using aligned

theorem letLayoutsAligned_lam_body (parameters : List Nat)
    (body : Expr) (aligned : letLayoutsAligned (.lam parameters body) = true) :
    letLayoutsAligned body = true := by
  simpa [letLayoutsAligned] using aligned

theorem letLayoutsAligned_ite_parts (condition yes no : Expr)
    (aligned : letLayoutsAligned (.ite condition yes no) = true) :
    letLayoutsAligned condition = true ∧ letLayoutsAligned yes = true ∧
      letLayoutsAligned no = true := by
  have parts := aligned
  simp only [letLayoutsAligned, Bool.and_eq_true] at parts
  exact ⟨parts.1.1, parts.1.2, parts.2⟩

theorem letLayoutsAligned_letMany_parts (ids : List Nat) (initializers : List Expr)
    (body : Expr) (aligned : letLayoutsAligned (.letMany ids initializers body) = true) :
    ids.length = initializers.length ∧ letLayoutsAlignedList initializers = true ∧
      letLayoutsAligned body = true := by
  have parts := aligned
  simp only [letLayoutsAligned, Bool.and_eq_true, decide_eq_true_eq] at parts
  exact ⟨parts.1.1, parts.1.2, parts.2⟩

theorem letLayoutsAligned_begin_parts (first : Expr) (rest : List Expr)
    (aligned : letLayoutsAligned (.begin first rest) = true) :
    letLayoutsAligned first = true ∧ letLayoutsAlignedList rest = true := by
  simpa [letLayoutsAligned, Bool.and_eq_true] using aligned

theorem letLayoutsAligned_add_parts (left right : Expr)
    (aligned : letLayoutsAligned (.add left right) = true) :
    letLayoutsAligned left = true ∧ letLayoutsAligned right = true := by
  simpa [letLayoutsAligned, Bool.and_eq_true] using aligned

theorem letLayoutsAligned_sub_parts (left right : Expr)
    (aligned : letLayoutsAligned (.sub left right) = true) :
    letLayoutsAligned left = true ∧ letLayoutsAligned right = true := by
  simpa [letLayoutsAligned, Bool.and_eq_true] using aligned

theorem letLayoutsAligned_mul_parts (left right : Expr)
    (aligned : letLayoutsAligned (.mul left right) = true) :
    letLayoutsAligned left = true ∧ letLayoutsAligned right = true := by
  simpa [letLayoutsAligned, Bool.and_eq_true] using aligned

theorem letLayoutsAligned_le_parts (left right : Expr)
    (aligned : letLayoutsAligned (.le left right) = true) :
    letLayoutsAligned left = true ∧ letLayoutsAligned right = true := by
  simpa [letLayoutsAligned, Bool.and_eq_true] using aligned

theorem letLayoutsAligned_intEq_parts (left right : Expr)
    (aligned : letLayoutsAligned (.intEq left right) = true) :
    letLayoutsAligned left = true ∧ letLayoutsAligned right = true := by
  simpa [letLayoutsAligned, Bool.and_eq_true] using aligned

theorem letLayoutsAligned_floatBin_parts (op : Surface.FloatBinOp) (left right : Expr)
    (aligned : letLayoutsAligned (.floatBin op left right) = true) :
    letLayoutsAligned left = true ∧ letLayoutsAligned right = true := by
  simpa [letLayoutsAligned, Bool.and_eq_true] using aligned

theorem letLayoutsAligned_cons_parts (head tail : Expr)
    (aligned : letLayoutsAligned (.cons head tail) = true) :
    letLayoutsAligned head = true ∧ letLayoutsAligned tail = true := by
  simpa [letLayoutsAligned, Bool.and_eq_true] using aligned

theorem letLayoutsAligned_some_body (value : Expr)
    (aligned : letLayoutsAligned (.some value) = true) :
    letLayoutsAligned value = true := by
  simpa [letLayoutsAligned] using aligned

theorem letLayoutsAligned_matchList_parts (target empty full : Expr)
    (head tail : Nat) (aligned : letLayoutsAligned (.matchList target empty head tail full) = true) :
    letLayoutsAligned target = true ∧ letLayoutsAligned empty = true ∧
      letLayoutsAligned full = true := by
  have parts := aligned
  simp only [letLayoutsAligned, Bool.and_eq_true] at parts
  exact ⟨parts.1.1, parts.1.2, parts.2⟩

theorem letLayoutsAligned_matchOption_parts (target empty full : Expr)
    (binder : Nat) (aligned : letLayoutsAligned (.matchOption target empty binder full) = true) :
    letLayoutsAligned target = true ∧ letLayoutsAligned empty = true ∧
      letLayoutsAligned full = true := by
  have parts := aligned
  simp only [letLayoutsAligned, Bool.and_eq_true] at parts
  exact ⟨parts.1.1, parts.1.2, parts.2⟩

/-- The let-layout invariant is hereditary over every immediate expression
child, including initializers and bodies beneath binders. -/
theorem letLayoutsAligned_children (expression : Expr)
    (aligned : letLayoutsAligned expression = true) :
    ∀ child ∈ expressionChildren expression, letLayoutsAligned child = true := by
  cases expression with
  | var _ | global _ | bool _ | int _ | float _ | string _ | character _ | unit | nil | none => simp [expressionChildren]
  | lam parameters body =>
      intro child member
      simp [expressionChildren] at member
      subst child
      exact letLayoutsAligned_lam_body parameters body aligned
  | app function arguments =>
      obtain ⟨functionAligned, argumentsAligned⟩ :=
        letLayoutsAligned_app_parts function arguments aligned
      intro child member
      simp only [expressionChildren, List.mem_cons] at member
      rcases member with same | inArguments
      · subst child
        exact functionAligned
      · exact letLayoutsAlignedList_mem arguments argumentsAligned inArguments
  | ite condition yes no =>
      obtain ⟨conditionAligned, yesAligned, noAligned⟩ :=
        letLayoutsAligned_ite_parts condition yes no aligned
      intro child member
      simp only [expressionChildren, List.mem_cons] at member
      rcases member with same | same | rest
      · subst child; exact conditionAligned
      · subst child; exact yesAligned
      · rcases rest with same | impossible
        · subst child; exact noAligned
        · simp at impossible
  | add left right =>
      obtain ⟨leftAligned, rightAligned⟩ := letLayoutsAligned_add_parts left right aligned
      intro child member
      simp only [expressionChildren, List.mem_cons] at member
      rcases member with same | member
      · subst child; exact leftAligned
      · simp at member
        subst child
        exact rightAligned
  | sub left right =>
      obtain ⟨leftAligned, rightAligned⟩ := letLayoutsAligned_sub_parts left right aligned
      intro child member
      simp only [expressionChildren, List.mem_cons] at member
      rcases member with same | member
      · subst child; exact leftAligned
      · simp at member
        subst child
        exact rightAligned
  | mul left right =>
      obtain ⟨leftAligned, rightAligned⟩ := letLayoutsAligned_mul_parts left right aligned
      intro child member
      simp only [expressionChildren, List.mem_cons] at member
      rcases member with same | member
      · subst child; exact leftAligned
      · simp at member
        subst child
        exact rightAligned
  | le left right =>
      obtain ⟨leftAligned, rightAligned⟩ := letLayoutsAligned_le_parts left right aligned
      intro child member
      simp only [expressionChildren, List.mem_cons] at member
      rcases member with same | member
      · subst child; exact leftAligned
      · simp at member
        subst child
        exact rightAligned
  | intEq left right =>
      obtain ⟨leftAligned, rightAligned⟩ := letLayoutsAligned_intEq_parts left right aligned
      intro child member
      simp only [expressionChildren, List.mem_cons] at member
      rcases member with same | member
      · subst child; exact leftAligned
      · simp at member
        subst child
        exact rightAligned
  | floatBin op left right =>
      obtain ⟨leftAligned, rightAligned⟩ := letLayoutsAligned_floatBin_parts op left right aligned
      intro child member
      simp only [expressionChildren, List.mem_cons] at member
      rcases member with same | member
      · subst child; exact leftAligned
      · simp at member
        subst child
        exact rightAligned
  | letMany ids initializers body =>
      obtain ⟨_, initializersAligned, bodyAligned⟩ :=
        letLayoutsAligned_letMany_parts ids initializers body aligned
      intro child member
      simp only [expressionChildren, List.mem_cons] at member
      rcases member with same | member
      · subst child; exact bodyAligned
      · exact letLayoutsAlignedList_mem initializers initializersAligned member
  | begin first rest =>
      obtain ⟨firstAligned, restAligned⟩ := letLayoutsAligned_begin_parts first rest aligned
      intro child member
      simp only [expressionChildren, List.mem_cons] at member
      rcases member with same | member
      · subst child; exact firstAligned
      · exact letLayoutsAlignedList_mem rest restAligned member
  | cons head tail =>
      obtain ⟨headAligned, tailAligned⟩ := letLayoutsAligned_cons_parts head tail aligned
      intro child member
      simp only [expressionChildren, List.mem_cons] at member
      rcases member with same | member
      · subst child; exact headAligned
      · simp at member
        subst child
        exact tailAligned
  | some value =>
      intro child member
      simp [expressionChildren] at member
      subst child
      exact letLayoutsAligned_some_body value aligned
  | matchList target empty head tail full =>
      obtain ⟨targetAligned, emptyAligned, fullAligned⟩ :=
        letLayoutsAligned_matchList_parts target empty full head tail aligned
      intro child member
      simp only [expressionChildren, List.mem_cons] at member
      rcases member with same | same | rest
      · subst child; exact targetAligned
      · subst child; exact emptyAligned
      · rcases rest with same | impossible
        · subst child; exact fullAligned
        · simp at impossible
  | matchOption target empty binder full =>
      obtain ⟨targetAligned, emptyAligned, fullAligned⟩ :=
        letLayoutsAligned_matchOption_parts target empty full binder aligned
      intro child member
      simp only [expressionChildren, List.mem_cons] at member
      rcases member with same | same | rest
      · subst child; exact targetAligned
      · subst child; exact emptyAligned
      · rcases rest with same | impossible
        · subst child; exact fullAligned
        · simp at impossible

theorem letLayoutsAligned_letMany_lengths (ids : List Nat) (initializers : List Expr)
    (body : Expr)
    (aligned : letLayoutsAligned (.letMany ids initializers body) = true) :
    ids.length = initializers.length := by
  simp only [letLayoutsAligned] at aligned
  change (decide (ids.length = initializers.length) &&
    letLayoutsAlignedList initializers && letLayoutsAligned body) = true at aligned
  have components :
      (decide (ids.length = initializers.length) &&
        letLayoutsAlignedList initializers) = true ∧
      letLayoutsAligned body = true := by
    simpa only [Bool.and_eq_true] using aligned
  have arity : decide (ids.length = initializers.length) = true ∧
      letLayoutsAlignedList initializers = true := by
    simpa only [Bool.and_eq_true] using components.1
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
          have resultEq : result = expression := by
            apply Option.some.inj
            simpa [decodeExprChecked, raw, aligned] using decoded
          rw [← resultEq]
          exact ⟨rfl, aligned⟩

/- Global value initializers use the same recursive let-layout validation as
function bodies. The unchecked decoder remains available for intermediate
subexpressions, while this list decoder is the top-level acceptance boundary. -/
def decodeExprsChecked : Nat → List Header → List Node → Option (List Expr)
  | 0, _, _ => none
  | fuel + 1, headers, [] => some []
  | fuel + 1, headers, node :: tail => do
      let expression ← decodeExprChecked fuel headers node
      let rest ← decodeExprsChecked fuel headers tail
      pure (expression :: rest)

theorem decodeExprsChecked_length {fuel : Nat} {headers : List Header}
    {nodes : List Node} {expressions : List Expr}
    (decoded : decodeExprsChecked fuel headers nodes = some expressions) :
    expressions.length = nodes.length := by
  induction nodes generalizing fuel expressions with
  | nil =>
      cases fuel with
      | zero => simp [decodeExprsChecked] at decoded
      | succ fuel =>
          simp [decodeExprsChecked] at decoded
          cases decoded
          rfl
  | cons node tail ih =>
      cases fuel with
      | zero => simp [decodeExprsChecked] at decoded
      | succ fuel =>
          cases headResult : decodeExprChecked fuel headers node with
          | none => simp [decodeExprsChecked, headResult] at decoded
          | some head =>
              cases tailResult : decodeExprsChecked fuel headers tail with
              | none => simp [decodeExprsChecked, headResult, tailResult] at decoded
              | some rest =>
                  have resultEq : head :: rest = expressions := by
                    simpa [decodeExprsChecked, headResult, tailResult] using decoded
                  cases resultEq
                  simp only [List.length_cons]
                  have tailLength := ih (fuel := fuel) (expressions := rest) tailResult
                  simp [tailLength]

theorem decodeExprsChecked_aligned {fuel : Nat} {headers : List Header}
    {nodes : List Node} {expressions : List Expr}
    (decoded : decodeExprsChecked fuel headers nodes = some expressions) :
    ∀ expression ∈ expressions, letLayoutsAligned expression = true := by
  induction nodes generalizing fuel expressions with
  | nil =>
      cases fuel with
      | zero => simp [decodeExprsChecked] at decoded
      | succ fuel =>
          simp [decodeExprsChecked] at decoded
          cases decoded
          intro expression member
          simp at member
  | cons node tail ih =>
      cases fuel with
      | zero => simp [decodeExprsChecked] at decoded
      | succ fuel =>
          cases headResult : decodeExprChecked fuel headers node with
          | none => simp [decodeExprsChecked, headResult] at decoded
          | some head =>
              cases tailResult : decodeExprsChecked fuel headers tail with
              | none => simp [decodeExprsChecked, headResult, tailResult] at decoded
              | some rest =>
                  have resultEq : head :: rest = expressions := by
                    simpa [decodeExprsChecked, headResult, tailResult] using decoded
                  cases resultEq
                  intro expression member
                  simp only [List.mem_cons] at member
                  rcases member with same | member
                  · cases same
                    exact (decodeExprChecked_spec headResult).2
                  · exact ih tailResult expression member

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
    (decodeExprChecked_letMany_lengths decoded).symm argumentsReflected bodyReflected
    value evaluated

def definitionsLetLayoutsAligned (definitions : Definitions) : Bool :=
  definitions.all (fun definition => letLayoutsAligned definition.2)

/- This stronger invariant rules out the missing-variable alias introduced by
`position`'s total fallback. `locals` are lexical binder identities, with the
first identity corresponding to de Bruijn index zero. -/
mutual
inductive IdentityScoped : List Nat → Expr → Prop where
  | var : ∀ {locals}, identity ∈ locals → IdentityScoped locals (.var identity)
  | global : ∀ {locals}, IdentityScoped locals (.global index)
  | bool : ∀ {locals}, IdentityScoped locals (.bool value)
  | int : ∀ {locals}, IdentityScoped locals (.int value)
  | float : ∀ {locals}, IdentityScoped locals (.float value)
  | string : ∀ {locals}, IdentityScoped locals (.string value)
  | character : ∀ {locals}, IdentityScoped locals (.character value)
  | unit : ∀ {locals}, IdentityScoped locals .unit
  | lam : ∀ {locals}, IdentityScoped (parameters ++ locals) body →
      IdentityScoped locals (.lam parameters body)
  | app : ∀ {locals}, IdentityScoped locals function → IdentityScopedList locals arguments →
      IdentityScoped locals (.app function arguments)
  | ite : ∀ {locals}, IdentityScoped locals condition → IdentityScoped locals yes →
      IdentityScoped locals no → IdentityScoped locals (.ite condition yes no)
  | add : ∀ {locals}, IdentityScoped locals left → IdentityScoped locals right →
      IdentityScoped locals (.add left right)
  | sub : ∀ {locals}, IdentityScoped locals left → IdentityScoped locals right →
      IdentityScoped locals (.sub left right)
  | mul : ∀ {locals}, IdentityScoped locals left → IdentityScoped locals right →
      IdentityScoped locals (.mul left right)
  | le : ∀ {locals}, IdentityScoped locals left → IdentityScoped locals right →
      IdentityScoped locals (.le left right)
  | intEq : ∀ {locals}, IdentityScoped locals left → IdentityScoped locals right →
      IdentityScoped locals (.intEq left right)
  | floatBin : ∀ {locals}, IdentityScoped locals left → IdentityScoped locals right →
      IdentityScoped locals (.floatBin operation left right)
  | letMany : ∀ {locals}, IdentityScopedList locals initializers →
      IdentityScoped (parameters ++ locals) body →
      IdentityScoped locals (.letMany parameters initializers body)
  | begin : ∀ {locals}, IdentityScoped locals first → IdentityScopedList locals rest →
      IdentityScoped locals (.begin first rest)
  | nil : ∀ {locals}, IdentityScoped locals .nil
  | cons : ∀ {locals}, IdentityScoped locals head → IdentityScoped locals tail →
      IdentityScoped locals (.cons head tail)
  | none : ∀ {locals}, IdentityScoped locals .none
  | some : ∀ {locals}, IdentityScoped locals value → IdentityScoped locals (.some value)
  | matchList : ∀ {locals}, IdentityScoped locals target → IdentityScoped locals empty →
      IdentityScoped (headIdentity :: tailIdentity :: locals) full →
      IdentityScoped locals (.matchList target empty headIdentity tailIdentity full)
  | matchOption : ∀ {locals}, IdentityScoped locals target → IdentityScoped locals empty →
      IdentityScoped (identity :: locals) full →
      IdentityScoped locals (.matchOption target empty identity full)

inductive IdentityScopedList : List Nat → List Expr → Prop where
  | nil : ∀ {locals}, IdentityScopedList locals []
  | cons : ∀ {locals}, IdentityScoped locals head → IdentityScopedList locals tail →
      IdentityScopedList locals (head :: tail)
end

/-- The scoped function and argument list are available independently when
splitting an application proof. -/
theorem identityScoped_app_parts {locals : List Nat} (function : Expr)
    (arguments : List Expr)
    (scopeProof : IdentityScoped locals (.app function arguments)) :
    IdentityScoped locals function ∧ IdentityScopedList locals arguments := by
  cases scopeProof with
  | app functionScoped argumentsScoped => exact ⟨functionScoped, argumentsScoped⟩

/-- A lambda body is scoped beneath its parameter identities. -/
theorem identityScoped_lambda_body {locals parameters : List Nat} (body : Expr)
    (scopeProof : IdentityScoped locals (.lam parameters body)) :
    IdentityScoped (parameters ++ locals) body := by
  cases scopeProof with
  | lam bodyScoped => exact bodyScoped

/-- A parallel let scopes every initializer in the incoming environment and
its body under the complete binder prefix. -/
theorem identityScoped_letMany_parts {locals ids : List Nat}
    (initializers : List Expr) (body : Expr)
    (scopeProof : IdentityScoped locals (.letMany ids initializers body)) :
    IdentityScopedList locals initializers ∧ IdentityScoped (ids ++ locals) body := by
  cases scopeProof with
  | letMany initializersScoped bodyScoped => exact ⟨initializersScoped, bodyScoped⟩

/-- `begin` evaluates every child in the same identity context. -/
theorem identityScoped_begin_parts {locals : List Nat} (first : Expr)
    (rest : List Expr)
    (scopeProof : IdentityScoped locals (.begin first rest)) :
    IdentityScoped locals first ∧ IdentityScopedList locals rest := by
  cases scopeProof with
  | begin firstScoped restScoped => exact ⟨firstScoped, restScoped⟩

/-- A list match keeps the empty branch in the incoming context and adds the
head/tail identities only in the cons branch. -/
theorem identityScoped_matchList_parts {locals : List Nat} (target empty : Expr)
    (headIdentity tailIdentity : Nat) (full : Expr)
    (scopeProof : IdentityScoped locals
      (.matchList target empty headIdentity tailIdentity full)) :
    IdentityScoped locals target ∧ IdentityScoped locals empty ∧
      IdentityScoped (headIdentity :: tailIdentity :: locals) full := by
  cases scopeProof with
  | matchList targetScoped emptyScoped fullScoped =>
      exact ⟨targetScoped, emptyScoped, fullScoped⟩

/-- An option match adds its identity only in the Some branch. -/
theorem identityScoped_matchOption_parts {locals : List Nat} (target empty : Expr)
    (identity : Nat) (full : Expr)
    (scopeProof : IdentityScoped locals (.matchOption target empty identity full)) :
    IdentityScoped locals target ∧ IdentityScoped locals empty ∧
      IdentityScoped (identity :: locals) full := by
  cases scopeProof with
  | matchOption targetScoped emptyScoped fullScoped =>
      exact ⟨targetScoped, emptyScoped, fullScoped⟩

/-- Every member of a scoped expression row inherits the same local identity
context. -/
theorem identityScopedList_mem {locals : List Nat} (expressions : List Expr)
    (scopeProof : IdentityScopedList locals expressions) {expression : Expr}
    (member : expression ∈ expressions) : IdentityScoped locals expression := by
  induction expressions with
  | nil => cases scopeProof; simp at member
  | cons head tail ih =>
      cases scopeProof with
      | cons headScoped tailScoped =>
          simp only [List.mem_cons] at member
          rcases member with same | member
          · cases same
            exact headScoped
          · exact ih tailScoped member

/-- A scoped variable is lowered to an in-range PolyIR environment index.
This rules out the out-of-range fallback used for a missing source identity. -/
theorem identityScoped_variable_lower_index {locals : List Nat} {identity : Nat}
    (scopeProof : IdentityScoped locals (.var identity)) :
    position identity locals < locals.length := by
  cases scopeProof with
  | var present => exact position_lt_length_of_mem identity locals present

/-- Every built-in function body synthesized by the decoder is scoped under
the identities of its parameters. -/
theorem readPrimitive_identityScoped {identity : Nat} {expression : Expr}
    (decoded : readPrimitive identity = some expression) :
    IdentityScoped [] expression := by
  unfold readPrimitive at decoded
  split at decoded <;> cases decoded <;> repeat' (first | constructor | simp)

theorem acceptedSite_variable_identityScoped (site : CBindingWalk.Site)
    (accepted : CBindingWalk.accepts site = true) :
    IdentityScoped (site.caller.map (fun entry => entry.identity))
      (.var site.selected) := by
  obtain ⟨binding, member, identityEq⟩ :=
    CBindingWalk.accepts_selected_identity_in_caller site accepted
  apply IdentityScoped.var
  rw [← identityEq]
  exact List.mem_map.mpr ⟨binding, member, rfl⟩

theorem acceptedCheck_reference_sites_identityScoped (fuel : Nat)
    (forms : List Node) (builtins : CBindingWalk.Environment)
    (accepted : CBindingWalk.check fuel forms builtins = true) :
    ∃ sites, CBindingWalk.references fuel forms builtins = some sites ∧
      ∀ site ∈ sites,
        IdentityScoped (site.caller.map (fun entry => entry.identity))
          (.var site.selected) := by
  obtain ⟨sites, decoded, siteFacts⟩ :=
    CBindingWalk.check_selected_identities_in_caller fuel forms builtins accepted
  refine ⟨sites, decoded, ?_⟩
  intro site member
  apply IdentityScoped.var
  exact siteFacts site member |>.2

/- Runtime closure scope is indexed by the captured identities, so an identity
used under the closure's parameter prefix must resolve in that prefix or in
the environment that was actually captured. -/
mutual
inductive ValueIdentityScoped : Value → Prop where
  | bool : ValueIdentityScoped (.bool value)
  | int : ValueIdentityScoped (.int value)
  | float : ValueIdentityScoped (.float value)
  | string : ValueIdentityScoped (.string value)
  | character : ValueIdentityScoped (.character value)
  | unit : ValueIdentityScoped .unit
  | closure : IdentityScoped (parameters ++ identities captured) body →
      EnvironmentIdentityScoped captured →
      ValueIdentityScoped (.closure parameters body captured)
  | global : ValueIdentityScoped (.global index)
  | nil : ValueIdentityScoped .nil
  | cons : ValueIdentityScoped head → ValueIdentityScoped tail →
      ValueIdentityScoped (.cons head tail)
  | none : ValueIdentityScoped .none
  | some : ValueIdentityScoped value → ValueIdentityScoped (.some value)

inductive EnvironmentIdentityScoped : Environment → Prop where
  | nil : EnvironmentIdentityScoped []
  | cons : ValueIdentityScoped value → EnvironmentIdentityScoped rest →
      EnvironmentIdentityScoped ((identity, value) :: rest)
end

theorem environmentIdentityScoped_append (left right : Environment)
    (leftScoped : EnvironmentIdentityScoped left)
    (rightScoped : EnvironmentIdentityScoped right) :
    EnvironmentIdentityScoped (left ++ right) := by
  induction left with
  | nil => exact rightScoped
  | cons head tail ih =>
      cases leftScoped with
      | cons valueScoped tailScoped => exact .cons valueScoped (ih tailScoped)

theorem environmentIdentityScoped_bind_append (ids : List Nat) (values : List Value)
    (environment : Environment)
    (valuesScoped : ∀ value ∈ values, ValueIdentityScoped value)
    (environmentScoped : EnvironmentIdentityScoped environment) :
    EnvironmentIdentityScoped (bind ids values ++ environment) := by
  induction ids generalizing values with
  | nil => simpa [bind] using environmentScoped
  | cons id rest ih =>
      cases values with
      | nil => simpa [bind] using environmentScoped
      | cons value tail =>
          have valueScoped := valuesScoped value (by simp)
          have tailScoped : ∀ item ∈ tail, ValueIdentityScoped item := by
            intro item member
            exact valuesScoped item (by simp [member])
          simpa [bind] using EnvironmentIdentityScoped.cons valueScoped
            (ih tail tailScoped)

theorem lambdaValue_identityScoped (environment : Environment) (parameters : List Nat)
    (body : Expr) (environmentScoped : EnvironmentIdentityScoped environment)
    (bodyScoped : IdentityScoped (parameters ++ identities environment) body) :
    ValueIdentityScoped (.closure parameters body environment) :=
  .closure bodyScoped environmentScoped

/-- Every definition body is well-scoped under its parameter identities. -/
def programIdentityScoped (program : Definitions) : Prop :=
  ∀ parameters body, (parameters, body) ∈ program → IdentityScoped parameters body

theorem programIdentityScoped_lookup (program : Definitions) (index : Nat)
    (parameters : List Nat) (body : Expr)
    (programScoped : programIdentityScoped program)
    (found : program[index]? = some (parameters, body)) :
    IdentityScoped parameters body := by
  induction program generalizing index with
  | nil =>
      have indexInvalid : ¬ index < 0 := by omega
      simp [getElem?_def, indexInvalid] at found
  | cons definition rest ih =>
      cases index with
      | zero =>
          have same : definition = (parameters, body) := by
            simpa [getElem?_def] using found
          cases same
          exact programScoped parameters body (by simp)
      | succ index =>
          have foundTail : rest[index]? = some (parameters, body) := by
            simpa [getElem?_def, List.length_cons, Nat.succ_lt_succ_iff] using found
          have restScoped : programIdentityScoped rest := by
            intro ps expression member
            exact programScoped ps expression (List.mem_cons_of_mem _ member)
          exact ih index restScoped foundTail

theorem environmentIdentityScoped_lookup (environment : Environment) (identity : Nat)
    (value : Value) (environmentScoped : EnvironmentIdentityScoped environment)
    (found : lookup identity environment = some value) : ValueIdentityScoped value := by
  induction environment with
  | nil => simp [lookup] at found
  | cons entry rest ih =>
      rcases entry with ⟨key, current⟩
      cases environmentScoped with
      | cons currentScoped restScoped =>
          by_cases same : key = identity
          · subst key
            have currentEq : current = value := by simpa [lookup] using found
            cases currentEq
            exact currentScoped
          · have tailFound : lookup identity rest = some value := by
              simpa [lookup, same] using found
            exact ih restScoped tailFound

/-- Identity scope is preserved by finite Named evaluation. In particular,
closures retain a body scoped by their parameter identities followed by the
identities of the captured environment. -/
theorem evaluation_preserves_valueIdentityScoped (program : Definitions)
    (programScoped : programIdentityScoped program) :
    ∀ {environment : Environment} {expression : Expr} {value : Value},
      Evaluates program environment expression value →
      EnvironmentIdentityScoped environment →
      IdentityScoped (identities environment) expression → ValueIdentityScoped value := by
  apply Evaluates.rec (program := program)
    (motive_1 := fun environment expression value _ =>
      EnvironmentIdentityScoped environment →
        IdentityScoped (identities environment) expression → ValueIdentityScoped value)
    (motive_2 := fun environment expressions values _ =>
      EnvironmentIdentityScoped environment →
        IdentityScopedList (identities environment) expressions →
        ∀ value ∈ values, ValueIdentityScoped value)
    (motive_3 := fun environment expressions previous value _ =>
      EnvironmentIdentityScoped environment →
        IdentityScopedList (identities environment) expressions →
        ValueIdentityScoped previous → ValueIdentityScoped value)
  all_goals intros
  all_goals try assumption
  all_goals try exact ValueIdentityScoped.bool
  all_goals try exact ValueIdentityScoped.int
  all_goals try exact ValueIdentityScoped.float
  all_goals try exact ValueIdentityScoped.string
  all_goals try exact ValueIdentityScoped.character
  all_goals try exact ValueIdentityScoped.unit
  all_goals try exact ValueIdentityScoped.global
  all_goals try exact ValueIdentityScoped.nil
  all_goals try exact ValueIdentityScoped.none
  case var =>
    rename_i identity environment value found environmentScoped expressionScoped
    exact environmentIdentityScoped_lookup environment identity value environmentScoped found
  case lam =>
    rename_i environment parameters body environmentScoped expressionScoped
    cases expressionScoped with
    | lam bodyScoped => exact ValueIdentityScoped.closure bodyScoped environmentScoped
  case appClosure =>
    rename_i environment function parameters body captured arguments values result
      evalFunction evalArguments arity evalBody ihFunction ihArguments ihBody
      environmentScoped expressionScoped
    cases expressionScoped with
    | app functionScoped argumentsScoped =>
      have functionScopedValue := ihFunction environmentScoped functionScoped
      have valuesScoped : ∀ value ∈ values, ValueIdentityScoped value :=
        ihArguments environmentScoped argumentsScoped
      cases functionScopedValue with
      | closure bodyScoped capturedScoped =>
          have bodyEnvironmentScoped := environmentIdentityScoped_bind_append
            parameters values captured valuesScoped capturedScoped
          have bodyScope : IdentityScoped
              (identities (bind parameters values ++ captured)) body := by
            rw [identities_bind_append parameters values captured arity]
            exact bodyScoped
          exact ihBody bodyEnvironmentScoped bodyScope
  case appGlobal =>
    rename_i environment function index arguments values parameters body result
      evalFunction evalArguments definitionFound arity evalBody ihFunction ihArguments ihBody
      environmentScoped expressionScoped
    cases expressionScoped with
    | app functionScoped argumentsScoped =>
      have valuesScoped : ∀ value ∈ values, ValueIdentityScoped value :=
        ihArguments environmentScoped argumentsScoped
      have bodyScoped := programIdentityScoped_lookup program index parameters body
        programScoped definitionFound
      have bodyEnvironmentScoped := environmentIdentityScoped_bind_append
        parameters values [] valuesScoped EnvironmentIdentityScoped.nil
      have bodyScope : IdentityScoped (identities (bind parameters values)) body := by
        rw [bind_identifiers parameters values arity]
        simpa using bodyScoped
      exact ihBody (by simpa using bodyEnvironmentScoped) bodyScope
  case ifTrue =>
    rename_i environment condition yes value no evalCondition evalYes ihCondition ihYes
      environmentScoped expressionScoped
    cases expressionScoped with
    | ite _ yesScoped _ => exact ihYes environmentScoped yesScoped
  case ifFalse =>
    rename_i environment condition no value yes evalCondition evalNo ihCondition ihNo
      environmentScoped expressionScoped
    cases expressionScoped with
    | ite _ _ noScoped => exact ihNo environmentScoped noScoped
  case letMany =>
    rename_i environment initializers values identifiers body result evalInitializers arity
      evalBody ihInitializers ihBody environmentScoped expressionScoped
    cases expressionScoped with
    | letMany initializersScoped bodyScoped =>
      have valuesScoped : ∀ value ∈ values, ValueIdentityScoped value :=
        ihInitializers environmentScoped initializersScoped
      have bodyEnvironmentScoped := environmentIdentityScoped_bind_append
        identifiers values environment valuesScoped environmentScoped
      have bodyScope : IdentityScoped
          (identities (bind identifiers values ++ environment)) body := by
        rw [identities_bind_append identifiers values environment arity]
        exact bodyScoped
      exact ihBody bodyEnvironmentScoped bodyScope
  case begin =>
    rename_i environment first previous rest result evalFirst evalRest ihFirst ihRest
      environmentScoped expressionScoped
    cases expressionScoped with
    | begin firstScoped restScoped =>
      exact ihRest environmentScoped restScoped (ihFirst environmentScoped firstScoped)
  case cons =>
    rename_i environment head headValue tail tailValue evalHead evalTail ihHead ihTail
      environmentScoped expressionScoped
    cases expressionScoped with
    | cons headScoped tailScoped =>
      exact ValueIdentityScoped.cons (ihHead environmentScoped headScoped)
        (ihTail environmentScoped tailScoped)
  case some =>
    rename_i environment expression value evalExpression ihExpression environmentScoped
      expressionScoped
    cases expressionScoped with
    | some valueScoped => exact ValueIdentityScoped.some (ihExpression environmentScoped valueScoped)
  case matchNil =>
    rename_i environment target empty value headBinder tailBinder full evalTarget evalEmpty
      ihTarget ihEmpty environmentScoped expressionScoped
    cases expressionScoped with
    | matchList _ emptyScoped _ => exact ihEmpty environmentScoped emptyScoped
  case matchCons =>
    rename_i environment target headValue tailValue headBinder tailBinder full value empty
      evalTarget evalFull ihTarget ihFull environmentScoped expressionScoped
    cases expressionScoped with
    | matchList _ _ fullScoped =>
      cases ihTarget environmentScoped (by assumption) with
      | cons headScoped tailScoped =>
        exact ihFull (.cons headScoped (.cons tailScoped environmentScoped)) fullScoped
  case matchNone =>
    rename_i environment target empty value binder full evalTarget evalEmpty ihTarget ihEmpty
      environmentScoped expressionScoped
    cases expressionScoped with
    | matchOption _ emptyScoped _ => exact ihEmpty environmentScoped emptyScoped
  case matchSome =>
    rename_i environment target item binder full value empty evalTarget evalFull ihTarget ihFull
      environmentScoped expressionScoped
    cases expressionScoped with
    | matchOption targetScoped _ fullScoped =>
      cases ihTarget environmentScoped targetScoped with
      | some itemScoped => exact ihFull (.cons itemScoped environmentScoped) fullScoped
  case nil =>
    rename_i environmentScoped expressionsScoped value member
    simp at member
  case cons =>
    rename_i environment head headValue tail values evalHead evalTail ihHead ihTail
      environmentScoped expressionsScoped value member
    cases expressionsScoped with
    | cons headScoped tailScoped =>
      rcases List.mem_cons.mp member with same | member
      · cases same
        exact ihHead environmentScoped headScoped
      · exact ihTail environmentScoped tailScoped _ member
  case cons =>
    rename_i environment head headValue tail previous result evalHead evalTail ihHead ihTail
      environmentScoped expressionsScoped previousScoped
    cases expressionsScoped with
    | cons headScoped tailScoped =>
      exact ihTail environmentScoped tailScoped (ihHead environmentScoped headScoped)

/- Runtime closures carry their source body and captured source environment.
This recursive invariant records that every such body obeys the binder/value
arity condition and that the condition remains true for closures nested in
captured lists, pairs, and options. -/
mutual
inductive ValueWellScoped : Value → Prop where
  | bool : ValueWellScoped (.bool value)
  | int : ValueWellScoped (.int value)
  | float : ValueWellScoped (.float value)
  | string : ValueWellScoped (.string value)
  | character : ValueWellScoped (.character value)
  | unit : ValueWellScoped .unit
  | closure : letLayoutsAligned body = true → EnvironmentWellScoped captured →
      ValueWellScoped (.closure parameters body captured)
  | global : ValueWellScoped (.global index)
  | nil : ValueWellScoped .nil
  | cons : ValueWellScoped head → ValueWellScoped tail →
      ValueWellScoped (.cons head tail)
  | none : ValueWellScoped .none
  | some : ValueWellScoped value → ValueWellScoped (.some value)

inductive EnvironmentWellScoped : Environment → Prop where
  | nil : EnvironmentWellScoped []
  | cons : ValueWellScoped value → EnvironmentWellScoped rest →
      EnvironmentWellScoped ((identity, value) :: rest)
end

abbrev valueWellScoped := ValueWellScoped
abbrev environmentWellScoped := EnvironmentWellScoped

/-- A closure's value-scope invariant packages both the body scope under its
parameter/captured identities and the scope invariant for the captured cells. -/
theorem valueIdentityScoped_closure_parts (parameters : List Nat) (body : Expr)
    (captured : Environment)
    (scopeProof : ValueIdentityScoped (.closure parameters body captured)) :
    IdentityScoped (parameters ++ identities captured) body ∧
      EnvironmentIdentityScoped captured := by
  cases scopeProof with
  | closure bodyScoped capturedScoped => exact ⟨bodyScoped, capturedScoped⟩

/-- A closure's layout invariant packages aligned nested `letMany` forms in
its body and well-scoped captured values. -/
theorem valueWellScoped_closure_parts (parameters : List Nat) (body : Expr)
    (captured : Environment)
    (scopeProof : ValueWellScoped (.closure parameters body captured)) :
    letLayoutsAligned body = true ∧ EnvironmentWellScoped captured := by
  cases scopeProof with
  | closure bodyAligned capturedScoped => exact ⟨bodyAligned, capturedScoped⟩

/-- Combined checked `letMany` invariants: identity references in initializers
use the old context, body references use the complete binder prefix, nested
layouts are aligned, and the row lengths agree. -/
theorem identityScoped_letMany_aligned {locals ids : List Nat}
    (initializers : List Expr) (body : Expr)
    (scopeProof : IdentityScoped locals (.letMany ids initializers body))
    (layoutProof : letLayoutsAligned (.letMany ids initializers body) = true) :
    IdentityScopedList locals initializers ∧
      IdentityScoped (ids ++ locals) body ∧
      ids.length = initializers.length ∧
      letLayoutsAlignedList initializers = true ∧ letLayoutsAligned body = true := by
  obtain ⟨initializersScoped, bodyScoped⟩ :=
    identityScoped_letMany_parts initializers body scopeProof
  obtain ⟨rowAligned, initializersAligned, bodyAligned⟩ :=
    letLayoutsAligned_letMany_parts ids initializers body layoutProof
  exact ⟨initializersScoped, bodyScoped, rowAligned, initializersAligned, bodyAligned⟩

def programWellScoped (definitions : Definitions) : Prop :=
  definitionsLetLayoutsAligned definitions = true

def executionWellScoped (definitions : Definitions) (environment : Environment) : Prop :=
  programWellScoped definitions ∧ environmentWellScoped environment

theorem environmentWellScoped_append (left right : Environment)
    (leftScoped : environmentWellScoped left)
    (rightScoped : environmentWellScoped right) :
    environmentWellScoped (left ++ right) := by
  induction left with
  | nil => exact rightScoped
  | cons head tail ih =>
      cases leftScoped with
      | cons valueScoped tailScoped => exact .cons valueScoped (ih tailScoped)

theorem environmentWellScoped_bind_append (ids : List Nat) (values : List Value)
    (environment : Environment)
    (valuesScoped : ∀ value ∈ values, valueWellScoped value)
    (environmentScoped : environmentWellScoped environment) :
    environmentWellScoped (bind ids values ++ environment) := by
  induction ids generalizing values with
  | nil => simpa [bind] using environmentScoped
  | cons id rest ih =>
      cases values with
      | nil => simpa [bind] using environmentScoped
      | cons value tail =>
          have valueScoped : valueWellScoped value := valuesScoped value (by simp)
          have tailScoped : ∀ item ∈ tail, valueWellScoped item := by
            intro item member
            exact valuesScoped item (by simp [member])
          simpa [bind] using EnvironmentWellScoped.cons valueScoped
            (ih tail tailScoped)

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
  ⟨header.identity, [], [], header.type, header.initializer, header.order, header.name⟩

@[simp] theorem GlobalHeader.decodeHeader_order (header : GlobalHeader) :
    (GlobalHeader.decodeHeader header).order = header.order := rfl

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

theorem globalIndex_append_of_none (identity : Nat) (left suffix : List Header)
    (prefixMissing : globalIndex identity left = none) :
    globalIndex identity (left ++ suffix) =
      (globalIndex identity suffix).map (left.length + ·) := by
  induction left with
  | nil => simp [globalIndex]
  | cons head tail ih =>
      by_cases same : head.identity = identity
      · simp [globalIndex, same] at prefixMissing
      · have tailMissing : globalIndex identity tail = none := by
          simpa [globalIndex, same] using prefixMissing
        cases suffixResult : globalIndex identity suffix with
        | none =>
            calc
              globalIndex identity (head :: (tail ++ suffix)) =
                  Option.map Nat.succ (globalIndex identity (tail ++ suffix)) := by
                simp [globalIndex, same]
              _ = Option.map Nat.succ
                  (Option.map (fun i => tail.length + i) (globalIndex identity suffix)) := by
                rw [ih tailMissing]
              _ = Option.map (fun i => (head :: tail).length + i) none := by
                simp [suffixResult]
        | some value =>
            calc
              globalIndex identity (head :: (tail ++ suffix)) =
                  Option.map Nat.succ (globalIndex identity (tail ++ suffix)) := by
                simp [globalIndex, same]
              _ = Option.map Nat.succ
                  (Option.map (fun i => tail.length + i) (globalIndex identity suffix)) := by
                rw [ih tailMissing]
              _ = Option.map (fun i => (head :: tail).length + i) (some value) := by
                simp [suffixResult, List.length_cons]
                omega

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
  decodeExprsChecked fuel (decodeHeadersWithGlobals functions values)
    (values.map GlobalHeader.initializer)

theorem decodeGlobalInitializers_length {fuel : Nat} {functions : List Header}
    {values : List GlobalHeader} {initializers : List Expr}
    (decoded : decodeGlobalInitializers fuel functions values = some initializers) :
    initializers.length = values.length := by
  have expressionsDecoded :
      decodeExprsChecked fuel (decodeHeadersWithGlobals functions values)
        (values.map GlobalHeader.initializer) = some initializers := by
    simpa [decodeGlobalInitializers] using decoded
  have length := decodeExprsChecked_length expressionsDecoded
  simpa using length

theorem decodeGlobalInitializers_aligned {fuel : Nat} {functions : List Header}
    {values : List GlobalHeader} {initializers : List Expr}
    (decoded : decodeGlobalInitializers fuel functions values = some initializers) :
    ∀ expression ∈ initializers, letLayoutsAligned expression = true := by
  apply decodeExprsChecked_aligned
  simpa [decodeGlobalInitializers] using decoded

def decodeProgramWithGlobals (fuel : Nat) (functions : List Header)
    (values : List GlobalHeader) :
    Option (Definitions × List Surface.Ty × List Expr) := do
  let headers := decodeHeadersWithGlobals functions values
  let definitions ← decodeFunctions fuel headers functions
  let initializers ← decodeGlobalInitializers fuel functions values
  return (definitions, values.map GlobalHeader.type, initializers)

def decodeTopLevelProgram (fuel : Nat) (forms : List Node) :
    Option (Definitions × List Surface.Ty × List Expr) := do
  let layout ← readProgramHeaders fuel 0 forms
  decodeProgramWithGlobals fuel layout.functions layout.globals

/- Preserve the mixed declaration sequence alongside the established decoded
function/value projections. This is the interface needed by consumers that
must reconstruct a source-order GlobalProgramEntry layout. -/
def decodeTopLevelProgramWithHeaders (fuel : Nat) (forms : List Node) :
    Option (ProgramHeaders × Definitions × List Surface.Ty × List Expr) := do
  let layout ← readProgramHeaders fuel 0 forms
  let (definitions, slotTypes, initializers) ←
    decodeProgramWithGlobals fuel layout.functions layout.globals
  return (layout, definitions, slotTypes, initializers)

theorem decodeTopLevelProgramWithHeaders_project
    (fuel : Nat) (forms : List Node) (layout : ProgramHeaders)
    (definitions : Definitions) (slotTypes : List Surface.Ty) (initializers : List Expr)
    (decoded : decodeTopLevelProgramWithHeaders fuel forms =
      some (layout, definitions, slotTypes, initializers)) :
    decodeTopLevelProgram fuel forms = some (definitions, slotTypes, initializers) := by
  unfold decodeTopLevelProgramWithHeaders at decoded
  cases layoutResult : readProgramHeaders fuel 0 forms with
  | none => simp [layoutResult] at decoded
  | some actualLayout =>
      cases programResult : decodeProgramWithGlobals fuel actualLayout.functions actualLayout.globals with
      | none => simp [layoutResult, programResult] at decoded
      | some actualProgram =>
          rcases actualProgram with ⟨actualDefinitions, actualTypes, actualInitializers⟩
          simp [layoutResult, programResult] at decoded
          obtain ⟨rfl, rfl, rfl, rfl⟩ := decoded
          simp [decodeTopLevelProgram, layoutResult, programResult]

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
          simp only [List.length_map]
          exact ⟨trivial,
            by simpa only [List.length_map] using
              (decodeGlobalInitializers_length initializerResult).symm⟩

theorem decodeProgramWithGlobals_initializers_aligned (fuel : Nat)
    (functions : List Header) (values : List GlobalHeader)
    (definitions : Definitions) (slotTypes : List Surface.Ty)
    (initializers : List Expr)
    (decoded : decodeProgramWithGlobals fuel functions values =
      some (definitions, slotTypes, initializers)) :
    ∀ expression ∈ initializers, letLayoutsAligned expression = true := by
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
          exact decodeGlobalInitializers_aligned initializerResult

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

theorem decodeTopLevelProgram_initializers_aligned (fuel : Nat) (forms : List Node)
    (definitions : Definitions) (slotTypes : List Surface.Ty)
    (initializers : List Expr)
    (decoded : decodeTopLevelProgram fuel forms =
      some (definitions, slotTypes, initializers)) :
    ∀ expression ∈ initializers, letLayoutsAligned expression = true := by
  unfold decodeTopLevelProgram at decoded
  cases layoutResult : readProgramHeaders fuel 0 forms with
  | none => simp [layoutResult] at decoded
  | some layout =>
      have innerDecoded :
          decodeProgramWithGlobals fuel layout.functions layout.globals =
            some (definitions, slotTypes, initializers) := by
        simpa [layoutResult] using decoded
      exact decodeProgramWithGlobals_initializers_aligned fuel layout.functions
        layout.globals definitions slotTypes initializers innerDecoded

theorem decodeFunctions_letLayoutsAligned (fuel : Nat) (headers : List Header)
    (functions : List Header) (definitions : Definitions)
    (decoded : decodeFunctions fuel headers functions = some definitions) :
    definitionsLetLayoutsAligned definitions = true := by
  induction functions generalizing definitions with
  | nil =>
      have definitionsEq : [] = definitions := Option.some.inj (by
        simpa [decodeFunctions] using decoded)
      cases definitionsEq
      rfl
  | cons header tail ih =>
      cases bodyResult : decodeExprChecked fuel headers header.body with
      | none =>
          simp [decodeFunctions, bodyResult] at decoded
      | some body =>
          cases restResult : decodeFunctions fuel headers tail with
          | none =>
              simp [decodeFunctions, bodyResult, restResult] at decoded
          | some rest =>
              have definitionsEq : (header.parameters.map Prod.fst, body) :: rest = definitions := by
                simpa [decodeFunctions, bodyResult, restResult] using decoded
              cases definitionsEq
              have tailAligned : definitionsLetLayoutsAligned rest = true := ih rest restResult
              have bodyAligned := (decodeExprChecked_spec bodyResult).2
              change (letLayoutsAligned body && definitionsLetLayoutsAligned rest) = true
              rw [bodyAligned, tailAligned]
              rfl

def decodeProgram (fuel : Nat) (forms : List Node) : Option Definitions := do
  let headers ← forms.mapM (readHeader fuel)
  decodeFunctions fuel headers headers

/- Raw decoding preserves the exact operational syntax but leaves checked
let-layout validation to the caller. This is useful when the caller already
has an independent well-scoped/type-checking derivation for the same forms. -/
def decodeFunctionsRaw (fuel : Nat) (headers : List Header) : List Header → Option Definitions
  | [] => some []
  | header :: tail => do
      let body ← decodeExpr fuel headers header.body
      let rest ← decodeFunctionsRaw fuel headers tail
      pure ((header.parameters.map Prod.fst, body) :: rest)

def decodeProgramRaw (fuel : Nat) (forms : List Node) : Option Definitions := do
  let headers ← forms.mapM (readHeader fuel)
  decodeFunctionsRaw fuel headers headers

theorem decodeFunctions_exists_of_each (fuel : Nat) (headers functions : List Header)
    (bodyDecodes : ∀ header ∈ functions,
      ∃ body, decodeExprChecked fuel headers header.body = some body) :
    ∃ definitions, decodeFunctions fuel headers functions = some definitions := by
  induction functions with
  | nil => exact ⟨[], by simp [decodeFunctions]⟩
  | cons header tail ih =>
      obtain ⟨body, bodyDecoded⟩ := bodyDecodes header (by simp)
      have tailDecodes : ∀ item ∈ tail,
          ∃ body, decodeExprChecked fuel headers item.body = some body := by
        intro item member
        exact bodyDecodes item (by simp [member])
      obtain ⟨definitions, tailDecoded⟩ := ih tailDecodes
      exact ⟨(header.parameters.map Prod.fst, body) :: definitions,
        by simp [decodeFunctions, bodyDecoded, tailDecoded]⟩

theorem decodeProgram_isSome_of_components (fuel : Nat) (forms : List Node)
    (headers : List Header)
    (headersDecoded : forms.mapM (readHeader fuel) = some headers)
    (bodiesDecoded : ∀ header ∈ headers,
      ∃ body, decodeExprChecked fuel headers header.body = some body) :
    (decodeProgram fuel forms).isSome = true := by
  simp only [decodeProgram, headersDecoded]
  obtain ⟨definitions, decoded⟩ :=
    decodeFunctions_exists_of_each fuel headers headers bodiesDecoded
  simp [decoded]

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

theorem decodeTopLevelProgram_functions_wellScoped (fuel : Nat) (forms : List Node)
    (definitions : Definitions) (slotTypes : List Surface.Ty)
    (initializers : List Expr)
    (decoded : decodeTopLevelProgram fuel forms =
      some (definitions, slotTypes, initializers)) :
    programWellScoped definitions := by
  unfold decodeTopLevelProgram at decoded
  cases layoutResult : readProgramHeaders fuel 0 forms with
  | none => simp [layoutResult] at decoded
  | some layout =>
      have innerDecoded :
          decodeProgramWithGlobals fuel layout.functions layout.globals =
            some (definitions, slotTypes, initializers) := by
        simpa [layoutResult] using decoded
      unfold decodeProgramWithGlobals at innerDecoded
      cases functionResult : decodeFunctions fuel
          (decodeHeadersWithGlobals layout.functions layout.globals) layout.functions with
      | none => simp [functionResult] at innerDecoded
      | some decodedDefinitions =>
          cases initializerResult : decodeGlobalInitializers fuel
              layout.functions layout.globals with
          | none => simp [functionResult, initializerResult] at innerDecoded
          | some decodedInitializers =>
              have resultEq :
                  (decodedDefinitions, layout.globals.map GlobalHeader.type,
                    decodedInitializers) = (definitions, slotTypes, initializers) := by
                simpa [functionResult, initializerResult] using innerDecoded
              cases resultEq
              exact decodeFunctions_letLayoutsAligned fuel
                (decodeHeadersWithGlobals layout.functions layout.globals)
                layout.functions definitions functionResult

theorem decodeTopLevelProgram_wellScoped (fuel : Nat) (forms : List Node)
    (definitions : Definitions) (slotTypes : List Surface.Ty)
    (initializers : List Expr)
    (decoded : decodeTopLevelProgram fuel forms =
      some (definitions, slotTypes, initializers)) :
    programWellScoped definitions ∧
      ∀ expression ∈ initializers, letLayoutsAligned expression = true := by
  exact ⟨decodeTopLevelProgram_functions_wellScoped fuel forms definitions
    slotTypes initializers decoded,
    decodeTopLevelProgram_initializers_aligned fuel forms definitions
      slotTypes initializers decoded⟩

/-- A successful mixed top-level decode exposes the exact header layout that
produced it, along with the value-slot type order, initializer count, and the
well-scopedness conditions needed by later typed runtime-layout construction. -/
theorem decodeTopLevelProgram_layout_and_initializer_conditions
    (fuel : Nat) (forms : List Node) (definitions : Definitions)
    (slotTypes : List Surface.Ty) (initializers : List Expr)
    (decoded : decodeTopLevelProgram fuel forms =
      some (definitions, slotTypes, initializers)) :
    ∃ layout : ProgramHeaders,
      readProgramHeaders fuel 0 forms = some layout ∧
      slotTypes = layout.globals.map GlobalHeader.type ∧
      slotTypes.length = initializers.length ∧
      programWellScoped definitions ∧
      ∀ expression ∈ initializers, letLayoutsAligned expression = true := by
  have decodedOriginal := decoded
  unfold decodeTopLevelProgram at decoded
  cases layoutResult : readProgramHeaders fuel 0 forms with
  | none => simp [layoutResult] at decoded
  | some layout =>
      have innerDecoded :
          decodeProgramWithGlobals fuel layout.functions layout.globals =
            some (definitions, slotTypes, initializers) := by
        simpa [layoutResult] using decoded
      have layoutFacts := decodeProgramWithGlobals_layout fuel layout.functions
        layout.globals definitions slotTypes initializers innerDecoded
      have scopedFacts := decodeTopLevelProgram_wellScoped fuel forms definitions
        slotTypes initializers decodedOriginal
      exact ⟨layout, rfl, layoutFacts.1, layoutFacts.2,
        scopedFacts.1, scopedFacts.2⟩

theorem decodedProgram_wellScoped (fuel : Nat) (forms : List Node)
    (definitions : Definitions)
    (decoded : decodeProgram fuel forms = some definitions) :
    programWellScoped definitions :=
  decodeProgram_letLayoutsAligned fuel forms definitions decoded

theorem lambda_closure_wellScoped (env : Environment) (parameters : List Nat)
    (body : Expr) (envScoped : environmentWellScoped env)
    (bodyAligned : letLayoutsAligned body = true) :
    valueWellScoped (.closure parameters body env) := by
  exact .closure bodyAligned envScoped

theorem sourceLambdaEvaluation_preserves_wellScoped (environment : Environment)
    (parameters : List Nat) (body : Expr)
    (environmentScoped : environmentWellScoped environment)
    (bodyAligned : letLayoutsAligned body = true) :
    valueWellScoped (.closure parameters body environment) :=
  lambda_closure_wellScoped environment parameters body environmentScoped bodyAligned

theorem definitionsLetLayoutsAligned_mem (definitions : Definitions)
    (aligned : definitionsLetLayoutsAligned definitions = true)
    (definition : List Nat × Expr) (member : definition ∈ definitions) :
    letLayoutsAligned definition.2 = true := by
  unfold definitionsLetLayoutsAligned at aligned
  exact List.all_eq_true.mp aligned definition member

theorem environmentWellScoped_lookup (environment : Environment) (identity : Nat)
    (value : Value) (scopeProof : environmentWellScoped environment)
    (found : lookup identity environment = some value) :
    valueWellScoped value := by
  induction environment with
  | nil => simp [lookup] at found
  | cons entry rest ih =>
      rcases entry with ⟨key, current⟩
      cases scopeProof with
      | cons currentScoped restScoped =>
          simp only [lookup] at found
          split at found
          · have same : current = value := Option.some.inj found
            cases same
            exact currentScoped
          · exact ih restScoped found

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

theorem program_lookup_body_wellScoped (program : Definitions) (index : Nat)
    (parameters : List Nat) (body : Expr)
    (programScoped : programWellScoped program)
    (found : program[index]? = some (parameters, body)) :
    letLayoutsAligned body = true := by
  have member := definition_mem_of_getElem? found
  exact definitionsLetLayoutsAligned_mem program
    (by simpa [programWellScoped] using programScoped) (parameters, body) member

theorem closureApplication_environment_wellScoped
    (parameters : List Nat) (body : Expr) (captured : Environment)
    (values : List Value)
    (closureScoped : valueWellScoped (.closure parameters body captured))
    (valuesScoped : ∀ value ∈ values, valueWellScoped value)
    (_arity : values.length = parameters.length) :
    letLayoutsAligned body = true ∧
      environmentWellScoped (bind parameters values ++ captured) := by
  cases closureScoped with
  | closure bodyAligned capturedScoped =>
      exact ⟨bodyAligned, environmentWellScoped_bind_append parameters values captured
        valuesScoped capturedScoped⟩

/-- A finite Named evaluation starting in a well-scoped environment preserves
the recursive closure/binder invariant, provided every program body and every
let layout is aligned. This is the source-side invariant needed to reflect
closures produced by an erased execution back through later applications. -/
theorem evaluation_preserves_valueWellScoped (program : Definitions)
    (programScoped : programWellScoped program) :
    ∀ {environment : Environment} {expression : Expr} {value : Value},
      Evaluates program environment expression value →
      environmentWellScoped environment → letLayoutsAligned expression = true →
      valueWellScoped value := by
  apply Evaluates.rec (program := program)
    (motive_1 := fun environment expression value _ =>
      environmentWellScoped environment → letLayoutsAligned expression = true →
        valueWellScoped value)
    (motive_2 := fun environment expressions values _ =>
      environmentWellScoped environment →
        (∀ expression ∈ expressions, letLayoutsAligned expression = true) →
        ∀ value ∈ values, valueWellScoped value)
    (motive_3 := fun environment expressions previous value _ =>
      environmentWellScoped environment →
        (∀ expression ∈ expressions, letLayoutsAligned expression = true) →
        valueWellScoped previous →
        valueWellScoped value)
  all_goals intros
  all_goals try assumption
  all_goals try (exact ValueWellScoped.bool)
  all_goals try (exact ValueWellScoped.int)
  all_goals try (exact ValueWellScoped.float)
  all_goals try (exact ValueWellScoped.string)
  all_goals try (exact ValueWellScoped.character)
  all_goals try (exact ValueWellScoped.unit)
  all_goals try (exact ValueWellScoped.global)
  all_goals try (exact ValueWellScoped.nil)
  all_goals try (exact ValueWellScoped.none)
  case var =>
    rename_i identity environment value found environmentScoped _aligned
    exact environmentWellScoped_lookup environment identity value environmentScoped found
  case lam =>
    rename_i environment parameters body environmentScoped aligned
    have bodyAligned : letLayoutsAligned body = true := by
      simpa [letLayoutsAligned] using aligned
    exact ValueWellScoped.closure bodyAligned environmentScoped
  case appClosure =>
    rename_i environment function parameters body captured arguments values result
      evalFunction evalArguments arity evalBody ihFunction ihArguments ihBody
      environmentScoped aligned
    rcases letLayoutsAligned_app_parts function arguments aligned with
      ⟨functionAligned, argumentsAligned⟩
    have functionScoped := ihFunction environmentScoped functionAligned
    have argumentsScoped : ∀ value ∈ values, valueWellScoped value :=
      ihArguments environmentScoped (by
        intro expression member
        exact letLayoutsAlignedList_mem arguments argumentsAligned member)
    obtain ⟨bodyAligned, bodyEnvironmentScoped⟩ := closureApplication_environment_wellScoped
      parameters body captured values functionScoped argumentsScoped arity
    simpa using ihBody bodyEnvironmentScoped bodyAligned
  case appGlobal =>
    rename_i environment function index arguments values parameters body result
      evalFunction evalArguments definitionFound arity evalBody ihFunction ihArguments ihBody
      environmentScoped aligned
    rcases letLayoutsAligned_app_parts function arguments aligned with
      ⟨functionAligned, argumentsAligned⟩
    have argumentsScoped : ∀ value ∈ values, valueWellScoped value :=
      ihArguments environmentScoped (by
        intro expression member
        exact letLayoutsAlignedList_mem arguments argumentsAligned member)
    have bodyAligned := program_lookup_body_wellScoped program index parameters body
      programScoped definitionFound
    have callEnvironmentScoped := environmentWellScoped_bind_append parameters values []
      argumentsScoped EnvironmentWellScoped.nil
    exact ihBody (by simpa using callEnvironmentScoped) bodyAligned
  case ifTrue =>
    rename_i environment condition yes result no evalCondition evalYes ihCondition ihYes
      environmentScoped aligned
    exact ihYes environmentScoped
      (letLayoutsAligned_ite_parts condition yes no aligned).2.1
  case ifFalse =>
    rename_i environment condition no result yes evalCondition evalNo ihCondition ihNo
      environmentScoped aligned
    exact ihNo environmentScoped
      (letLayoutsAligned_ite_parts condition yes no aligned).2.2
  case letMany =>
    rename_i environment initializers values ids body result evalInitializers arity evalBody
      ihInitializers ihBody environmentScoped aligned
    rcases letLayoutsAligned_letMany_parts ids initializers body aligned with
      ⟨_arityAligned, initializersAligned, bodyAligned⟩
    have valuesScoped : ∀ value ∈ values, valueWellScoped value :=
      ihInitializers environmentScoped (by
        intro expression member
        exact letLayoutsAlignedList_mem initializers initializersAligned member)
    have bodyEnvironmentScoped := environmentWellScoped_bind_append ids values environment
      valuesScoped environmentScoped
    exact ihBody bodyEnvironmentScoped bodyAligned
  case begin =>
    rename_i environment first previous rest result evalFirst evalRest ihFirst ihRest
      environmentScoped aligned
    rcases letLayoutsAligned_begin_parts first rest aligned with
      ⟨firstAligned, restAligned⟩
    exact ihRest environmentScoped (by
      intro expression member
      exact letLayoutsAlignedList_mem rest restAligned member)
      (ihFirst environmentScoped firstAligned)
  case cons =>
    rename_i environment head headValue tail tailValue evalHead evalTail ihHead ihTail
      environmentScoped aligned
    rcases letLayoutsAligned_cons_parts head tail aligned with ⟨headAligned, tailAligned⟩
    exact ValueWellScoped.cons (ihHead environmentScoped headAligned)
      (ihTail environmentScoped tailAligned)
  case some =>
    rename_i environment expression value evalExpression ihExpression environmentScoped aligned
    exact ValueWellScoped.some (ihExpression environmentScoped
      (letLayoutsAligned_some_body expression aligned))
  case matchNil =>
    rename_i environment target empty value head tail full evalTarget evalEmpty ihTarget ihEmpty
      environmentScoped aligned
    rcases letLayoutsAligned_matchList_parts target empty full head tail aligned with
      ⟨_targetAligned, emptyAligned, _fullAligned⟩
    exact ihEmpty environmentScoped emptyAligned
  case matchCons =>
    rename_i environment target headValue tailValue headBinder tailBinder full value empty
      evalTarget evalFull ihTarget ihFull environmentScoped aligned
    rcases letLayoutsAligned_matchList_parts target empty full headBinder tailBinder aligned with
      ⟨_targetAligned, _emptyAligned, fullAligned⟩
    have pairScoped := ihTarget environmentScoped
      (letLayoutsAligned_matchList_parts target empty full headBinder tailBinder aligned).1
    cases pairScoped with
    | cons headScoped tailScoped =>
        exact ihFull (.cons headScoped (.cons tailScoped environmentScoped)) fullAligned
  case matchNone =>
    rename_i environment target empty value binder full evalTarget evalEmpty ihTarget ihEmpty
      environmentScoped aligned
    rcases letLayoutsAligned_matchOption_parts target empty full binder aligned with
      ⟨_targetAligned, emptyAligned, _fullAligned⟩
    exact ihEmpty environmentScoped emptyAligned
  case matchSome =>
    rename_i environment target item binder full value empty evalTarget evalFull ihTarget ihFull
      environmentScoped aligned
    rcases letLayoutsAligned_matchOption_parts target empty full binder aligned with
      ⟨targetAligned, _emptyAligned, fullAligned⟩
    cases h : ihTarget environmentScoped targetAligned with
    | some itemScoped => exact ihFull (.cons itemScoped environmentScoped) fullAligned
  case nil =>
    rename_i environment envScoped _ value member
    simp at member
  case cons =>
    rename_i environment head headValue tail values evalHead evalTail ihHead ihTail
      environmentScoped aligned value member
    simp only [List.mem_cons] at member
    rcases member with same | inTail
    · cases same
      exact ihHead environmentScoped (aligned head (by simp))
    · exact ihTail environmentScoped
        (fun expression inTail' => aligned expression (List.mem_cons_of_mem _ inTail'))
        value inTail
  case cons =>
    rename_i environment head headValue tail result previous evalHead evalTail ihHead ihTail
      environmentScoped aligned previousScoped
    have headScoped := ihHead environmentScoped (aligned head (by simp))
    exact ihTail environmentScoped
      (fun expression member => aligned expression (List.mem_cons_of_mem _ member)) headScoped

/-- A body obtained from a successfully decoded function program inherits the
same closure-safe result invariant from decoding and finite evaluation. -/
theorem decodeProgram_body_evaluation_preserves_valueWellScoped
    (fuel : Nat) (forms : List Node) (definitions : Definitions)
    (decoded : decodeProgram fuel forms = some definitions)
    (index : Nat) (parameters : List Nat) (body : Expr)
    (found : definitions[index]? = some (parameters, body))
    (environment : Environment) (value : Value)
    (environmentScoped : environmentWellScoped environment)
    (evaluated : Evaluates definitions environment body value) :
    valueWellScoped value := by
  apply evaluation_preserves_valueWellScoped definitions
    (decodedProgram_wellScoped fuel forms definitions decoded) evaluated environmentScoped
  exact program_lookup_body_wellScoped definitions index parameters body
    (decodedProgram_wellScoped fuel forms definitions decoded) found

/-- Initializers returned by the mixed top-level decoder also preserve the
closure-safe invariant when they evaluate in a well-scoped environment. -/
theorem decodeTopLevel_initializer_evaluation_preserves_valueWellScoped
    (fuel : Nat) (forms : List Node) (definitions : Definitions)
    (slotTypes : List Surface.Ty) (initializers : List Expr)
    (decoded : decodeTopLevelProgram fuel forms =
      some (definitions, slotTypes, initializers))
    (environment : Environment) (expression : Expr) (value : Value)
    (member : expression ∈ initializers)
    (environmentScoped : environmentWellScoped environment)
    (evaluated : Evaluates definitions environment expression value) :
    valueWellScoped value := by
  have aligned := decodeTopLevelProgram_wellScoped fuel forms definitions slotTypes
    initializers decoded
  apply evaluation_preserves_valueWellScoped definitions aligned.1 evaluated environmentScoped
  exact aligned.2 expression member

theorem decodeProgram_lookup_letMany_lengths (fuel : Nat) (forms : List Node)
    (definitions : Definitions) (decoded : decodeProgram fuel forms = some definitions)
    {index : Nat} {parameters ids : List Nat} {initializers : List Expr} {body : Expr}
    (found : definitions[index]? = some (parameters, .letMany ids initializers body)) :
    ids.length = initializers.length :=
  decodeProgram_member_letMany_lengths fuel forms definitions decoded parameters ids
    initializers body (definition_mem_of_getElem? found)

end NLisp.Named
