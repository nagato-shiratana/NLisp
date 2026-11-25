import NLisp.CMacroCopy
import NLisp.TypedExpansion

namespace NLisp.CBindingWalk

open CNameResolution

/- Annotated C output. The independently executed walk constructs environments
from declarations and lexical binders, never from C's environment observations. -/
inductive Node where
  | atom : CMacroCopy.Atom → Nat → Node
  | list : List Node → Node
  deriving Repr

noncomputable def Node.erase : Node → CMacroCopy.Tree :=
  Node.rec (motive_1 := fun _ => CMacroCopy.Tree)
    (motive_2 := fun _ => List CMacroCopy.Tree)
    (fun a _ => CMacroCopy.Tree.atom a) (fun _ children => CMacroCopy.Tree.list children)
    [] (fun _ _ head tail => head :: tail)

abbrev Environment := List Entry
abbrev Definitions := List Environment

structure Site where
  name : String
  selected : Nat
  environment : Environment
  caller : Environment
  deriving Repr

/- IDs are disjoint from lexer tokens (1 mod 3) and fresh binders (2 mod 3). -/
def builtinEnvironment : Environment :=
  (["+", "-", "*", "<", "<=", ">", ">=", "integer=", "quotient", "remainder",
    "boolean=", "not", "float+", "float-", "float*", "float/", "float<", "float<=",
    "float>", "float>=", "float=", "to-float", "float-truncate", "string=",
    "string-append", "character="].enum.map
      (fun (index, name) => (⟨name, 3 * (index + 1), 3 * (index + 1)⟩ : Entry))).reverse

theorem builtinEnvironment_floatArithmetic_ids :
    findName builtinEnvironment "float+" = some ⟨"float+", 39, 39⟩ ∧
    findName builtinEnvironment "float-" = some ⟨"float-", 42, 42⟩ ∧
    findName builtinEnvironment "float*" = some ⟨"float*", 45, 45⟩ ∧
    findName builtinEnvironment "float/" = some ⟨"float/", 48, 48⟩ := by
  decide

/-- The 26 entries in C's builtin table are assigned the same stable
three-step identities used by name resolution. This pins every C builtin
spelling to the identity consumed by the Lean annotated-tree walk. -/
theorem builtinEnvironment_all_ids :
    findName builtinEnvironment "+" = some ⟨"+", 3, 3⟩ ∧
    findName builtinEnvironment "-" = some ⟨"-", 6, 6⟩ ∧
    findName builtinEnvironment "*" = some ⟨"*", 9, 9⟩ ∧
    findName builtinEnvironment "<" = some ⟨"<", 12, 12⟩ ∧
    findName builtinEnvironment "<=" = some ⟨"<=", 15, 15⟩ ∧
    findName builtinEnvironment ">" = some ⟨">", 18, 18⟩ ∧
    findName builtinEnvironment ">=" = some ⟨">=", 21, 21⟩ ∧
    findName builtinEnvironment "integer=" = some ⟨"integer=", 24, 24⟩ ∧
    findName builtinEnvironment "quotient" = some ⟨"quotient", 27, 27⟩ ∧
    findName builtinEnvironment "remainder" = some ⟨"remainder", 30, 30⟩ ∧
    findName builtinEnvironment "boolean=" = some ⟨"boolean=", 33, 33⟩ ∧
    findName builtinEnvironment "not" = some ⟨"not", 36, 36⟩ ∧
    findName builtinEnvironment "float+" = some ⟨"float+", 39, 39⟩ ∧
    findName builtinEnvironment "float-" = some ⟨"float-", 42, 42⟩ ∧
    findName builtinEnvironment "float*" = some ⟨"float*", 45, 45⟩ ∧
    findName builtinEnvironment "float/" = some ⟨"float/", 48, 48⟩ ∧
    findName builtinEnvironment "float<" = some ⟨"float<", 51, 51⟩ ∧
    findName builtinEnvironment "float<=" = some ⟨"float<=", 54, 54⟩ ∧
    findName builtinEnvironment "float>" = some ⟨"float>", 57, 57⟩ ∧
    findName builtinEnvironment "float>=" = some ⟨"float>=", 60, 60⟩ ∧
    findName builtinEnvironment "float=" = some ⟨"float=", 63, 63⟩ ∧
    findName builtinEnvironment "to-float" = some ⟨"to-float", 66, 66⟩ ∧
    findName builtinEnvironment "float-truncate" = some ⟨"float-truncate", 69, 69⟩ ∧
    findName builtinEnvironment "string=" = some ⟨"string=", 72, 72⟩ ∧
    findName builtinEnvironment "string-append" = some ⟨"string-append", 75, 75⟩ ∧
    findName builtinEnvironment "character=" = some ⟨"character=", 78, 78⟩ := by
  decide

/-- Primitive identities used by the independently typed expansion model.
The order is the C `builtin_specs` order, which is also the order used when
assigning stable identities above. -/
def builtinPrimitive : String → Option TypedExpansion.Primitive
  | "+" => some .add | "-" => some .sub | "*" => some .mul
  | "<" => some .lt | "<=" => some .le | ">" => some .gt | ">=" => some .ge
  | "integer=" => some .intEq | "quotient" => some .quotient
  | "remainder" => some .remainder | "boolean=" => some .boolEq | "not" => some .not
  | "float+" => some .fadd | "float-" => some .fsub | "float*" => some .fmul
  | "float/" => some .fdiv | "float<" => some .flt | "float<=" => some .fle
  | "float>" => some .fgt | "float>=" => some .fge | "float=" => some .floatEq
  | "to-float" => some .toFloat | "float-truncate" => some .truncate
  | "string=" => some .stringEq | "string-append" => some .append
  | "character=" => some .charEq | _ => none

theorem builtinEnvironment_primitiveRows :
    (builtinEnvironment.reverse.map (fun entry => (entry.identity,
      builtinPrimitive entry.name))) =
    [(3, some .add), (6, some .sub), (9, some .mul), (12, some .lt),
     (15, some .le), (18, some .gt), (21, some .ge), (24, some .intEq),
     (27, some .quotient), (30, some .remainder), (33, some .boolEq),
     (36, some .not), (39, some .fadd), (42, some .fsub), (45, some .fmul),
     (48, some .fdiv), (51, some .flt), (54, some .fle), (57, some .fgt),
     (60, some .fge), (63, some .floatEq), (66, some .toFloat),
     (69, some .truncate), (72, some .stringEq), (75, some .append),
     (78, some .charEq)] := by
  decide

theorem builtinEnvironment_primitiveTypeRows :
    (builtinEnvironment.reverse.map (fun entry => (entry.identity,
      (builtinPrimitive entry.name).map TypedExpansion.Primitive.type))) =
    [(3, some (.fn .integer (.fn .integer .integer))),
     (6, some (.fn .integer (.fn .integer .integer))),
     (9, some (.fn .integer (.fn .integer .integer))),
     (12, some (.fn .integer (.fn .integer .boolean))),
     (15, some (.fn .integer (.fn .integer .boolean))),
     (18, some (.fn .integer (.fn .integer .boolean))),
     (21, some (.fn .integer (.fn .integer .boolean))),
     (24, some (.fn .integer (.fn .integer .boolean))),
     (27, some (.fn .integer (.fn .integer (.option .integer)))),
     (30, some (.fn .integer (.fn .integer (.option .integer)))),
     (33, some (.fn .boolean (.fn .boolean .boolean))),
     (36, some (.fn .boolean .boolean)),
     (39, some (.fn .floating (.fn .floating .floating))),
     (42, some (.fn .floating (.fn .floating .floating))),
     (45, some (.fn .floating (.fn .floating .floating))),
     (48, some (.fn .floating (.fn .floating .floating))),
     (51, some (.fn .floating (.fn .floating .boolean))),
     (54, some (.fn .floating (.fn .floating .boolean))),
     (57, some (.fn .floating (.fn .floating .boolean))),
     (60, some (.fn .floating (.fn .floating .boolean))),
     (63, some (.fn .floating (.fn .floating .boolean))),
     (66, some (.fn .integer .floating)),
     (69, some (.fn .floating (.option .integer))),
     (72, some (.fn .string (.fn .string .boolean))),
     (75, some (.fn .string (.fn .string .string))),
     (78, some (.fn .character (.fn .character .boolean)))] := by
  decide

def entry : Node → Option Entry
  | .atom a _ => if Lexical.identifier a.name then some ⟨a.name, a.token, a.token⟩ else none
  | _ => none

def named : Node → String → Bool
  | .atom a _, name => a.name == name
  | _, _ => false

def literal := Lexical.literal

def bindParameters : List Node → Environment → Option Environment
  | [], env => some env
  | .list [name, _] :: tail, env => do
      let binding ← entry name
      bindParameters tail (binding :: env)
  | _, _ => none

def bindPatterns (parameters : List Node) (env : Environment) : Option Environment :=
  parameters.foldrM (fun node current => do return (← entry node) :: current) env

def functionParts : Node → Option (Node × List Node × Node)
  | .list [head, name, .list parameters, _, body] =>
      if named head "defun" then some (name, parameters, body) else none
  | .list [head, name, .list [forallHead, _, .list parameters, _], body] =>
      if named head "defun" && named forallHead "forall" then some (name, parameters, body) else none
  | _ => none

def valueParts : Node → Option (Node × Node)
  | .list [head, .list [name, _], value] =>
      if named head "define" then some (name, value) else none
  | _ => none

def globals (forms : List Node) (builtins : Environment) : Option Environment :=
  forms.foldlM (fun env form =>
    match functionParts form with
    | some (name, _, _) => do return (← entry name) :: env
    | none => if (valueParts form).isSome then some env else none) builtins

def definitionScopes : List Node → Environment → Option Definitions
  | [], env => some [env]
  | form :: tail, env => do
      let next : Environment ← match valueParts form with
        | some (name, _) => (entry name).map (fun binding => binding :: env)
        | none => if (functionParts form).isSome then some env else none
      return env :: (← definitionScopes tail next)

structure WalkOperations where
  walk : Definitions → Environment → Node → Option (List Site)
  walkMany : Definitions → Environment → List Node → Option (List Site)
  walkBindings : Definitions → Environment → Environment → List Node → Option (List Site × Environment)
  walkMatch : Definitions → Environment → List Node → Option (List Site)
  walkCases : Definitions → Environment → List Node → Option (List Site)

def walkOperations : Nat → WalkOperations
  | 0 => ⟨fun _ _ _ => none, fun _ _ _ => none, fun _ _ _ _ => none,
      fun _ _ _ => none, fun _ _ _ => none⟩
  | fuel + 1 =>
      let previous := walkOperations fuel
      { walk := fun definitions env tree =>
          match tree with
          | .atom a selected =>
              if literal a.name then
                if selected == 0 then some [] else none
              else do
                let actualEnv ← match a.origin with
                  | none => some env
                  | some index => definitions[index]?
                pure [⟨a.name, selected, actualEnv, env⟩]
          | .list items => do
              match items with
              | [] => none
              | head :: tail =>
                  if named head "lambda" then
                    match tail with
                    | [.list parameters, _, body] =>
                        previous.walk definitions (← bindParameters parameters env) body
                    | _ => none
                  else if named head "let" then
                    match tail with
                    | [.list bindings, body] =>
                        let (sites, inner) ← previous.walkBindings definitions env env bindings
                        return sites ++ (← previous.walk definitions inner body)
                    | _ => none
                  else if named head "match" then previous.walkMatch definitions env items
                  else if named head "type-app" then
                    match tail with
                    | fn :: _ => previous.walk definitions env fn
                    | _ => none
                  else if named head "Nil" || named head "None" then some []
                  else if named head "Some" || named head "Cons" then previous.walkMany definitions env (tail.drop 1)
                  else if named head "if" || named head "begin" then previous.walkMany definitions env tail
                  else previous.walkMany definitions env items
        walkMany := fun definitions env trees =>
          match trees with
          | [] => some []
          | head :: tail => do
              return (← previous.walk definitions env head) ++ (← previous.walkMany definitions env tail)
        walkBindings := fun definitions env inner trees =>
          match trees with
          | [] => some ([], inner)
          | .list [.list [name, _], value] :: tail => do
              let binding ← entry name
              let sites ← previous.walk definitions env value
              let (remaining, final) ← previous.walkBindings definitions env (binding :: inner) tail
              return (sites ++ remaining, final)
          | _ => none
        walkMatch := fun definitions env trees =>
          match trees with
          | _ :: scrutinee :: cases => do
              return (← previous.walk definitions env scrutinee) ++ (← previous.walkCases definitions env cases)
          | _ => none
        walkCases := fun definitions env trees =>
          match trees with
          | [] => some []
          | .list [.list (_ :: parameters), body] :: tail => do
              let inner ← bindPatterns parameters env
              return (← previous.walk definitions inner body) ++ (← previous.walkCases definitions env tail)
          | _ => none }

def walk (fuel : Nat) := (walkOperations fuel).walk
def walkMany (fuel : Nat) := (walkOperations fuel).walkMany
def walkBindings (fuel : Nat) := (walkOperations fuel).walkBindings
def walkMatch (fuel : Nat) := (walkOperations fuel).walkMatch
def walkCases (fuel : Nat) := (walkOperations fuel).walkCases

def walkDeclaration (fuel : Nat) (definitions : Definitions) (form : Node)
    (env : Environment) : Option (List Site × Environment) :=
  match functionParts form with
  | some (_, parameters, body) => do
      let inner ← bindParameters parameters env
      let sites ← walk fuel definitions inner body
      pure (sites, env)
  | none => match valueParts form with
    | some (name, value) => do
        let sites ← walk fuel definitions env value
        let binding ← entry name
        pure (sites, binding :: env)
    | none => none

def walkProgram (fuel : Nat) (definitions : Definitions) : List Node → Environment → Option (List Site)
  | [], _ => some []
  | form :: tail, env => do
      let (sites, next) ← walkDeclaration fuel definitions form env
      return sites ++ (← walkProgram fuel definitions tail next)

def references (fuel : Nat) (forms : List Node) (builtins : Environment) : Option (List Site) := do
  let env ← globals forms builtins
  walkProgram fuel (← definitionScopes forms env) forms env

def accepts (site : Site) : Bool :=
  match findName site.environment site.name with
  | none => false
  | some binding => decide (site.selected = binding.identity ∧ binding ∈ site.caller) &&
      ScopedSyntax.uniqueIds (scope (fun _ => .unit) site.environment) &&
      ScopedSyntax.uniqueIds (scope (fun _ => .unit) site.caller)

theorem accepts_selected_identity_in_caller (site : Site) (accepted : accepts site = true) :
    ∃ binding, binding ∈ site.caller ∧ binding.identity = site.selected := by
  unfold accepts at accepted
  cases found : findName site.environment site.name with
  | none => simp [found] at accepted
  | some binding =>
      simp only [found, Bool.and_eq_true] at accepted
      have facts : site.selected = binding.identity ∧ binding ∈ site.caller :=
        of_decide_eq_true accepted.1.1
      exact ⟨binding, facts.2, facts.1.symm⟩

/- Cost only the linked-environment name lookup performed by `accepts`.
Structural checks for membership and unique scope identifiers are deliberately
outside this partial cost model. -/
def acceptsWithLookupCost (site : Site) : Bool × Nat :=
  let (found, cost) := findNameWithByteCost site.environment site.name
  let accepted := match found with
    | none => false
    | some binding =>
        decide (site.selected = binding.identity ∧ binding ∈ site.caller) &&
          ScopedSyntax.uniqueIds (scope (fun _ => .unit) site.environment) &&
          ScopedSyntax.uniqueIds (scope (fun _ => .unit) site.caller)
  (accepted, 8 * cost)

theorem acceptsWithLookupCost_result (site : Site) :
    (acceptsWithLookupCost site).1 = accepts site := by
  simp [acceptsWithLookupCost, accepts, findNameWithByteCost_result]

def checkSitesWithLookupCost : List Site → Bool × Nat
  | [] => (true, 0)
  | site :: rest =>
      let (tailAccepted, tailCost) := checkSitesWithLookupCost rest
      let (siteAccepted, siteCost) := acceptsWithLookupCost site
      (siteAccepted && tailAccepted, siteCost + tailCost)

theorem checkSitesWithLookupCost_result (sites : List Site) :
    (checkSitesWithLookupCost sites).1 = sites.all accepts := by
  induction sites with
  | nil => rfl
  | cons site rest ih =>
      simp [checkSitesWithLookupCost, acceptsWithLookupCost_result, ih]

def check (fuel : Nat) (forms : List Node) (builtins : Environment) : Bool :=
  match references fuel forms builtins with
  | none => false
  | some sites => sites.all accepts

def checkWithLookupCost (fuel : Nat) (forms : List Node) (builtins : Environment) :
    Bool × Nat :=
  match references fuel forms builtins with
  | none => (false, 0)
  | some sites => checkSitesWithLookupCost sites

theorem checkWithLookupCost_result (fuel : Nat) (forms : List Node)
    (builtins : Environment) :
    (checkWithLookupCost fuel forms builtins).1 = check fuel forms builtins := by
  unfold checkWithLookupCost check
  cases references fuel forms builtins <;> simp [checkSitesWithLookupCost_result]

def Corresponds (site : Site) : Prop :=
  ∀ interpret : Nat → ScopedSyntax.Ty,
    ScopedSyntax.Valid (scope interpret site.environment) ∧
    ScopedSyntax.Valid (scope interpret site.caller) ∧
    ∃ (binding : Entry)
      (reference : ScopedSyntax.Var (ScopedSyntax.types (scope interpret site.environment))
        (interpret binding.typeTag))
      (callerReference : ScopedSyntax.Var (ScopedSyntax.types (scope interpret site.caller))
        (interpret binding.typeTag)),
      findName site.environment site.name = some binding ∧
      ScopedSyntax.bindingId (scope interpret site.environment) reference = site.selected ∧
      ScopedSyntax.bindingId (scope interpret site.caller) callerReference = site.selected

theorem accepts_sound (site : Site) (accepted : accepts site = true) : Corresponds site := by
  unfold accepts at accepted
  cases found : findName site.environment site.name with
  | none => simp [found] at accepted
  | some binding =>
      have both : (site.selected = binding.identity ∧ binding ∈ site.caller) ∧
          ScopedSyntax.uniqueIds (scope (fun _ => .unit) site.environment) = true ∧
          ScopedSyntax.uniqueIds (scope (fun _ => .unit) site.caller) = true := by
        simpa [found, Bool.and_eq_true, and_assoc] using accepted
      have same := both.1.1
      intro interpret
      refine ⟨?_, ?_, ?_⟩
      · unfold ScopedSyntax.Valid
        rw [scope_ids_invariant site.environment interpret (fun _ => .unit)]
        exact both.2.1
      · unfold ScopedSyntax.Valid
        rw [scope_ids_invariant site.caller interpret (fun _ => .unit)]
        exact both.2.2
      · obtain ⟨reference, identity⟩ := checked_lookup_corresponds site.environment site.name binding found interpret
        obtain ⟨callerReference, callerIdentity⟩ := member_to_scoped_variable site.caller binding both.1.2 interpret
        exact ⟨binding, reference, callerReference, found, identity.trans same.symm,
          callerIdentity.trans same.symm⟩

theorem check_sound (fuel : Nat) (forms : List Node) (builtins : Environment)
    (accepted : check fuel forms builtins = true) :
    ∃ sites, references fuel forms builtins = some sites ∧ ∀ site ∈ sites, Corresponds site := by
  unfold check at accepted
  cases result : references fuel forms builtins with
  | none => simp [result] at accepted
  | some sites =>
      refine ⟨sites, rfl, ?_⟩
      have all : sites.all accepts = true := by simpa [result] using accepted
      intro site member
      exact accepts_sound site (List.all_eq_true.mp all site member)

theorem check_selected_identities_in_caller (fuel : Nat) (forms : List Node)
    (builtins : Environment) (accepted : check fuel forms builtins = true) :
    ∃ sites, references fuel forms builtins = some sites ∧
      ∀ site ∈ sites, accepts site = true ∧
        site.selected ∈ site.caller.map (fun entry => entry.identity) := by
  unfold check at accepted
  cases result : references fuel forms builtins with
  | none => simp [result] at accepted
  | some sites =>
      have allAccepted : sites.all accepts = true := by simpa [result] using accepted
      refine ⟨sites, rfl, ?_⟩
      intro site member
      have siteAccepted := List.all_eq_true.mp allAccepted site member
      obtain ⟨binding, bindingMember, selected⟩ :=
        accepts_selected_identity_in_caller site siteAccepted
      exact ⟨siteAccepted, List.mem_map.mpr ⟨binding, bindingMember, selected⟩⟩

end NLisp.CBindingWalk
