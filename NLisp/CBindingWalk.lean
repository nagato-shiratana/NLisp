import NLisp.CMacroCopy
import NLisp.TypedExpansion
import NLisp.Lexical

namespace NLisp.CBindingWalk

open CNameResolution
open NLisp.Lexical

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

noncomputable def Node.nodeCount : Node → Nat :=
  Node.rec (motive_1 := fun _ => Nat)
    (motive_2 := fun _ => Nat)
    (fun _ _ => 1) (fun _ children => children + 1)
    0 (fun _ _ head tail => head + tail)

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

/-- The two registered String builtins have the C table's intended curried
types and executable Text semantics: byte comparison is Lean string equality,
and byte-buffer concatenation decodes to Lean string append (including NUL). -/
theorem builtinStringOperations_CText_semantics (left right : String) :
    builtinPrimitive "string=" = some .stringEq ∧
      TypedExpansion.Primitive.type .stringEq =
        .fn .string (.fn .string .boolean) ∧
      CTextModel.stringEqual (CTextModel.ofString left) (CTextModel.ofString right) =
        decide (left = right) ∧
    builtinPrimitive "string-append" = some .append ∧
      TypedExpansion.Primitive.type .append =
        .fn .string (.fn .string .string) ∧
      CTextModel.stringAppend (CTextModel.ofString left) (CTextModel.ofString right) =
        CTextModel.ofString (left ++ right) ∧
      decodeUtf8 (CTextModel.stringAppend (CTextModel.ofString left)
        (CTextModel.ofString right)).bytes = some (left ++ right) := by
  exact ⟨rfl, rfl, CTextModel.stringEqual_ofString_iff left right,
    rfl, rfl, CTextModel.stringAppend_ofString left right,
    CTextModel.decode_stringAppend_ofString left right⟩

/-- C stores a character as its Unicode scalar value. Equality on those
`uint32_t` values agrees with Lean `Char` equality, and the registered
character builtin has the matching curried primitive type. -/
theorem builtinCharacterEquality_semantics (left right : Char) :
    builtinPrimitive "character=" = some .charEq ∧
      TypedExpansion.Primitive.type .charEq =
        .fn .character (.fn .character .boolean) ∧
      (left.toNat == right.toNat) = decide (left = right) := by
  have charValueInjective : left.toNat = right.toNat → left = right := by
    intro same
    rw [← Lexical.char_ofNat_toNat_identity left,
      ← Lexical.char_ofNat_toNat_identity right, same]
  refine ⟨rfl, rfl, ?_⟩
  by_cases same : left.toNat = right.toNat
  · have charactersEqual := charValueInjective same
    subst right
    simp
  · have different : (left.toNat == right.toNat) = false :=
      (beq_eq_false_iff_ne _ _).mpr same
    have charactersDifferent : left ≠ right := by
      intro equality
      exact same (congrArg Char.toNat equality)
    simp [different, charactersDifferent]

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

def walkSpecialHeadNames : List String :=
  ["lambda", "let", "match", "type-app", "Nil", "None", "Some", "Cons",
    "if", "begin"]

def walkOrdinaryHead (head : Node) : Prop :=
  ∀ name, name ∈ walkSpecialHeadNames → named head name = false

noncomputable def nodeListNodeCount (nodes : List Node) : Nat :=
  CMacroCopy.treeListNodeCount (nodes.map Node.erase)

noncomputable def annotatedNodeListCount : List Node → Nat
  | [] => 0
  | head :: tail => Node.nodeCount head + annotatedNodeListCount tail

theorem annotatedNodeListCount_cons (head : Node) (tail : List Node) :
    annotatedNodeListCount (head :: tail) =
      Node.nodeCount head + annotatedNodeListCount tail := rfl

theorem nodeCount_list_eq_annotatedNodeListCount (nodes : List Node) :
    Node.nodeCount (.list nodes) = annotatedNodeListCount nodes + 1 := by
  induction nodes with
  | nil => simp [Node.nodeCount, annotatedNodeListCount]
  | cons head tail ih =>
      simp [Node.nodeCount] at ih
      simp [Node.nodeCount, annotatedNodeListCount]
      omega

theorem nodeListNodeCount_cons (head : Node) (tail : List Node) :
    nodeListNodeCount (head :: tail) =
      CMacroCopy.treeNodeCount (Node.erase head) + nodeListNodeCount tail := rfl

/-- If every child walk emits no more sites than syntax nodes, the mutually
recursive list walker emits no more sites than the full input node list. -/
theorem walkMany_sites_le_nodeCount
    (fuel : Nat) (definitions : Definitions) (env : Environment)
    (trees : List Node) (sites : List Site)
    (walkBound : ∀ subfuel, subfuel ≤ fuel → ∀ tree childSites,
      walk subfuel definitions env tree = some childSites →
        childSites.length ≤ CMacroCopy.treeNodeCount (Node.erase tree))
    (accepted : walkMany fuel definitions env trees = some sites) :
    sites.length ≤ nodeListNodeCount trees := by
  induction fuel generalizing trees sites with
  | zero => simp [walkMany, walkOperations] at accepted
  | succ fuel ih =>
      cases trees with
      | nil =>
          simp [walkMany, walkOperations] at accepted
          subst sites
          simp [nodeListNodeCount]
      | cons head tail =>
          change (do
            let headSites ← walk fuel definitions env head
            let tailSites ← walkMany fuel definitions env tail
            pure (headSites ++ tailSites)) = some sites at accepted
          obtain ⟨headSites, headAccepted, tailBind⟩ := Option.bind_eq_some.mp accepted
          obtain ⟨tailSites, tailAccepted, sitesEq⟩ := Option.bind_eq_some.mp tailBind
          have headBound := walkBound fuel (by omega) head headSites headAccepted
          have tailBound := ih tail tailSites
            (fun subfuel subfuelBound tree childSites childAccepted =>
              walkBound subfuel (by omega) tree childSites childAccepted)
            tailAccepted
          have sitesEq' : headSites ++ tailSites = sites := by simpa using sitesEq
          rw [← sitesEq']
          simp only [List.length_append, nodeListNodeCount_cons]
          omega

/-- The same list-walker argument over annotated syntax's native measure.
This form composes directly with structural `Node.nodeCount` bounds and does
not require erasing the annotated tree first. -/
theorem walkMany_sites_le_annotatedNodeCount
    (fuel : Nat) (definitions : Definitions) (env : Environment)
    (trees : List Node) (sites : List Site)
    (walkBound : ∀ subfuel, subfuel ≤ fuel → ∀ tree childSites,
      walk subfuel definitions env tree = some childSites →
        childSites.length ≤ Node.nodeCount tree)
    (accepted : walkMany fuel definitions env trees = some sites) :
    sites.length ≤ annotatedNodeListCount trees := by
  induction fuel generalizing trees sites with
  | zero => simp [walkMany, walkOperations] at accepted
  | succ fuel ih =>
      cases trees with
      | nil =>
          simp [walkMany, walkOperations] at accepted
          subst sites
          simp [annotatedNodeListCount]
      | cons head tail =>
          change (do
            let headSites ← walk fuel definitions env head
            let tailSites ← walkMany fuel definitions env tail
            pure (headSites ++ tailSites)) = some sites at accepted
          obtain ⟨headSites, headAccepted, tailBind⟩ := Option.bind_eq_some.mp accepted
          obtain ⟨tailSites, tailAccepted, sitesEq⟩ := Option.bind_eq_some.mp tailBind
          have headBound := walkBound fuel (by omega) head headSites headAccepted
          have tailBound := ih tail tailSites
            (fun subfuel subfuelBound tree childSites childAccepted =>
              walkBound subfuel (by omega) tree childSites childAccepted)
            tailAccepted
          have sitesEq' : headSites ++ tailSites = sites := by simpa using sitesEq
          rw [← sitesEq']
          simp only [List.length_append, annotatedNodeListCount_cons]
          omega

/-- A row-indexed variant only asks for pointwise walk bounds on nodes that
actually occur in the input list. -/
theorem walkMany_sites_le_annotatedNodeCount_of_rows
    (fuel : Nat) (definitions : Definitions) (env : Environment)
    (trees : List Node) (sites : List Site)
    (walkBound : ∀ subfuel, subfuel ≤ fuel → ∀ tree, tree ∈ trees →
      ∀ childSites, walk subfuel definitions env tree = some childSites →
        childSites.length ≤ Node.nodeCount tree)
    (accepted : walkMany fuel definitions env trees = some sites) :
    sites.length ≤ annotatedNodeListCount trees := by
  induction fuel generalizing trees sites with
  | zero => simp [walkMany, walkOperations] at accepted
  | succ fuel ih =>
      cases trees with
      | nil =>
          simp [walkMany, walkOperations] at accepted
          subst sites
          simp [annotatedNodeListCount]
      | cons head tail =>
          change (do
            let headSites ← walk fuel definitions env head
            let tailSites ← walkMany fuel definitions env tail
            pure (headSites ++ tailSites)) = some sites at accepted
          obtain ⟨headSites, headAccepted, tailBind⟩ := Option.bind_eq_some.mp accepted
          obtain ⟨tailSites, tailAccepted, sitesEq⟩ := Option.bind_eq_some.mp tailBind
          have headBound := walkBound fuel (by omega) head (by simp) headSites headAccepted
          have tailBound := ih tail tailSites
            (fun subfuel subfuelBound tree member childSites childAccepted =>
              walkBound subfuel (by omega) tree (List.mem_cons_of_mem head member)
                childSites childAccepted)
            tailAccepted
          have sitesEq' : headSites ++ tailSites = sites := by simpa using sitesEq
          rw [← sitesEq']
          simp only [List.length_append, annotatedNodeListCount_cons]
          omega

theorem walk_atom_sites_length_le_one (fuel : Nat) (definitions : Definitions)
    (env : Environment) (atom : CMacroCopy.Atom) (selected : Nat) (sites : List Site)
    (accepted : walk fuel definitions env (.atom atom selected) = some sites) :
    sites.length ≤ 1 := by
  cases fuel with
  | zero => simp [walk, walkOperations] at accepted
  | succ fuel =>
      by_cases isLiteral : literal atom.name
      · by_cases selectedZero : selected == 0
        · simp [walk, walkOperations, isLiteral, selectedZero] at accepted
          rcases accepted with ⟨_, rfl⟩
          simp
        · simp_all [walk, walkOperations, isLiteral, selectedZero]
      · cases origin : atom.origin with
        | none =>
            simp [walk, walkOperations, isLiteral, origin] at accepted
            cases accepted
            simp
        | some index =>
            cases found : definitions[index]? with
            | none => simp [walk, walkOperations, isLiteral, origin, found] at accepted
            | some actualEnv =>
                simp [walk, walkOperations, isLiteral, origin, found] at accepted
                cases accepted
                simp

theorem walk_atom_sites_le_nodeCount (fuel : Nat) (definitions : Definitions)
    (env : Environment) (atom : CMacroCopy.Atom) (selected : Nat) (sites : List Site)
    (accepted : walk fuel definitions env (.atom atom selected) = some sites) :
    sites.length ≤ Node.nodeCount (.atom atom selected) := by
  have sitesBound := walk_atom_sites_length_le_one fuel definitions env atom selected
    sites accepted
  have atomCount : Node.nodeCount (.atom atom selected) = 1 := by
    simp [Node.nodeCount]
  omega

theorem walk_nilNone_sites_le_nodeCount
    (fuel : Nat) (definitions : Definitions) (env : Environment)
    (atom : CMacroCopy.Atom) (selected : Nat) (tail : List Node)
    (sites : List Site)
    (nilOrNone : (atom.name == "Nil" || atom.name == "None") = true)
    (accepted : walk (fuel + 1) definitions env
      (.list (Node.atom atom selected :: tail)) = some sites) :
    sites.length ≤ Node.nodeCount (.list (Node.atom atom selected :: tail)) := by
  have sitesEmpty : sites = [] := by
    cases isNil : (atom.name == "Nil") with
    | true =>
        have isNilEq : atom.name = "Nil" := of_decide_eq_true isNil
        have notLambda : "Nil" ≠ "lambda" := by decide
        have notLet : "Nil" ≠ "let" := by decide
        have notMatch : "Nil" ≠ "match" := by decide
        have notTypeApp : "Nil" ≠ "type-app" := by decide
        simpa [walk, walkOperations, named, isNilEq, notLambda, notLet,
          notMatch, notTypeApp] using accepted.symm
    | false =>
        have isNoneEq : atom.name = "None" := by
          simpa [isNil] using nilOrNone
        have isNone : (atom.name == "None") = true := by simp [isNoneEq]
        have notLambda : "None" ≠ "lambda" := by decide
        have notLet : "None" ≠ "let" := by decide
        have notMatch : "None" ≠ "match" := by decide
        have notTypeApp : "None" ≠ "type-app" := by decide
        simpa [walk, walkOperations, named, isNil, isNone, isNoneEq,
          notLambda, notLet, notMatch, notTypeApp] using accepted.symm
  subst sites
  simp

/-- On a flat list of annotated atoms, the reference walk emits at most one
site per atom.  This gives an unconditional syntax-node bound for the common
case where a call's operator and operands are all identifiers or literals. -/
theorem walkMany_atomList_sites_le_nodeCount
    (fuel : Nat) (definitions : Definitions) (env : Environment)
    (atoms : List (CMacroCopy.Atom × Nat)) (sites : List Site)
    (accepted : walkMany fuel definitions env
      (atoms.map (fun atom => Node.atom atom.1 atom.2)) = some sites) :
    sites.length ≤ nodeListNodeCount
      (atoms.map (fun atom => Node.atom atom.1 atom.2)) := by
  induction atoms generalizing sites fuel with
  | nil =>
      cases fuel <;> simp [walkMany, walkOperations] at accepted
      cases accepted
      simp [nodeListNodeCount]
  | cons atom rest ih =>
      cases fuel with
      | zero => simp [walkMany, walkOperations] at accepted
      | succ fuel =>
          change (do
            let headSites ← walk fuel definitions env (Node.atom atom.1 atom.2)
            let tailSites ← walkMany fuel definitions env
              (rest.map (fun item => Node.atom item.1 item.2))
            pure (headSites ++ tailSites)) = some sites at accepted
          obtain ⟨headSites, headAccepted, tailBind⟩ := Option.bind_eq_some.mp accepted
          obtain ⟨tailSites, tailAccepted, sitesEq⟩ := Option.bind_eq_some.mp tailBind
          have headBound := walk_atom_sites_length_le_one fuel definitions env
            atom.1 atom.2 headSites headAccepted
          have tailBound := ih fuel tailSites tailAccepted
          have sitesEq' : headSites ++ tailSites = sites := by simpa using sitesEq
          rw [← sitesEq']
          simp only [List.length_append]
          change headSites.length + tailSites.length ≤
            CMacroCopy.treeNodeCount (Node.erase (Node.atom atom.1 atom.2)) +
              nodeListNodeCount (rest.map (fun item => Node.atom item.1 item.2))
          have atomNodeCount : CMacroCopy.treeNodeCount
              (Node.erase (Node.atom atom.1 atom.2)) = 1 := by
            cases atom.1
            simp [Node.erase, CMacroCopy.treeNodeCount]
          omega

theorem nodeListNodeCount_atomList_eq_length
    (atoms : List (CMacroCopy.Atom × Nat)) :
    nodeListNodeCount (atoms.map (fun atom => Node.atom atom.1 atom.2)) =
      atoms.length := by
  induction atoms with
  | nil => rfl
  | cons atom rest ih =>
      change nodeListNodeCount
          (Node.atom atom.1 atom.2 :: rest.map (fun item => Node.atom item.1 item.2)) =
        Nat.succ rest.length
      rw [nodeListNodeCount_cons, ih]
      have atomNodeCount : CMacroCopy.treeNodeCount
          (Node.erase (Node.atom atom.1 atom.2)) = 1 := by
        cases atom.1
        simp [Node.erase, CMacroCopy.treeNodeCount]
      omega

/-- The accepted flat-atom walk therefore emits no more sites than the
number of source atoms, without requiring a separate syntax-tree measure. -/
theorem walkMany_atomList_sites_le_length
    (fuel : Nat) (definitions : Definitions) (env : Environment)
    (atoms : List (CMacroCopy.Atom × Nat)) (sites : List Site)
    (accepted : walkMany fuel definitions env
      (atoms.map (fun atom => Node.atom atom.1 atom.2)) = some sites) :
    sites.length ≤ atoms.length := by
  calc
    sites.length ≤ nodeListNodeCount
        (atoms.map (fun atom => Node.atom atom.1 atom.2)) :=
      walkMany_atomList_sites_le_nodeCount fuel definitions env atoms sites accepted
    _ = atoms.length := nodeListNodeCount_atomList_eq_length atoms

theorem annotatedNodeListCount_atomList_eq_length
    (atoms : List (CMacroCopy.Atom × Nat)) :
    annotatedNodeListCount (atoms.map (fun atom => Node.atom atom.1 atom.2)) =
      atoms.length := by
  induction atoms with
  | nil => rfl
  | cons atom rest ih =>
      change Node.nodeCount (Node.atom atom.1 atom.2) +
        annotatedNodeListCount (rest.map (fun item => Node.atom item.1 item.2)) =
        rest.length + 1
      have atomCount : Node.nodeCount (Node.atom atom.1 atom.2) = 1 := by
        simp [Node.nodeCount]
      rw [atomCount, ih]
      omega

theorem walkMany_atomList_sites_le_annotatedNodeCount
    (fuel : Nat) (definitions : Definitions) (env : Environment)
    (atoms : List (CMacroCopy.Atom × Nat)) (sites : List Site)
    (accepted : walkMany fuel definitions env
      (atoms.map (fun atom => Node.atom atom.1 atom.2)) = some sites) :
    sites.length ≤ annotatedNodeListCount
      (atoms.map (fun atom => Node.atom atom.1 atom.2)) := by
  apply walkMany_sites_le_annotatedNodeCount_of_rows fuel definitions env _ sites
  · intro subfuel _ tree member childSites childAccepted
    obtain ⟨atom, _, treeEq⟩ := List.mem_map.mp member
    subst tree
    exact walk_atom_sites_le_nodeCount subfuel definitions env atom.1 atom.2
      childSites childAccepted
  · exact accepted

/-- An ordinary application-shaped list delegates directly to `walkMany`;
its references are therefore bounded by the number of operator/operand
atoms, and hence by the source tree's node count. -/
theorem walk_ordinaryAtomList_sites_le_length
    (fuel : Nat) (definitions : Definitions) (env : Environment)
    (head : CMacroCopy.Atom × Nat) (rest : List (CMacroCopy.Atom × Nat))
    (sites : List Site)
    (ordinary : walkOrdinaryHead (Node.atom head.1 head.2))
    (accepted : walk (fuel + 1) definitions env
      (.list ((head :: rest).map (fun atom => Node.atom atom.1 atom.2))) = some sites) :
    sites.length ≤ (head :: rest).length := by
  have ordinaryFalse (name : String) (member : name ∈ walkSpecialHeadNames) :
      named (Node.atom head.1 head.2) name = false := ordinary name member
  have manyAccepted : walkMany fuel definitions env
      ((head :: rest).map (fun atom => Node.atom atom.1 atom.2)) = some sites := by
    simpa [walk, walkOperations, walkSpecialHeadNames, ordinaryFalse] using accepted
  exact walkMany_atomList_sites_le_length fuel definitions env (head :: rest)
    sites manyAccepted

theorem nodeCount_atomList (atoms : List (CMacroCopy.Atom × Nat)) :
    Node.nodeCount (.list (atoms.map
      (fun atom => Node.atom atom.1 atom.2))) = atoms.length + 1 := by
  induction atoms with
  | nil => simp [Node.nodeCount]
  | cons atom rest ih =>
      simp [Node.nodeCount] at ih
      simp [Node.nodeCount]
      omega

theorem walk_ordinaryAtomList_sites_le_nodeCount
    (fuel : Nat) (definitions : Definitions) (env : Environment)
    (head : CMacroCopy.Atom × Nat) (rest : List (CMacroCopy.Atom × Nat))
    (sites : List Site)
    (ordinary : walkOrdinaryHead (Node.atom head.1 head.2))
    (accepted : walk (fuel + 1) definitions env
      (.list ((head :: rest).map (fun atom => Node.atom atom.1 atom.2))) = some sites) :
    sites.length ≤ Node.nodeCount (.list ((head :: rest).map
      (fun atom => Node.atom atom.1 atom.2))) := by
  have ordinaryFalse (name : String) (member : name ∈ walkSpecialHeadNames) :
      named (Node.atom head.1 head.2) name = false := ordinary name member
  have manyAccepted : walkMany fuel definitions env
      ((head :: rest).map (fun atom => Node.atom atom.1 atom.2)) = some sites := by
    simpa [walk, walkOperations, walkSpecialHeadNames, ordinaryFalse] using accepted
  have sitesBound := walkMany_atomList_sites_le_annotatedNodeCount
    fuel definitions env (head :: rest) sites manyAccepted
  have rootCount : Node.nodeCount (.list
      ((head :: rest).map (fun atom => Node.atom atom.1 atom.2))) =
      annotatedNodeListCount
        ((head :: rest).map (fun atom => Node.atom atom.1 atom.2)) + 1 := by
    exact nodeCount_list_eq_annotatedNodeListCount _
  rw [rootCount]
  exact Nat.le_trans sitesBound (Nat.le_add_right _ _)

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

/-- Byte-comparison budget for the single linked-environment scan used by a
reference-site check. It charges the query bytes, each candidate binding's
name bytes, and one terminating comparison per examined entry. -/
def acceptsLookupBudget (site : Site) : Nat :=
  8 * site.environment.foldr
    (fun entry rest => site.name.toUTF8.data.size + entry.name.toUTF8.data.size + 1 + rest) 0

def environmentNameBytes (environment : Environment) : Nat :=
  environment.foldr (fun entry rest => entry.name.toUTF8.data.size + rest) 0

theorem acceptsLookupBudget_expanded (site : Site) :
    acceptsLookupBudget site = 8 *
      (site.environment.length * (site.name.toUTF8.data.size + 1) +
        environmentNameBytes site.environment) := by
  have aux (environment : Environment) :
      8 * environment.foldr
        (fun entry rest => site.name.toUTF8.data.size + entry.name.toUTF8.data.size + 1 + rest) 0 =
        8 * (environment.length * (site.name.toUTF8.data.size + 1) +
          environmentNameBytes environment) := by
    induction environment with
    | nil => simp [environmentNameBytes]
    | cons entry rest ih =>
        simp only [List.foldr, environmentNameBytes]
        have ih' := ih
        simp only [environmentNameBytes] at ih'
        rw [Nat.mul_add, ih']
        simp only [List.length_cons, Nat.succ_mul]
        omega
  exact aux site.environment

theorem acceptsWithLookupCost_cost_le (site : Site) :
    (acceptsWithLookupCost site).2 ≤ acceptsLookupBudget site := by
  have lookupBound := findNameWithByteCost_le_lengths site.environment site.name
  simp only [acceptsWithLookupCost, acceptsLookupBudget]
  omega

def checkSitesWithLookupCost : List Site → Bool × Nat
  | [] => (true, 0)
  | site :: rest =>
      let (tailAccepted, tailCost) := checkSitesWithLookupCost rest
      let (siteAccepted, siteCost) := acceptsWithLookupCost site
      (siteAccepted && tailAccepted, siteCost + tailCost)

theorem checkSitesWithLookupCost_result (sites : List Site) :
    (checkSitesWithLookupCost sites).1 = sites.all accepts := by
  induction sites with
  | nil => simp [checkSitesWithLookupCost]
  | cons site rest ih =>
      simp [checkSitesWithLookupCost, acceptsWithLookupCost_result, ih]

theorem checkSitesWithLookupCost_cost_le (sites : List Site) :
    (checkSitesWithLookupCost sites).2 ≤
      sites.foldr (fun site rest => acceptsLookupBudget site + rest) 0 := by
  induction sites with
  | nil => simp [checkSitesWithLookupCost]
  | cons site rest ih =>
      have siteBound := acceptsWithLookupCost_cost_le site
      simp only [checkSitesWithLookupCost, List.foldr]
      omega

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

theorem checkWithLookupCost_lookup_budget (fuel : Nat) (forms : List Node)
    (builtins : Environment) :
    (checkWithLookupCost fuel forms builtins).2 ≤
      match references fuel forms builtins with
      | none => 0
      | some sites => sites.foldr (fun site rest => acceptsLookupBudget site + rest) 0 := by
  unfold checkWithLookupCost
  cases references fuel forms builtins with
  | none => simp
  | some sites => exact checkSitesWithLookupCost_cost_le sites

/- Extend the partial byte lookup meter with the remaining list scans in
`accepts`: caller membership and the pairwise identity checks for both scoped
environments. The equality/identity comparisons use one abstract unit each. -/
def containsEntryWithCost (target : Entry) : List Entry → Bool × Nat
  | [] => (false, 0)
  | head :: tail =>
      if target = head then (true, 1)
      else
        let (found, cost) := containsEntryWithCost target tail
        (found, cost + 1)

theorem containsEntryWithCost_result (target : Entry) (entries : List Entry) :
    (containsEntryWithCost target entries).1 = decide (target ∈ entries) := by
  induction entries with
  | nil => simp [containsEntryWithCost]
  | cons head tail ih =>
      by_cases equal : target = head
      · simp [containsEntryWithCost, equal]
      · simp [containsEntryWithCost, equal, ih]

theorem containsEntryWithCost_cost_le (target : Entry) (entries : List Entry) :
    (containsEntryWithCost target entries).2 ≤ entries.length := by
  induction entries with
  | nil => simp [containsEntryWithCost]
  | cons head tail ih =>
      by_cases equal : target = head
      · simp [containsEntryWithCost, equal]
      · simp only [containsEntryWithCost, if_neg equal, List.length_cons]
        omega

def acceptsWithFullCost (site : Site) : Bool × Nat :=
  let (found, lookupCost) := findNameWithByteCost site.environment site.name
  match found with
  | none => (false, 8 * lookupCost)
  | some binding =>
      let (member, memberCost) := containsEntryWithCost binding site.caller
      let (environmentUnique, environmentCost) :=
        ScopedSyntax.uniqueIdsWithCost (scope (fun _ => .unit) site.environment)
      let (callerUnique, callerCost) :=
        ScopedSyntax.uniqueIdsWithCost (scope (fun _ => .unit) site.caller)
      ((decide (site.selected = binding.identity) && member) &&
          environmentUnique && callerUnique,
        8 * lookupCost + memberCost + 1 + environmentCost + callerCost)

theorem acceptsWithFullCost_result (site : Site) :
    (acceptsWithFullCost site).1 = accepts site := by
  unfold accepts
  cases lookup : findNameWithByteCost site.environment site.name with
  | mk found lookupCost =>
      have foundEq : found = findName site.environment site.name := by
        calc
          found = (findNameWithByteCost site.environment site.name).1 := by rw [lookup]
          _ = findName site.environment site.name := findNameWithByteCost_result _ _
      cases found with
      | none =>
          rw [← foundEq]
          simp [acceptsWithFullCost, lookup]
      | some binding =>
          rw [← foundEq]
          simp [acceptsWithFullCost, lookup, containsEntryWithCost_result,
            ScopedSyntax.uniqueIdsWithCost_result]

def acceptsFullCostBudget (site : Site) : Nat :=
  acceptsLookupBudget site + (1 + site.caller.length +
    site.environment.length * site.environment.length +
    site.caller.length * site.caller.length)

theorem acceptsWithFullCost_cost_le (site : Site) :
    (acceptsWithFullCost site).2 ≤ acceptsFullCostBudget site := by
  cases found : findNameWithByteCost site.environment site.name with
  | mk result lookupCost =>
      have lookupCostEq : (findNameWithByteCost site.environment site.name).2 = lookupCost :=
        congrArg Prod.snd found
      have rawLookupBound := findNameWithByteCost_le_lengths site.environment site.name
      have lookupBound : 8 * lookupCost ≤ acceptsLookupBudget site := by
        have multiplied := Nat.mul_le_mul_left 8 rawLookupBound
        simpa [acceptsLookupBudget, lookupCostEq] using multiplied
      have lookupBound' := lookupBound
      unfold acceptsLookupBudget at lookupBound'
      cases result with
      | none =>
          simp only [acceptsWithFullCost, found]
          unfold acceptsFullCostBudget
          exact Nat.le_trans lookupBound (Nat.le_add_right _ _)
      | some binding =>
          have membershipBound := containsEntryWithCost_cost_le binding site.caller
          have environmentUniqueBound := ScopedSyntax.uniqueIdsWithCost_cost_le
            (scope (fun _ => .unit) site.environment)
          have callerUniqueBound := ScopedSyntax.uniqueIdsWithCost_cost_le
            (scope (fun _ => .unit) site.caller)
          have environmentScopedLength :
              (scope (fun _ => .unit) site.environment).length = site.environment.length := by
            simp [scope]
          have callerScopedLength :
              (scope (fun _ => .unit) site.caller).length = site.caller.length := by
            simp [scope]
          have environmentUniqueBudget :
              (ScopedSyntax.uniqueIdsWithCost
                (scope (fun _ => .unit) site.environment)).2 ≤
                site.environment.length * site.environment.length := by
            simpa [environmentScopedLength] using environmentUniqueBound
          have callerUniqueBudget :
              (ScopedSyntax.uniqueIdsWithCost
                (scope (fun _ => .unit) site.caller)).2 ≤
                site.caller.length * site.caller.length := by
            simpa [callerScopedLength] using callerUniqueBound
          have fullCost : (acceptsWithFullCost site).2 =
              8 * lookupCost + (containsEntryWithCost binding site.caller).2 + 1 +
                (ScopedSyntax.uniqueIdsWithCost
                  (scope (fun _ => .unit) site.environment)).2 +
                (ScopedSyntax.uniqueIdsWithCost
                  (scope (fun _ => .unit) site.caller)).2 := by
            simp [acceptsWithFullCost, found]
          rw [fullCost]
          unfold acceptsFullCostBudget acceptsLookupBudget
          omega

def checkSitesWithFullCost : List Site → Bool × Nat
  | [] => (true, 0)
  | site :: rest =>
      let (tailAccepted, tailCost) := checkSitesWithFullCost rest
      let (siteAccepted, siteCost) := acceptsWithFullCost site
      (siteAccepted && tailAccepted, siteCost + tailCost)

theorem checkSitesWithFullCost_result (sites : List Site) :
    (checkSitesWithFullCost sites).1 = sites.all accepts := by
  induction sites with
  | nil => simp [checkSitesWithFullCost]
  | cons site rest ih =>
      simp [checkSitesWithFullCost, acceptsWithFullCost_result, ih]

theorem checkSitesWithFullCost_cost_le (sites : List Site) :
    (checkSitesWithFullCost sites).2 ≤
      sites.foldr (fun site rest => acceptsFullCostBudget site + rest) 0 := by
  induction sites with
  | nil => simp [checkSitesWithFullCost]
  | cons site rest ih =>
      have siteBound := acceptsWithFullCost_cost_le site
      simp only [checkSitesWithFullCost, List.foldr]
      omega

def checkWithFullCost (fuel : Nat) (forms : List Node) (builtins : Environment) :
    Bool × Nat :=
  match references fuel forms builtins with
  | none => (false, 0)
  | some sites => checkSitesWithFullCost sites

theorem checkWithFullCost_result (fuel : Nat) (forms : List Node)
    (builtins : Environment) :
    (checkWithFullCost fuel forms builtins).1 = check fuel forms builtins := by
  unfold checkWithFullCost check
  cases references fuel forms builtins <;>
    simp [checkSitesWithFullCost_result]

theorem checkWithFullCost_cost_le (fuel : Nat) (forms : List Node)
    (builtins : Environment) :
    (checkWithFullCost fuel forms builtins).2 ≤
      match references fuel forms builtins with
      | none => 0
      | some sites => sites.foldr (fun site rest => acceptsFullCostBudget site + rest) 0 := by
  unfold checkWithFullCost
  cases references fuel forms builtins with
  | none => simp
  | some sites => exact checkSitesWithFullCost_cost_le sites

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
