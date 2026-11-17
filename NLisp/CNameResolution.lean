import NLisp.ScopedSyntax

namespace NLisp.CNameResolution

/- The immutable linked environment observed at C's tfind boundary. Types
are opaque tags: the theorem holds for every interpretation of those tags. -/
structure Entry where
  name : String
  identity : Nat
  typeTag : Nat
  deriving DecidableEq, Repr

def findName : List Entry → String → Option Entry
  | [], _ => none
  | entry :: tail, name => if name = entry.name then some entry else findName tail name

inductive Resolves : List Entry → String → Entry → Prop where
  | here : name = entry.name → Resolves (entry :: tail) name entry
  | there : name ≠ other.name → Resolves tail name entry → Resolves (other :: tail) name entry

theorem findName_sound (environment : List Entry) (name : String) (entry : Entry)
    (accepted : findName environment name = some entry) : Resolves environment name entry := by
  induction environment with
  | nil => simp [findName] at accepted
  | cons head tail ih =>
      by_cases equal : name = head.name
      · simp [findName, equal] at accepted
        subst entry
        exact .here equal
      · exact .there equal (ih (by simpa [findName, equal] using accepted))

def scope (interpret : Nat → ScopedSyntax.Ty) (environment : List Entry) : ScopedSyntax.Scope :=
  environment.map (fun entry => ⟨entry.identity, interpret entry.typeTag⟩)

theorem resolves_to_scoped_variable
    (interpret : Nat → ScopedSyntax.Ty) (resolved : Resolves environment name entry) :
    ∃ reference : ScopedSyntax.Var (ScopedSyntax.types (scope interpret environment)) (interpret entry.typeTag),
      ScopedSyntax.bindingId (scope interpret environment) reference = entry.identity := by
  induction resolved with
  | here _ => exact ⟨.zero, rfl⟩
  | there _ _ ih =>
      rcases ih with ⟨reference, same⟩
      exact ⟨.succ reference, same⟩

theorem member_to_scoped_variable (environment : List Entry) (entry : Entry)
    (member : entry ∈ environment) (interpret : Nat → ScopedSyntax.Ty) :
    ∃ reference : ScopedSyntax.Var (ScopedSyntax.types (scope interpret environment)) (interpret entry.typeTag),
      ScopedSyntax.bindingId (scope interpret environment) reference = entry.identity := by
  induction environment with
  | nil => cases member
  | cons head tail ih =>
      cases List.mem_cons.mp member with
      | inl same => cases same; exact ⟨.zero, rfl⟩
      | inr later =>
          obtain ⟨reference, identity⟩ := ih later
          exact ⟨.succ reference, identity⟩

theorem checked_lookup_corresponds
    (environment : List Entry) (name : String) (entry : Entry)
    (accepted : findName environment name = some entry)
    (interpret : Nat → ScopedSyntax.Ty) :
    ∃ reference : ScopedSyntax.Var (ScopedSyntax.types (scope interpret environment)) (interpret entry.typeTag),
      ScopedSyntax.bindingId (scope interpret environment) reference = entry.identity :=
  resolves_to_scoped_variable interpret (findName_sound environment name entry accepted)

structure Observation where
  name : String
  selected : Entry
  deriving DecidableEq, Repr

def checkObservations (environment : List Entry) (observations : List Observation) : Bool :=
  observations.all (fun observation => decide (findName environment observation.name = some observation.selected))

theorem observations_correspond (environment : List Entry) (observations : List Observation)
    (accepted : checkObservations environment observations = true) :
    ∀ observation ∈ observations, ∀ interpret : Nat → ScopedSyntax.Ty,
      ∃ reference : ScopedSyntax.Var (ScopedSyntax.types (scope interpret environment))
          (interpret observation.selected.typeTag),
        ScopedSyntax.bindingId (scope interpret environment) reference = observation.selected.identity := by
  intro observation member interpret
  have all := List.all_eq_true.mp accepted
  exact checked_lookup_corresponds environment observation.name observation.selected
    (of_decide_eq_true (all observation member)) interpret

theorem shadowed_binding_not_selected
    (first second : Entry) (tail : List Entry) (_sameName : first.name = second.name)
    (different : first.identity ≠ second.identity) :
    findName (first :: second :: tail) first.name ≠ some second := by
  intro accepted
  have equal : first = second := by simpa [findName] using accepted
  exact different (congrArg Entry.identity equal)

theorem all_scope_ids (environment : List Entry) (interpret : Nat → ScopedSyntax.Ty) (p : Nat → Bool) :
  (scope interpret environment).all (fun b => p b.identity) = environment.all (fun e => p e.identity) := by
  induction environment with
  | nil => rfl
  | cons head tail ih =>
      change (p head.identity && (scope interpret tail).all (fun b => p b.identity)) = _
      rw [ih]
      rfl
 theorem scope_ids_invariant (environment : List Entry) (interpret other : Nat → ScopedSyntax.Ty) :
  ScopedSyntax.uniqueIds (scope interpret environment) = ScopedSyntax.uniqueIds (scope other environment) := by
  induction environment with
  | nil => rfl
  | cons head tail ih =>
      change ((scope interpret tail).all (fun b => head.identity != b.identity) &&
        ScopedSyntax.uniqueIds (scope interpret tail)) =
        ((scope other tail).all (fun b => head.identity != b.identity) &&
        ScopedSyntax.uniqueIds (scope other tail))
      rw [all_scope_ids, all_scope_ids, ih]

end NLisp.CNameResolution
