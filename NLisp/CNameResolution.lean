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

/- Source index returned by the same left-to-right scan as C `rfind`. -/
def findNameIndex : List Entry → String → Option Nat
  | [], _ => none
  | entry :: tail, name =>
      if name = entry.name then some 0 else (findNameIndex tail name).map Nat.succ

theorem findNameIndex_sound (environment : List Entry) (name : String) (index : Nat)
    (found : findNameIndex environment name = some index) :
    ∃ entry, findName environment name = some entry ∧ environment.get? index = some entry := by
  induction environment generalizing index with
  | nil => simp [findNameIndex] at found
  | cons head tail ih =>
      by_cases same : name = head.name
      · simp [findNameIndex, same] at found
        subst index
        exact ⟨head, by simp [findName, same], by simp⟩
      · cases index with
        | zero => simp [findNameIndex, same] at found
        | succ index =>
            have tailFound : findNameIndex tail name = some index := by
              simpa [findNameIndex, same] using found
            obtain ⟨entry, selected, indexed⟩ := ih index tailFound
            exact ⟨entry, by simp [findName, same, selected], by simpa using indexed⟩

theorem findNameIndex_complete (environment : List Entry) (name : String) (entry : Entry)
    (found : findName environment name = some entry) :
    ∃ index, findNameIndex environment name = some index ∧
      environment.get? index = some entry := by
  induction environment with
  | nil => simp [findName] at found
  | cons head tail ih =>
      by_cases same : name = head.name
      · simp [findName, same] at found
        subst entry
        exact ⟨0, by simp [findNameIndex, same], by simp⟩
      · have tailFound : findName tail name = some entry := by
          simpa [findName, same] using found
        obtain ⟨index, indexFound, indexedEntry⟩ := ih tailFound
        refine ⟨index + 1, ?_, ?_⟩
        · simpa [findNameIndex, same] using congrArg (Option.map Nat.succ) indexFound
        · simpa using indexedEntry

/-- C `rbind` prepends a cell and `rfind` returns the first string match.
Therefore a newly prepended binding shadows every older binding with the same
name, independent of their identities or type tags. -/
theorem findName_prepend_shadows (entry : Entry) (tail : List Entry) :
    findName (entry :: tail) entry.name = some entry := by
  simp [findName]

/-- A newly prepended binding with a different spelling leaves lookup of the
requested spelling to the older environment. -/
theorem findName_prepend_different (entry : Entry) (tail : List Entry)
    (name : String) (different : name ≠ entry.name) :
    findName (entry :: tail) name = findName tail name := by
  simp [findName, different]

/- Costed form of the same immutable-environment lookup. One unit is charged
for each entry whose name is compared, including a successful final lookup. -/
def findNameWithCost : List Entry → String → Option Entry × Nat
  | [], _ => (none, 0)
  | entry :: tail, name =>
      if name = entry.name then (some entry, 1)
      else
        let (found, cost) := findNameWithCost tail name
        (found, cost + 1)

theorem findNameWithCost_result (environment : List Entry) (name : String) :
    (findNameWithCost environment name).1 = findName environment name := by
  induction environment with
  | nil => rfl
  | cons entry tail ih =>
      by_cases equal : name = entry.name <;> simp [findNameWithCost, findName, equal, ih]

theorem findNameWithCost_le_length (environment : List Entry) (name : String) :
    (findNameWithCost environment name).2 ≤ environment.length := by
  induction environment with
  | nil => simp [findNameWithCost]
  | cons entry tail ih =>
      by_cases equal : name = entry.name
      · simp [findNameWithCost, equal]
      · simp only [findNameWithCost, if_neg equal]
        simp only [List.length_cons]
        omega

/- A conservative strcmp cost: one byte comparison per byte in either string,
plus the terminating NUL comparison. The bound deliberately ignores early
mismatches, so it is compositional over a linked-list scan. -/
def findNameWithByteCost : List Entry → String → Option Entry × Nat
  | [], _ => (none, 0)
  | entry :: tail, name =>
      let comparisonCost := name.toUTF8.data.size + entry.name.toUTF8.data.size + 1
      if name = entry.name then (some entry, comparisonCost)
      else
        let (found, cost) := findNameWithByteCost tail name
        (found, cost + comparisonCost)

theorem findNameWithByteCost_result (environment : List Entry) (name : String) :
    (findNameWithByteCost environment name).1 = findName environment name := by
  induction environment with
  | nil => rfl
  | cons entry tail ih =>
      by_cases equal : name = entry.name <;>
        simp [findNameWithByteCost, findName, equal, ih]

theorem findNameWithByteCost_le_lengths (environment : List Entry) (name : String) :
    (findNameWithByteCost environment name).2 ≤
      environment.foldr
        (fun entry rest => name.toUTF8.data.size + entry.name.toUTF8.data.size + 1 + rest) 0 := by
  induction environment with
  | nil => simp [findNameWithByteCost]
  | cons entry tail ih =>
      let comparisonCost := name.toUTF8.data.size + entry.name.toUTF8.data.size + 1
      by_cases equal : name = entry.name
      · simp [findNameWithByteCost, comparisonCost, equal, List.foldr]
        omega
      · simp only [findNameWithByteCost, if_neg equal]
        simp only [List.foldr]
        omega

/- C's runtime keeps the linked RBind environment fixed while initializer
results mutate the Value pointer stored in a selected cell. Model the cells by
identity and the mutable payload separately from name resolution. -/
abbrev CellStore (α : Type) := Nat → Option α

def writeCell {α : Type} (store : CellStore α) (identity : Nat) (value : α) : CellStore α :=
  fun queried => if queried = identity then some value else store queried

def readName {α : Type} (environment : List Entry) (store : CellStore α) (name : String) :
    Option α :=
  (findName environment name).bind (fun entry => store entry.identity)

theorem readName_after_cell_write {α : Type} (environment : List Entry)
    (store : CellStore α) (name : String) (entry : Entry) (value : α)
    (selected : findName environment name = some entry) :
    readName environment (writeCell store entry.identity value) name = some value := by
  simp [readName, selected, writeCell]

/-- Updating a different RBind cell cannot change the value selected by C's
front-to-back name search. This is the frame property for shared-cell writes. -/
theorem readName_after_other_cell_write {α : Type} (environment : List Entry)
    (store : CellStore α) (name : String) (entry : Entry)
    (writtenIdentity : Nat) (value : α)
    (selected : findName environment name = some entry)
    (different : writtenIdentity ≠ entry.identity) :
    readName environment (writeCell store writtenIdentity value) name =
      readName environment store name := by
  have selectedCell : entry.identity ≠ writtenIdentity := Ne.symm different
  simp [readName, selected, writeCell, selectedCell]

/-- Closures keep the same captured name environment when another global
initializer commits its cell; names resolved to different identities retain
their prior payload. -/
theorem captured_environment_other_cell_write
    {α : Type} (capturedEnvironment : List Entry) (store : CellStore α)
    (name : String) (entry : Entry) (writtenIdentity : Nat) (value : α)
    (selected : findName capturedEnvironment name = some entry)
    (different : writtenIdentity ≠ entry.identity) :
    readName capturedEnvironment (writeCell store writtenIdentity value) name =
      readName capturedEnvironment store name :=
  readName_after_other_cell_write capturedEnvironment store name entry
    writtenIdentity value selected different

theorem captured_environment_reads_later_cell_value
    {α : Type} (capturedEnvironment : List Entry) (store : CellStore α)
    (name : String) (entry : Entry) (value : α)
    (selected : findName capturedEnvironment name = some entry) :
    readName capturedEnvironment (writeCell store entry.identity value) name = some value :=
  readName_after_cell_write capturedEnvironment store name entry value selected

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

/- Recompute every observation lookup with an explicit byte-comparison cost.
The result is the same conjunction as `checkObservations`; the cost is in bits
(eight units per conservative UTF-8 byte comparison). -/
def checkObservationsWithCost (environment : List Entry) :
    List Observation → Bool × Nat
  | [] => (true, 0)
  | observation :: rest =>
      let (tailAccepted, tailCost) := checkObservationsWithCost environment rest
      let (found, lookupCost) := findNameWithByteCost environment observation.name
      (decide (found = some observation.selected) && tailAccepted, 8 * lookupCost + tailCost)

theorem checkObservationsWithCost_result (environment : List Entry)
    (observations : List Observation) :
    (checkObservationsWithCost environment observations).1 =
      checkObservations environment observations := by
  induction observations with
  | nil => rfl
  | cons observation rest ih =>
      simp [checkObservationsWithCost, checkObservations, findNameWithByteCost_result, ih]

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
