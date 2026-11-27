import NLisp.PolymorphicSafety
import NLisp.TypedExpansion
import NLisp.NamedDecoder

namespace NLisp.GlobalIR
open PolyIR

/- A global read is represented by a zero-argument getter in the function
table. The current store is passed to evaluation, so a closure created during
initialization never freezes a missing global value in its local environment.
User functions still have one shared, erased body and their original arity. -/
inductive Definition where
  | function : RuntimeDefinition → Definition
  | getter : Nat → Definition

/- Source functions occupy the prefix of the combined GlobalIR table. This
constructor produces the runtime-index/source-definition-index relation for
that prefix; global value getters are appended after it. -/
def functionSourcesFor : Nat → List (Nat × Nat)
  | 0 => []
  | count + 1 => (count, count) :: functionSourcesFor count

theorem mem_functionSourcesFor_iff (functionCount runtimeIndex sourceIndex : Nat) :
    (runtimeIndex, sourceIndex) ∈ functionSourcesFor functionCount ↔
      runtimeIndex = sourceIndex ∧ sourceIndex < functionCount := by
  induction functionCount with
  | zero => simp [functionSourcesFor]
  | succ count ih =>
      simp only [functionSourcesFor, List.mem_cons]
      constructor
      · rintro (last | old)
        · rcases Prod.mk.inj last with ⟨rfl, rfl⟩
          exact ⟨rfl, by omega⟩
        · rcases ih.mp old with ⟨same, oldBound⟩
          exact ⟨same, by omega⟩
      · rintro ⟨same, bound⟩
        subst runtimeIndex
        by_cases atLast : sourceIndex = count
        · subst sourceIndex
          exact Or.inl rfl
        · exact Or.inr (ih.mpr ⟨rfl, by omega⟩)

/- GlobalIR indexes getters and functions in one definition table. This map
records the getter definition index for each source global-value definition
index; function indices are absent from the map. -/
def getterFor : List (Nat × Nat) → Nat → Option Nat
  | [], _ => none
  | (source, getter) :: rest, index =>
      if source = index then some getter else getterFor rest index

/- Global value references use the same combined index as their appended
getter. The slot offset is kept explicit so the map can be built directly
from the number of function definitions and the slot-type layout. -/
def getterMappingsFrom (firstIndex : Nat) : List Surface.Ty → List (Nat × Nat)
  | [] => []
  | _ :: types => (firstIndex, firstIndex) :: getterMappingsFrom (firstIndex + 1) types

def getterMappings (functionCount : Nat) (slotTypes : List Surface.Ty) :
    List (Nat × Nat) :=
  getterMappingsFrom functionCount slotTypes

private theorem getElem?_some_lt_length {α : Type} (items : List α)
    (index : Nat) (item : α) (found : items[index]? = some item) :
    index < items.length := by
  simp only [getElem?_def] at found
  split at found
  · assumption
  · contradiction

private theorem getElem?_eq_get? {α : Type u} (items : List α) (index : Nat) :
    items[index]? = items.get? index := by
  by_cases h : index < items.length
  · simp only [getElem?_def, dif_pos h]
    exact (List.get?_eq_some).2 ⟨h, rfl⟩ |>.symm
  · have hle : items.length ≤ index := Nat.le_of_not_gt h
    simp only [getElem?_def, dif_neg h]
    exact (List.get?_eq_none).2 hle |>.symm

@[simp] private theorem getElem?_cons_succ {α : Type} (head : α) (tail : List α)
    (index : Nat) : (head :: tail)[index + 1]? = tail[index]? := by
  by_cases h : index < tail.length
  · have h' : index + 1 < (head :: tail).length := by
      simpa only [Nat.add_one, List.length_cons] using Nat.succ_lt_succ h
    simp only [getElem?_def]
    rw [dif_pos h', dif_pos h]
    rfl
  · have h' : ¬ index + 1 < (head :: tail).length := by
      intro hyp
      have : index < tail.length := by
        have h'' : Nat.succ index < Nat.succ tail.length := by
          simpa only [Nat.add_one, List.length_cons] using hyp
        exact Nat.succ_lt_succ_iff.mp h''
      exact h this
    simp only [getElem?_def]
    rw [dif_neg h', dif_neg h]

@[simp] private theorem getElem?_cons_zero {α : Type} (head : α) (tail : List α) :
    (head :: tail)[0]? = some head := by
  rw [getElem?_def, dif_pos (by simp)]
  rfl

theorem getElem?_map {α β : Type} (f : α → β) (items : List α)
    (index : Nat) : (items.map f)[index]? = (items[index]?).map f := by
  calc
    (items.map f)[index]? = (items.map f).get? index := getElem?_eq_get? _ _
    _ = (items.get? index).map f := List.get?_map f items index
    _ = (items[index]?).map f := by rw [getElem?_eq_get?]

theorem getterFor_getterMappingsFrom (firstIndex index : Nat) (types : List Surface.Ty)
    (bound : index < types.length) :
    getterFor (getterMappingsFrom firstIndex types) (firstIndex + index) =
      some (firstIndex + index) := by
  induction types generalizing firstIndex index with
  | nil => exact False.elim (Nat.not_lt_zero _ bound)
  | cons type tail ih =>
      cases index with
      | zero => simp [getterMappingsFrom, getterFor]
      | succ index =>
          have tailBound : index < tail.length := by
            simpa only [Nat.add_one, List.length_cons, Nat.succ_lt_succ_iff] using bound
          have different : firstIndex ≠ firstIndex + Nat.succ index := by omega
          have tailMapped := ih (firstIndex + 1) index tailBound
          have slotEq : firstIndex + Nat.succ index = firstIndex + 1 + index := by omega
          simp only [getterMappingsFrom, getterFor, if_neg different]
          rw [show firstIndex + Nat.succ index = (firstIndex + 1) + index by omega]
          exact tailMapped

theorem getterFor_getterMappings (functionCount index : Nat)
    (slotTypes : List Surface.Ty) (bound : index < slotTypes.length) :
    getterFor (getterMappings functionCount slotTypes) (functionCount + index) =
      some (functionCount + index) :=
  getterFor_getterMappingsFrom functionCount index slotTypes bound

mutual
def lowerGlobalReads (getters : List (Nat × Nat)) (term : Term) : Term :=
  match term with
  | .var index => .var index
  | .global index => match getterFor getters index with
      | some getter => .app (.global getter) []
      | none => .global index
  | .bool value => .bool value
  | .int value => .int value
  | .float value => .float value
  | .string value => .string value
  | .character value => .character value
  | .unit => .unit
  | .lam arity body => .lam arity (lowerGlobalReads getters body)
  | .app (.global index) arguments =>
      let arguments' := lowerGlobalReadsMany getters arguments
      match getterFor getters index with
      | some getter =>
          -- The source's nullary header application is the cell read itself.
          -- If the loaded value is applied here, read it before applying args.
          if arguments.isEmpty then .app (.global getter) []
          else .app (.app (.global getter) []) arguments'
      | none => .app (.global index) arguments'
  | .app function arguments =>
      .app (lowerGlobalReads getters function) (lowerGlobalReadsMany getters arguments)
  | .ite condition yes no =>
      .ite (lowerGlobalReads getters condition) (lowerGlobalReads getters yes)
        (lowerGlobalReads getters no)
  | .add left right => .add (lowerGlobalReads getters left) (lowerGlobalReads getters right)
  | .sub left right => .sub (lowerGlobalReads getters left) (lowerGlobalReads getters right)
  | .mul left right => .mul (lowerGlobalReads getters left) (lowerGlobalReads getters right)
  | .le left right => .le (lowerGlobalReads getters left) (lowerGlobalReads getters right)
  | .intEq left right => .intEq (lowerGlobalReads getters left) (lowerGlobalReads getters right)
  | .letMany values body =>
      .letMany (lowerGlobalReadsMany getters values) (lowerGlobalReads getters body)
  | .begin first rest =>
      .begin (lowerGlobalReads getters first) (lowerGlobalReadsMany getters rest)
  | .nil => .nil
  | .cons head tail => .cons (lowerGlobalReads getters head) (lowerGlobalReads getters tail)
  | .none => .none
  | .some value => .some (lowerGlobalReads getters value)
  | .matchList target empty full =>
      .matchList (lowerGlobalReads getters target) (lowerGlobalReads getters empty)
        (lowerGlobalReads getters full)
  | .matchOption target empty full =>
      .matchOption (lowerGlobalReads getters target) (lowerGlobalReads getters empty)
        (lowerGlobalReads getters full)
  | .floatBin op left right => .floatBin op
      (lowerGlobalReads getters left) (lowerGlobalReads getters right)
termination_by sizeOf term
decreasing_by all_goals simp_wf; omega

def lowerGlobalReadsMany (getters : List (Nat × Nat)) (terms : List Term) : List Term :=
  match terms with
  | [] => []
  | term :: rest => lowerGlobalReads getters term :: lowerGlobalReadsMany getters rest
termination_by sizeOf terms
decreasing_by all_goals simp_wf; omega
end

theorem lowerGlobalReads_global_getter (getters : List (Nat × Nat)) (index getter : Nat)
    (mapped : getterFor getters index = some getter) :
    lowerGlobalReads getters (.global index) = .app (.global getter) [] := by
  simp [lowerGlobalReads, mapped]

theorem lowerGlobalReads_global_value_getter (functionCount index : Nat)
    (slotTypes : List Surface.Ty) (bound : index < slotTypes.length) :
    lowerGlobalReads (getterMappings functionCount slotTypes)
        (.global (functionCount + index)) =
      .app (.global (functionCount + index)) [] := by
  apply lowerGlobalReads_global_getter
  exact getterFor_getterMappings functionCount index slotTypes bound

theorem lowerGlobalReads_zero_arg_value_getter (getters : List (Nat × Nat))
    (index getter : Nat) (mapped : getterFor getters index = some getter) :
    lowerGlobalReads getters (.app (.global index) []) = .app (.global getter) [] := by
  simp [lowerGlobalReads, mapped, List.isEmpty]

theorem lowerGlobalReads_zero_arg_mapped_value (functionCount index : Nat)
    (slotTypes : List Surface.Ty) (bound : index < slotTypes.length) :
    lowerGlobalReads (getterMappings functionCount slotTypes)
        (.app (.global (functionCount + index)) []) =
      .app (.global (functionCount + index)) [] := by
  exact lowerGlobalReads_zero_arg_value_getter _ _ _
    (getterFor_getterMappings functionCount index slotTypes bound)

theorem lowerGlobalReads_surface_value_reference (getters : List (Nat × Nat))
    (index getter : Nat) (mapped : getterFor getters index = some getter) :
    lowerGlobalReads getters (PolyIR.erase (Surface.Expr.app (.global index []) [])) =
      .app (.global getter) [] := by
  change lowerGlobalReads getters (.app (.global index) []) = .app (.global getter) []
  exact lowerGlobalReads_zero_arg_value_getter getters index getter mapped

theorem lowerGlobalReads_nonempty_value_application (getters : List (Nat × Nat))
    (index getter : Nat) (arguments : List Term)
    (mapped : getterFor getters index = some getter) (nonempty : arguments ≠ []) :
    lowerGlobalReads getters (.app (.global index) arguments) =
      .app (.app (.global getter) []) (lowerGlobalReadsMany getters arguments) := by
  cases arguments with
  | nil => exact False.elim (nonempty rfl)
  | cons head tail => simp [lowerGlobalReads, mapped, List.isEmpty]

/- Relate the combined runtime table to its source signatures and storage
layout. Function bodies are erased and then rewritten so global value reads
call the appended getters. -/
structure GlobalProgramTyped (globals : List Surface.Signature)
    (definitions : Surface.Definitions) (slotTypes : List Surface.Ty)
    (functionSources : List (Nat × Nat))
    (program : List Definition) : Prop where
  global_entry : ∀ (index : Nat) (signature : Surface.Signature),
    globals[index]? = some signature →
      (∃ sourceIndex body, (index, sourceIndex) ∈ functionSources ∧
        definitions[sourceIndex]? = some (signature, body) ∧
        signature.wellFormed ∧
        Surface.HasType globals signature.typeArity signature.parameters body signature.result ∧
        program[index]? = some (.function
          ⟨signature.parameters.length,
            lowerGlobalReads (getterMappings definitions.length slotTypes)
              (PolyIR.erase body)⟩)) ∨
      (∃ slot type, program[index]? = some (.getter slot) ∧
        signature = ⟨0, [], type⟩ ∧ type.wellFormed 0 ∧ slotTypes[slot]? = some type)
  getter_entry : ∀ (index slot : Nat), program[index]? = some (.getter slot) →
    ∃ type, globals[index]? = some ⟨0, [], type⟩ ∧ type.wellFormed 0 ∧
      slotTypes[slot]? = some type
  function_entry : ∀ (index : Nat) (runtime : RuntimeDefinition),
    program[index]? = some (.function runtime) →
      ∃ sourceIndex signature body, (index, sourceIndex) ∈ functionSources ∧
        globals[index]? = some signature ∧
        definitions[sourceIndex]? = some (signature, body) ∧ signature.wellFormed ∧
        Surface.HasType globals signature.typeArity signature.parameters body signature.result ∧
        runtime = ⟨signature.parameters.length,
          lowerGlobalReads (getterMappings definitions.length slotTypes)
            (PolyIR.erase body)⟩

theorem function_layout_typed (globals : List Surface.Signature)
    (definitions : Surface.Definitions) (slotTypes : List Surface.Ty)
    (functionSources : List (Nat × Nat)) (program : List Definition)
    (typed : GlobalProgramTyped globals definitions slotTypes functionSources program)
    (index : Nat) (runtime : RuntimeDefinition)
    (entry : program[index]? = some (.function runtime)) :
    ∃ sourceIndex signature body, (index, sourceIndex) ∈ functionSources ∧
      globals[index]? = some signature ∧
      definitions[sourceIndex]? = some (signature, body) ∧ signature.wellFormed ∧
      Surface.HasType globals signature.typeArity signature.parameters body signature.result ∧
      runtime = ⟨signature.parameters.length,
        lowerGlobalReads (getterMappings definitions.length slotTypes)
          (PolyIR.erase body)⟩ :=
  typed.function_entry index runtime entry

theorem getter_layout_typed (globals : List Surface.Signature)
    (definitions : Surface.Definitions) (slotTypes : List Surface.Ty)
    (functionSources : List (Nat × Nat)) (program : List Definition)
    (typed : GlobalProgramTyped globals definitions slotTypes functionSources program)
    (index slot : Nat) (entry : program[index]? = some (.getter slot)) :
    ∃ type, globals[index]? = some ⟨0, [], type⟩ ∧ type.wellFormed 0 ∧
      slotTypes[slot]? = some type :=
  typed.getter_entry index slot entry

def functionEntries (definitions : Surface.Definitions) (slotTypes : List Surface.Ty) :
    List Definition :=
  definitions.map (fun definition =>
    .function ⟨definition.1.parameters.length,
      lowerGlobalReads (getterMappings definitions.length slotTypes)
        (PolyIR.erase definition.2)⟩)

def getterEntriesFrom (firstSlot : Nat) : List Surface.Ty → List Definition
  | [] => []
  | _ :: types => .getter firstSlot :: getterEntriesFrom (firstSlot + 1) types

def getterEntries (slotTypes : List Surface.Ty) : List Definition :=
  getterEntriesFrom 0 slotTypes

@[simp] theorem getterEntriesFrom_length (firstSlot : Nat) (slotTypes : List Surface.Ty) :
    (getterEntriesFrom firstSlot slotTypes).length = slotTypes.length := by
  induction slotTypes generalizing firstSlot with
  | nil => rfl
  | cons type tail ih => simp [getterEntriesFrom, ih]

def assembleProgram (definitions : Surface.Definitions) (slotTypes : List Surface.Ty) :
    List Definition :=
  functionEntries definitions slotTypes ++ getterEntries slotTypes

/- Assemble directly from the identity-resolved source decoder. The decoded
function indices remain a prefix; all value-global references are rewritten
to calls of the getters appended after that prefix. -/
noncomputable def namedFunctionEntries (functions : Named.Definitions) (slotTypes : List Surface.Ty) :
    List Definition :=
  (Named.lowerDefinitions functions).map (fun runtime =>
    .function ⟨runtime.arity,
      lowerGlobalReads (getterMappings functions.length slotTypes) runtime.body⟩)

@[simp] theorem namedFunctionEntries_length (functions : Named.Definitions)
    (slotTypes : List Surface.Ty) :
    (namedFunctionEntries functions slotTypes).length = functions.length := by
  simp [namedFunctionEntries, Named.lowerDefinitions]

noncomputable def assembleNamedProgram (functions : Named.Definitions) (slotTypes : List Surface.Ty) :
    List Definition :=
  namedFunctionEntries functions slotTypes ++ getterEntries slotTypes

@[simp] theorem assembleNamedProgram_length (functions : Named.Definitions)
    (slotTypes : List Surface.Ty) :
    (assembleNamedProgram functions slotTypes).length = functions.length + slotTypes.length := by
  simp [assembleNamedProgram, getterEntries]

noncomputable def lowerNamedInitializers (functions : Named.Definitions) (slotTypes : List Surface.Ty)
    (initializers : List Named.Expr) : List Term :=
  initializers.map (fun initializer =>
    lowerGlobalReads (getterMappings functions.length slotTypes)
      (Named.lower [] initializer))

@[simp] theorem lowerNamedInitializers_length (functions : Named.Definitions)
    (slotTypes : List Surface.Ty) (initializers : List Named.Expr) :
    (lowerNamedInitializers functions slotTypes initializers).length = initializers.length := by
  simp [lowerNamedInitializers]

@[simp] theorem assembleProgram_length (definitions : Surface.Definitions)
    (slotTypes : List Surface.Ty) :
    (assembleProgram definitions slotTypes).length = definitions.length + slotTypes.length := by
  simp [assembleProgram, functionEntries, getterEntries]

@[simp] theorem functionEntries_length (definitions : Surface.Definitions)
    (slotTypes : List Surface.Ty) :
    (functionEntries definitions slotTypes).length = definitions.length := by
  simp [functionEntries]

theorem getterEntriesFrom_lookup (firstSlot index : Nat) (types : List Surface.Ty)
    (bound : index < types.length) :
    (getterEntriesFrom firstSlot types)[index]? = some (.getter (firstSlot + index)) := by
  rw [getElem?_eq_get?]
  induction types generalizing firstSlot index with
  | nil => exact False.elim (Nat.not_lt_zero _ bound)
  | cons type tail ih =>
      cases index with
      | zero => simp [getterEntriesFrom]
      | succ index =>
          have tailBound : index < tail.length := by
            simpa only [Nat.add_one, List.length_cons, Nat.succ_lt_succ_iff] using bound
          simp only [getterEntriesFrom, List.get?_cons_succ]
          rw [show firstSlot + (index + 1) = firstSlot + 1 + index by omega]
          exact ih (firstSlot + 1) index tailBound

theorem getterEntriesFrom_entry (firstSlot index slot : Nat) (types : List Surface.Ty)
    (entry : (getterEntriesFrom firstSlot types)[index]? = some (.getter slot)) :
    index < types.length ∧ slot = firstSlot + index := by
  rw [getElem?_eq_get?] at entry
  induction types generalizing firstSlot index slot with
  | nil =>
      have impossible : (getterEntriesFrom firstSlot ([] : List Surface.Ty)).get? index =
          some (.getter slot) := by simpa [getterEntriesFrom] using entry
      simp [getterEntriesFrom] at impossible
  | cons type tail ih =>
      cases index with
      | zero =>
          simp [getterEntriesFrom] at entry
          cases entry
          exact ⟨by simp, by omega⟩
      | succ index =>
          simp only [getterEntriesFrom, List.get?_cons_succ] at entry
          have tailEntry :
              (getterEntriesFrom (firstSlot + 1) tail).get? index = some (.getter slot) := entry
          obtain ⟨tailBound, slotEq⟩ := ih (firstSlot + 1) index slot tailEntry
          have indexEq : firstSlot + Nat.succ index = firstSlot + 1 + index := by omega
          exact ⟨Nat.succ_lt_succ tailBound, slotEq.trans indexEq.symm⟩

theorem append_lookup_right (left right : List α) (index : Nat) :
    (left ++ right)[left.length + index]? = right[index]? := by
  calc
    (left ++ right)[left.length + index]? = (left ++ right).get? (left.length + index) :=
      getElem?_eq_get? (left ++ right) (left.length + index)
    _ = right.get? index := by
      have hle : left.length ≤ left.length + index := Nat.le_add_right _ _
      rw [List.get?_append_right hle]
      congr 1
      omega
    _ = right[index]? := (@getElem?_eq_get? α right index).symm

theorem append_lookup_left (left right : List α) (index : Nat)
    (bound : index < left.length) :
    (left ++ right)[index]? = left[index]? := by
  calc
    (left ++ right)[index]? = (left ++ right).get? index :=
      getElem?_eq_get? (left ++ right) index
    _ = left.get? index := List.get?_append bound
    _ = left[index]? := (@getElem?_eq_get? α left index).symm

theorem lookup_some_lt {α : Type} (values : List α) (index : Nat) (value : α)
    (entry : values[index]? = some value) : index < values.length := by
  exact getElem?_some_lt_length values index value entry

theorem lookup_exists_of_lt {α : Type} (values : List α) (index : Nat)
    (bound : index < values.length) : ∃ value, values[index]? = some value := by
  induction values generalizing index with
  | nil => exact False.elim (Nat.not_lt_zero _ bound)
  | cons head tail ih =>
      cases index with
      | zero => exact ⟨head, by simp [getElem?_def]⟩
      | succ index =>
          have tailBound : index < tail.length := by
            simpa only [Nat.add_one, List.length_cons, Nat.succ_lt_succ_iff] using bound
          obtain ⟨value, entry⟩ := ih index tailBound
          exact ⟨value, by simpa using entry⟩

theorem assembleProgram_getter_lookup (definitions : Surface.Definitions)
    (slotTypes : List Surface.Ty) (slot : Nat) (bound : slot < slotTypes.length) :
    (assembleProgram definitions slotTypes)[definitions.length + slot]? =
      some (.getter slot) := by
  have lookup := append_lookup_right (functionEntries definitions slotTypes)
    (getterEntries slotTypes) slot
  have getter := getterEntriesFrom_lookup 0 slot slotTypes bound
  simpa [assembleProgram, functionEntries_length, getterEntries] using lookup.trans getter

theorem assembleNamedProgram_getter_lookup (functions : Named.Definitions)
    (slotTypes : List Surface.Ty) (slot : Nat) (bound : slot < slotTypes.length) :
    (assembleNamedProgram functions slotTypes)[functions.length + slot]? =
      some (.getter slot) := by
  have lookup := append_lookup_right (namedFunctionEntries functions slotTypes)
    (getterEntries slotTypes) slot
  have getter := getterEntriesFrom_lookup 0 slot slotTypes bound
  simpa [assembleNamedProgram, namedFunctionEntries_length, getterEntries] using
    lookup.trans getter

theorem functionEntries_lookup (definitions : Surface.Definitions)
    (slotTypes : List Surface.Ty) (index : Nat) :
    (functionEntries definitions slotTypes)[index]? =
      (definitions[index]?).map (fun definition =>
        .function ⟨definition.1.parameters.length,
          lowerGlobalReads (getterMappings definitions.length slotTypes)
            (PolyIR.erase definition.2)⟩) := by
  simp [functionEntries, getElem?_map]

theorem assembleProgram_function_lookup (definitions : Surface.Definitions)
    (slotTypes : List Surface.Ty) (index : Nat) (bound : index < definitions.length) :
    (assembleProgram definitions slotTypes)[index]? =
      (definitions[index]?).map (fun definition =>
        .function ⟨definition.1.parameters.length,
          lowerGlobalReads (getterMappings definitions.length slotTypes)
            (PolyIR.erase definition.2)⟩) := by
  have lookup := append_lookup_left (functionEntries definitions slotTypes)
    (getterEntries slotTypes) index (by simpa using bound)
  simpa [assembleProgram, functionEntries_lookup] using lookup

theorem assembled_function_source_layout (definitions : Surface.Definitions)
    (slotTypes : List Surface.Ty) (index : Nat) (signature : Surface.Signature)
    (body : Surface.Expr) (bound : index < definitions.length)
    (entry : definitions[index]? = some (signature, body)) :
    (index, index) ∈ functionSourcesFor definitions.length ∧
    (assembleProgram definitions slotTypes)[index]? =
      some (.function ⟨signature.parameters.length,
        lowerGlobalReads (getterMappings definitions.length slotTypes) (PolyIR.erase body)⟩) := by
  have sourceMember := (mem_functionSourcesFor_iff definitions.length index index).mpr
    ⟨rfl, bound⟩
  have runtimeEntry := assembleProgram_function_lookup definitions slotTypes index bound
  exact ⟨sourceMember, by simpa [entry] using runtimeEntry⟩

def getterSignaturesFrom : List Surface.Ty → List Surface.Signature
  := fun types => types.map (fun type => ⟨0, [], type⟩)

def getterSignatures (slotTypes : List Surface.Ty) : List Surface.Signature :=
  getterSignaturesFrom slotTypes

@[simp] theorem getterSignaturesFrom_length (slotTypes : List Surface.Ty) :
    (getterSignaturesFrom slotTypes).length = slotTypes.length := by
  induction slotTypes with
  | nil => rfl
  | cons type tail ih => simp [getterSignaturesFrom, ih]

def assembleGlobals (definitions : Surface.Definitions) (slotTypes : List Surface.Ty) :
    List Surface.Signature :=
  definitions.map Prod.fst ++ getterSignatures slotTypes

theorem map_fst_zip_eq_left {α β : Type} (left : List α) (right : List β)
    (sameLength : left.length = right.length) :
    (left.zip right).map Prod.fst = left := by
  induction left generalizing right with
  | nil => simp
  | cons head tail ih =>
      cases right with
      | nil => simp at sameLength
      | cons other rest =>
          simp only [List.zip_cons_cons, List.map_cons]
          congr 1
          apply ih
          simp at sameLength
          omega

theorem sourceSignatures_lookup (definitions : Surface.Definitions) (index : Nat) :
    (definitions.map Prod.fst)[index]? = (definitions[index]?).map Prod.fst := by
  rw [getElem?_map]

theorem assembleGlobals_function_lookup (definitions : Surface.Definitions)
    (slotTypes : List Surface.Ty) (index : Nat) (bound : index < definitions.length) :
    (assembleGlobals definitions slotTypes)[index]? =
      (definitions[index]?).map Prod.fst := by
  have functionLength : (definitions.map Prod.fst).length = definitions.length := by simp
  have lookup := append_lookup_left (definitions.map Prod.fst)
    (getterSignatures slotTypes) index (by simpa [functionLength] using bound)
  simpa [assembleGlobals, sourceSignatures_lookup] using lookup

@[simp] theorem assembleGlobals_length (definitions : Surface.Definitions)
    (slotTypes : List Surface.Ty) :
    (assembleGlobals definitions slotTypes).length = definitions.length + slotTypes.length := by
  simp [assembleGlobals, getterSignatures]

theorem getterSignaturesFrom_lookup (index : Nat) (types : List Surface.Ty) :
    (getterSignaturesFrom types)[index]? =
      (types[index]?).map (fun type => (⟨0, [], type⟩ : Surface.Signature)) := by
  simp [getterSignaturesFrom, getElem?_map]

theorem assembleGlobals_getter_lookup (definitions : Surface.Definitions)
    (slotTypes : List Surface.Ty) (slot : Nat) :
    (assembleGlobals definitions slotTypes)[definitions.length + slot]? =
      (slotTypes[slot]?).map (fun type => (⟨0, [], type⟩ : Surface.Signature)) := by
  have lookup := append_lookup_right (definitions.map Prod.fst)
    (getterSignatures slotTypes) slot
  have slotLookup := getterSignaturesFrom_lookup slot slotTypes
  have functionLength : (definitions.map Prod.fst).length = definitions.length := by simp
  rw [assembleGlobals]
  rw [functionLength] at lookup
  simpa [getterSignatures] using lookup.trans slotLookup

theorem assembled_getter_layout (definitions : Surface.Definitions)
    (slotTypes : List Surface.Ty) (slot : Nat) (type : Surface.Ty)
    (slotEntry : slotTypes[slot]? = some type) :
    (assembleGlobals definitions slotTypes)[definitions.length + slot]? =
      some ⟨0, [], type⟩ ∧
    (assembleProgram definitions slotTypes)[definitions.length + slot]? =
      some (.getter slot) := by
  have signatureEntry := assembleGlobals_getter_lookup definitions slotTypes slot
  have slotBound := getElem?_some_lt_length slotTypes slot type slotEntry
  have runtimeEntry := assembleProgram_getter_lookup definitions slotTypes slot slotBound
  exact ⟨by simpa [slotEntry] using signatureEntry, runtimeEntry⟩

structure AssembledSourceTyped (definitions : Surface.Definitions)
    (slotTypes : List Surface.Ty) : Prop where
  function_typed : ∀ (index : Nat) (signature : Surface.Signature) (body : Surface.Expr),
    definitions[index]? = some (signature, body) →
      signature.wellFormed ∧
        Surface.HasType (assembleGlobals definitions slotTypes) signature.typeArity
          signature.parameters body signature.result
  slot_wellFormed : ∀ (slot : Nat) (type : Surface.Ty),
    slotTypes[slot]? = some type → type.wellFormed 0

/- A successful independent elaboration against the assembled function and
getter signatures supplies the function half of the GlobalIR layout proof.
Value initializer typing remains a separate obligation because those
expressions are evaluated against the evolving store. -/
theorem assembledSourceTyped_of_elaborated (fuel : Nat)
    (signatures : List Surface.Signature) (bodies : List Surface.Expr)
    (slotTypes : List Surface.Ty)
    (checked : (Surface.elaborateDefinitions fuel
      (assembleGlobals (signatures.zip bodies) slotTypes) signatures bodies).isSome = true)
    (slotTyped : ∀ (slot : Nat) (type : Surface.Ty),
      slotTypes[slot]? = some type → type.wellFormed 0) :
    AssembledSourceTyped (signatures.zip bodies) slotTypes := by
  refine ⟨?_, slotTyped⟩
  intro index signature body sourceEntry
  exact (Surface.elaborateDefinitions_typed (fuel := fuel)
    (globals := assembleGlobals (signatures.zip bodies) slotTypes)
    (signatures := signatures) (bodies := bodies) checked).lookupDefinition sourceEntry

theorem assembleProgram_typed (definitions : Surface.Definitions)
    (slotTypes : List Surface.Ty)
    (sourceTyped : AssembledSourceTyped definitions slotTypes) :
    GlobalProgramTyped (assembleGlobals definitions slotTypes) definitions slotTypes
      (functionSourcesFor definitions.length) (assembleProgram definitions slotTypes) := by
  constructor
  · intro index signature signatureEntry
    have indexBound := lookup_some_lt (assembleGlobals definitions slotTypes) index signature
      signatureEntry
    rw [assembleGlobals_length] at indexBound
    by_cases functionIndex : index < definitions.length
    · obtain ⟨sourceDefinition, sourceEntry⟩ :=
        lookup_exists_of_lt definitions index functionIndex
      rcases sourceDefinition with ⟨sourceSignature, body⟩
      have signatureLayout := assembleGlobals_function_lookup definitions slotTypes index functionIndex
      rw [sourceEntry] at signatureLayout
      have sameSignature : sourceSignature = signature := by
        rw [signatureLayout] at signatureEntry
        simp at signatureEntry
        exact signatureEntry
      subst signature
      obtain ⟨signatureWellFormed, bodyTyped⟩ :=
        sourceTyped.function_typed index sourceSignature body sourceEntry
      have runtimeLayout := assembleProgram_function_lookup definitions slotTypes index functionIndex
      rw [sourceEntry] at runtimeLayout
      have runtimeEntry :
          (assembleProgram definitions slotTypes)[index]? = some (.function
            ⟨sourceSignature.parameters.length,
              lowerGlobalReads (getterMappings definitions.length slotTypes)
                (PolyIR.erase body)⟩) := by
        simpa using runtimeLayout
      left
      refine ⟨index, body, ?_, sourceEntry, signatureWellFormed, bodyTyped, runtimeEntry⟩
      exact (mem_functionSourcesFor_iff definitions.length index index).mpr
        ⟨rfl, functionIndex⟩
    · let slot := index - definitions.length
      have indexEq : index = definitions.length + slot := by
        dsimp [slot]
        omega
      have slotBound : slot < slotTypes.length := by omega
      obtain ⟨type, slotEntry⟩ := lookup_exists_of_lt slotTypes slot slotBound
      have signatureLayout := assembleGlobals_getter_lookup definitions slotTypes slot
      rw [indexEq] at signatureEntry
      rw [signatureLayout, slotEntry] at signatureEntry
      have sameSignature : signature = ⟨0, [], type⟩ :=
        (Option.some.inj signatureEntry).symm
      have typeWellFormed := sourceTyped.slot_wellFormed slot type slotEntry
      have runtimeEntry := assembleProgram_getter_lookup definitions slotTypes slot slotBound
      right
      exact ⟨slot, type, by simpa [indexEq] using runtimeEntry, sameSignature,
        typeWellFormed, slotEntry⟩
  · intro index slot runtimeEntry
    have indexBound := lookup_some_lt (assembleProgram definitions slotTypes) index
      (.getter slot) runtimeEntry
    rw [assembleProgram_length] at indexBound
    by_cases functionIndex : index < definitions.length
    · have functionEntry := assembleProgram_function_lookup definitions slotTypes index functionIndex
      rw [functionEntry] at runtimeEntry
      cases sourceEntry : definitions[index]? with
      | none => simp [sourceEntry] at runtimeEntry
      | some definition => simp [sourceEntry] at runtimeEntry
    · let slotIndex := index - definitions.length
      have indexEq : index = definitions.length + slotIndex := by
        dsimp [slotIndex]
        omega
      have slotBound : slotIndex < slotTypes.length := by omega
      have getterEntry := assembleProgram_getter_lookup definitions slotTypes slotIndex slotBound
      rw [indexEq, getterEntry] at runtimeEntry
      have definitionsEq := Option.some.inj runtimeEntry
      have slotEq : slotIndex = slot := by
        exact Definition.getter.inj definitionsEq
      subst slot
      obtain ⟨type, slotEntry⟩ := lookup_exists_of_lt slotTypes slotIndex slotBound
      refine ⟨type, ?_, sourceTyped.slot_wellFormed slotIndex type slotEntry, slotEntry⟩
      rw [indexEq, assembleGlobals_getter_lookup, slotEntry]
      simp
  · intro index runtime runtimeEntry
    have indexBound := lookup_some_lt (assembleProgram definitions slotTypes) index
      (.function runtime) runtimeEntry
    rw [assembleProgram_length] at indexBound
    by_cases functionIndex : index < definitions.length
    · obtain ⟨sourceDefinition, sourceEntry⟩ :=
        lookup_exists_of_lt definitions index functionIndex
      rcases sourceDefinition with ⟨signature, body⟩
      have layout := assembleProgram_function_lookup definitions slotTypes index functionIndex
      rw [sourceEntry] at layout
      have runtimeEq : runtime = ⟨signature.parameters.length,
          lowerGlobalReads (getterMappings definitions.length slotTypes)
            (PolyIR.erase body)⟩ := by
        rw [layout] at runtimeEntry
        have definitionEq := Option.some.inj runtimeEntry
        injection definitionEq with runtimeSame
        exact runtimeSame.symm
      have globalsEntry := assembleGlobals_function_lookup definitions slotTypes index functionIndex
      rw [sourceEntry] at globalsEntry
      obtain ⟨signatureWellFormed, bodyTyped⟩ :=
        sourceTyped.function_typed index signature body sourceEntry
      exact ⟨index, signature, body,
        (mem_functionSourcesFor_iff definitions.length index index).mpr ⟨rfl, functionIndex⟩,
        globalsEntry, sourceEntry, signatureWellFormed, bodyTyped, runtimeEq⟩
    · let slot := index - definitions.length
      have indexEq : index = definitions.length + slot := by
        dsimp [slot]
        omega
      have slotBound : slot < slotTypes.length := by omega
      have getterEntry := assembleProgram_getter_lookup definitions slotTypes slot slotBound
      rw [indexEq, getterEntry] at runtimeEntry
      simp at runtimeEntry

theorem assembleProgram_typed_of_elaborated (fuel : Nat)
    (signatures : List Surface.Signature) (bodies : List Surface.Expr)
    (slotTypes : List Surface.Ty)
    (checked : (Surface.elaborateDefinitions fuel
      (assembleGlobals (signatures.zip bodies) slotTypes) signatures bodies).isSome = true)
    (slotTyped : ∀ (slot : Nat) (type : Surface.Ty),
      slotTypes[slot]? = some type → type.wellFormed 0) :
    GlobalProgramTyped (assembleGlobals (signatures.zip bodies) slotTypes)
      (signatures.zip bodies) slotTypes
      (functionSourcesFor (signatures.zip bodies).length)
      (assembleProgram (signatures.zip bodies) slotTypes) :=
  by
    exact assembleProgram_typed (signatures.zip bodies) slotTypes
      (assembledSourceTyped_of_elaborated fuel signatures bodies slotTypes checked slotTyped)

theorem assembled_global_value_read_layout (definitions : Surface.Definitions)
    (slotTypes : List Surface.Ty) (slot : Nat) (bound : slot < slotTypes.length) :
    lowerGlobalReads (getterMappings definitions.length slotTypes)
        (.global (definitions.length + slot)) =
      .app (.global (definitions.length + slot)) [] ∧
    (assembleProgram definitions slotTypes)[definitions.length + slot]? =
      some (.getter slot) := by
  exact ⟨lowerGlobalReads_global_value_getter definitions.length slot slotTypes bound,
    assembleProgram_getter_lookup definitions slotTypes slot bound⟩

theorem lowerGlobalReads_global_function (getters : List (Nat × Nat)) (index : Nat)
    (unmapped : getterFor getters index = none) :
    lowerGlobalReads getters (.global index) = .global index := by
  simp [lowerGlobalReads, unmapped]

theorem lowerGlobalReads_local (getters : List (Nat × Nat)) (index : Nat) :
    lowerGlobalReads getters (.var index) = .var index := by
  simp [lowerGlobalReads]

inductive Fault where
  | core : PolyIR.Fault → Fault
  | beforeInitialization : Nat → Fault
  deriving DecidableEq

abbrev Store := List (Option Value)

private theorem indexed_lookup_eq_get? {α : Type} (values : List α) (index : Nat) :
    values[index]? = values.get? index := by
  induction values generalizing index with
  | nil => cases index <;> simp [getElem?_def]
  | cons head tail ih => cases index with
      | zero => simp [getElem?_def]
      | succ index => simpa [getElem?_def, Nat.succ_lt_succ_iff] using ih index

/- Each initialized slot is checked against its source-level global type. An
empty slot carries no value and is permitted during ordered initialization. -/
def StoreWellTyped (globals : List Surface.Signature) (slotTypes : List Surface.Ty) (store : Store) : Prop :=
  ∀ slot (value : PolyIR.Value) (type : Surface.Ty), store.get? slot = some (some value) →
    slotTypes.get? slot = some type → PolyIR.ValueTyped globals value type

theorem readGlobal_preserves_type (globals : List Surface.Signature) (slotTypes : List Surface.Ty)
    (store : Store) (slot : Nat) (value : PolyIR.Value) (type : Surface.Ty)
    (storeTyped : StoreWellTyped globals slotTypes store)
    (slotType : slotTypes.get? slot = some type)
    (initialized : store.get? slot = some (some value)) :
    PolyIR.ValueTyped globals value type :=
  storeTyped slot value type initialized slotType

def readGlobal (store : Store) (slot : Nat) : Except Fault Value :=
  match store[slot]? with
  | some (some value) => .ok value
  | some none => .error (.beforeInitialization slot)
  | none => .error (.core .unbound)

/-- For an in-range, well-typed slot, a getter either returns a value of the
declared slot type or reports exactly the source-level early-read fault. It
cannot fail with an unrelated core shape/lookup error. -/
theorem readGlobal_type_safe_or_before_initialization
    (globals : List Surface.Signature) (slotTypes : List Surface.Ty) (store : Store)
    (slot : Nat) (type : Surface.Ty)
    (slotType : slotTypes.get? slot = some type)
    (slotPresent : (store[slot]?).isSome = true)
    (storeTyped : StoreWellTyped globals slotTypes store) :
    (∃ value, readGlobal store slot = .ok value ∧ PolyIR.ValueTyped globals value type) ∨
      readGlobal store slot = .error (.beforeInitialization slot) := by
  cases entry : store[slot]? with
  | none => simp [entry] at slotPresent
  | some cell =>
      cases cell with
      | none =>
          exact Or.inr (by simp [readGlobal, entry])
      | some value =>
          apply Or.inl
          refine ⟨value, by simp [readGlobal, entry], ?_⟩
          have initialized : store.get? slot = some (some value) := by
            rw [← indexed_lookup_eq_get?]
            exact entry
          exact storeTyped slot value type initialized slotType

/-- If the store follows the declared slot layout, every declared slot is
present in the store. Thus callers with the usual layout invariant do not
need to provide a separate bounds/presence hypothesis to establish getter
safety. -/
theorem readGlobal_type_safe_or_before_initialization_of_layout
    (globals : List Surface.Signature) (slotTypes : List Surface.Ty) (store : Store)
    (slot : Nat) (type : Surface.Ty)
    (slotType : slotTypes.get? slot = some type)
    (layout : store.length = slotTypes.length)
    (storeTyped : StoreWellTyped globals slotTypes store) :
    (∃ value, readGlobal store slot = .ok value ∧ PolyIR.ValueTyped globals value type) ∨
      readGlobal store slot = .error (.beforeInitialization slot) := by
  have slotBound : slot < slotTypes.length := (List.get?_eq_some.mp slotType).1
  have storeBound : slot < store.length := by omega
  have slotPresent : (store[slot]?).isSome = true := by
    simp [getElem?_def, storeBound]
  exact readGlobal_type_safe_or_before_initialization globals slotTypes store slot type
    slotType slotPresent storeTyped

mutual
def evaluate (program : List Definition) (store : Store) : Nat → List Value → Term → Except Fault Value
  | 0, _, _ => .error (.core .outOfFuel)
  | fuel + 1, env, term => do
    match term with
    | .var i => match env[i]? with | some value => pure value | none => .error (.core .unbound)
    | .global i => match program[i]? with | some _ => pure (.global i) | none => .error (.core .unbound)
    | .bool b => pure (.bool b)
    | .int n => pure (.int n)
    | .float x => pure (.float x)
      | .string value => pure (.string value)
      | .character value => pure (.character value)
    | .floatBin op left right => do
      let leftValue ← evaluate program store fuel env left
      let rightValue ← evaluate program store fuel env right
      match leftValue, rightValue with
      | .float x, .float y =>
        pure (.float (match op with
          | .add => Float.add x y
          | .sub => Float.sub x y
          | .mul => Float.mul x y
          | .div => Float.div x y))
      | _, _ => .error (.core .wrongShape)
    | .unit => pure .unit
    | .lam arity body => pure (.closure arity body env)
    | .app f args =>
      let function ← evaluate program store fuel env f
      let values ← evaluateArgs program store fuel env args
      match function with
      | .closure arity body captured =>
        if values.length = arity then evaluate program store fuel (values ++ captured) body
        else .error (.core .wrongArity)
      | .global i =>
        match program[i]? with
        | none => .error (.core .unbound)
        | some (.function definition) =>
          if values.length = definition.arity then evaluate program store fuel values definition.body
          else .error (.core .wrongArity)
        | some (.getter slot) =>
          if values.isEmpty then readGlobal store slot else .error (.core .wrongArity)
      | _ => .error (.core .wrongShape)
    | .ite c yes no =>
      match ← evaluate program store fuel env c with
      | .bool true => evaluate program store fuel env yes
      | .bool false => evaluate program store fuel env no
      | _ => .error (.core .wrongShape)
    | .add a b | .sub a b | .mul a b | .le a b | .intEq a b =>
      let left ← evaluate program store fuel env a
      let right ← evaluate program store fuel env b
      match left, right with
      | .int x, .int y =>
        match term with
        | .add _ _ => pure (.int (x + y))
        | .sub _ _ => pure (.int (x - y))
        | .mul _ _ => pure (.int (x * y))
        | .le _ _ => pure (.bool (decide (x ≤ y)))
        | _ => pure (.bool (x == y))
      | _, _ => .error (.core .wrongShape)
    | .letMany values body =>
      let bindings ← evaluateArgs program store fuel env values
      evaluate program store fuel (bindings ++ env) body
    | .begin first rest =>
      let value ← evaluate program store fuel env first
      evaluateSequence program store fuel env value rest
    | .nil => pure .nil
    | .cons head tail => return .cons (← evaluate program store fuel env head) (← evaluate program store fuel env tail)
    | .none => pure .none
    | .some value => return .some (← evaluate program store fuel env value)
    | .matchList target empty full =>
      match ← evaluate program store fuel env target with
      | .nil => evaluate program store fuel env empty
      | .cons head tail => evaluate program store fuel (head :: tail :: env) full
      | _ => .error (.core .wrongShape)
    | .matchOption target empty full =>
      match ← evaluate program store fuel env target with
      | .none => evaluate program store fuel env empty
      | .some value => evaluate program store fuel (value :: env) full
      | _ => .error (.core .wrongShape)

def evaluateArgs (program : List Definition) (store : Store) : Nat → List Value → List Term → Except Fault (List Value)
  | 0, _, _ => .error (.core .outOfFuel)
  | _ + 1, _, [] => pure []
  | fuel + 1, env, head :: tail => return (← evaluate program store fuel env head) ::
      (← evaluateArgs program store fuel env tail)

def evaluateSequence (program : List Definition) (store : Store) :
    Nat → List Value → Value → List Term → Except Fault Value
  | 0, _, _, _ => .error (.core .outOfFuel)
  | _ + 1, _, value, [] => pure value
  | fuel + 1, env, _, head :: tail => do
    let value ← evaluate program store fuel env head
    evaluateSequence program store fuel env value tail
end

/-- A successful singleton argument-list evaluation exposes the strictly
smaller fuel used for its sole element. This is the fuel bridge needed when
composing typed child evaluations through application and parallel-let rules. -/
theorem evaluateArgs_singleton_success
    (program : List Definition) (store : Store) (fuel : Nat)
    (environment : List Value) (term : Term) (value : Value)
    (success : evaluateArgs program store fuel environment [term] = .ok [value]) :
    ∃ remaining, fuel = remaining + 1 ∧
      evaluate program store remaining environment term = .ok value := by
  cases fuel with
  | zero => simp [evaluateArgs] at success
  | succ remaining =>
    cases remaining with
    | zero =>
        cases result : evaluate program store 0 environment term <;>
          simp [evaluateArgs, result, bind, Except.bind, Except.pure] at success
    | succ remaining =>
        cases result : evaluate program store (remaining + 1) environment term with
        | error fault =>
            simp [evaluateArgs, result, bind, Except.bind, Except.pure] at success
        | ok actual =>
            have same : actual = value := by
              simpa [evaluateArgs, result, bind, Except.bind, Except.pure,
                Pure.pure, List.cons.injEq] using success
            subst value
            exact ⟨remaining + 1, by omega, result⟩

/-- A successful singleton argument evaluation has exactly one result, and
records the fuel used to evaluate its element. -/
theorem evaluateArgs_singleton_result
    (program : List Definition) (store : Store) (fuel : Nat)
    (environment : List Value) (term : Term) (values : List Value)
    (success : evaluateArgs program store fuel environment [term] = .ok values) :
    ∃ value remaining, values = [value] ∧ fuel = remaining + 2 ∧
      evaluate program store (remaining + 1) environment term = .ok value := by
  cases fuel with
  | zero => simp [evaluateArgs] at success
  | succ fuel =>
    cases fuel with
    | zero =>
        cases result : evaluate program store 0 environment term <;>
          simp [evaluateArgs, result, bind, Except.bind, Except.pure] at success
    | succ remaining =>
        cases result : evaluate program store (remaining + 1) environment term with
        | error fault =>
            simp [evaluateArgs, result, bind, Except.bind, Except.pure] at success
        | ok value =>
            have valuesEq : values = [value] := by
              simpa [evaluateArgs, result, bind, Except.bind, Except.pure,
                Pure.pure, List.cons.injEq] using success.symm
            exact ⟨value, remaining, valuesEq, by omega, result⟩

/-- A successful two-element argument-list evaluation exposes both values
and the successively smaller budgets used for the two initializers. -/
theorem evaluateArgs_pair_result
    (program : List Definition) (store : Store) (fuel : Nat)
    (environment : List Value) (first second : Term) (values : List Value)
    (success : evaluateArgs program store fuel environment [first, second] = .ok values) :
    ∃ firstValue secondValue remaining, values = [firstValue, secondValue] ∧
      fuel = remaining + 3 ∧
      evaluate program store (remaining + 2) environment first = .ok firstValue ∧
      evaluate program store (remaining + 1) environment second = .ok secondValue := by
  cases fuel with
  | zero => simp [evaluateArgs] at success
  | succ fuel =>
    cases fuel with
    | zero =>
        cases firstResult : evaluate program store 0 environment first <;>
          simp [evaluateArgs, firstResult, bind, Except.bind, Except.pure] at success
    | succ fuel =>
      cases fuel with
      | zero =>
          cases firstResult : evaluate program store 1 environment first with
          | error fault =>
              simp [evaluateArgs, firstResult, bind, Except.bind, Except.pure] at success
          | ok firstValue =>
              cases secondResult : evaluate program store 0 environment second <;>
                simp [evaluateArgs, firstResult, secondResult,
                  bind, Except.bind, Except.pure] at success
      | succ remaining =>
        cases firstResult : evaluate program store (remaining + 2) environment first with
        | error fault =>
            simp [evaluateArgs, firstResult, bind, Except.bind] at success
        | ok firstValue =>
          cases tailResult : evaluateArgs program store (remaining + 2) environment
              [second] with
          | error fault =>
              simp [evaluateArgs, firstResult, tailResult, bind, Except.bind] at success
          | ok tailValues =>
            obtain ⟨secondValue, tailRemaining, tailValuesEq, _tailFuelEq,
              secondResult⟩ := evaluateArgs_singleton_result program store
                (remaining + 2) environment second tailValues tailResult
            subst tailValues
            have valuesEq : values = [firstValue, secondValue] := by
              simpa [evaluateArgs, firstResult, tailResult, bind, Except.bind,
                Except.pure, Pure.pure] using success.symm
            have secondResult' :
                evaluate program store (remaining + 1) environment second = .ok secondValue := by
              have fuelEq : tailRemaining = remaining := by omega
              rw [fuelEq] at secondResult
              exact secondResult
            exact ⟨firstValue, secondValue, remaining, valuesEq, by omega,
              firstResult, secondResult'⟩

/-- Every signature entry described by a typed GlobalIR layout has a runtime
definition at the same index. Evaluating that global reference returns the
typed global value, independently of the current store and local environment. -/
theorem evaluate_global_value_preserves_type
    (globals : List Surface.Signature) (definitions : Surface.Definitions)
    (slotTypes : List Surface.Ty) (functionSources : List (Nat × Nat))
    (program : List Definition) (typed : GlobalProgramTyped globals definitions
      slotTypes functionSources program)
    (assignment : Nat → Surface.Ty) (store : Store) (fuel index : Nat)
    (environment : List Value) (signature : Surface.Signature)
    (signatureFound : globals[index]? = some signature) :
    evaluate program store (fuel + 1) environment (.global index) = .ok (.global index) ∧
      PolyIR.ValueTyped globals (.global index)
        (.fn (Surface.interpretTypes assignment signature.parameters)
          (Surface.interpret assignment signature.result)) := by
  have runtimeFound : ∃ runtime, program[index]? = some runtime := by
    rcases typed.global_entry index signature signatureFound with functionEntry | getterEntry
    · obtain ⟨sourceIndex, body, _source, _bodyFound, _valid, _bodyTyped, runtimeFound⟩ := functionEntry
      exact ⟨.function ⟨signature.parameters.length,
        lowerGlobalReads (getterMappings definitions.length slotTypes) (PolyIR.erase body)⟩,
        runtimeFound⟩
    · obtain ⟨slot, type, runtimeFound, _sameSignature, _typeValid, _slotType⟩ := getterEntry
      exact ⟨.getter slot, runtimeFound⟩
  refine ⟨?_, .global signatureFound⟩
  obtain ⟨runtime, runtimeFound⟩ := runtimeFound
  simp [evaluate, runtimeFound, pure, Except.pure]

/-- Evaluating a Surface-typed lambda in a typed local environment creates a
GlobalIR closure with the corresponding function type. The captured values are
preserved verbatim, so the source typing derivation can be used directly. -/
theorem evaluate_typed_lambda_preserves_type
    (globals : List Surface.Signature) (assignment : Nat → Surface.Ty)
    (context parameters : List Surface.Ty) (result : Surface.Ty)
    (program : List Definition) (store : Store) (fuel : Nat)
    (environment : List Value) (body : Surface.Expr)
    (typing : Surface.HasType globals 0 context
      (.lam parameters result body) (.fn parameters result))
    (environmentTyped : ValuesTyped globals environment
      (Surface.interpretTypes assignment context)) :
    evaluate program store (fuel + 1) environment
      (.lam parameters.length (PolyIR.erase body)) =
        .ok (.closure parameters.length (PolyIR.erase body) environment) ∧
      PolyIR.ValueTyped globals
        (.closure parameters.length (PolyIR.erase body) environment)
        (.fn (Surface.interpretTypes assignment parameters)
          (Surface.interpret assignment result)) := by
  cases typing with
  | lam _ _ bodyTyped =>
      constructor
      · simp [evaluate, pure, Except.pure]
      · exact .closure bodyTyped environmentTyped

/-- The closure-application rule preserves the argument type for the identity
function. This composes argument evaluation, lambda creation, arity checking,
and the body variable read in one GlobalIR execution. -/
theorem evaluate_identity_application_preserves_type
    (globals : List Surface.Signature) (assignment : Nat → Surface.Ty)
    (program : List Definition) (store : Store) (fuel : Nat)
    (environment : List Value) (argument : Term) (value : Value)
    (type : Surface.Ty)
    (argumentTyped : PolyIR.ValueTyped globals value (Surface.interpret assignment type))
    (argumentEvaluates : evaluate program store fuel environment argument = .ok value) :
    evaluate program store (fuel + 2) environment
      (.app (.lam 1 (.var 0)) [argument]) = .ok value ∧
      PolyIR.ValueTyped globals value (Surface.interpret assignment type) := by
  cases fuel with
  | zero => simp [evaluate] at argumentEvaluates
  | succ remaining =>
      constructor
      · simp [evaluate, evaluateArgs, argumentEvaluates, bind, Except.bind, Except.pure,
          Pure.pure, List.isEmpty]
      · exact argumentTyped

/-- A one-binding parallel let whose body reads its newly bound variable
returns the initializer value with the same type. This composes initializer
evaluation, the let environment extension, and local-variable evaluation. -/
theorem evaluate_letOne_variable_preserves_type
    (globals : List Surface.Signature) (program : List Definition) (store : Store)
    (fuel : Nat) (environment : List Value) (initializer : Term)
    (initialValue : Value) (type : Surface.Ty)
    (initializerEvaluates : evaluate program store fuel environment initializer =
      .ok initialValue)
    (initializerTyped : PolyIR.ValueTyped globals initialValue type) :
    evaluate program store (fuel + 2) environment
      (.letMany [initializer] (.var 0)) = .ok initialValue ∧
      PolyIR.ValueTyped globals initialValue type := by
  constructor
  · cases fuel with
    | zero => simp [evaluate] at initializerEvaluates
    | succ remaining =>
        simp [evaluate, evaluateArgs, initializerEvaluates]
  · exact initializerTyped

theorem evaluate_add_of_children (program : List Definition) (store : Store)
    (environment : List Value) (fuel : Nat) (left right : Term) (x y : Int)
    (leftEvaluates : evaluate program store fuel environment left = .ok (.int x))
    (rightEvaluates : evaluate program store fuel environment right = .ok (.int y)) :
    evaluate program store (fuel + 1) environment (.add left right) = .ok (.int (x + y)) := by
  simp [evaluate, leftEvaluates, rightEvaluates, bind, Except.bind, Except.pure] <;> rfl

theorem evaluate_sub_of_children (program : List Definition) (store : Store)
    (environment : List Value) (fuel : Nat) (left right : Term) (x y : Int)
    (leftEvaluates : evaluate program store fuel environment left = .ok (.int x))
    (rightEvaluates : evaluate program store fuel environment right = .ok (.int y)) :
    evaluate program store (fuel + 1) environment (.sub left right) = .ok (.int (x - y)) := by
  simp [evaluate, leftEvaluates, rightEvaluates, bind, Except.bind, Except.pure] <;> rfl

theorem evaluate_mul_of_children (program : List Definition) (store : Store)
    (environment : List Value) (fuel : Nat) (left right : Term) (x y : Int)
    (leftEvaluates : evaluate program store fuel environment left = .ok (.int x))
    (rightEvaluates : evaluate program store fuel environment right = .ok (.int y)) :
    evaluate program store (fuel + 1) environment (.mul left right) = .ok (.int (x * y)) := by
  simp [evaluate, leftEvaluates, rightEvaluates, bind, Except.bind, Except.pure] <;> rfl

theorem evaluate_le_of_children (program : List Definition) (store : Store)
    (environment : List Value) (fuel : Nat) (left right : Term) (x y : Int)
    (leftEvaluates : evaluate program store fuel environment left = .ok (.int x))
    (rightEvaluates : evaluate program store fuel environment right = .ok (.int y)) :
    evaluate program store (fuel + 1) environment (.le left right) =
      .ok (.bool (decide (x ≤ y))) := by
  simp [evaluate, leftEvaluates, rightEvaluates, bind, Except.bind, Except.pure] <;> rfl

theorem evaluate_intEq_of_children (program : List Definition) (store : Store)
    (environment : List Value) (fuel : Nat) (left right : Term) (x y : Int)
    (leftEvaluates : evaluate program store fuel environment left = .ok (.int x))
    (rightEvaluates : evaluate program store fuel environment right = .ok (.int y)) :
    evaluate program store (fuel + 1) environment (.intEq left right) =
      .ok (.bool (x == y)) := by
  simp [evaluate, leftEvaluates, rightEvaluates, bind, Except.bind, Except.pure] <;> rfl

def floatBinValue (operation : Surface.FloatBinOp) (x y : Float) : Float :=
  match operation with
  | .add => Float.add x y
  | .sub => Float.sub x y
  | .mul => Float.mul x y
  | .div => Float.div x y

theorem evaluate_floatBin_of_children (program : List Definition) (store : Store)
    (environment : List Value) (fuel : Nat) (operation : Surface.FloatBinOp)
    (left right : Term) (x y : Float)
    (leftEvaluates : evaluate program store fuel environment left = .ok (.float x))
    (rightEvaluates : evaluate program store fuel environment right = .ok (.float y)) :
    evaluate program store (fuel + 1) environment (.floatBin operation left right) =
      .ok (.float (floatBinValue operation x y)) := by
  simp [evaluate, floatBinValue, leftEvaluates, rightEvaluates, bind, Except.bind, Except.pure, pure]

/-- Exact fault order for a floating binary operation: evaluate the left
operand, then the right operand, then check that both results are Float. -/
theorem evaluate_floatBin_error_iff (program : List Definition) (store : Store)
    (operation : Surface.FloatBinOp) (fuel : Nat) (environment : List Value)
    (left right : Term) (fault : Fault) :
    evaluate program store (fuel + 1) environment (.floatBin operation left right) =
        .error fault ↔
      (∃ leftFault,
        evaluate program store fuel environment left = .error leftFault ∧ fault = leftFault) ∨
      (∃ leftValue rightFault,
        evaluate program store fuel environment left = .ok leftValue ∧
        evaluate program store fuel environment right = .error rightFault ∧ fault = rightFault) ∨
      (∃ leftValue rightValue,
        evaluate program store fuel environment left = .ok leftValue ∧
        evaluate program store fuel environment right = .ok rightValue ∧
        (¬ ∃ x y, leftValue = .float x ∧ rightValue = .float y) ∧
        fault = .core .wrongShape) := by
  simp only [evaluate, bind, Except.bind, pure, Except.pure]
  cases leftResult : evaluate program store fuel environment left with
  | error leftFault => simp [leftResult, eq_comm]
  | ok leftValue =>
      cases rightResult : evaluate program store fuel environment right with
      | error rightFault => simp [leftResult, rightResult, eq_comm]
      | ok rightValue =>
          cases leftValue <;> cases rightValue <;> simp [leftResult, rightResult, eq_comm]

/-- Characterization of successful Float binary operations. -/
theorem evaluate_floatBin_success_iff (program : List Definition) (store : Store)
    (operation : Surface.FloatBinOp) (fuel : Nat) (environment : List Value)
    (left right : Term) (result : Value) :
    evaluate program store (fuel + 1) environment (.floatBin operation left right) = .ok result ↔
      ∃ x y,
        evaluate program store fuel environment left = .ok (.float x) ∧
        evaluate program store fuel environment right = .ok (.float y) ∧
        result = .float (floatBinValue operation x y) := by
  simp only [evaluate, bind, Except.bind, pure, Except.pure]
  cases leftResult : evaluate program store fuel environment left with
  | error fault => simp [leftResult]
  | ok leftValue =>
      cases rightResult : evaluate program store fuel environment right with
      | error fault => simp [leftResult, rightResult]
      | ok rightValue =>
          cases leftValue <;> cases rightValue <;>
            simp [leftResult, rightResult, floatBinValue, eq_comm]

theorem evaluate_floatBin_typed_of_children (globals : List Surface.Signature)
    (program : List Definition) (store : Store) (environment : List Value)
    (fuel : Nat) (operation : Surface.FloatBinOp) (left right : Term)
    (x y : Float)
    (leftEvaluates : evaluate program store fuel environment left = .ok (.float x))
    (rightEvaluates : evaluate program store fuel environment right = .ok (.float y)) :
    evaluate program store (fuel + 1) environment (.floatBin operation left right) =
        .ok (.float (floatBinValue operation x y)) ∧
      PolyIR.ValueTyped globals (.float (floatBinValue operation x y)) .float := by
  exact ⟨evaluate_floatBin_of_children program store environment fuel operation left right x y
    leftEvaluates rightEvaluates, .float⟩

/- The core integer operators preserve their result types in the GlobalIR
evaluator. These lemmas expose the typing fact alongside the evaluator
equation, so initializer and function proofs can compose operator cases
without reopening the evaluator definition. -/
theorem evaluate_add_typed_of_children (globals : List Surface.Signature)
    (program : List Definition) (store : Store) (environment : List Value)
    (fuel : Nat) (left right : Term) (x y : Int)
    (leftEvaluates : evaluate program store fuel environment left = .ok (.int x))
    (rightEvaluates : evaluate program store fuel environment right = .ok (.int y)) :
    evaluate program store (fuel + 1) environment (.add left right) =
        .ok (.int (x + y)) ∧ PolyIR.ValueTyped globals (.int (x + y)) .integer := by
  exact ⟨evaluate_add_of_children program store environment fuel left right x y
    leftEvaluates rightEvaluates, .int⟩

theorem evaluate_sub_typed_of_children (globals : List Surface.Signature)
    (program : List Definition) (store : Store) (environment : List Value)
    (fuel : Nat) (left right : Term) (x y : Int)
    (leftEvaluates : evaluate program store fuel environment left = .ok (.int x))
    (rightEvaluates : evaluate program store fuel environment right = .ok (.int y)) :
    evaluate program store (fuel + 1) environment (.sub left right) =
        .ok (.int (x - y)) ∧ PolyIR.ValueTyped globals (.int (x - y)) .integer := by
  exact ⟨evaluate_sub_of_children program store environment fuel left right x y
    leftEvaluates rightEvaluates, .int⟩

theorem evaluate_mul_typed_of_children (globals : List Surface.Signature)
    (program : List Definition) (store : Store) (environment : List Value)
    (fuel : Nat) (left right : Term) (x y : Int)
    (leftEvaluates : evaluate program store fuel environment left = .ok (.int x))
    (rightEvaluates : evaluate program store fuel environment right = .ok (.int y)) :
    evaluate program store (fuel + 1) environment (.mul left right) =
        .ok (.int (x * y)) ∧ PolyIR.ValueTyped globals (.int (x * y)) .integer := by
  exact ⟨evaluate_mul_of_children program store environment fuel left right x y
    leftEvaluates rightEvaluates, .int⟩

theorem evaluate_le_typed_of_children (globals : List Surface.Signature)
    (program : List Definition) (store : Store) (environment : List Value)
    (fuel : Nat) (left right : Term) (x y : Int)
    (leftEvaluates : evaluate program store fuel environment left = .ok (.int x))
    (rightEvaluates : evaluate program store fuel environment right = .ok (.int y)) :
    evaluate program store (fuel + 1) environment (.le left right) =
        .ok (.bool (decide (x ≤ y))) ∧
      PolyIR.ValueTyped globals (.bool (decide (x ≤ y))) .boolean := by
  exact ⟨evaluate_le_of_children program store environment fuel left right x y
    leftEvaluates rightEvaluates, .bool⟩

inductive IntegerOptionalOperation where
  | quotient
  | remainder
  deriving DecidableEq, Repr

def IntegerOptionalOperation.toPrimitive : IntegerOptionalOperation → TypedExpansion.Primitive
  | .quotient => .quotient
  | .remainder => .remainder

def IntegerOptionalOperation.evaluate (operation : IntegerOptionalOperation)
    (left right : Int) : Option Int :=
  TypedExpansion.integerOptional operation.toPrimitive left right

/- Convert the independent integer builtin specification to the runtime
Option representation. -/
def integerOptionalRuntimeValue (operation : TypedExpansion.Primitive)
    (left right : Int) : Value :=
  match TypedExpansion.integerOptional operation left right with
  | none => .none
  | some value => .some (.int value)

/-- Every result of the specified quotient/remainder operation has the
runtime Option Integer type, including the zero-divisor `none` case. -/
theorem integerOptionalRuntimeValue_typed (globals : List Surface.Signature)
    (operation : TypedExpansion.Primitive) (left right : Int) :
    PolyIR.ValueTyped globals (integerOptionalRuntimeValue operation left right)
      (.option .integer) := by
  unfold integerOptionalRuntimeValue
  cases TypedExpansion.integerOptional operation left right with
  | none => exact .none
  | some value => exact .some .int

/-- Operational contract for a native integer quotient/remainder call after
its two IR arguments are evaluated. `GlobalIR.Term` currently represents
native builtins through the definition table, so this rule is kept explicit
until builtin values are represented directly in that IR. -/
def evaluateIntegerOptionalCall (program : List Definition) (store : Store)
    (operation : IntegerOptionalOperation) : Nat → List Value → Term → Term →
      Except Fault Value
  | 0, _, _, _ => .error (.core .outOfFuel)
  | fuel + 1, environment, left, right => do
      let leftValue ← evaluate program store fuel environment left
      let rightValue ← evaluate program store fuel environment right
      match leftValue, rightValue with
      | .int x, .int y => pure (integerOptionalRuntimeValue operation.toPrimitive x y)
      | _, _ => .error (.core .wrongShape)

/-- Runtime value specified for the registered `to-float` primitive. The
integer-to-binary64 rounding correspondence with C's GMP helper is a separate
numeric refinement obligation. -/
def integerToFloatRuntimeValue (integer : Int) : Value :=
  .float (Float.ofInt integer)

theorem integerToFloatRuntimeValue_typed (globals : List Surface.Signature)
    (integer : Int) :
    PolyIR.ValueTyped globals (integerToFloatRuntimeValue integer) .float := by
  exact .float

/-- Operational contract for the unary native integer-to-float call after its
operand is evaluated. As with the other native helpers, this models the
registered builtin until native closures are represented in `GlobalIR.Term`. -/
def evaluateIntegerToFloatCall (program : List Definition) (store : Store) :
    Nat → List Value → Term → Except Fault Value
  | 0, _, _ => .error (.core .outOfFuel)
  | fuel + 1, environment, operand => do
      let value ← evaluate program store fuel environment operand
      match value with
      | .int integer => pure (integerToFloatRuntimeValue integer)
      | _ => .error (.core .wrongShape)

theorem evaluateIntegerToFloatCall_of_integer_child
    (globals : List Surface.Signature) (program : List Definition) (store : Store)
    (fuel : Nat) (environment : List Value) (operand : Term) (integer : Int)
    (operandEvaluates : evaluate program store fuel environment operand = .ok (.int integer)) :
    evaluateIntegerToFloatCall program store (fuel + 1) environment operand =
        .ok (integerToFloatRuntimeValue integer) ∧
      PolyIR.ValueTyped globals (integerToFloatRuntimeValue integer) .float := by
  constructor
  · simp [evaluateIntegerToFloatCall, operandEvaluates, bind, Except.bind,
      Except.pure, pure]
  · exact integerToFloatRuntimeValue_typed globals integer

/-- Runtime value for `float-truncate` over an explicit binary64 encoding.
This bit-oriented entry point preserves NaN payload and signed-zero cases in
the independent numeric specification even though Lean's `Float` API does
not expose a raw-bit reinterpretation operation. -/
def floatTruncateRuntimeValue (bits : UInt64) : Value :=
  match TypedExpansion.binary64Truncate bits with
  | none => .none
  | some integer => .some (.int integer)

theorem floatTruncateRuntimeValue_typed (globals : List Surface.Signature)
    (bits : UInt64) :
    PolyIR.ValueTyped globals (floatTruncateRuntimeValue bits) (.option .integer) := by
  unfold floatTruncateRuntimeValue
  cases TypedExpansion.binary64Truncate bits with
  | none => exact .none
  | some integer => exact .some .int

/-- Runtime model for the registered Boolean equality builtin. -/
def evaluateBooleanEqualityValue (left right : Bool) : Value :=
  .bool (left == right)

theorem evaluateBooleanEqualityValue_typed (globals : List Surface.Signature)
    (left right : Bool) :
    PolyIR.ValueTyped globals (evaluateBooleanEqualityValue left right) .boolean :=
  .bool

/-- Operational contract for the binary Boolean equality builtin after its
two operands have been evaluated. -/
def evaluateBooleanEqualityCall (program : List Definition) (store : Store) :
    Nat → List Value → Term → Term → Except Fault Value
  | 0, _, _, _ => .error (.core .outOfFuel)
  | fuel + 1, environment, left, right => do
      let leftValue ← evaluate program store fuel environment left
      let rightValue ← evaluate program store fuel environment right
      match leftValue, rightValue with
      | .bool x, .bool y => pure (evaluateBooleanEqualityValue x y)
      | _, _ => .error (.core .wrongShape)

theorem evaluateBooleanEqualityCall_of_boolean_children
    (globals : List Surface.Signature) (program : List Definition) (store : Store)
    (fuel : Nat) (environment : List Value) (left right : Term) (x y : Bool)
    (leftEvaluates : evaluate program store fuel environment left = .ok (.bool x))
    (rightEvaluates : evaluate program store fuel environment right = .ok (.bool y)) :
    evaluateBooleanEqualityCall program store (fuel + 1) environment left right =
        .ok (evaluateBooleanEqualityValue x y) ∧
      PolyIR.ValueTyped globals (evaluateBooleanEqualityValue x y) .boolean := by
  constructor
  · simp [evaluateBooleanEqualityCall, leftEvaluates, rightEvaluates,
      evaluateBooleanEqualityValue, bind, Except.bind, Except.pure, pure]
  · exact evaluateBooleanEqualityValue_typed globals x y

/-- Operational contract for Boolean negation after its operand evaluates. -/
def evaluateBooleanNotCall (program : List Definition) (store : Store) :
    Nat → List Value → Term → Except Fault Value
  | 0, _, _ => .error (.core .outOfFuel)
  | fuel + 1, environment, operand => do
      let value ← evaluate program store fuel environment operand
      match value with
      | .bool b => pure (.bool (!b))
      | _ => .error (.core .wrongShape)

theorem evaluateBooleanNotCall_of_boolean_child
    (globals : List Surface.Signature) (program : List Definition) (store : Store)
    (fuel : Nat) (environment : List Value) (operand : Term) (value : Bool)
    (operandEvaluates : evaluate program store fuel environment operand = .ok (.bool value)) :
    evaluateBooleanNotCall program store (fuel + 1) environment operand = .ok (.bool (!value)) ∧
      PolyIR.ValueTyped globals (.bool (!value)) .boolean := by
  constructor
  · simp [evaluateBooleanNotCall, operandEvaluates, bind, Except.bind,
      Except.pure, pure]
  · exact .bool

/-- The five C Float comparisons. The explicit NaN guard matches IEEE/C
ordered comparisons: every relational comparison and equality is false when
either operand is NaN. -/
inductive FloatComparisonOperation where
  | lt | le | gt | ge | eq
  deriving DecidableEq, Repr

def FloatComparisonOperation.toPrimitive : FloatComparisonOperation → TypedExpansion.Primitive
  | .lt => .flt
  | .le => .fle
  | .gt => .fgt
  | .ge => .fge
  | .eq => .floatEq

def FloatComparisonOperation.evaluate (operation : FloatComparisonOperation)
    (left right : Float) : Bool :=
  if left.isNaN || right.isNaN then false else
  match operation with
  | .lt => decide (left < right)
  | .le => decide (left ≤ right)
  | .gt => decide (left > right)
  | .ge => decide (left ≥ right)
  | .eq => left == right

theorem FloatComparisonOperation.evaluate_left_nan
    (operation : FloatComparisonOperation) (left right : Float)
    (leftNaN : left.isNaN = true) :
    operation.evaluate left right = false := by
  simp [FloatComparisonOperation.evaluate, leftNaN]

theorem FloatComparisonOperation.evaluate_right_nan
    (operation : FloatComparisonOperation) (left right : Float)
    (rightNaN : right.isNaN = true) :
    operation.evaluate left right = false := by
  simp [FloatComparisonOperation.evaluate, rightNaN]

/-- Outside the NaN case, Float comparison evaluation is exactly the selected
IEEE/C comparison operator. -/
theorem FloatComparisonOperation.evaluate_of_not_nan
    (operation : FloatComparisonOperation) (left right : Float)
    (leftNotNaN : left.isNaN = false) (rightNotNaN : right.isNaN = false) :
    operation.evaluate left right =
      match operation with
      | .lt => decide (left < right)
      | .le => decide (left ≤ right)
      | .gt => decide (left > right)
      | .ge => decide (left ≥ right)
      | .eq => left == right := by
  cases operation <;>
    simp [FloatComparisonOperation.evaluate, leftNotNaN, rightNotNaN]

def floatComparisonRuntimeValue (operation : FloatComparisonOperation)
    (left right : Float) : Value :=
  .bool (operation.evaluate left right)

theorem FloatComparisonOperation.runtimeValue_nan
    (operation : FloatComparisonOperation) (left right : Float)
    (leftNaN : left.isNaN = true) :
    floatComparisonRuntimeValue operation left right = .bool false := by
  simp [floatComparisonRuntimeValue,
    FloatComparisonOperation.evaluate_left_nan operation left right leftNaN]

theorem floatComparisonRuntimeValue_typed (globals : List Surface.Signature)
    (operation : FloatComparisonOperation) (left right : Float) :
    PolyIR.ValueTyped globals (floatComparisonRuntimeValue operation left right) .boolean :=
  .bool

def evaluateFloatComparisonCall (program : List Definition) (store : Store)
    (operation : FloatComparisonOperation) : Nat → List Value → Term → Term → Except Fault Value
  | 0, _, _, _ => .error (.core .outOfFuel)
  | fuel + 1, environment, left, right => do
      let leftValue ← evaluate program store fuel environment left
      let rightValue ← evaluate program store fuel environment right
      match leftValue, rightValue with
      | .float x, .float y => pure (floatComparisonRuntimeValue operation x y)
      | _, _ => .error (.core .wrongShape)

theorem evaluateFloatComparisonCall_of_float_children
    (globals : List Surface.Signature) (program : List Definition) (store : Store)
    (operation : FloatComparisonOperation) (fuel : Nat) (environment : List Value)
    (left right : Term) (x y : Float)
    (leftEvaluates : evaluate program store fuel environment left = .ok (.float x))
    (rightEvaluates : evaluate program store fuel environment right = .ok (.float y)) :
    evaluateFloatComparisonCall program store operation (fuel + 1) environment left right =
        .ok (floatComparisonRuntimeValue operation x y) ∧
      PolyIR.ValueTyped globals (floatComparisonRuntimeValue operation x y) .boolean := by
  constructor
  · simp [evaluateFloatComparisonCall, leftEvaluates, rightEvaluates,
      bind, Except.bind, Except.pure, pure]
  · exact floatComparisonRuntimeValue_typed globals operation x y

/-- Exact fault order for a floating comparison: evaluate left, then right,
then reject either non-Float value. -/
theorem evaluateFloatComparisonCall_error_iff (program : List Definition) (store : Store)
    (operation : FloatComparisonOperation) (fuel : Nat) (environment : List Value)
    (left right : Term) (fault : Fault) :
    evaluateFloatComparisonCall program store operation (fuel + 1) environment left right =
        .error fault ↔
      (∃ leftFault,
        evaluate program store fuel environment left = .error leftFault ∧ fault = leftFault) ∨
      (∃ leftValue rightFault,
        evaluate program store fuel environment left = .ok leftValue ∧
        evaluate program store fuel environment right = .error rightFault ∧ fault = rightFault) ∨
      (∃ leftValue rightValue,
        evaluate program store fuel environment left = .ok leftValue ∧
        evaluate program store fuel environment right = .ok rightValue ∧
        (¬ ∃ x y, leftValue = .float x ∧ rightValue = .float y) ∧
        fault = .core .wrongShape) := by
  simp only [evaluateFloatComparisonCall, bind, Except.bind, pure, Except.pure]
  cases leftResult : evaluate program store fuel environment left with
  | error leftFault => simp [leftResult, eq_comm]
  | ok leftValue =>
      cases rightResult : evaluate program store fuel environment right with
      | error rightFault => simp [leftResult, rightResult, eq_comm]
      | ok rightValue =>
          cases leftValue <;> cases rightValue <;> simp [leftResult, rightResult, eq_comm]

/-- Characterization of successful Float comparison helper calls for arbitrary
operand terms. A result is successful exactly when both terms evaluate to
Float values, in left-to-right evaluator order. -/
theorem evaluateFloatComparisonCall_success_iff (program : List Definition) (store : Store)
    (operation : FloatComparisonOperation) (fuel : Nat) (environment : List Value)
    (left right : Term) (result : Value) :
    evaluateFloatComparisonCall program store (operation) (fuel + 1) environment left right =
        .ok result ↔
      ∃ x y,
        evaluate program store fuel environment left = .ok (.float x) ∧
        evaluate program store fuel environment right = .ok (.float y) ∧
        result = floatComparisonRuntimeValue operation x y := by
  simp only [evaluateFloatComparisonCall, bind, Except.bind, pure, Except.pure]
  cases leftResult : evaluate program store fuel environment left with
  | error leftFault => simp [leftResult]
  | ok leftValue =>
      cases rightResult : evaluate program store fuel environment right with
      | error rightFault => simp [leftResult, rightResult]
      | ok rightValue =>
          cases leftValue <;> cases rightValue <;>
            simp [leftResult, rightResult, floatComparisonRuntimeValue, eq_comm]

/-- Every successful Float comparison helper result has Boolean type, even
when no assumptions are made about the operand terms. -/
theorem evaluateFloatComparisonCall_preserves_type (globals : List Surface.Signature)
    (program : List Definition) (store : Store) (operation : FloatComparisonOperation)
    (fuel : Nat) (environment : List Value) (left right : Term) (result : Value)
    (success : evaluateFloatComparisonCall program store operation fuel environment left right =
      .ok result) :
    PolyIR.ValueTyped globals result .boolean := by
  cases fuel with
  | zero => simp [evaluateFloatComparisonCall] at success
  | succ remaining =>
      obtain ⟨x, y, leftEvaluates, rightEvaluates, resultEq⟩ :=
        (evaluateFloatComparisonCall_success_iff program store operation remaining
          environment left right result).mp (by simpa using success)
      rw [resultEq]
      exact floatComparisonRuntimeValue_typed globals operation x y

/-- The native Option-valued integer call evaluates to the shared runtime
result and preserves its Option Integer type whenever both integer operands
evaluate successfully. -/
theorem evaluateIntegerOptionalCall_of_integer_children
    (globals : List Surface.Signature) (program : List Definition) (store : Store)
    (operation : IntegerOptionalOperation) (fuel : Nat) (environment : List Value)
    (left right : Term) (x y : Int)
    (leftEvaluates : evaluate program store fuel environment left = .ok (.int x))
    (rightEvaluates : evaluate program store fuel environment right = .ok (.int y)) :
    evaluateIntegerOptionalCall program store operation (fuel + 1) environment left right =
        .ok (integerOptionalRuntimeValue operation.toPrimitive x y) ∧
      PolyIR.ValueTyped globals (integerOptionalRuntimeValue operation.toPrimitive x y)
        (.option .integer) := by
  constructor
  · cases operation <;>
      simp [evaluateIntegerOptionalCall, IntegerOptionalOperation.evaluate,
        integerOptionalRuntimeValue, leftEvaluates, rightEvaluates,
        bind, Except.bind, pure, Except.pure, TypedExpansion.integerOptional]
  · exact integerOptionalRuntimeValue_typed globals operation.toPrimitive x y

/-- The native quotient/remainder call reports an error from evaluating its
left operand without evaluating or replacing that error. -/
theorem evaluateIntegerOptionalCall_left_error
    (program : List Definition) (store : Store)
    (operation : IntegerOptionalOperation) (fuel : Nat) (environment : List Value)
    (left right : Term) (fault : Fault)
    (leftFails : evaluate program store fuel environment left = .error fault) :
    evaluateIntegerOptionalCall program store operation (fuel + 1) environment left right =
      .error fault := by
  simp [evaluateIntegerOptionalCall, leftFails, bind, Except.bind]

/-- Once the left operand has evaluated to an integer, a right-operand fault
is propagated unchanged by the Option-valued integer operation. -/
theorem evaluateIntegerOptionalCall_right_error
    (program : List Definition) (store : Store)
    (operation : IntegerOptionalOperation) (fuel : Nat) (environment : List Value)
    (left right : Term) (x : Int) (fault : Fault)
    (leftEvaluates : evaluate program store fuel environment left = .ok (.int x))
    (rightFails : evaluate program store fuel environment right = .error fault) :
    evaluateIntegerOptionalCall program store operation (fuel + 1) environment left right =
      .error fault := by
  simp [evaluateIntegerOptionalCall, leftEvaluates, rightFails, bind, Except.bind]

/-- If both operands evaluate successfully but at least one is not an
integer, the native operation reports the evaluator's wrong-shape fault. -/
theorem evaluateIntegerOptionalCall_wrong_shape
    (program : List Definition) (store : Store)
    (operation : IntegerOptionalOperation) (fuel : Nat) (environment : List Value)
    (left right : Term) (leftValue rightValue : Value)
    (leftEvaluates : evaluate program store fuel environment left = .ok leftValue)
    (rightEvaluates : evaluate program store fuel environment right = .ok rightValue)
    (wrongShape : ¬ ∃ x y, leftValue = .int x ∧ rightValue = .int y) :
    evaluateIntegerOptionalCall program store operation (fuel + 1) environment left right =
      .error (.core .wrongShape) := by
  simp [evaluateIntegerOptionalCall, leftEvaluates, rightEvaluates, bind, Except.bind]
  cases leftValue <;> cases rightValue <;> simp_all

/-- Exact success characterization for the Option-valued integer call helper.
It succeeds precisely when both operands evaluate to integers, and returns
the shared Option semantics for those values. -/
theorem evaluateIntegerOptionalCall_success_iff
    (program : List Definition) (store : Store) (operation : IntegerOptionalOperation)
    (fuel : Nat) (environment : List PolyIR.Value) (left right : PolyIR.Term)
    (result : PolyIR.Value) :
    evaluateIntegerOptionalCall program store operation (fuel + 1) environment left right =
        .ok result ↔
      ∃ x y, evaluate program store fuel environment left = .ok (.int x) ∧
        evaluate program store fuel environment right = .ok (.int y) ∧
        result = integerOptionalRuntimeValue operation.toPrimitive x y := by
  simp only [evaluateIntegerOptionalCall, bind, Except.bind, pure, Except.pure]
  cases leftResult : evaluate program store fuel environment left with
  | error fault => simp [leftResult]
  | ok leftValue =>
      cases rightResult : evaluate program store fuel environment right with
      | error fault => simp [leftResult, rightResult]
      | ok rightValue =>
          cases leftValue <;> cases rightValue <;>
            simp [leftResult, rightResult, integerOptionalRuntimeValue, eq_comm]

/-- Exact error classification for the Option-valued integer call helper.
The helper evaluates the left operand, then the right operand, and only then
checks their runtime shapes. -/
theorem evaluateIntegerOptionalCall_error_iff
    (program : List Definition) (store : Store) (operation : IntegerOptionalOperation)
    (fuel : Nat) (environment : List PolyIR.Value) (left right : PolyIR.Term)
    (fault : Fault) :
    evaluateIntegerOptionalCall program store operation (fuel + 1) environment left right =
        .error fault ↔
      (∃ leftFault, evaluate program store fuel environment left = .error leftFault ∧
        fault = leftFault) ∨
      (∃ leftValue rightFault, evaluate program store fuel environment left = .ok leftValue ∧
        evaluate program store fuel environment right = .error rightFault ∧
        fault = rightFault) ∨
      (∃ leftValue rightValue, evaluate program store fuel environment left = .ok leftValue ∧
        evaluate program store fuel environment right = .ok rightValue ∧
        (¬ ∃ x y, leftValue = .int x ∧ rightValue = .int y) ∧ fault = .core .wrongShape) := by
  simp only [evaluateIntegerOptionalCall, bind, Except.bind, pure, Except.pure]
  cases leftResult : evaluate program store fuel environment left with
  | error leftFault => simp [leftResult, eq_comm]
  | ok leftValue =>
      cases rightResult : evaluate program store fuel environment right with
      | error rightFault => simp [leftResult, rightResult, eq_comm]
      | ok rightValue =>
          cases leftValue <;> cases rightValue <;>
            simp [leftResult, rightResult, eq_comm]

/-- Zero fuel is the sole out-of-fuel case of this helper. -/
theorem evaluateIntegerOptionalCall_zero_fuel
    (program : List Definition) (store : Store) (operation : IntegerOptionalOperation)
    (environment : List PolyIR.Value) (left right : PolyIR.Term) :
    evaluateIntegerOptionalCall program store operation 0 environment left right =
      .error (.core .outOfFuel) := rfl

/-- Any successful result of the standalone Option-valued integer call
helper has type Option Integer, for arbitrary operand terms. -/
theorem evaluateIntegerOptionalCall_preserves_type
    (globals : List Surface.Signature) (program : List Definition) (store : Store)
    (operation : IntegerOptionalOperation) (fuel : Nat)
    (environment : List PolyIR.Value) (left right : PolyIR.Term) (result : PolyIR.Value)
    (success : evaluateIntegerOptionalCall program store operation fuel environment left right =
      .ok result) :
    PolyIR.ValueTyped globals result (.option .integer) := by
  obtain ⟨leftInteger, rightInteger, leftEvaluates, rightEvaluates, resultEq⟩ :=
    (evaluateIntegerOptionalCall_success_iff program store operation (fuel - 1)
      environment left right result).mp (by
        cases fuel with
        | zero => simp [evaluateIntegerOptionalCall] at success
        | succ remaining => simpa using success)
  rw [resultEq]
  exact integerOptionalRuntimeValue_typed globals operation.toPrimitive leftInteger rightInteger

theorem evaluate_intEq_typed_of_children (globals : List Surface.Signature)
    (program : List Definition) (store : Store) (environment : List Value)
    (fuel : Nat) (left right : Term) (x y : Int)
    (leftEvaluates : evaluate program store fuel environment left = .ok (.int x))
    (rightEvaluates : evaluate program store fuel environment right = .ok (.int y)) :
    evaluate program store (fuel + 1) environment (.intEq left right) =
        .ok (.bool (x == y)) ∧ PolyIR.ValueTyped globals (.bool (x == y)) .boolean := by
  exact ⟨evaluate_intEq_of_children program store environment fuel left right x y
    leftEvaluates rightEvaluates, .bool⟩

/-- A successful GlobalIR local-variable read preserves the type stored in
the corresponding source context slot. This is the environment lookup case
needed when extending evaluator preservation beyond closed terms. -/
theorem evaluate_var_preserves_type (globals : List Surface.Signature)
    (assignment : Nat → Surface.Ty) (types : List Surface.Ty)
    (program : List Definition) (store : Store) (fuel index : Nat)
    (environment : List Value) (value : Value) (type : Surface.Ty)
    (environmentTyped : ValuesTyped globals environment
      (Surface.interpretTypes assignment types))
    (typeFound : types[index]? = some type)
    (success : evaluate program store fuel environment (.var index) = .ok value) :
    ValueTyped globals value (Surface.interpret assignment type) := by
  obtain ⟨expected, lookupExpected, expectedTyped⟩ :=
    ValuesTyped.lookup environmentTyped typeFound
  have lookupValue : environment[index]? = some value := by
    cases fuel with
    | zero => simp [evaluate] at success
    | succ remaining =>
        change (match environment[index]? with
          | some found => Except.ok found
          | none => (Except.error (.core .unbound) : Except Fault Value)) = .ok value at success
        cases lookup : environment[index]? with
        | none => simp [lookup] at success
        | some found =>
            have same : found = value := by simpa [lookup] using success
            simp [lookup, same]
  have same : expected = value := Option.some.inj (lookupExpected.symm.trans lookupValue)
  cases same
  exact expectedTyped

/-- Surface typing supplies the context-index fact consumed by the local
variable evaluator lemma, yielding a direct typed-variable preservation rule. -/
theorem evaluate_typed_var_preserves_type (globals : List Surface.Signature)
    (assignment : Nat → Surface.Ty) (context : List Surface.Ty)
    (program : List Definition) (store : Store) (fuel index : Nat)
    (environment : List Value) (value : Value) (type : Surface.Ty)
    (typing : Surface.HasType globals 0 context (.var index) type)
    (environmentTyped : ValuesTyped globals environment
      (Surface.interpretTypes assignment context))
    (success : evaluate program store fuel environment (.var index) = .ok value) :
    ValueTyped globals value (Surface.interpret assignment type) := by
  cases typing with
  | var typeFound =>
      exact evaluate_var_preserves_type globals assignment context program store fuel index
        environment value type environmentTyped typeFound success

/-- Float literals are preserved by the complete GlobalIR evaluator for every
positive fuel, independently of the store and environment. This isolates the
binary64 payload from the polymorphic type valuation: the evaluator returns
the same float bits and the typing rule assigns the fixed `float` type. -/
theorem evaluate_float_literal_preserves_type
    (globals : List Surface.Signature) (program : List Definition) (store : Store)
    (fuel : Nat) (environment : List Value) (number : Float) :
    evaluate program store (fuel + 1) environment (.float number) = .ok (.float number) ∧
      ValueTyped globals (.float number) .float := by
  constructor
  · simp [evaluate, Pure.pure, Except.pure]
  · exact .float

/-- The integer-literal/arithmetic fragment has evaluator type preservation
without assumptions on the program, store, or environment. This is the
structural fragment used by closed arithmetic initializers. -/
inductive ArithmeticTerm : Term → Surface.Ty → Prop where
  | bool : ArithmeticTerm (.bool value) .boolean
  | int : ArithmeticTerm (.int value) .integer
  | float : ArithmeticTerm (.float value) .float
  | string : ArithmeticTerm (.string value) .string
  | character : ArithmeticTerm (.character value) .character
  | unit : ArithmeticTerm .unit .unit
  | nil : ArithmeticTerm .nil (.list element)
  | none : ArithmeticTerm .none (.option element)
  | some : ArithmeticTerm value element →
      ArithmeticTerm (.some value) (.option element)
  | cons : ArithmeticTerm head element → ArithmeticTerm tail (.list element) →
      ArithmeticTerm (.cons head tail) (.list element)
  | ite : ArithmeticTerm condition .boolean → ArithmeticTerm yes resultType →
      ArithmeticTerm no resultType → ArithmeticTerm (.ite condition yes no) resultType
  | matchOption : ArithmeticTerm target (.option element) →
      ArithmeticTerm empty resultType → ArithmeticTerm full resultType →
      ArithmeticTerm (.matchOption target empty full) resultType
  | matchList : ArithmeticTerm target (.list element) →
      ArithmeticTerm empty resultType → ArithmeticTerm full resultType →
      ArithmeticTerm (.matchList target empty full) resultType
  | letOne : ArithmeticTerm initializer initializerType →
      ArithmeticTerm body resultType →
      ArithmeticTerm (.letMany [initializer] body) resultType
  | letManyClosed (body : Term) (resultType : Surface.Ty) (initializers : List Term) :
      ArithmeticTerm body resultType →
      ArithmeticTerm (.letMany initializers body) resultType
  | add : ArithmeticTerm left .integer → ArithmeticTerm right .integer →
      ArithmeticTerm (.add left right) .integer
  | sub : ArithmeticTerm left .integer → ArithmeticTerm right .integer →
      ArithmeticTerm (.sub left right) .integer
  | mul : ArithmeticTerm left .integer → ArithmeticTerm right .integer →
      ArithmeticTerm (.mul left right) .integer
  | le : ArithmeticTerm left .integer → ArithmeticTerm right .integer →
      ArithmeticTerm (.le left right) .boolean
  | intEq : ArithmeticTerm left .integer → ArithmeticTerm right .integer →
      ArithmeticTerm (.intEq left right) .boolean
  | floatBin : ArithmeticTerm left .float → ArithmeticTerm right .float →
      ArithmeticTerm (.floatBin op left right) .float

theorem evaluate_arithmetic_preserves_type
    (globals : List Surface.Signature) (program : List Definition) (store : Store)
    (fuel : Nat) (environment : List Value) (term : Term) (type : Surface.Ty)
    (arithmetic : ArithmeticTerm term type) (value : Value)
    (success : evaluate program store fuel environment term = .ok value) :
    PolyIR.ValueTyped globals value type := by
  induction arithmetic generalizing fuel environment value with
  | bool =>
      cases fuel with
      | zero => simp [evaluate] at success
      | succ fuel =>
          simp [evaluate] at success
          cases success
          exact .bool
  | int =>
      cases fuel with
      | zero => simp [evaluate] at success
      | succ fuel =>
          simp [evaluate] at success
          cases success
          exact .int
  | float =>
      cases fuel with
      | zero => simp [evaluate] at success
      | succ fuel =>
          simp [evaluate] at success
          cases success
          exact .float
  | string =>
      cases fuel with
      | zero => simp [evaluate] at success
      | succ fuel =>
          simp [evaluate] at success
          cases success
          exact .string
  | character =>
      cases fuel with
      | zero => simp [evaluate] at success
      | succ fuel =>
          simp [evaluate] at success
          cases success
          exact .character
  | unit =>
      cases fuel with
      | zero => simp [evaluate] at success
      | succ fuel =>
          simp [evaluate] at success
          cases success
          exact .unit
  | nil =>
      cases fuel with
      | zero => simp [evaluate] at success
      | succ fuel =>
          simp [evaluate] at success
          cases success
          exact .nil
  | none =>
      cases fuel with
      | zero => simp [evaluate] at success
      | succ fuel =>
          simp [evaluate] at success
          cases success
          exact .none
  | letOne initializerTyped bodyTyped initializerIH bodyIH =>
      rename_i initializer initializerType body resultType
      cases fuel with
      | zero => simp [evaluate] at success
      | succ fuel =>
          change (do
            let bindings ← evaluateArgs program store fuel environment [initializer]
            evaluate program store fuel (bindings ++ environment) body) = .ok value at success
          cases argumentsResult : evaluateArgs program store fuel environment
              [initializer] with
          | error fault =>
              simp [evaluate, argumentsResult, bind, Except.bind] at success
          | ok values =>
              obtain ⟨initializerValue, remaining, valuesEq, fuelEq, initializerResult⟩ :=
                evaluateArgs_singleton_result program store fuel environment initializer
                  values argumentsResult
              subst values
              have _initializerValueTyped := initializerIH (remaining + 1)
                environment initializerValue initializerResult
              have bodySuccess :
                  evaluate program store fuel (initializerValue :: environment) body =
                    .ok value := by
                simpa [argumentsResult, bind, Except.bind, Except.pure,
                  List.singleton_append] using success
              exact bodyIH fuel (initializerValue :: environment) value bodySuccess
  | letManyClosed body resultType initializers bodyTyped bodyIH =>
      cases fuel with
      | zero => simp [evaluate] at success
      | succ fuel =>
          change (do
            let bindings ← evaluateArgs program store fuel environment initializers
            evaluate program store fuel (bindings ++ environment) body) = .ok value at success
          cases argumentsResult : evaluateArgs program store fuel environment initializers with
          | error fault =>
              simp [evaluate, argumentsResult, bind, Except.bind] at success
          | ok bindings =>
              have bodySuccess :
                  evaluate program store fuel (bindings ++ environment) body = .ok value := by
                simpa [argumentsResult, bind, Except.bind, Except.pure] using success
              exact bodyIH fuel (bindings ++ environment) value bodySuccess
  | some childTyped childIH =>
      rename_i childTerm elementType
      cases fuel with
      | zero => simp [evaluate] at success
      | succ fuel =>
          cases childResult : evaluate program store fuel environment childTerm with
          | error fault => simp [evaluate, childResult, bind, Except.bind] at success
          | ok childValue =>
              have childValueTyped := childIH fuel environment childValue childResult
              rw [show evaluate program store (fuel + 1) environment (.some childTerm) =
                .ok (.some childValue) by
                  simp [evaluate, childResult, bind, Except.bind, Except.pure] <;> rfl] at success
              cases success
              exact .some childValueTyped
  | cons headTyped tailTyped headIH tailIH =>
      rename_i headTerm elementType tailTerm
      cases fuel with
      | zero => simp [evaluate] at success
      | succ fuel =>
          cases headResult : evaluate program store fuel environment headTerm with
          | error fault => simp [evaluate, headResult, bind, Except.bind] at success
          | ok headValue =>
              have headValueTyped := headIH fuel environment headValue headResult
              cases tailResult : evaluate program store fuel environment tailTerm with
              | error fault => simp [evaluate, headResult, tailResult, bind, Except.bind] at success
              | ok tailValue =>
                  have tailValueTyped := tailIH fuel environment tailValue tailResult
                  rw [show evaluate program store (fuel + 1) environment
                    (.cons headTerm tailTerm) =
                    .ok (.cons headValue tailValue) by
                      simp [evaluate, headResult, tailResult, bind, Except.bind,
                        Except.pure] <;> rfl] at success
                  cases success
                  exact .cons headValueTyped tailValueTyped
  | ite conditionTyped yesTyped noTyped conditionIH yesIH noIH =>
      rename_i conditionTerm resultType yesTerm noTerm
      cases fuel with
      | zero => simp [evaluate] at success
      | succ fuel =>
          cases conditionResult : evaluate program store fuel environment conditionTerm with
          | error fault => simp [evaluate, conditionResult, bind, Except.bind] at success
          | ok conditionValue =>
              have conditionValueTyped := conditionIH fuel environment conditionValue conditionResult
              cases conditionValueTyped with
              | bool =>
                  rename_i conditionBool
                  cases conditionBool with
                  | false =>
                      cases noResult : evaluate program store fuel environment noTerm with
                      | error fault => simp [evaluate, conditionResult, noResult,
                          bind, Except.bind] at success
                      | ok noValue =>
                          have noValueTyped := noIH fuel environment noValue noResult
                          simp [evaluate, conditionResult, noResult, bind, Except.bind,
                            Except.pure] at success
                          cases success
                          exact noValueTyped
                  | true =>
                      cases yesResult : evaluate program store fuel environment resultType with
                      | error fault => simp [evaluate, conditionResult, yesResult,
                          bind, Except.bind] at success
                      | ok yesValue =>
                          have yesValueTyped := yesIH fuel environment yesValue yesResult
                          simp [evaluate, conditionResult, yesResult, bind, Except.bind,
                            Except.pure] at success
                          cases success
                          exact yesValueTyped
  | matchOption targetTyped emptyTyped fullTyped targetIH emptyIH fullIH =>
      rename_i targetTerm elementType emptyTerm resultType fullTerm
      cases fuel with
      | zero => simp [evaluate] at success
      | succ fuel =>
          cases targetResult : evaluate program store fuel environment targetTerm with
          | error fault => simp [evaluate, targetResult, bind, Except.bind] at success
          | ok targetValue =>
              have targetValueTyped := targetIH fuel environment targetValue targetResult
              cases targetValueTyped with
              | none =>
                  cases emptyResult : evaluate program store fuel environment emptyTerm with
                  | error fault => simp [evaluate, targetResult, emptyResult,
                      bind, Except.bind] at success
                  | ok resultValue =>
                      have resultTyped := emptyIH fuel environment resultValue emptyResult
                      simp [evaluate, targetResult, emptyResult, bind, Except.bind,
                        Except.pure] at success
                      cases success
                      exact resultTyped
              | some payloadTyped =>
                  rename_i payloadValue
                  cases fullResult : evaluate program store fuel
                      (payloadValue :: environment) fullTerm with
                  | error fault => simp [evaluate, targetResult, fullResult,
                      bind, Except.bind] at success
                  | ok resultValue =>
                      have resultTyped := fullIH fuel (payloadValue :: environment)
                        resultValue fullResult
                      simp [evaluate, targetResult, fullResult, bind, Except.bind,
                        Except.pure] at success
                      cases success
                      exact resultTyped
  | matchList targetTyped emptyTyped fullTyped targetIH emptyIH fullIH =>
      rename_i targetTerm elementType emptyTerm resultType fullTerm
      cases fuel with
      | zero => simp [evaluate] at success
      | succ fuel =>
          cases targetResult : evaluate program store fuel environment targetTerm with
          | error fault => simp [evaluate, targetResult, bind, Except.bind] at success
          | ok targetValue =>
              have targetValueTyped := targetIH fuel environment targetValue targetResult
              cases targetValueTyped with
              | nil =>
                  cases emptyResult : evaluate program store fuel environment emptyTerm with
                  | error fault => simp [evaluate, targetResult, emptyResult,
                      bind, Except.bind] at success
                  | ok resultValue =>
                      have resultTyped := emptyIH fuel environment resultValue emptyResult
                      simp [evaluate, targetResult, emptyResult, bind, Except.bind,
                        Except.pure] at success
                      cases success
                      exact resultTyped
              | cons headTyped tailTyped =>
                  rename_i headValue tailValue
                  cases fullResult : evaluate program store fuel
                      (headValue :: tailValue :: environment) fullTerm with
                  | error fault => simp [evaluate, targetResult, fullResult,
                      bind, Except.bind] at success
                  | ok resultValue =>
                      have resultTyped := fullIH fuel
                        (headValue :: tailValue :: environment) resultValue fullResult
                      simp [evaluate, targetResult, fullResult, bind, Except.bind,
                        Except.pure] at success
                      cases success
                      exact resultTyped
  | add leftTyped rightTyped leftIH rightIH =>
      rename_i leftTerm rightTerm
      cases fuel with
      | zero => simp [evaluate] at success
      | succ fuel =>
          cases leftResult : evaluate program store fuel environment leftTerm with
          | error fault => simp [evaluate, leftResult, bind, Except.bind] at success
          | ok leftValue =>
              have leftValueTyped := leftIH fuel environment leftValue leftResult
              cases leftValueTyped
              rename_i x
              cases rightResult : evaluate program store fuel environment rightTerm with
              | error fault => simp [evaluate, leftResult, rightResult, bind, Except.bind] at success
              | ok rightValue =>
                  have rightValueTyped := rightIH fuel environment rightValue rightResult
                  cases rightValueTyped
                  rename_i y
                  rw [evaluate_add_of_children program store environment fuel leftTerm rightTerm x y
                    leftResult rightResult] at success
                  cases success
                  exact .int
  | sub leftTyped rightTyped leftIH rightIH =>
      rename_i leftTerm rightTerm
      cases fuel with
      | zero => simp [evaluate] at success
      | succ fuel =>
          cases leftResult : evaluate program store fuel environment leftTerm with
          | error fault => simp [evaluate, leftResult, bind, Except.bind] at success
          | ok leftValue =>
              have leftValueTyped := leftIH fuel environment leftValue leftResult
              cases leftValueTyped
              rename_i x
              cases rightResult : evaluate program store fuel environment rightTerm with
              | error fault => simp [evaluate, leftResult, rightResult, bind, Except.bind] at success
              | ok rightValue =>
                  have rightValueTyped := rightIH fuel environment rightValue rightResult
                  cases rightValueTyped
                  rename_i y
                  rw [evaluate_sub_of_children program store environment fuel leftTerm rightTerm x y
                    leftResult rightResult] at success
                  cases success
                  exact .int
  | mul leftTyped rightTyped leftIH rightIH =>
      rename_i leftTerm rightTerm
      cases fuel with
      | zero => simp [evaluate] at success
      | succ fuel =>
          cases leftResult : evaluate program store fuel environment leftTerm with
          | error fault => simp [evaluate, leftResult, bind, Except.bind] at success
          | ok leftValue =>
              have leftValueTyped := leftIH fuel environment leftValue leftResult
              cases leftValueTyped
              rename_i x
              cases rightResult : evaluate program store fuel environment rightTerm with
              | error fault => simp [evaluate, leftResult, rightResult, bind, Except.bind] at success
              | ok rightValue =>
                  have rightValueTyped := rightIH fuel environment rightValue rightResult
                  cases rightValueTyped
                  rename_i y
                  rw [evaluate_mul_of_children program store environment fuel leftTerm rightTerm x y
                    leftResult rightResult] at success
                  cases success
                  exact .int
  | le leftTyped rightTyped leftIH rightIH =>
      rename_i leftTerm rightTerm
      cases fuel with
      | zero => simp [evaluate] at success
      | succ fuel =>
          cases leftResult : evaluate program store fuel environment leftTerm with
          | error fault => simp [evaluate, leftResult, bind, Except.bind] at success
          | ok leftValue =>
              have leftValueTyped := leftIH fuel environment leftValue leftResult
              cases leftValueTyped
              rename_i x
              cases rightResult : evaluate program store fuel environment rightTerm with
              | error fault => simp [evaluate, leftResult, rightResult, bind, Except.bind] at success
              | ok rightValue =>
                  have rightValueTyped := rightIH fuel environment rightValue rightResult
                  cases rightValueTyped
                  rename_i y
                  rw [evaluate_le_of_children program store environment fuel leftTerm rightTerm x y
                    leftResult rightResult] at success
                  cases success
                  exact .bool

  | intEq leftTyped rightTyped leftIH rightIH =>
      rename_i leftTerm rightTerm
      cases fuel with
      | zero => simp [evaluate] at success
      | succ fuel =>
          cases leftResult : evaluate program store fuel environment leftTerm with
          | error fault => simp [evaluate, leftResult, bind, Except.bind] at success
          | ok leftValue =>
              have leftValueTyped := leftIH fuel environment leftValue leftResult
              cases leftValueTyped
              rename_i x
              cases rightResult : evaluate program store fuel environment rightTerm with
              | error fault => simp [evaluate, leftResult, rightResult, bind, Except.bind] at success
              | ok rightValue =>
                  have rightValueTyped := rightIH fuel environment rightValue rightResult
                  cases rightValueTyped
                  rename_i y
                  rw [evaluate_intEq_of_children program store environment fuel leftTerm rightTerm x y
                    leftResult rightResult] at success
                  cases success
                  exact .bool
  | floatBin leftTyped rightTyped leftIH rightIH =>
      rename_i leftTerm rightTerm op
      cases fuel with
      | zero => simp [evaluate] at success
      | succ fuel =>
          cases leftResult : evaluate program store fuel environment leftTerm with
          | error fault => simp [evaluate, leftResult, bind, Except.bind] at success
          | ok leftValue =>
              have leftValueTyped := leftIH fuel environment leftValue leftResult
              cases leftValueTyped
              rename_i x
              cases rightResult : evaluate program store fuel environment rightTerm with
              | error fault => simp [evaluate, leftResult, rightResult, bind, Except.bind] at success
              | ok rightValue =>
                  have rightValueTyped := rightIH fuel environment rightValue rightResult
                  cases rightValueTyped
                  rename_i y
                  simp [evaluate, leftResult, rightResult, bind, Except.bind] at success
                  cases success
                  exact .float

/-- A context-indexed extension of the closed arithmetic fragment. It adds
de Bruijn local reads and one-binding parallel lets, so the let body can
actually refer to the value introduced by its initializer. -/
inductive ContextualArithmeticTerm (globals : List Surface.Signature) (assignment : Nat → Surface.Ty) :
    List Surface.Ty → Term → Surface.Ty → Prop where
  | closed : ArithmeticTerm term type →
      ContextualArithmeticTerm globals assignment context term type
  | lambda : Surface.HasType globals 0 context
        (.lam parameters result body) (.fn parameters result) →
      ContextualArithmeticTerm globals assignment context
        (.lam parameters.length (PolyIR.erase body))
        (.fn (Surface.interpretTypes assignment parameters)
          (Surface.interpret assignment result))
  | var : context[index]? = some type →
      ContextualArithmeticTerm globals assignment context (.var index)
        (Surface.interpret assignment type)
  | letOne : ContextualArithmeticTerm globals assignment context initializer
        (Surface.interpret assignment initializerType) →
      ContextualArithmeticTerm globals assignment (initializerType :: context) body resultType →
      ContextualArithmeticTerm globals assignment context (.letMany [initializer] body) resultType
  | letTwo : ContextualArithmeticTerm globals assignment context first
        (Surface.interpret assignment firstType) →
      ContextualArithmeticTerm globals assignment context second
        (Surface.interpret assignment secondType) →
      ContextualArithmeticTerm globals assignment (firstType :: secondType :: context) body resultType →
      ContextualArithmeticTerm globals assignment context (.letMany [first, second] body) resultType
  | add : ContextualArithmeticTerm globals assignment context left .integer →
      ContextualArithmeticTerm globals assignment context right .integer →
      ContextualArithmeticTerm globals assignment context (.add left right) .integer
  | sub : ContextualArithmeticTerm globals assignment context left .integer →
      ContextualArithmeticTerm globals assignment context right .integer →
      ContextualArithmeticTerm globals assignment context (.sub left right) .integer
  | mul : ContextualArithmeticTerm globals assignment context left .integer →
      ContextualArithmeticTerm globals assignment context right .integer →
      ContextualArithmeticTerm globals assignment context (.mul left right) .integer
  | le : ContextualArithmeticTerm globals assignment context left .integer →
      ContextualArithmeticTerm globals assignment context right .integer →
      ContextualArithmeticTerm globals assignment context (.le left right) .boolean
  | intEq : ContextualArithmeticTerm globals assignment context left .integer →
      ContextualArithmeticTerm globals assignment context right .integer →
      ContextualArithmeticTerm globals assignment context (.intEq left right) .boolean
  | floatBin (operation : Surface.FloatBinOp) :
      ContextualArithmeticTerm globals assignment context left .float →
      ContextualArithmeticTerm globals assignment context right .float →
      ContextualArithmeticTerm globals assignment context (.floatBin operation left right) .float
  | some : ContextualArithmeticTerm globals assignment context value elementType →
      ContextualArithmeticTerm globals assignment context (.some value) (.option elementType)
  | cons : ContextualArithmeticTerm globals assignment context head elementType →
      ContextualArithmeticTerm globals assignment context tail (.list elementType) →
      ContextualArithmeticTerm globals assignment context (.cons head tail) (.list elementType)
  | matchOption : ContextualArithmeticTerm globals assignment context target
        (.option (Surface.interpret assignment elementType)) →
      ContextualArithmeticTerm globals assignment context empty resultType →
      ContextualArithmeticTerm globals assignment (elementType :: context) full resultType →
      ContextualArithmeticTerm globals assignment context (.matchOption target empty full) resultType
  | matchList : ContextualArithmeticTerm globals assignment context target
        (.list (Surface.interpret assignment elementType)) →
      ContextualArithmeticTerm globals assignment context empty resultType →
      ContextualArithmeticTerm globals assignment
        (elementType :: .list elementType :: context) full resultType →
      ContextualArithmeticTerm globals assignment context (.matchList target empty full) resultType
  | ite : ContextualArithmeticTerm globals assignment context condition .boolean →
      ContextualArithmeticTerm globals assignment context yes resultType →
      ContextualArithmeticTerm globals assignment context no resultType →
      ContextualArithmeticTerm globals assignment context (.ite condition yes no) resultType

/-- Extend the contextual arithmetic fragment with references to entries in a
typed GlobalIR layout. This admits function values at their declared
polymorphic signature while retaining the existing proof for local arithmetic
and constructor expressions. -/
inductive ContextualGlobalArithmeticTerm (globals : List Surface.Signature)
    (assignment : Nat → Surface.Ty) : List Surface.Ty → Term → Surface.Ty → Prop where
  | arithmetic : ContextualArithmeticTerm globals assignment context term type →
      ContextualGlobalArithmeticTerm globals assignment context term type
  | global : globals[index]? = some signature →
      ContextualGlobalArithmeticTerm globals assignment context (.global index)
        (.fn (Surface.interpretTypes assignment signature.parameters)
          (Surface.interpret assignment signature.result))

inductive ContextualGlobalArithmeticTerms (globals : List Surface.Signature)
    (assignment : Nat → Surface.Ty) (context : List Surface.Ty) :
    List Surface.Ty → List Term → Prop where
  | nil : ContextualGlobalArithmeticTerms globals assignment context [] []
  | cons : ContextualGlobalArithmeticTerm globals assignment context term
        (Surface.interpret assignment type) →
      ContextualGlobalArithmeticTerms globals assignment context types terms →
      ContextualGlobalArithmeticTerms globals assignment context (type :: types)
        (term :: terms)

/-- A typed runtime fragment that adds lowered value reads to the existing
global arithmetic/function-reference fragment. Getter references are the
zero-argument applications emitted by `lowerGlobalReads`. -/
inductive ContextualGlobalRuntimeTerm (globals : List Surface.Signature)
    (assignment : Nat → Surface.Ty) (definitions : Surface.Definitions)
    (slotTypes : List Surface.Ty) (functionSources : List (Nat × Nat))
    (program : List Definition) (context : List Surface.Ty) : Term → Surface.Ty → Prop where
  | arithmetic {term type} :
      ContextualGlobalArithmeticTerm globals assignment context term type →
      ContextualGlobalRuntimeTerm globals assignment definitions slotTypes functionSources
        program context term type
  | getter {index slot type} :
      program[index]? = some (.getter slot) →
      globals[index]? = some ⟨0, [], type⟩ →
      ContextualGlobalRuntimeTerm globals assignment definitions slotTypes functionSources
        program context (.app (.global index) []) type
  | lambdaApplication {parameters : List Nat} {arguments : List Term}
      {argumentTypes : List Surface.Ty} {body : Term} {resultType : Surface.Ty} :
      ContextualGlobalArithmeticTerms globals assignment context argumentTypes arguments →
      argumentTypes.length = parameters.length →
      ContextualGlobalArithmeticTerm globals assignment (argumentTypes ++ context)
        body (Surface.interpret assignment resultType) →
      ContextualGlobalRuntimeTerm globals assignment definitions slotTypes functionSources
        program context (.app (.lam parameters.length body) arguments)
        (Surface.interpret assignment resultType)

/-- Sequences may mix arithmetic/global-reference terms with lowered getter
reads; as with the ordinary global sequence fragment, the final term fixes
the result type. -/
inductive ContextualGlobalRuntimeSequence (globals : List Surface.Signature)
    (assignment : Nat → Surface.Ty) (definitions : Surface.Definitions)
    (slotTypes : List Surface.Ty) (functionSources : List (Nat × Nat))
    (program : List Definition) (context : List Surface.Ty) :
    List Term → Surface.Ty → Prop where
  | last : ContextualGlobalRuntimeTerm globals assignment definitions slotTypes
      functionSources program context term type →
      ContextualGlobalRuntimeSequence globals assignment definitions slotTypes
        functionSources program context [term] type
  | skip : ContextualGlobalRuntimeTerm globals assignment definitions slotTypes
      functionSources program context first firstType →
      ContextualGlobalRuntimeSequence globals assignment definitions slotTypes
        functionSources program context rest resultType →
      ContextualGlobalRuntimeSequence globals assignment definitions slotTypes
        functionSources program context (first :: rest) resultType

inductive ContextualGlobalRuntimeTerms (globals : List Surface.Signature)
    (assignment : Nat → Surface.Ty) (definitions : Surface.Definitions)
    (slotTypes : List Surface.Ty) (functionSources : List (Nat × Nat))
    (program : List Definition) (context : List Surface.Ty) :
    List Surface.Ty → List Term → Prop where
  | nil : ContextualGlobalRuntimeTerms globals assignment definitions slotTypes
      functionSources program context [] []
  | cons : ContextualGlobalRuntimeTerm globals assignment definitions slotTypes
      functionSources program context term (Surface.interpret assignment type) →
      ContextualGlobalRuntimeTerms globals assignment definitions slotTypes
        functionSources program context types terms →
      ContextualGlobalRuntimeTerms globals assignment definitions slotTypes
        functionSources program context (type :: types) (term :: terms)

inductive ContextualGlobalRuntimeIntegerOptionalCall (globals : List Surface.Signature)
    (assignment : Nat → Surface.Ty) (definitions : Surface.Definitions)
    (slotTypes : List Surface.Ty) (functionSources : List (Nat × Nat))
    (program : List Definition) (context : List Surface.Ty) :
    IntegerOptionalOperation → Term → Term → Prop where
  | mk (operation : IntegerOptionalOperation) (left right : Term) :
      ContextualGlobalRuntimeTerm globals assignment definitions slotTypes
        functionSources program context left .integer →
      ContextualGlobalRuntimeTerm globals assignment definitions slotTypes
        functionSources program context right .integer →
      ContextualGlobalRuntimeIntegerOptionalCall globals assignment definitions slotTypes
        functionSources program context operation left right

/-- Runtime typing for Float comparisons whose operands may read initialized
global value slots through generated getters. -/
inductive ContextualGlobalRuntimeFloatComparisonCall (globals : List Surface.Signature)
    (assignment : Nat → Surface.Ty) (definitions : Surface.Definitions)
    (slotTypes : List Surface.Ty) (functionSources : List (Nat × Nat))
    (program : List Definition) (context : List Surface.Ty) :
    FloatComparisonOperation → Term → Term → Prop where
  | mk (operation : FloatComparisonOperation) (left right : Term) :
      ContextualGlobalRuntimeTerm globals assignment definitions slotTypes
        functionSources program context left .float →
      ContextualGlobalRuntimeTerm globals assignment definitions slotTypes
        functionSources program context right .float →
      ContextualGlobalRuntimeFloatComparisonCall globals assignment definitions slotTypes
        functionSources program context operation left right

/-- Runtime typing for Float arithmetic over operands that may include global
getter reads. -/
inductive ContextualGlobalRuntimeFloatBinCall (globals : List Surface.Signature)
    (assignment : Nat → Surface.Ty) (definitions : Surface.Definitions)
    (slotTypes : List Surface.Ty) (functionSources : List (Nat × Nat))
    (program : List Definition) (context : List Surface.Ty) :
    Surface.FloatBinOp → Term → Term → Prop where
  | mk (operation : Surface.FloatBinOp) (left right : Term) :
      ContextualGlobalRuntimeTerm globals assignment definitions slotTypes
        functionSources program context left .float →
      ContextualGlobalRuntimeTerm globals assignment definitions slotTypes
        functionSources program context right .float →
      ContextualGlobalRuntimeFloatBinCall globals assignment definitions slotTypes
        functionSources program context operation left right

/-- Contextual typing for the native Option-valued integer operations. Their
runtime boundary is `evaluateIntegerOptionalCall`, which evaluates both
integer operands and represents division by zero as `none`. -/
inductive ContextualGlobalIntegerOptionalCall (globals : List Surface.Signature)
    (assignment : Nat → Surface.Ty) (context : List Surface.Ty) :
    IntegerOptionalOperation → Term → Term → Prop where
  | mk (operation : IntegerOptionalOperation) (left right : Term) :
      ContextualGlobalArithmeticTerm globals assignment context left .integer →
      ContextualGlobalArithmeticTerm globals assignment context right .integer →
      ContextualGlobalIntegerOptionalCall globals assignment context operation left right

/-- Pointwise contextual typing for the initializer list of a parallel let.
Each initializer is checked in the original context, matching `letMany`
evaluation; the resulting types are prepended to the body's context. -/
inductive ContextualArithmeticTerms (globals : List Surface.Signature) (assignment : Nat → Surface.Ty)
    (context : List Surface.Ty) : List Surface.Ty → List Term → Prop where
  | nil : ContextualArithmeticTerms globals assignment context [] []
  | cons : ContextualArithmeticTerm globals assignment context term
        (Surface.interpret assignment type) →
      ContextualArithmeticTerms globals assignment context types terms →
      ContextualArithmeticTerms globals assignment context (type :: types) (term :: terms)

/-- A nonempty sequence whose last expression determines the result type.
Earlier expressions run in the same environment and their values are dropped. -/
inductive ContextualArithmeticSequence (globals : List Surface.Signature) (assignment : Nat → Surface.Ty)
    (context : List Surface.Ty) : List Term → Surface.Ty → Prop where
  | last : ContextualArithmeticTerm globals assignment context term type →
      ContextualArithmeticSequence globals assignment context [term] type
  | skip : ContextualArithmeticTerm globals assignment context first firstType →
      ContextualArithmeticSequence globals assignment context rest resultType →
      ContextualArithmeticSequence globals assignment context (first :: rest) resultType

inductive ContextualGlobalArithmeticSequence (globals : List Surface.Signature)
    (assignment : Nat → Surface.Ty) (context : List Surface.Ty) :
    List Term → Surface.Ty → Prop where
  | last : ContextualGlobalArithmeticTerm globals assignment context term type →
      ContextualGlobalArithmeticSequence globals assignment context [term] type
  | skip : ContextualGlobalArithmeticTerm globals assignment context first firstType →
      ContextualGlobalArithmeticSequence globals assignment context rest resultType →
      ContextualGlobalArithmeticSequence globals assignment context (first :: rest) resultType

/-- Successful evaluation preserves types for closed arithmetic terms plus
typed local variables and one-binding lets whose body may use the new binder. -/
theorem evaluate_contextualArithmetic_preserves_type
    (globals : List Surface.Signature) (assignment : Nat → Surface.Ty)
    (program : List Definition) (store : Store) (context : List Surface.Ty)
    (fuel : Nat) (environment : List Value) (term : Term) (type : Surface.Ty)
    (typing : ContextualArithmeticTerm globals assignment context term type)
    (environmentTyped : ValuesTyped globals environment
      (Surface.interpretTypes assignment context))
    (value : Value)
    (success : evaluate program store fuel environment term = .ok value) :
    PolyIR.ValueTyped globals value type := by
  induction typing generalizing fuel environment value with
  | closed arithmetic =>
      exact evaluate_arithmetic_preserves_type globals program store fuel
        environment _ _ arithmetic value success
  | var typeFound =>
      rename_i localContext localIndex localType
      exact evaluate_var_preserves_type globals assignment localContext program store
        fuel localIndex environment value localType environmentTyped typeFound success
  | lambda typing =>
      rename_i localContext parameters result body
      cases fuel with
      | zero => simp [evaluate] at success
      | succ fuel =>
          obtain ⟨evaluated, valueTyped⟩ := evaluate_typed_lambda_preserves_type
            globals assignment localContext parameters result program store fuel
            environment body typing environmentTyped
          rw [evaluated] at success
          cases success
          exact valueTyped
  | add leftTyped rightTyped leftIH rightIH =>
      rename_i left right
      cases fuel with
      | zero => simp [evaluate] at success
      | succ fuel =>
          cases leftResult : evaluate program store fuel environment left with
          | error fault => simp [evaluate, leftResult, bind, Except.bind] at success
          | ok leftValue =>
              have leftValueTyped := leftIH fuel environment environmentTyped leftValue leftResult
              cases leftValueTyped
              rename_i x
              cases rightResult : evaluate program store fuel environment right with
              | error fault => simp [evaluate, leftResult, rightResult, bind, Except.bind] at success
              | ok rightValue =>
                  have rightValueTyped := rightIH fuel environment environmentTyped rightValue rightResult
                  cases rightValueTyped
                  rename_i y
                  rw [evaluate_add_of_children program store environment fuel left right x y
                    leftResult rightResult] at success
                  cases success
                  exact .int
  | sub leftTyped rightTyped leftIH rightIH =>
      rename_i left right
      cases fuel with
      | zero => simp [evaluate] at success
      | succ fuel =>
          cases leftResult : evaluate program store fuel environment left with
          | error fault => simp [evaluate, leftResult, bind, Except.bind] at success
          | ok leftValue =>
              have leftValueTyped := leftIH fuel environment environmentTyped leftValue leftResult
              cases leftValueTyped
              rename_i x
              cases rightResult : evaluate program store fuel environment right with
              | error fault => simp [evaluate, leftResult, rightResult, bind, Except.bind] at success
              | ok rightValue =>
                  have rightValueTyped := rightIH fuel environment environmentTyped rightValue rightResult
                  cases rightValueTyped
                  rename_i y
                  rw [evaluate_sub_of_children program store environment fuel left right x y
                    leftResult rightResult] at success
                  cases success
                  exact .int
  | mul leftTyped rightTyped leftIH rightIH =>
      rename_i left right
      cases fuel with
      | zero => simp [evaluate] at success
      | succ fuel =>
          cases leftResult : evaluate program store fuel environment left with
          | error fault => simp [evaluate, leftResult, bind, Except.bind] at success
          | ok leftValue =>
              have leftValueTyped := leftIH fuel environment environmentTyped leftValue leftResult
              cases leftValueTyped
              rename_i x
              cases rightResult : evaluate program store fuel environment right with
              | error fault => simp [evaluate, leftResult, rightResult, bind, Except.bind] at success
              | ok rightValue =>
                  have rightValueTyped := rightIH fuel environment environmentTyped rightValue rightResult
                  cases rightValueTyped
                  rename_i y
                  rw [evaluate_mul_of_children program store environment fuel left right x y
                    leftResult rightResult] at success
                  cases success
                  exact .int
  | le leftTyped rightTyped leftIH rightIH =>
      rename_i left right
      cases fuel with
      | zero => simp [evaluate] at success
      | succ fuel =>
          cases leftResult : evaluate program store fuel environment left with
          | error fault => simp [evaluate, leftResult, bind, Except.bind] at success
          | ok leftValue =>
              have leftValueTyped := leftIH fuel environment environmentTyped leftValue leftResult
              cases leftValueTyped
              rename_i x
              cases rightResult : evaluate program store fuel environment right with
              | error fault => simp [evaluate, leftResult, rightResult, bind, Except.bind] at success
              | ok rightValue =>
                  have rightValueTyped := rightIH fuel environment environmentTyped rightValue rightResult
                  cases rightValueTyped
                  rename_i y
                  rw [evaluate_le_of_children program store environment fuel left right x y
                    leftResult rightResult] at success
                  cases success
                  exact .bool
  | intEq leftTyped rightTyped leftIH rightIH =>
      rename_i left right
      cases fuel with
      | zero => simp [evaluate] at success
      | succ fuel =>
          cases leftResult : evaluate program store fuel environment left with
          | error fault => simp [evaluate, leftResult, bind, Except.bind] at success
          | ok leftValue =>
              have leftValueTyped := leftIH fuel environment environmentTyped leftValue leftResult
              cases leftValueTyped
              rename_i x
              cases rightResult : evaluate program store fuel environment right with
              | error fault => simp [evaluate, leftResult, rightResult, bind, Except.bind] at success
              | ok rightValue =>
                  have rightValueTyped := rightIH fuel environment environmentTyped rightValue rightResult
                  cases rightValueTyped
                  rename_i y
                  rw [evaluate_intEq_of_children program store environment fuel left right x y
                    leftResult rightResult] at success
                  cases success
                  exact .bool
  | floatBin operation leftTyped rightTyped leftIH rightIH =>
      rename_i left right
      cases fuel with
      | zero => simp [evaluate] at success
      | succ fuel =>
          cases leftResult : evaluate program store fuel environment left with
          | error fault => simp [evaluate, leftResult, bind, Except.bind] at success
          | ok leftValue =>
              have leftValueTyped := leftIH fuel environment environmentTyped leftValue leftResult
              cases leftValueTyped
              rename_i x
              cases rightResult : evaluate program store fuel environment right with
              | error fault => simp [evaluate, leftResult, rightResult, bind, Except.bind] at success
              | ok rightValue =>
                  have rightValueTyped := rightIH fuel environment environmentTyped rightValue rightResult
                  cases rightValueTyped
                  rename_i y
                  rw [evaluate_floatBin_of_children program store environment fuel operation left right x y
                    leftResult rightResult] at success
                  cases success
                  exact .float
  | some childTyped childIH =>
      rename_i childTerm elementType
      cases fuel with
      | zero => simp [evaluate] at success
      | succ fuel =>
          cases childResult : evaluate program store fuel environment childTerm with
          | error fault => simp [evaluate, childResult, bind, Except.bind] at success
          | ok childValue =>
              have childValueTyped := childIH fuel environment environmentTyped
                childValue childResult
              rw [show evaluate program store (fuel + 1) environment (.some childTerm) =
                .ok (.some childValue) by
                  simp [evaluate, childResult, bind, Except.bind, Except.pure] <;> rfl] at success
              cases success
              exact .some childValueTyped
  | cons headTyped tailTyped headIH tailIH =>
      rename_i headTerm elementType tailTerm
      cases fuel with
      | zero => simp [evaluate] at success
      | succ fuel =>
          cases headResult : evaluate program store fuel environment headTerm with
          | error fault => simp [evaluate, headResult, bind, Except.bind] at success
          | ok headValue =>
              have headValueTyped := headIH fuel environment environmentTyped
                headValue headResult
              cases tailResult : evaluate program store fuel environment tailTerm with
              | error fault => simp [evaluate, headResult, tailResult, bind, Except.bind] at success
              | ok tailValue =>
                  have tailValueTyped := tailIH fuel environment environmentTyped
                    tailValue tailResult
                  rw [show evaluate program store (fuel + 1) environment
                    (.cons headTerm tailTerm) = .ok (.cons headValue tailValue) by
                      simp [evaluate, headResult, tailResult, bind, Except.bind,
                        Except.pure] <;> rfl] at success
                  cases success
                  exact .cons headValueTyped tailValueTyped
  | matchOption targetTyped emptyTyped fullTyped targetIH emptyIH fullIH =>
      rename_i localContext target elementType empty resultType full
      cases fuel with
      | zero => simp [evaluate] at success
      | succ fuel =>
          cases targetResult : evaluate program store fuel environment target with
          | error fault => simp [evaluate, targetResult, bind, Except.bind] at success
          | ok targetValue =>
              have targetValueTyped := targetIH fuel environment environmentTyped
                targetValue targetResult
              cases targetValueTyped with
              | none =>
                  cases emptyResult : evaluate program store fuel environment empty with
                  | error fault => simp [evaluate, targetResult, emptyResult,
                      bind, Except.bind] at success
                  | ok resultValue =>
                      have resultTyped := emptyIH fuel environment environmentTyped
                        resultValue emptyResult
                      simp [evaluate, targetResult, emptyResult, bind, Except.bind,
                        Except.pure] at success
                      cases success
                      exact resultTyped
              | some payloadTyped =>
                  rename_i payloadValue
                  have bodyEnvironmentTyped : ValuesTyped globals
                      (payloadValue :: environment)
                      (Surface.interpretTypes assignment (elementType :: localContext)) := by
                    simpa [Surface.interpretTypes] using
                      (ValuesTyped.cons payloadTyped environmentTyped)
                  cases fullResult : evaluate program store fuel
                      (payloadValue :: environment) full with
                  | error fault => simp [evaluate, targetResult, fullResult,
                      bind, Except.bind] at success
                  | ok resultValue =>
                      have resultTyped := fullIH fuel (payloadValue :: environment)
                        bodyEnvironmentTyped resultValue fullResult
                      simp [evaluate, targetResult, fullResult, bind, Except.bind,
                        Except.pure] at success
                      cases success
                      exact resultTyped
  | matchList targetTyped emptyTyped fullTyped targetIH emptyIH fullIH =>
      rename_i localContext target elementType empty resultType full
      cases fuel with
      | zero => simp [evaluate] at success
      | succ fuel =>
          cases targetResult : evaluate program store fuel environment target with
          | error fault => simp [evaluate, targetResult, bind, Except.bind] at success
          | ok targetValue =>
              have targetValueTyped := targetIH fuel environment environmentTyped
                targetValue targetResult
              cases targetValueTyped with
              | nil =>
                  cases emptyResult : evaluate program store fuel environment empty with
                  | error fault => simp [evaluate, targetResult, emptyResult,
                      bind, Except.bind] at success
                  | ok resultValue =>
                      have resultTyped := emptyIH fuel environment environmentTyped
                        resultValue emptyResult
                      simp [evaluate, targetResult, emptyResult, bind, Except.bind,
                        Except.pure] at success
                      cases success
                      exact resultTyped
              | cons headTyped tailTyped =>
                  rename_i headValue tailValue
                  have bodyEnvironmentTyped : ValuesTyped globals
                      (headValue :: tailValue :: environment)
                      (Surface.interpretTypes assignment
                        (elementType :: .list elementType :: localContext)) := by
                    simpa [Surface.interpretTypes, Surface.interpret] using
                      (ValuesTyped.cons headTyped (.cons tailTyped environmentTyped))
                  cases fullResult : evaluate program store fuel
                      (headValue :: tailValue :: environment) full with
                  | error fault => simp [evaluate, targetResult, fullResult,
                      bind, Except.bind] at success
                  | ok resultValue =>
                      have resultTyped := fullIH fuel
                        (headValue :: tailValue :: environment)
                        bodyEnvironmentTyped resultValue fullResult
                      simp [evaluate, targetResult, fullResult, bind, Except.bind,
                        Except.pure] at success
                      cases success
                      exact resultTyped
  | ite conditionTyped yesTyped noTyped conditionIH yesIH noIH =>
      rename_i condition yes resultType no
      cases fuel with
      | zero => simp [evaluate] at success
      | succ fuel =>
          cases conditionResult : evaluate program store fuel environment condition with
          | error fault => simp [evaluate, conditionResult, bind, Except.bind] at success
          | ok conditionValue =>
              have conditionValueTyped := conditionIH fuel environment environmentTyped
                conditionValue conditionResult
              have conditionBoolExists : ∃ b, conditionValue = .bool b := by
                cases conditionValueTyped
                exact ⟨_, rfl⟩
              obtain ⟨conditionBool, conditionValueEq⟩ := conditionBoolExists
              cases conditionValueEq
              cases conditionBool with
              | false =>
                  cases noResult : evaluate program store fuel environment no with
                  | error fault => simp [evaluate, conditionResult, noResult,
                      bind, Except.bind] at success
                  | ok noValue =>
                      have noValueTyped := noIH fuel environment environmentTyped
                        noValue noResult
                      simp [evaluate, conditionResult, noResult, bind, Except.bind,
                        Except.pure] at success
                      cases success
                      exact noValueTyped
              | true =>
                  cases yesResult : evaluate program store fuel environment yes with
                  | error fault => simp [evaluate, conditionResult, yesResult,
                      bind, Except.bind] at success
                  | ok yesValue =>
                      have yesValueTyped := yesIH fuel environment environmentTyped
                        yesValue yesResult
                      simp [evaluate, conditionResult, yesResult, bind, Except.bind,
                        Except.pure] at success
                      cases success
                      exact yesValueTyped
  | letTwo firstTyped secondTyped bodyTyped firstIH secondIH bodyIH =>
      rename_i localContext first firstType second secondType body resultType
      cases fuel with
      | zero => simp [evaluate] at success
      | succ fuel =>
          change (do
            let bindings ← evaluateArgs program store fuel environment [first, second]
            evaluate program store fuel (bindings ++ environment) body) = .ok value at success
          cases argumentsResult : evaluateArgs program store fuel environment
              [first, second] with
          | error fault =>
              simp [argumentsResult, bind, Except.bind] at success
          | ok values =>
              obtain ⟨firstValue, secondValue, remaining, valuesEq, _fuelEq,
                firstResult, secondResult⟩ := evaluateArgs_pair_result program store fuel
                  environment first second values argumentsResult
              subst values
              have firstValueTyped := firstIH (remaining + 2) environment
                environmentTyped firstValue firstResult
              have secondValueTyped := secondIH (remaining + 1) environment
                environmentTyped secondValue secondResult
              have bodyEnvironmentTyped : ValuesTyped globals
                  (firstValue :: secondValue :: environment)
                  (Surface.interpretTypes assignment
                    (firstType :: secondType :: localContext)) := by
                simpa [Surface.interpretTypes] using
                  (ValuesTyped.cons firstValueTyped (.cons secondValueTyped environmentTyped))
              have bodySuccess : evaluate program store fuel
                  (firstValue :: secondValue :: environment) body = .ok value := by
                simpa [argumentsResult, bind, Except.bind, Except.pure] using success
              exact bodyIH fuel (firstValue :: secondValue :: environment)
                bodyEnvironmentTyped value bodySuccess
  | letOne initializerTyped bodyTyped initializerIH bodyIH =>
      rename_i localContext initializer initializerType body resultType
      cases fuel with
      | zero => simp [evaluate] at success
      | succ fuel =>
          change (do
            let bindings ← evaluateArgs program store fuel environment [initializer]
            evaluate program store fuel (bindings ++ environment) body) = .ok value at success
          cases argumentsResult : evaluateArgs program store fuel environment
              [initializer] with
          | error fault =>
              simp [argumentsResult, bind, Except.bind] at success
          | ok values =>
              obtain ⟨initializerValue, remaining, valuesEq, _fuelEq, initializerResult⟩ :=
                evaluateArgs_singleton_result program store fuel environment initializer
                  values argumentsResult
              subst values
              have initializerValueTyped := initializerIH (remaining + 1)
                environment environmentTyped initializerValue initializerResult
              have bodyEnvironmentTyped : ValuesTyped globals
                  (initializerValue :: environment)
                  (Surface.interpretTypes assignment (initializerType :: localContext)) := by
                simpa [Surface.interpretTypes] using
                  (ValuesTyped.cons initializerValueTyped environmentTyped)
              have bodySuccess : evaluate program store fuel
                  (initializerValue :: environment) body = .ok value := by
                simpa [argumentsResult, bind, Except.bind, Except.pure,
                  List.singleton_append] using success
              exact bodyIH fuel (initializerValue :: environment) bodyEnvironmentTyped
                value bodySuccess

/-- The contextual arithmetic preservation result also covers global function
references when the runtime table is obtained from a `GlobalProgramTyped`
layout. -/
theorem evaluate_contextualGlobalArithmeticTerm_preserves_type
    (globals : List Surface.Signature) (assignment : Nat → Surface.Ty)
    (definitions : Surface.Definitions) (slotTypes : List Surface.Ty)
    (functionSources : List (Nat × Nat)) (program : List Definition)
    (programTyped : GlobalProgramTyped globals definitions slotTypes functionSources program)
    (store : Store) (context : List Surface.Ty) (fuel : Nat)
    (environment : List Value) (environmentTyped : ValuesTyped globals environment
      (Surface.interpretTypes assignment context)) (term : Term) (type : Surface.Ty)
    (typing : ContextualGlobalArithmeticTerm globals assignment context term type)
    (value : Value)
    (success : evaluate program store fuel environment term = .ok value) :
    PolyIR.ValueTyped globals value type := by
  cases typing with
  | arithmetic arithmeticTyping =>
      exact evaluate_contextualArithmetic_preserves_type globals assignment program store
        context fuel environment term type arithmeticTyping environmentTyped value success
  | global signatureFound =>
      rename_i index signature
      obtain ⟨evaluated, valueTyped⟩ := evaluate_global_value_preserves_type
        globals definitions slotTypes functionSources program programTyped assignment store
        (fuel - 1) index environment signature signatureFound
      have fuelPositive : 0 < fuel := by
        cases fuel with
        | zero => simp [evaluate] at success
        | succ fuel => omega
      have evalEq : fuel = (fuel - 1) + 1 := by omega
      rw [evalEq, evaluated] at success
      cases success
      exact valueTyped

/-- A successful typed contextual quotient/remainder call has integer-typed
operands and an Option Integer result. This connects the native call helper
to the same contextual fragment used for GlobalIR function bodies. -/
theorem evaluate_contextualGlobalIntegerOptionalCall_preserves_type
    (globals : List Surface.Signature) (assignment : Nat → Surface.Ty)
    (definitions : Surface.Definitions) (slotTypes : List Surface.Ty)
    (functionSources : List (Nat × Nat)) (program : List Definition)
    (programTyped : GlobalProgramTyped globals definitions slotTypes functionSources program)
    (store : Store) (context : List Surface.Ty) (fuel : Nat)
    (environment : List Value)
    (environmentTyped : ValuesTyped globals environment
      (Surface.interpretTypes assignment context))
    (operation : IntegerOptionalOperation) (left right : Term)
    (typing : ContextualGlobalIntegerOptionalCall globals assignment context operation left right)
    (result : Value)
    (success : evaluateIntegerOptionalCall program store operation fuel environment left right =
      .ok result) :
    PolyIR.ValueTyped globals result (.option .integer) ∧
      ∃ leftValue rightValue,
        evaluate program store (fuel - 1) environment left = .ok leftValue ∧
        evaluate program store (fuel - 1) environment right = .ok rightValue ∧
        PolyIR.ValueTyped globals leftValue .integer ∧
        PolyIR.ValueTyped globals rightValue .integer := by
  cases fuel with
  | zero => simp [evaluateIntegerOptionalCall] at success
  | succ fuel =>
      obtain ⟨leftInteger, rightInteger, leftEval, rightEval, resultEq⟩ :=
        (evaluateIntegerOptionalCall_success_iff program store operation fuel environment
          left right result).mp (by simpa using success)
      cases typing with
      | mk leftTyping rightTyping =>
          have leftTyped := evaluate_contextualGlobalArithmeticTerm_preserves_type
            globals assignment definitions slotTypes functionSources program programTyped
            store context fuel environment environmentTyped left .integer leftTyping
            (.int leftInteger) leftEval
          have rightTyped := evaluate_contextualGlobalArithmeticTerm_preserves_type
            globals assignment definitions slotTypes functionSources program programTyped
            store context fuel environment environmentTyped right .integer rightTyping
            (.int rightInteger) rightEval
          refine ⟨?_, .int leftInteger, .int rightInteger, ?_, ?_, ?_, ?_⟩
          · rw [resultEq]
            exact integerOptionalRuntimeValue_typed globals operation.toPrimitive
              leftInteger rightInteger
          · exact leftEval
          · exact rightEval
          · exact leftTyped
          · exact rightTyped

theorem evaluate_contextualGlobalArithmeticTerms_preserves_type
    (globals : List Surface.Signature) (assignment : Nat → Surface.Ty)
    (definitions : Surface.Definitions) (slotTypes : List Surface.Ty)
    (functionSources : List (Nat × Nat)) (program : List Definition)
    (programTyped : GlobalProgramTyped globals definitions slotTypes functionSources program)
    (store : Store) (context : List Surface.Ty) (fuel : Nat)
    (environment : List Value) (environmentTyped : ValuesTyped globals environment
      (Surface.interpretTypes assignment context)) (terms : List Term) (types : List Surface.Ty)
    (typing : ContextualGlobalArithmeticTerms globals assignment context types terms)
    (values : List Value)
    (success : evaluateArgs program store fuel environment terms = .ok values) :
    ValuesTyped globals values (Surface.interpretTypes assignment types) := by
  induction typing generalizing fuel values with
  | nil =>
      cases fuel with
      | zero => simp [evaluateArgs] at success
      | succ fuel =>
          have valuesEmpty : values = [] := by
            simpa [evaluateArgs, pure, Except.pure] using success.symm
          subst values
          exact .nil
  | cons headTyped tailTyped tailIH =>
      rename_i headTerm headType tailTypes tailTerms
      cases fuel with
      | zero => simp [evaluateArgs] at success
      | succ fuel =>
          cases headResult : evaluate program store fuel environment headTerm with
          | error fault => simp [evaluateArgs, headResult, bind, Except.bind] at success
          | ok headValue =>
              cases tailResult : evaluateArgs program store fuel environment tailTerms with
              | error fault =>
                  simp [evaluateArgs, headResult, tailResult, bind, Except.bind] at success
              | ok tailValues =>
                  have headTypedValue := evaluate_contextualGlobalArithmeticTerm_preserves_type
                    globals assignment definitions slotTypes functionSources program programTyped
                    store context fuel environment environmentTyped headTerm
                    (Surface.interpret assignment headType) headTyped headValue headResult
                  have tailTypedValues := tailIH fuel tailValues tailResult
                  have valuesEq : values = headValue :: tailValues := by
                    simpa [evaluateArgs, headResult, tailResult, bind, Except.bind,
                      Except.pure, Pure.pure, List.cons.injEq] using success.symm
                  subst values
                  simpa [Surface.interpretTypes] using
                    (ValuesTyped.cons headTypedValue tailTypedValues)

/-- Parallel `letMany` preserves types when its initializers and body may
refer to typed GlobalIR entries. Initializers are checked and evaluated in
the incoming local context; their resulting values are then prepended in the
same order used by the evaluator before checking the body. -/
theorem evaluate_contextualGlobalLetMany_preserves_type
    (globals : List Surface.Signature) (assignment : Nat → Surface.Ty)
    (definitions : Surface.Definitions) (slotTypes : List Surface.Ty)
    (functionSources : List (Nat × Nat)) (program : List Definition)
    (programTyped : GlobalProgramTyped globals definitions slotTypes functionSources program)
    (store : Store) (context types : List Surface.Ty)
    (fuel : Nat) (environment : List Value) (initializers : List Term)
    (body : Term) (resultType : Surface.Ty)
    (initializersTyped : ContextualGlobalArithmeticTerms globals assignment context types initializers)
    (bodyTyped : ContextualGlobalArithmeticTerm globals assignment (types ++ context) body resultType)
    (environmentTyped : ValuesTyped globals environment
      (Surface.interpretTypes assignment context))
    (value : Value)
    (success : evaluate program store fuel environment
      (.letMany initializers body) = .ok value) :
    PolyIR.ValueTyped globals value resultType := by
  cases fuel with
  | zero => simp [evaluate, bind, Except.bind, Except.pure] at success
  | succ fuel =>
      change (do
        let bindings ← evaluateArgs program store fuel environment initializers
        evaluate program store fuel (bindings ++ environment) body) = .ok value at success
      cases initializersResult : evaluateArgs program store fuel environment initializers with
      | error fault => simp [initializersResult, bind, Except.bind] at success
      | ok bindings =>
          have bindingsTyped := evaluate_contextualGlobalArithmeticTerms_preserves_type
            globals assignment definitions slotTypes functionSources program programTyped
            store context fuel environment environmentTyped initializers types
            initializersTyped bindings initializersResult
          have bodyEnvironmentTyped : ValuesTyped globals (bindings ++ environment)
              (Surface.interpretTypes assignment (types ++ context)) := by
            simpa [Surface.interpretTypes_append] using
              (ValuesTyped.append bindingsTyped environmentTyped)
          have bodySuccess : evaluate program store fuel (bindings ++ environment) body =
              .ok value := by
            simpa [initializersResult, bind, Except.bind, Except.pure] using success
          exact evaluate_contextualGlobalArithmeticTerm_preserves_type globals assignment
            definitions slotTypes functionSources program programTyped store (types ++ context)
            fuel (bindings ++ environment) bodyEnvironmentTyped body resultType bodyTyped value
            bodySuccess

theorem evaluate_contextualGlobalArithmeticSequence_preserves_type
    (globals : List Surface.Signature) (assignment : Nat → Surface.Ty)
    (definitions : Surface.Definitions) (slotTypes : List Surface.Ty)
    (functionSources : List (Nat × Nat)) (program : List Definition)
    (programTyped : GlobalProgramTyped globals definitions slotTypes functionSources program)
    (store : Store) (context : List Surface.Ty) (fuel : Nat)
    (environment : List Value) (previous : Value) (terms : List Term)
    (resultType : Surface.Ty)
    (typing : ContextualGlobalArithmeticSequence globals assignment context terms resultType)
    (environmentTyped : ValuesTyped globals environment
      (Surface.interpretTypes assignment context))
    (value : Value)
    (success : evaluateSequence program store fuel environment previous terms = .ok value) :
    PolyIR.ValueTyped globals value resultType := by
  induction typing generalizing fuel environment previous value with
  | last expressionTyped =>
      rename_i term type
      cases fuel with
      | zero => simp [evaluateSequence] at success
      | succ fuel =>
          cases fuel with
          | zero => simp [evaluateSequence, evaluate, bind, Except.bind] at success
          | succ fuel =>
              cases expressionResult : evaluate program store (fuel + 1) environment term with
              | error fault => simp [evaluateSequence, expressionResult, bind, Except.bind] at success
              | ok expressionValue =>
                  have expressionValueTyped := evaluate_contextualGlobalArithmeticTerm_preserves_type
                    globals assignment definitions slotTypes functionSources program programTyped
                    store context (fuel + 1) environment environmentTyped term type expressionTyped
                    expressionValue expressionResult
                  have valueEq : value = expressionValue := by
                    simpa [evaluateSequence, expressionResult, bind, Except.bind,
                      Except.pure, Pure.pure] using success.symm
                  cases valueEq
                  exact expressionValueTyped
  | skip firstTyped restTyped restIH =>
      rename_i firstTerm firstType restTerms resultType
      cases fuel with
      | zero => simp [evaluateSequence] at success
      | succ fuel =>
          cases firstResult : evaluate program store fuel environment firstTerm with
          | error fault => simp [evaluateSequence, firstResult, bind, Except.bind] at success
          | ok firstValue =>
              have restSuccess : evaluateSequence program store fuel environment
                  firstValue restTerms = .ok value := by
                simpa [evaluateSequence, firstResult, bind, Except.bind] using success
              exact restIH fuel environment firstValue environmentTyped value restSuccess

theorem evaluate_contextualGlobalBegin_preserves_type
    (globals : List Surface.Signature) (assignment : Nat → Surface.Ty)
    (definitions : Surface.Definitions) (slotTypes : List Surface.Ty)
    (functionSources : List (Nat × Nat)) (program : List Definition)
    (programTyped : GlobalProgramTyped globals definitions slotTypes functionSources program)
    (store : Store) (context : List Surface.Ty) (fuel : Nat)
    (environment : List Value) (first : Term) (firstType : Surface.Ty)
    (rest : List Term) (resultType : Surface.Ty)
    (firstTyped : ContextualGlobalArithmeticTerm globals assignment context first firstType)
    (restTyped : ContextualGlobalArithmeticSequence globals assignment context rest resultType)
    (environmentTyped : ValuesTyped globals environment
      (Surface.interpretTypes assignment context))
    (value : Value)
    (success : evaluate program store fuel environment (.begin first rest) = .ok value) :
    PolyIR.ValueTyped globals value resultType := by
  cases fuel with
  | zero => simp [evaluate] at success
  | succ fuel =>
      change (do
        let firstValue ← evaluate program store fuel environment first
        evaluateSequence program store fuel environment firstValue rest) = .ok value at success
      cases firstResult : evaluate program store fuel environment first with
      | error fault => simp [firstResult, bind, Except.bind] at success
      | ok firstValue =>
          have restSuccess : evaluateSequence program store fuel environment
              firstValue rest = .ok value := by
            simpa [firstResult, bind, Except.bind] using success
          exact evaluate_contextualGlobalArithmeticSequence_preserves_type
            globals assignment definitions slotTypes functionSources program programTyped
            store context fuel environment firstValue rest resultType restTyped environmentTyped
            value restSuccess

theorem evaluate_contextualGlobalBegin_empty_preserves_type
    (globals : List Surface.Signature) (assignment : Nat → Surface.Ty)
    (definitions : Surface.Definitions) (slotTypes : List Surface.Ty)
    (functionSources : List (Nat × Nat)) (program : List Definition)
    (programTyped : GlobalProgramTyped globals definitions slotTypes functionSources program)
    (store : Store) (context : List Surface.Ty) (fuel : Nat)
    (environment : List Value) (first : Term) (type : Surface.Ty)
    (firstTyped : ContextualGlobalArithmeticTerm globals assignment context first type)
    (environmentTyped : ValuesTyped globals environment
      (Surface.interpretTypes assignment context))
    (value : Value)
    (success : evaluate program store fuel environment (.begin first []) = .ok value) :
    PolyIR.ValueTyped globals value type := by
  cases fuel with
  | zero => simp [evaluate] at success
  | succ fuel =>
      cases fuel with
      | zero => simp [evaluate, evaluateSequence, bind, Except.bind] at success
      | succ fuel =>
          cases firstResult : evaluate program store (fuel + 1) environment first with
          | error fault => simp [evaluate, evaluateSequence, firstResult,
              bind, Except.bind] at success
          | ok firstValue =>
              have firstValueTyped := evaluate_contextualGlobalArithmeticTerm_preserves_type
                globals assignment definitions slotTypes functionSources program programTyped
                store context (fuel + 1) environment environmentTyped first type firstTyped
                firstValue firstResult
              have valueEq : value = firstValue := by
                simpa [evaluate, evaluateSequence, firstResult, bind, Except.bind,
                  Except.pure, Pure.pure] using success.symm
              cases valueEq
              exact firstValueTyped

/-- A zero-argument GlobalIR function call preserves the result type when its
runtime body is in the contextual global arithmetic fragment. This composes
global dispatch with the body evaluator's preservation theorem. -/
theorem evaluate_contextual_zero_arity_global_call_preserves_type
    (globals : List Surface.Signature) (assignment : Nat → Surface.Ty)
    (definitions : Surface.Definitions) (slotTypes : List Surface.Ty)
    (functionSources : List (Nat × Nat)) (program : List Definition)
    (programTyped : GlobalProgramTyped globals definitions slotTypes functionSources program)
    (store : Store) (fuel index : Nat) (runtime : RuntimeDefinition)
    (fuelPositive : 0 < fuel)
    (runtimeEntry : program[index]? = some (.function runtime))
    (arityZero : runtime.arity = 0) (resultType : Surface.Ty)
    (bodyTyping : ContextualGlobalArithmeticTerm globals assignment [] runtime.body resultType)
    (bodySuccess : evaluate program store fuel [] runtime.body = .ok value)
    (callSuccess : evaluate program store (fuel + 1) []
      (.app (.global index) []) = .ok value) :
    PolyIR.ValueTyped globals value resultType := by
  have runtimeAt : program[index]? = some (.function runtime) := runtimeEntry
  have functionSuccess : evaluate program store fuel [] (.global index) = .ok (.global index) := by
    cases fuel with
    | zero => omega
    | succ remaining => simp [evaluate, runtimeAt, pure, Except.pure]
  have argumentsSuccess : evaluateArgs program store fuel [] [] = .ok [] := by
    cases fuel with
    | zero => omega
    | succ remaining => simp [evaluateArgs, pure, Except.pure]
  have callEq : evaluate program store (fuel + 1) [] (.app (.global index) []) =
      evaluate program store fuel [] runtime.body := by
    simp [evaluate, functionSuccess, argumentsSuccess, runtimeAt, arityZero,
      bind, Except.bind, Except.pure, pure]
  rw [callEq, bodySuccess] at callSuccess
  cases callSuccess
  exact evaluate_contextualGlobalArithmeticTerm_preserves_type globals assignment definitions
    slotTypes functionSources program programTyped store [] fuel [] .nil runtime.body resultType
    bodyTyping value bodySuccess

/-- The same preservation argument for arbitrary arity: every argument is
evaluated in the caller environment, its contextual typing establishes the
argument value types, and the typed function body runs in that value
environment. -/
theorem evaluate_contextual_global_call_preserves_type
    (globals : List Surface.Signature) (assignment : Nat → Surface.Ty)
    (definitions : Surface.Definitions) (slotTypes : List Surface.Ty)
    (functionSources : List (Nat × Nat)) (program : List Definition)
    (programTyped : GlobalProgramTyped globals definitions slotTypes functionSources program)
    (store : Store) (fuel index : Nat) (runtime : RuntimeDefinition)
    (fuelPositive : 0 < fuel)
    (runtimeEntry : program[index]? = some (.function runtime))
    (terms : List Term) (argumentTypes : List Surface.Ty)
    (argumentsTyping : ContextualGlobalArithmeticTerms globals assignment [] argumentTypes terms)
    (values : List Value)
    (argumentsSuccess : evaluateArgs program store fuel [] terms = .ok values)
    (arity : runtime.arity = values.length) (resultType : Surface.Ty)
    (bodyTyping : ContextualGlobalArithmeticTerm globals assignment argumentTypes
      runtime.body resultType)
    (bodySuccess : evaluate program store fuel values runtime.body = .ok result) :
    evaluate program store (fuel + 1) [] (.app (.global index) terms) = .ok result →
      PolyIR.ValueTyped globals result resultType := by
  intro callSuccess
  have runtimeAt : program[index]? = some (.function runtime) := runtimeEntry
  have functionSuccess : evaluate program store fuel [] (.global index) = .ok (.global index) := by
    cases fuel with
    | zero => omega
    | succ remaining => simp [evaluate, runtimeAt, pure, Except.pure]
  have argumentsTyped := evaluate_contextualGlobalArithmeticTerms_preserves_type
    globals assignment definitions slotTypes functionSources program programTyped store [] fuel []
    .nil terms argumentTypes argumentsTyping values argumentsSuccess
  have callEq : evaluate program store (fuel + 1) [] (.app (.global index) terms) =
      evaluate program store fuel values runtime.body := by
    simp [evaluate, functionSuccess, argumentsSuccess, runtimeAt, arity,
      bind, Except.bind, Except.pure, pure]
  rw [callEq, bodySuccess] at callSuccess
  cases callSuccess
  exact evaluate_contextualGlobalArithmeticTerm_preserves_type globals assignment definitions
    slotTypes functionSources program programTyped store argumentTypes fuel values argumentsTyped
    runtime.body resultType bodyTyping result bodySuccess

/-- Global function calls also preserve their result type when their argument
expressions read from an arbitrary typed caller environment. The function
body still runs in the argument environment, as required by GlobalIR. -/
theorem evaluate_contextual_global_call_preserves_type_in_context
    (globals : List Surface.Signature) (assignment : Nat → Surface.Ty)
    (definitions : Surface.Definitions) (slotTypes : List Surface.Ty)
    (functionSources : List (Nat × Nat)) (program : List Definition)
    (programTyped : GlobalProgramTyped globals definitions slotTypes functionSources program)
    (store : Store) (callerContext : List Surface.Ty)
    (callerEnvironment : List Value)
    (callerEnvironmentTyped : ValuesTyped globals callerEnvironment
      (Surface.interpretTypes assignment callerContext))
    (fuel index : Nat) (runtime : RuntimeDefinition)
    (fuelPositive : 0 < fuel)
    (runtimeEntry : program[index]? = some (.function runtime))
    (terms : List Term) (argumentTypes : List Surface.Ty)
    (argumentsTyping : ContextualGlobalArithmeticTerms globals assignment callerContext
      argumentTypes terms)
    (values : List Value)
    (argumentsSuccess : evaluateArgs program store fuel callerEnvironment terms = .ok values)
    (arity : runtime.arity = values.length) (resultType : Surface.Ty)
    (bodyTyping : ContextualGlobalArithmeticTerm globals assignment argumentTypes
      runtime.body resultType)
    (bodySuccess : evaluate program store fuel values runtime.body = .ok result)
    (callSuccess : evaluate program store (fuel + 1) callerEnvironment
      (.app (.global index) terms) = .ok result) :
    PolyIR.ValueTyped globals result resultType := by
  have runtimeAt : program[index]? = some (.function runtime) := runtimeEntry
  have functionSuccess : evaluate program store fuel callerEnvironment (.global index) =
      .ok (.global index) := by
    cases fuel with
    | zero => omega
    | succ remaining => simp [evaluate, runtimeAt, pure, Except.pure]
  have argumentsTyped := evaluate_contextualGlobalArithmeticTerms_preserves_type
    globals assignment definitions slotTypes functionSources program programTyped store
    callerContext fuel callerEnvironment callerEnvironmentTyped terms argumentTypes
    argumentsTyping values argumentsSuccess
  have callEq : evaluate program store (fuel + 1) callerEnvironment
      (.app (.global index) terms) = evaluate program store fuel values runtime.body := by
    simp [evaluate, functionSuccess, argumentsSuccess, runtimeAt, arity,
      bind, Except.bind, Except.pure, pure]
  rw [callEq, bodySuccess] at callSuccess
  cases callSuccess
  exact evaluate_contextualGlobalArithmeticTerm_preserves_type globals assignment
    definitions slotTypes functionSources program programTyped store argumentTypes fuel values
    argumentsTyped runtime.body resultType bodyTyping result bodySuccess

/-- Type preservation for an application whose computed callee evaluates to
a typed global function value. This extends the direct-global-call theorem to
callees produced by arbitrary evaluation, while argument and body typing are
kept explicit at this fragment boundary. -/
theorem evaluate_contextual_computed_global_call_preserves_type
    (globals : List Surface.Signature) (assignment : Nat → Surface.Ty)
    (definitions : Surface.Definitions) (slotTypes : List Surface.Ty)
    (functionSources : List (Nat × Nat)) (program : List Definition)
    (programTyped : GlobalProgramTyped globals definitions slotTypes functionSources program)
    (store : Store) (callerContext : List Surface.Ty)
    (callerEnvironment : List Value)
    (callerEnvironmentTyped : ValuesTyped globals callerEnvironment
      (Surface.interpretTypes assignment callerContext))
    (fuel index : Nat) (runtime : RuntimeDefinition) (function : Term)
    (functionSuccess : evaluate program store fuel callerEnvironment function =
      .ok (.global index))
    (fuelPositive : 0 < fuel)
    (runtimeEntry : program[index]? = some (.function runtime))
    (terms : List Term) (argumentTypes : List Surface.Ty)
    (argumentsTyping : ContextualGlobalArithmeticTerms globals assignment callerContext
      argumentTypes terms)
    (values : List Value)
    (argumentsSuccess : evaluateArgs program store fuel callerEnvironment terms = .ok values)
    (arityAgreement : runtime.arity = values.length) (resultType : Surface.Ty)
    (bodyTyping : ContextualGlobalArithmeticTerm globals assignment argumentTypes
      runtime.body resultType)
    (callSuccess : evaluate program store (fuel + 1) callerEnvironment
      (.app function terms) = .ok result) :
    PolyIR.ValueTyped globals result resultType := by
  have functionGlobalSuccess : evaluate program store fuel callerEnvironment (.global index) =
      .ok (.global index) := by
    cases fuel with
    | zero => omega
    | succ remaining => simp [evaluate, runtimeEntry, pure, Except.pure]
  have computedCallEq : evaluate program store (fuel + 1) callerEnvironment
      (.app function terms) = evaluate program store fuel values runtime.body := by
    simp [evaluate, functionSuccess, argumentsSuccess, runtimeEntry, arityAgreement,
      bind, Except.bind, Except.pure, pure]
  rw [computedCallEq] at callSuccess
  have directCallEq : evaluate program store (fuel + 1) callerEnvironment
      (.app (.global index) terms) = evaluate program store fuel values runtime.body := by
    simp [evaluate, functionGlobalSuccess, argumentsSuccess, runtimeEntry, arityAgreement,
      bind, Except.bind, Except.pure, pure]
  have directCallSuccess : evaluate program store (fuel + 1) callerEnvironment
      (.app (.global index) terms) = .ok result := by
    rw [directCallEq]
    exact callSuccess
  exact evaluate_contextual_global_call_preserves_type_in_context globals assignment
    definitions slotTypes functionSources program programTyped store callerContext
    callerEnvironment callerEnvironmentTyped fuel index runtime fuelPositive runtimeEntry
    terms argumentTypes argumentsTyping values argumentsSuccess arityAgreement resultType
    bodyTyping callSuccess directCallSuccess

/-- The evaluator's closure-call rule preserves an already established result
type for any captured body. This separates the call-by-value application
step from the fragment-specific proof that the closure body is type safe. -/
theorem evaluate_closure_application_preserves_type_from_body_result
    (globals : List Surface.Signature) (program : List Definition) (store : Store)
    (fuel : Nat) (callerEnvironment captured : List Value)
    (function : Term) (arity : Nat) (body : Term)
    (functionSuccess : evaluate program store fuel callerEnvironment function =
      .ok (.closure arity body captured))
    (terms : List Term) (values : List Value)
    (argumentsSuccess : evaluateArgs program store fuel callerEnvironment terms = .ok values)
    (arityAgreement : values.length = arity)
    (result : Value) (resultType : Surface.Ty)
    (bodySuccess : evaluate program store fuel (values ++ captured) body = .ok result)
    (bodyResultTyped : PolyIR.ValueTyped globals result resultType) :
    evaluate program store (fuel + 1) callerEnvironment (.app function terms) = .ok result ∧
      PolyIR.ValueTyped globals result resultType := by
  have callEq : evaluate program store (fuel + 1) callerEnvironment
      (.app function terms) = evaluate program store fuel (values ++ captured) body := by
    simp [evaluate, functionSuccess, argumentsSuccess, arityAgreement, bind, Except.bind,
      Except.pure, pure]
  exact ⟨callEq.trans bodySuccess, bodyResultTyped⟩

/-- A syntactic lambda application preserves the body result type for
arbitrary arity when its arguments and body are in the contextual global
arithmetic fragment. This composes lambda creation, argument evaluation,
closure arity, captured-environment typing, and body evaluation. -/
theorem evaluate_contextual_lambda_application_preserves_type
    (globals : List Surface.Signature) (assignment : Nat → Surface.Ty)
    (definitions : Surface.Definitions) (slotTypes : List Surface.Ty)
    (functionSources : List (Nat × Nat)) (program : List Definition)
    (programTyped : GlobalProgramTyped globals definitions slotTypes functionSources program)
    (store : Store) (context argumentTypes : List Surface.Ty)
    (fuel : Nat) (environment : List Value)
    (environmentTyped : ValuesTyped globals environment
      (Surface.interpretTypes assignment context))
    (parameters : List Nat) (body : Surface.Expr) (terms : List Term)
    (argumentsTyping : ContextualGlobalArithmeticTerms globals assignment context
      argumentTypes terms)
    (arity : argumentTypes.length = parameters.length)
    (values : List Value)
    (argumentsSuccess : evaluateArgs program store fuel environment terms = .ok values)
    (resultType : Surface.Ty)
    (bodyTyping : ContextualGlobalArithmeticTerm globals assignment
      (argumentTypes ++ context) (PolyIR.erase body)
      (Surface.interpret assignment resultType))
    (result : Value)
    (bodySuccess : evaluate program store fuel (values ++ environment)
      (PolyIR.erase body) = .ok result)
    (callSuccess : evaluate program store (fuel + 1) environment
      (.app (.lam parameters.length (PolyIR.erase body)) terms) = .ok result) :
    PolyIR.ValueTyped globals result (Surface.interpret assignment resultType) := by
  have argumentsTyped := evaluate_contextualGlobalArithmeticTerms_preserves_type
    globals assignment definitions slotTypes functionSources program programTyped store
    context fuel environment environmentTyped terms argumentTypes argumentsTyping values
    argumentsSuccess
  have bodyEnvironmentTyped : ValuesTyped globals (values ++ environment)
      (Surface.interpretTypes assignment (argumentTypes ++ context)) := by
    simpa [Surface.interpretTypes_append] using
      (ValuesTyped.append argumentsTyped environmentTyped)
  have functionSuccess : evaluate program store fuel environment
      (.lam parameters.length (PolyIR.erase body)) =
        .ok (.closure parameters.length (PolyIR.erase body) environment) := by
    cases fuel with
    | zero => simp [evaluate, bind, Except.bind] at callSuccess
    | succ remaining => simp [evaluate, pure, Except.pure]
  have valuesArity : values.length = parameters.length := by
    calc
      values.length = (Surface.interpretTypes assignment argumentTypes).length :=
        argumentsTyped.length
      _ = argumentTypes.length := Surface.interpretTypes_length assignment argumentTypes
      _ = parameters.length := arity
  have bodyResultTyped := evaluate_contextualGlobalArithmeticTerm_preserves_type
    globals assignment definitions slotTypes functionSources program programTyped store
    (argumentTypes ++ context) fuel
    (values ++ environment) bodyEnvironmentTyped (PolyIR.erase body)
    (Surface.interpret assignment resultType) bodyTyping result bodySuccess
  obtain ⟨callResult, callTyped⟩ :=
    evaluate_closure_application_preserves_type_from_body_result globals program store fuel
      environment environment (.lam parameters.length (PolyIR.erase body)) parameters.length
      (PolyIR.erase body) functionSuccess terms values argumentsSuccess valuesArity result
      (Surface.interpret assignment resultType) bodySuccess bodyResultTyped
  rw [callSuccess] at callResult
  cases callResult
  exact callTyped

/-- Type preservation for application of an arbitrary evaluated closure.
The closure may capture an environment distinct from the caller environment;
argument and captured values are typed independently, then combined in the
same order used by GlobalIR evaluation. -/
theorem evaluate_contextual_closure_application_preserves_type
    (globals : List Surface.Signature) (assignment : Nat → Surface.Ty)
    (definitions : Surface.Definitions) (slotTypes : List Surface.Ty)
    (functionSources : List (Nat × Nat)) (program : List Definition)
    (programTyped : GlobalProgramTyped globals definitions slotTypes functionSources program)
    (store : Store) (callerContext argumentTypes capturedTypes : List Surface.Ty)
    (fuel : Nat) (callerEnvironment captured : List Value)
    (callerEnvironmentTyped : ValuesTyped globals callerEnvironment
      (Surface.interpretTypes assignment callerContext))
    (function : Term) (arity : Nat) (body : Term)
    (functionSuccess : evaluate program store fuel callerEnvironment function =
      .ok (.closure arity body captured))
    (terms : List Term)
    (argumentsTyping : ContextualGlobalArithmeticTerms globals assignment callerContext
      argumentTypes terms)
    (values : List Value)
    (argumentsSuccess : evaluateArgs program store fuel callerEnvironment terms = .ok values)
    (arityAgreement : argumentTypes.length = arity)
    (capturedTyped : ValuesTyped globals captured
      (Surface.interpretTypes assignment capturedTypes))
    (resultType : Surface.Ty)
    (bodyTyping : ContextualGlobalArithmeticTerm globals assignment
      (argumentTypes ++ capturedTypes) body (Surface.interpret assignment resultType))
    (result : Value)
    (bodySuccess : evaluate program store fuel (values ++ captured) body = .ok result) :
    evaluate program store (fuel + 1) callerEnvironment (.app function terms) = .ok result ∧
      PolyIR.ValueTyped globals result (Surface.interpret assignment resultType) := by
  have argumentsTyped := evaluate_contextualGlobalArithmeticTerms_preserves_type
    globals assignment definitions slotTypes functionSources program programTyped store
    callerContext fuel callerEnvironment callerEnvironmentTyped terms argumentTypes
    argumentsTyping values argumentsSuccess
  have bodyEnvironmentTyped : ValuesTyped globals (values ++ captured)
      (Surface.interpretTypes assignment (argumentTypes ++ capturedTypes)) := by
    simpa [Surface.interpretTypes_append] using
      (ValuesTyped.append argumentsTyped capturedTyped)
  have valuesArity : values.length = arity := by
    calc
      values.length = (Surface.interpretTypes assignment argumentTypes).length :=
        argumentsTyped.length
      _ = argumentTypes.length := Surface.interpretTypes_length assignment argumentTypes
      _ = arity := arityAgreement
  have bodyResultTyped := evaluate_contextualGlobalArithmeticTerm_preserves_type
    globals assignment definitions slotTypes functionSources program programTyped store
    (argumentTypes ++ capturedTypes) fuel
    (values ++ captured) bodyEnvironmentTyped body (Surface.interpret assignment resultType)
    bodyTyping result bodySuccess
  exact evaluate_closure_application_preserves_type_from_body_result globals program store fuel
    callerEnvironment captured function arity body functionSuccess terms values argumentsSuccess
    valuesArity result (Surface.interpret assignment resultType) bodySuccess bodyResultTyped

/- Any successful parallel evaluation of a pointwise-typed initializer list
produces values with the corresponding declared types. -/
theorem evaluate_contextualArithmeticTerms_preserves_type
    (globals : List Surface.Signature) (assignment : Nat → Surface.Ty)
    (program : List Definition) (store : Store) (context : List Surface.Ty)
    (fuel : Nat) (environment : List Value) (terms : List Term) (types : List Surface.Ty)
    (typing : ContextualArithmeticTerms globals assignment context types terms)
    (environmentTyped : ValuesTyped globals environment
      (Surface.interpretTypes assignment context))
    (values : List Value)
    (success : evaluateArgs program store fuel environment terms = .ok values) :
    ValuesTyped globals values (Surface.interpretTypes assignment types) := by
  induction typing generalizing fuel values with
  | nil =>
      cases values with
      | nil => exact .nil
      | cons value values =>
          cases fuel with
          | zero => simp [evaluateArgs] at success
          | succ fuel =>
              change Except.ok [] = Except.ok (value :: values) at success
              cases success
  | cons headTyped tailTyped tailIH =>
      rename_i headTerm headType tailTypes tailTerms
      cases fuel with
      | zero => simp [evaluateArgs] at success
      | succ fuel =>
          cases headResult : evaluate program store fuel environment headTerm with
          | error fault => simp [evaluateArgs, headResult, bind, Except.bind] at success
          | ok headValue =>
              cases tailResult : evaluateArgs program store fuel environment tailTerms with
              | error fault => simp [evaluateArgs, headResult, tailResult,
                  bind, Except.bind] at success
              | ok tailValues =>
                  have headValueTyped := evaluate_contextualArithmetic_preserves_type
                    globals assignment program store context fuel environment headTerm
                    (Surface.interpret assignment headType) headTyped
                    environmentTyped headValue headResult
                  have tailValuesTyped := tailIH fuel tailValues tailResult
                  have resultEq : values = headValue :: tailValues := by
                    simpa [evaluateArgs, headResult, tailResult, bind, Except.bind,
                      Except.pure, Pure.pure] using success.symm
                  subst values
                  simpa [Surface.interpretTypes] using
                    (ValuesTyped.cons headValueTyped tailValuesTyped)

/-- A successful `evaluateSequence` over a contextually typed nonempty list
returns a value of the final expression's type. -/
theorem evaluate_contextualArithmeticSequence_preserves_type
    (globals : List Surface.Signature) (assignment : Nat → Surface.Ty)
    (program : List Definition) (store : Store) (context : List Surface.Ty)
    (fuel : Nat) (environment : List Value) (previous : Value)
    (terms : List Term) (resultType : Surface.Ty)
    (typing : ContextualArithmeticSequence globals assignment context terms resultType)
    (environmentTyped : ValuesTyped globals environment
      (Surface.interpretTypes assignment context))
    (value : Value)
    (success : evaluateSequence program store fuel environment previous terms = .ok value) :
    PolyIR.ValueTyped globals value resultType := by
  induction typing generalizing fuel environment previous value with
  | last expressionTyped =>
      rename_i term type
      cases fuel with
      | zero => simp [evaluateSequence] at success
      | succ fuel =>
          cases fuel with
          | zero => simp [evaluateSequence, evaluate, bind, Except.bind] at success
          | succ fuel =>
              cases expressionResult : evaluate program store (fuel + 1) environment term with
              | error fault => simp [evaluateSequence, expressionResult, bind, Except.bind] at success
              | ok expressionValue =>
                  have expressionValueTyped := evaluate_contextualArithmetic_preserves_type
                    globals assignment program store context (fuel + 1) environment term type
                    expressionTyped environmentTyped expressionValue expressionResult
                  have valueEq : value = expressionValue := by
                    simpa [evaluateSequence, expressionResult, bind, Except.bind,
                      Except.pure, Pure.pure] using success.symm
                  cases valueEq
                  exact expressionValueTyped
  | skip firstTyped restTyped restIH =>
      rename_i firstTerm firstType restTerms resultType
      cases fuel with
      | zero => simp [evaluateSequence] at success
      | succ fuel =>
          cases firstResult : evaluate program store fuel environment firstTerm with
          | error fault => simp [evaluateSequence, firstResult, bind, Except.bind] at success
          | ok firstValue =>
              have restSuccess : evaluateSequence program store fuel environment
                  firstValue restTerms = .ok value := by
                simpa [evaluateSequence, firstResult, bind, Except.bind] using success
              exact restIH fuel environment firstValue environmentTyped value restSuccess

/-- A contextually typed `begin` with a nonempty tail preserves the tail's
final type; the first expression and every earlier tail expression are
evaluated in the same local environment and discarded. -/
theorem evaluate_contextualBegin_preserves_type
    (globals : List Surface.Signature) (assignment : Nat → Surface.Ty)
    (program : List Definition) (store : Store) (context : List Surface.Ty)
    (fuel : Nat) (environment : List Value) (first : Term) (firstType : Surface.Ty)
    (rest : List Term) (resultType : Surface.Ty)
    (firstTyped : ContextualArithmeticTerm globals assignment context first firstType)
    (restTyped : ContextualArithmeticSequence globals assignment context rest resultType)
    (environmentTyped : ValuesTyped globals environment
      (Surface.interpretTypes assignment context))
    (value : Value)
    (success : evaluate program store fuel environment (.begin first rest) = .ok value) :
    PolyIR.ValueTyped globals value resultType := by
  cases fuel with
  | zero => simp [evaluate] at success
  | succ fuel =>
      change (do
        let firstValue ← evaluate program store fuel environment first
        evaluateSequence program store fuel environment firstValue rest) = .ok value at success
      cases firstResult : evaluate program store fuel environment first with
      | error fault => simp [firstResult, bind, Except.bind] at success
      | ok firstValue =>
          have restSuccess : evaluateSequence program store fuel environment
              firstValue rest = .ok value := by
            simpa [firstResult, bind, Except.bind] using success
          exact evaluate_contextualArithmeticSequence_preserves_type
            globals assignment program store context fuel environment firstValue rest
            resultType restTyped environmentTyped value restSuccess

/-- The empty-tail `begin` returns its first expression's value, subject to
the evaluator's fuel check for the empty sequence. -/
theorem evaluate_contextualBegin_empty_preserves_type
    (globals : List Surface.Signature) (assignment : Nat → Surface.Ty)
    (program : List Definition) (store : Store) (context : List Surface.Ty)
    (fuel : Nat) (environment : List Value) (first : Term) (type : Surface.Ty)
    (firstTyped : ContextualArithmeticTerm globals assignment context first type)
    (environmentTyped : ValuesTyped globals environment
      (Surface.interpretTypes assignment context))
    (value : Value)
    (success : evaluate program store fuel environment (.begin first []) = .ok value) :
    PolyIR.ValueTyped globals value type := by
  cases fuel with
  | zero => simp [evaluate] at success
  | succ fuel =>
      cases fuel with
      | zero => simp [evaluate, evaluateSequence, bind, Except.bind] at success
      | succ fuel =>
          cases firstResult : evaluate program store (fuel + 1) environment first with
          | error fault => simp [evaluate, evaluateSequence, firstResult,
              bind, Except.bind] at success
          | ok firstValue =>
              have firstValueTyped := evaluate_contextualArithmetic_preserves_type
                globals assignment program store context (fuel + 1) environment first type
                firstTyped environmentTyped firstValue firstResult
              have valueEq : value = firstValue := by
                simpa [evaluate, evaluateSequence, firstResult, bind, Except.bind,
                  Except.pure, Pure.pure] using success.symm
              cases valueEq
              exact firstValueTyped

/-- Type preservation for arbitrary-length parallel `letMany` terms. All
initializers are typed in the incoming context, and their evaluated values are
prepended in order before the body is evaluated. -/
theorem evaluate_contextualLetMany_preserves_type
    (globals : List Surface.Signature) (assignment : Nat → Surface.Ty)
    (program : List Definition) (store : Store) (context types : List Surface.Ty)
    (fuel : Nat) (environment : List Value) (initializers : List Term)
    (body : Term) (resultType : Surface.Ty)
    (initializersTyped : ContextualArithmeticTerms globals assignment context types initializers)
    (bodyTyped : ContextualArithmeticTerm globals assignment (types ++ context) body resultType)
    (environmentTyped : ValuesTyped globals environment
      (Surface.interpretTypes assignment context))
    (value : Value)
    (success : evaluate program store fuel environment
      (.letMany initializers body) = .ok value) :
    PolyIR.ValueTyped globals value resultType := by
  cases fuel with
  | zero => simp [evaluate] at success
  | succ fuel =>
      change (do
        let bindings ← evaluateArgs program store fuel environment initializers
        evaluate program store fuel (bindings ++ environment) body) = .ok value at success
      cases initializersResult : evaluateArgs program store fuel environment initializers with
      | error fault => simp [initializersResult, bind, Except.bind] at success
      | ok bindings =>
          have bindingsTyped := evaluate_contextualArithmeticTerms_preserves_type
            globals assignment program store context fuel environment initializers types
            initializersTyped environmentTyped bindings initializersResult
          have bodyEnvironmentTyped : ValuesTyped globals (bindings ++ environment)
              (Surface.interpretTypes assignment (types ++ context)) := by
            simpa [Surface.interpretTypes_append] using
              (ValuesTyped.append bindingsTyped environmentTyped)
          have bodySuccess : evaluate program store fuel (bindings ++ environment) body =
              .ok value := by
            simpa [initializersResult, bind, Except.bind, Except.pure] using success
          exact evaluate_contextualArithmetic_preserves_type globals assignment program store
            (types ++ context) fuel (bindings ++ environment) body resultType
            bodyTyped bodyEnvironmentTyped value bodySuccess

def initializeValues (program : List Definition) : Nat → Store → Nat → List Term → Except Fault Store
  | 0, _, _, _ => .error (.core .outOfFuel)
  | _ + 1, store, _, [] => pure store
  | fuel + 1, store, slot, head :: tail => do
    let value ← evaluate program store fuel [] head
    initializeValues program fuel (store.set slot (some value)) (slot + 1) tail

/- Divergence for the fuel-bounded evaluator means that every positive fuel
budget is exhausted. This definition is specific to the deterministic
big-step model; it does not identify finite runtime faults as divergence. -/
def Diverges (program : List Definition) (store : Store) (env : List Value) (term : Term) : Prop :=
  ∀ fuel, 0 < fuel → evaluate program store fuel env term = .error (.core .outOfFuel)

theorem recursive_getter_call_diverges :
    Diverges [.function ⟨0, .app (.global 0) []⟩] [] [] (.app (.global 0) []) := by
  intro fuel positive
  cases fuel with
  | zero => omega
  | succ fuel =>
    induction fuel with
    | zero => simp [evaluate, evaluateArgs, bind, Except.bind]
    | succ fuel ih =>
      have ih' := ih (by omega)
      have globalEval :
          evaluate [.function ⟨0, .app (.global 0) []⟩] [] (fuel + 1) [] (.global 0) =
            .ok (.global 0) := by simp [evaluate, getElem?_def, pure, Except.pure]
      have emptyArgs :
          evaluateArgs [.function ⟨0, .app (.global 0) []⟩] [] (fuel + 1) [] [] = .ok [] := by
        simp [evaluateArgs, pure, Except.pure]
      simp [evaluate, globalEval, emptyArgs, getElem?_def, bind, Except.bind, ih']

theorem initializeValues_stops_on_divergence (program : List Definition)
    (store : Store) (slot fuel : Nat) (head : Term) (tail : List Term)
    (diverges : Diverges program store [] head) :
    initializeValues program (fuel + 1) store slot (head :: tail) =
      .error (.core .outOfFuel) := by
  cases fuel with
  | zero => simp [initializeValues, evaluate, bind, Except.bind]
  | succ fuel =>
    have step := diverges (fuel + 1) (by omega)
    simp [initializeValues, step, bind, Except.bind]

/-- A divergent initializer after any successfully evaluated prefix exhausts
the sequential initializer walk. The prefix may commit arbitrary values to
the store; divergence is stated against that resulting store. -/
theorem initializeValues_stops_on_divergence_after_prefix
    (program : List Definition) (fuel : Nat) (store : Store) (slot : Nat)
    (initializersBefore : List Term) (head : Term) (tail : List Term) (after : Store)
    (prefixSuccess : initializeValues program (fuel + initializersBefore.length + 2)
      store slot initializersBefore = .ok after)
    (diverges : Diverges program after [] head) :
    initializeValues program (fuel + initializersBefore.length + 2) store slot
      (initializersBefore ++ head :: tail) = .error (.core .outOfFuel) := by
  induction initializersBefore generalizing fuel store slot after with
  | nil =>
      have afterEq : after = store := by
        have storeEq : store = after := by
          simpa [initializeValues, pure, Except.pure] using prefixSuccess
        exact storeEq.symm
      subst after
      exact initializeValues_stops_on_divergence program store slot (fuel + 1)
        head tail diverges
  | cons first rest ih =>
      have fuelEq : fuel + (rest.length + 1) + 2 = (fuel + rest.length + 2) + 1 := by omega
      have prefixStep : initializeValues program ((fuel + rest.length + 2) + 1)
          store slot (first :: rest) = .ok after := by
        simpa [List.length_cons, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using prefixSuccess
      cases firstEval : evaluate program store (fuel + rest.length + 2) [] first with
      | error fault => simp [initializeValues, firstEval, bind, Except.bind] at prefixStep
      | ok value =>
          have restSuccess : initializeValues program (fuel + rest.length + 2)
              (store.set slot (some value)) (slot + 1) rest = .ok after := by
            simpa [initializeValues, firstEval] using prefixStep
          have restDiverges := ih fuel (store.set slot (some value)) (slot + 1)
            after restSuccess diverges
          have mainFuelEq : fuel + (rest.length + 1) + 2 =
              (fuel + rest.length + 2) + 1 := by omega
          simp only [List.length_cons]
          rw [mainFuelEq]
          simp only [List.cons_append, initializeValues, firstEval]
          exact restDiverges

theorem initializeValues_stops_on_error (program : List Definition) (fuel : Nat)
    (store : Store) (slot : Nat) (head : Term) (tail : List Term) (fault : Fault)
    (step : evaluate program store fuel [] head = .error fault) :
    initializeValues program (fuel + 1) store slot (head :: tail) = .error fault := by
  simp [initializeValues, step, bind, Except.bind]

/-- An initializer fault after a successful prefix is returned unchanged by
the sequential initializer walk. -/
theorem initializeValues_reports_error_after_prefix
    (program : List Definition) (fuel : Nat) (store : Store) (slot : Nat)
    (initializersBefore : List Term) (head : Term) (tail : List Term)
    (after : Store) (fault : Fault)
    (prefixSuccess : initializeValues program (fuel + initializersBefore.length + 2)
      store slot initializersBefore = .ok after)
    (faultStep : evaluate program after (fuel + 1) [] head = .error fault) :
    initializeValues program (fuel + initializersBefore.length + 2) store slot
      (initializersBefore ++ head :: tail) = .error fault := by
  induction initializersBefore generalizing fuel store slot after with
  | nil =>
      have storeEq : store = after := by
        simpa [initializeValues, pure, Except.pure] using prefixSuccess
      subst after
      exact initializeValues_stops_on_error program (fuel + 1) store slot head tail fault
        faultStep
  | cons first rest ih =>
      have prefixStep : initializeValues program ((fuel + rest.length + 2) + 1)
          store slot (first :: rest) = .ok after := by
        simpa [List.length_cons, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using prefixSuccess
      cases firstEval : evaluate program store (fuel + rest.length + 2) [] first with
      | error firstFault =>
          simp [initializeValues, firstEval, bind, Except.bind] at prefixStep
      | ok value =>
          have restSuccess : initializeValues program (fuel + rest.length + 2)
              (store.set slot (some value)) (slot + 1) rest = .ok after := by
            simpa [initializeValues, firstEval] using prefixStep
          have restFault := ih fuel (store.set slot (some value)) (slot + 1)
            after restSuccess faultStep
          have fuelEq : fuel + (rest.length + 1) + 2 =
              (fuel + rest.length + 2) + 1 := by omega
          simp only [List.length_cons]
          rw [fuelEq]
          simp only [List.cons_append, initializeValues, firstEval]
          exact restFault

theorem initializeValues_commits_head (program : List Definition) (fuel : Nat)
    (store : Store) (slot : Nat) (head : Term) (tail : List Term) (value : Value)
    (result : Store)
    (step : evaluate program store fuel [] head = .ok value)
    (rest : initializeValues program fuel (store.set slot (some value)) (slot + 1) tail =
      .ok result) :
    initializeValues program (fuel + 1) store slot (head :: tail) = .ok result := by
  simp [initializeValues, step, rest, bind, Except.bind]

structure Program where
  definitions : List Definition
  initializers : List Term
  entry : Nat

def run (program : Program) (fuel : Nat) : Except Fault Value := do
  let store ← initializeValues program.definitions fuel (List.replicate program.initializers.length none)
    0 program.initializers
  evaluate program.definitions store fuel [] (.app (.global program.entry) [])

/-- GlobalIR propagates an initializer fault as the program result before it
attempts to evaluate the entry function. -/
theorem run_reports_initializer_fault (program : Program) (fuel : Nat) (fault : Fault)
    (initialization : initializeValues program.definitions fuel
      (List.replicate program.initializers.length none) 0 program.initializers = .error fault) :
    run program fuel = .error fault := by
  change (initializeValues program.definitions fuel
    (List.replicate program.initializers.length none) 0 program.initializers).bind
      (fun store => evaluate program.definitions store fuel []
        (.app (.global program.entry) [])) = .error fault
  rw [initialization]
  rfl

/-- A fault in the first initializer is returned by `run` unchanged.  This
connects expression-level runtime faults to the observable program result. -/
theorem run_reports_first_initializer_fault (program : Program) (fuel : Nat)
    (fault : Fault) (head : Term) (tail : List Term)
    (initializers : program.initializers = head :: tail)
    (step : evaluate program.definitions
      (List.replicate program.initializers.length none) fuel [] head = .error fault) :
    run program (fuel + 1) = .error fault := by
  apply run_reports_initializer_fault program (fuel + 1) fault
  rw [initializers]
  exact initializeValues_stops_on_error program.definitions fuel
    (List.replicate (head :: tail).length none) 0 head tail fault (by
      simpa [initializers] using step)

/-- Divergence of the first top-level initializer reaches the observable
program result as fuel exhaustion. Later initializers and the entry function
are not evaluated after that nonterminating initializer. -/
theorem run_reports_first_initializer_diverges (program : Program) (fuel : Nat)
    (head : Term) (tail : List Term)
    (initializers : program.initializers = head :: tail)
    (diverges : Diverges program.definitions
      (List.replicate (head :: tail).length none) [] head) :
    run program (fuel + 1) = .error (.core .outOfFuel) := by
  apply run_reports_initializer_fault program (fuel + 1) (.core .outOfFuel)
  rw [initializers]
  exact initializeValues_stops_on_divergence program.definitions
    (List.replicate (head :: tail).length none) 0 fuel head tail diverges

/-- Divergence at an arbitrary initializer position propagates through the
successfully committed prefix to the observable result of `run`. -/
theorem run_reports_initializer_diverges_after_prefix (program : Program) (fuel : Nat)
    (initializersBefore : List Term) (head : Term) (tail : List Term) (after : Store)
    (layout : program.initializers = initializersBefore ++ head :: tail)
    (prefixSuccess : initializeValues program.definitions
      (fuel + initializersBefore.length + 2)
      (List.replicate program.initializers.length none) 0 initializersBefore = .ok after)
    (diverges : Diverges program.definitions after [] head) :
    run program (fuel + initializersBefore.length + 2) = .error (.core .outOfFuel) := by
  apply run_reports_initializer_fault program (fuel + initializersBefore.length + 2)
    (.core .outOfFuel)
  rw [layout]
  exact initializeValues_stops_on_divergence_after_prefix program.definitions fuel
    (List.replicate (initializersBefore ++ head :: tail).length none) 0
    initializersBefore head tail after
    (by simpa [layout] using prefixSuccess) diverges

/-- A fault at an arbitrary top-level initializer position propagates after
the preceding initializer prefix has committed successfully. -/
theorem run_reports_initializer_fault_after_prefix (program : Program) (fuel : Nat)
    (initializersBefore : List Term) (head : Term) (tail : List Term)
    (after : Store) (fault : Fault)
    (layout : program.initializers = initializersBefore ++ head :: tail)
    (prefixSuccess : initializeValues program.definitions
      (fuel + initializersBefore.length + 2)
      (List.replicate program.initializers.length none) 0 initializersBefore = .ok after)
    (faultStep : evaluate program.definitions after (fuel + 1) [] head = .error fault) :
    run program (fuel + initializersBefore.length + 2) = .error fault := by
  apply run_reports_initializer_fault program (fuel + initializersBefore.length + 2) fault
  rw [layout]
  exact initializeValues_reports_error_after_prefix program.definitions fuel
    (List.replicate (initializersBefore ++ head :: tail).length none) 0
    initializersBefore head tail after fault
    (by simpa [layout] using prefixSuccess) faultStep

noncomputable def programOfNamed (functions : Named.Definitions) (slotTypes : List Surface.Ty)
    (initializers : List Named.Expr) (entry : Nat) : Program :=
  ⟨assembleNamedProgram functions slotTypes,
    lowerNamedInitializers functions slotTypes initializers, entry⟩

theorem programOfNamed_definition_count (functions : Named.Definitions)
    (slotTypes : List Surface.Ty) (initializers : List Named.Expr) (entry : Nat) :
    (programOfNamed functions slotTypes initializers entry).definitions.length =
      functions.length + slotTypes.length := by
  simp [programOfNamed]

theorem programOfNamed_getter_lookup (functions : Named.Definitions)
    (slotTypes : List Surface.Ty) (initializers : List Named.Expr) (entry slot : Nat)
    (slotBound : slot < slotTypes.length) :
    (programOfNamed functions slotTypes initializers entry).definitions[functions.length + slot]? =
      some (.getter slot) := by
  simpa [programOfNamed] using
    assembleNamedProgram_getter_lookup functions slotTypes slot slotBound

theorem programOfNamed_initializer_count (functions : Named.Definitions)
    (slotTypes : List Surface.Ty) (initializers : List Named.Expr) (entry : Nat)
    (aligned : slotTypes.length = initializers.length) :
    (programOfNamed functions slotTypes initializers entry).initializers.length =
      slotTypes.length := by
  simp [programOfNamed, lowerNamedInitializers, aligned]

theorem decodedProgram_initializer_count (fuel : Nat) (forms : List CBindingWalk.Node)
    (functions : Named.Definitions) (slotTypes : List Surface.Ty)
    (initializers : List Named.Expr) (entry : Nat)
    (decoded : Named.decodeTopLevelProgram fuel forms =
      some (functions, slotTypes, initializers)) :
    (programOfNamed functions slotTypes initializers entry).initializers.length =
      slotTypes.length :=
  programOfNamed_initializer_count functions slotTypes initializers entry
    (Named.decodeTopLevelProgram_layout fuel forms functions slotTypes initializers decoded)

theorem decodedProgram_layout (fuel : Nat) (forms : List CBindingWalk.Node)
    (functions : Named.Definitions) (slotTypes : List Surface.Ty)
    (initializers : List Named.Expr) (entry slot : Nat)
    (decoded : Named.decodeTopLevelProgram fuel forms =
      some (functions, slotTypes, initializers)) (slotBound : slot < slotTypes.length) :
    (programOfNamed functions slotTypes initializers entry).definitions.length =
        functions.length + slotTypes.length ∧
      (programOfNamed functions slotTypes initializers entry).initializers.length =
        slotTypes.length ∧
      (programOfNamed functions slotTypes initializers entry).definitions[functions.length + slot]? =
        some (.getter slot) := by
  exact ⟨programOfNamed_definition_count functions slotTypes initializers entry,
    decodedProgram_initializer_count fuel forms functions slotTypes initializers entry decoded,
    programOfNamed_getter_lookup functions slotTypes initializers entry slot slotBound⟩

/- A closure stores only its lexical environment. Its creation does not read,
or snapshot, any global cell. -/
@[simp] theorem evaluate_lambda_store_independent (program : List Definition)
    (firstStore secondStore : Store) (fuel : Nat) (env : List Value)
    (arity : Nat) (body : Term) :
    evaluate program firstStore (fuel + 1) env (.lam arity body) =
      evaluate program secondStore (fuel + 1) env (.lam arity body) := rfl

/- Getter calls consult the store passed to this evaluation. In particular,
the same getter can produce different results before and after initialization. -/
theorem getter_call_reads_current_store (program : List Definition) (store : Store)
    (fuel index slot : Nat) (value : Value)
    (getter : program[index]? = some (.getter slot))
    (initialized : store[slot]? = some (some value)) :
    evaluate program store (fuel + 2) [] (.app (.global index) []) = .ok value := by
  simp [evaluate, evaluateArgs, getter, readGlobal, initialized, List.isEmpty]

theorem getter_call_reads_current_environment (program : List Definition) (store : Store)
    (fuel index slot : Nat) (environment : List Value) (value : Value)
    (getter : program[index]? = some (.getter slot))
    (initialized : store[slot]? = some (some value)) :
    evaluate program store (fuel + 2) environment (.app (.global index) []) = .ok value := by
  simp [evaluate, evaluateArgs, getter, readGlobal, initialized, List.isEmpty]

/-- A closure created while a value cell is empty captures no stale cell
contents. Calling it later evaluates its getter body against the later store. -/
theorem closure_created_before_initialization_reads_later_store
    (program : List Definition) (before after : Store) (fuel index slot : Nat)
    (value : Value) (getter : program[index]? = some (.getter slot))
    (beforeEmpty : before[slot]? = some none)
    (afterInitialized : after[slot]? = some (some value)) :
    evaluate program before 1 [] (.lam 0 (.app (.global index) [])) =
        .ok (.closure 0 (.app (.global index) []) []) ∧
      evaluate program before (fuel + 2) [] (.app (.global index) []) =
        .error (.beforeInitialization slot) ∧
      evaluate program after (fuel + 4)
        [.closure 0 (.app (.global index) []) []] (.app (.var 0) []) = .ok value := by
  constructor
  · rfl
  · constructor
    · simp [evaluate, evaluateArgs, getter, readGlobal, beforeEmpty, List.isEmpty]
    · exact by
        have bodyEvaluation := getter_call_reads_current_store program after (fuel + 1)
          index slot value getter afterInitialized
        simpa [evaluate, evaluateArgs, bodyEvaluation, List.isEmpty] using bodyEvaluation

theorem lowered_zero_arg_value_reads_current_store
    (getters : List (Nat × Nat)) (program : List Definition) (store : Store)
    (fuel sourceIndex getterIndex slot : Nat) (value : Value)
    (mapped : getterFor getters sourceIndex = some getterIndex)
    (getter : program[getterIndex]? = some (.getter slot))
    (initialized : store[slot]? = some (some value)) :
    evaluate program store (fuel + 2) []
      (lowerGlobalReads getters (.app (.global sourceIndex) [])) = .ok value := by
  rw [lowerGlobalReads_zero_arg_value_getter getters sourceIndex getterIndex mapped]
  exact getter_call_reads_current_store program store fuel getterIndex slot value getter initialized

theorem lowered_surface_value_reference_reads_current_store
    (getters : List (Nat × Nat)) (program : List Definition) (store : Store)
    (fuel sourceIndex getterIndex slot : Nat) (value : Value)
    (mapped : getterFor getters sourceIndex = some getterIndex)
    (getter : program[getterIndex]? = some (.getter slot))
    (initialized : store[slot]? = some (some value)) :
    evaluate program store (fuel + 2) []
      (lowerGlobalReads getters (PolyIR.erase (Surface.Expr.app (.global sourceIndex []) []))) =
        .ok value := by
  rw [lowerGlobalReads_surface_value_reference getters sourceIndex getterIndex mapped]
  exact getter_call_reads_current_store program store fuel getterIndex slot value getter initialized

theorem getter_call_preserves_type (program : List Definition) (globals : List Surface.Signature)
    (slotTypes : List Surface.Ty) (store : Store) (fuel index slot : Nat)
    (value : PolyIR.Value) (type : Surface.Ty)
    (getter : program[index]? = some (.getter slot))
    (slotType : slotTypes[slot]? = some type)
    (storeTyped : StoreWellTyped globals slotTypes store)
    (initialized : store[slot]? = some (some value)) :
    ∃ result, evaluate program store (fuel + 2) [] (.app (.global index) []) = .ok result ∧
      PolyIR.ValueTyped globals result type := by
  have evaluated := getter_call_reads_current_store program store fuel index slot value getter initialized
  have slotType' : slotTypes.get? slot = some type := by
    rw [← indexed_lookup_eq_get?]
    exact slotType
  have initialized' : store.get? slot = some (some value) := by
    rw [← indexed_lookup_eq_get?]
    exact initialized
  exact ⟨value, evaluated, readGlobal_preserves_type globals slotTypes store slot value type
    storeTyped slotType' initialized'⟩

theorem typed_getter_call_preserves_type (program : List Definition)
    (globals : List Surface.Signature) (definitions : Surface.Definitions)
    (slotTypes : List Surface.Ty) (functionSources : List (Nat × Nat))
    (store : Store) (fuel index slot : Nat)
    (value : PolyIR.Value)
    (typed : GlobalProgramTyped globals definitions slotTypes functionSources program)
    (getter : program[index]? = some (.getter slot))
    (storeTyped : StoreWellTyped globals slotTypes store)
    (initialized : store[slot]? = some (some value)) :
    ∃ type result, globals[index]? = some ⟨0, [], type⟩ ∧ type.wellFormed 0 ∧
      slotTypes[slot]? = some type ∧
      evaluate program store (fuel + 2) [] (.app (.global index) []) = .ok result ∧
      PolyIR.ValueTyped globals result type := by
  obtain ⟨type, signatureEntry, typeWellFormed, slotType⟩ :=
    getter_layout_typed globals definitions slotTypes functionSources program typed index slot getter
  obtain ⟨result, evaluated, resultTyped⟩ := getter_call_preserves_type
    program globals slotTypes store fuel index slot value type getter slotType storeTyped initialized
  exact ⟨type, result, signatureEntry, typeWellFormed, slotType, evaluated, resultTyped⟩

theorem typed_getter_call_preserves_type_in_environment (program : List Definition)
    (globals : List Surface.Signature) (definitions : Surface.Definitions)
    (slotTypes : List Surface.Ty) (functionSources : List (Nat × Nat))
    (store : Store) (fuel index slot : Nat) (environment : List Value)
    (value : PolyIR.Value)
    (typed : GlobalProgramTyped globals definitions slotTypes functionSources program)
    (getter : program[index]? = some (.getter slot))
    (storeTyped : StoreWellTyped globals slotTypes store)
    (initialized : store[slot]? = some (some value)) :
    ∃ type result, globals[index]? = some ⟨0, [], type⟩ ∧ type.wellFormed 0 ∧
      slotTypes[slot]? = some type ∧
      evaluate program store (fuel + 2) environment (.app (.global index) []) = .ok result ∧
      PolyIR.ValueTyped globals result type := by
  obtain ⟨type, signatureEntry, typeWellFormed, slotType⟩ :=
    getter_layout_typed globals definitions slotTypes functionSources program typed index slot getter
  have slotType' : slotTypes.get? slot = some type := by
    rw [← indexed_lookup_eq_get?]
    exact slotType
  have initialized' : store.get? slot = some (some value) := by
    rw [← indexed_lookup_eq_get?]
    exact initialized
  have evaluated := getter_call_reads_current_environment program store fuel index slot
    environment value getter initialized
  exact ⟨type, value, signatureEntry, typeWellFormed, slotType, evaluated,
    readGlobal_preserves_type globals slotTypes store slot value type storeTyped slotType' initialized'⟩

/-- A getter call is type safe whenever its declared store slot is populated.
This composes the layout theorem with `StoreWellTyped`, so callers need not
name the cell's value separately. -/
theorem typed_getter_call_preserves_type_of_populated_store (program : List Definition)
    (globals : List Surface.Signature) (definitions : Surface.Definitions)
    (slotTypes : List Surface.Ty) (functionSources : List (Nat × Nat))
    (store : Store) (fuel index slot : Nat)
    (typed : GlobalProgramTyped globals definitions slotTypes functionSources program)
    (getter : program[index]? = some (.getter slot))
    (storeTyped : StoreWellTyped globals slotTypes store)
    (populated : ∀ slot, slot < slotTypes.length →
      ∃ value, store[slot]? = some (some value)) :
    ∃ type result, globals[index]? = some ⟨0, [], type⟩ ∧ type.wellFormed 0 ∧
      slotTypes[slot]? = some type ∧
      evaluate program store (fuel + 2) [] (.app (.global index) []) = .ok result ∧
      PolyIR.ValueTyped globals result type := by
  obtain ⟨type, signatureEntry, typeWellFormed, slotType⟩ :=
    getter_layout_typed globals definitions slotTypes functionSources program typed index slot getter
  have slotTypeGet : slotTypes.get? slot = some type := by
    rw [← indexed_lookup_eq_get?]
    exact slotType
  have slotBound : slot < slotTypes.length := (List.get?_eq_some.mp slotTypeGet).1
  obtain ⟨value, initialized⟩ := populated slot slotBound
  obtain ⟨result, evaluated, resultTyped⟩ := getter_call_preserves_type
    program globals slotTypes store fuel index slot value type getter slotType storeTyped initialized
  exact ⟨type, result, signatureEntry, typeWellFormed, slotType, evaluated, resultTyped⟩

/-- A source global-value reference lowered through its getter evaluates to a
value of the declared slot type whenever that slot is initialized and the
store satisfies its typed layout. This connects getter lowering, the runtime
table layout, and the getter's type preservation in one theorem. -/
theorem assembled_global_value_read_preserves_type
    (definitions : Surface.Definitions) (slotTypes : List Surface.Ty)
    (store : Store) (fuel slot : Nat) (type : Surface.Ty)
    (slotType : slotTypes[slot]? = some type)
    (storeTyped : StoreWellTyped (assembleGlobals definitions slotTypes) slotTypes store)
    (initialized : ∃ value, store[slot]? = some (some value)) :
    ∃ result,
      evaluate (assembleProgram definitions slotTypes) store (fuel + 2) []
        (lowerGlobalReads (getterMappings definitions.length slotTypes)
          (.global (definitions.length + slot))) = .ok result ∧
      PolyIR.ValueTyped (assembleGlobals definitions slotTypes) result type := by
  obtain ⟨value, cellInitialized⟩ := initialized
  have slotBound : slot < slotTypes.length := by
    have slotTypeGet : slotTypes.get? slot = some type := by
      rw [← indexed_lookup_eq_get?]
      exact slotType
    exact (List.get?_eq_some.mp slotTypeGet).1
  have getterEntry := assembleProgram_getter_lookup definitions slotTypes slot slotBound
  obtain ⟨result, evaluated, resultTyped⟩ := getter_call_preserves_type
    (assembleProgram definitions slotTypes)
    (assembleGlobals definitions slotTypes) slotTypes store fuel
    (definitions.length + slot) slot value type getterEntry slotType storeTyped cellInitialized
  rw [lowerGlobalReads_global_value_getter definitions.length slot slotTypes slotBound]
  exact ⟨result, evaluated, resultTyped⟩

theorem getter_call_reports_early_read (program : List Definition) (store : Store)
    (fuel index slot : Nat)
    (getter : program[index]? = some (.getter slot))
    (uninitialized : store[slot]? = some none) :
    evaluate program store (fuel + 2) [] (.app (.global index) []) =
      .error (.beforeInitialization slot) := by
  simp [evaluate, evaluateArgs, getter, readGlobal, uninitialized, List.isEmpty]

theorem typed_getter_call_reports_early_read (program : List Definition)
    (globals : List Surface.Signature) (definitions : Surface.Definitions)
    (slotTypes : List Surface.Ty) (functionSources : List (Nat × Nat))
    (store : Store) (fuel index slot : Nat)
    (typed : GlobalProgramTyped globals definitions slotTypes functionSources program)
    (getter : program[index]? = some (.getter slot))
    (uninitialized : store[slot]? = some none) :
    ∃ type, globals[index]? = some ⟨0, [], type⟩ ∧ type.wellFormed 0 ∧
      slotTypes[slot]? = some type ∧
      evaluate program store (fuel + 2) [] (.app (.global index) []) =
        .error (.beforeInitialization slot) := by
  obtain ⟨type, signatureEntry, typeWellFormed, slotType⟩ :=
    getter_layout_typed globals definitions slotTypes functionSources program typed index slot getter
  exact ⟨type, signatureEntry, typeWellFormed, slotType,
    getter_call_reports_early_read program store fuel index slot getter uninitialized⟩

/-- A typed getter in a layout-aligned, well-typed store either returns a
value of its declared type or reports the exact early-read fault for its slot.
No unrelated core fault is possible on this zero-argument getter path. -/
theorem typed_getter_call_type_safe_or_early_read (program : List Definition)
    (globals : List Surface.Signature) (definitions : Surface.Definitions)
    (slotTypes : List Surface.Ty) (functionSources : List (Nat × Nat))
    (store : Store) (fuel index slot : Nat)
    (typed : GlobalProgramTyped globals definitions slotTypes functionSources program)
    (getter : program[index]? = some (.getter slot))
    (storeLayout : store.length = slotTypes.length)
    (storeTyped : StoreWellTyped globals slotTypes store) :
    ∃ type, globals[index]? = some ⟨0, [], type⟩ ∧ slotTypes[slot]? = some type ∧
      ((∃ value, evaluate program store (fuel + 2) [] (.app (.global index) []) = .ok value ∧
          PolyIR.ValueTyped globals value type) ∨
        evaluate program store (fuel + 2) [] (.app (.global index) []) =
          .error (.beforeInitialization slot)) := by
  obtain ⟨type, signatureEntry, typeWellFormed, slotType⟩ :=
    getter_layout_typed globals definitions slotTypes functionSources program typed index slot getter
  have slotTypeGet : slotTypes.get? slot = some type := by
    rw [← indexed_lookup_eq_get?]
    exact slotType
  rcases readGlobal_type_safe_or_before_initialization_of_layout globals slotTypes store
      slot type slotTypeGet storeLayout storeTyped with safe | early
  · rcases safe with ⟨value, readSuccess, valueTyped⟩
    cases entry : store[slot]? with
    | none => simp [readGlobal, entry] at readSuccess
    | some cell =>
        cases cell with
        | none => simp [readGlobal, entry] at readSuccess
        | some stored =>
            simp [readGlobal, entry] at readSuccess
            subst stored
            have getterSuccess := getter_call_reads_current_store program store fuel index slot
              value getter entry
            exact ⟨type, signatureEntry, slotType, Or.inl ⟨value, getterSuccess, valueTyped⟩⟩
  · have uninitialized : store[slot]? = some none := by
      cases entry : store[slot]? with
      | none => simp [readGlobal, entry] at early
      | some cell =>
          cases cell with
          | none => rfl
          | some value => simp [readGlobal, entry] at early
    exact ⟨type, signatureEntry, slotType, Or.inr
      (getter_call_reports_early_read program store fuel index slot getter uninitialized)⟩

/-- The getter safety dichotomy is independent of the caller's local
environment. This is the form needed when a global value is read from inside
a closure body. -/
theorem typed_getter_call_type_safe_or_early_read_in_environment
    (program : List Definition) (globals : List Surface.Signature)
    (definitions : Surface.Definitions) (slotTypes : List Surface.Ty)
    (functionSources : List (Nat × Nat)) (store : Store) (fuel index slot : Nat)
    (environment : List Value)
    (typed : GlobalProgramTyped globals definitions slotTypes functionSources program)
    (getter : program[index]? = some (.getter slot))
    (storeLayout : store.length = slotTypes.length)
    (storeTyped : StoreWellTyped globals slotTypes store) :
    ∃ type, globals[index]? = some ⟨0, [], type⟩ ∧ slotTypes[slot]? = some type ∧
      ((∃ value, evaluate program store (fuel + 2) environment
          (.app (.global index) []) = .ok value ∧ PolyIR.ValueTyped globals value type) ∨
        evaluate program store (fuel + 2) environment (.app (.global index) []) =
          .error (.beforeInitialization slot)) := by
  obtain ⟨type, signatureEntry, _typeWellFormed, slotType⟩ :=
    getter_layout_typed globals definitions slotTypes functionSources program typed index slot getter
  have slotTypeGet : slotTypes.get? slot = some type := by
    rw [← indexed_lookup_eq_get?]
    exact slotType
  rcases readGlobal_type_safe_or_before_initialization_of_layout globals slotTypes store
      slot type slotTypeGet storeLayout storeTyped with safe | early
  · rcases safe with ⟨value, readSuccess, valueTyped⟩
    cases entry : store[slot]? with
    | none => simp [readGlobal, entry] at readSuccess
    | some cell =>
        cases cell with
        | none => simp [readGlobal, entry] at readSuccess
        | some stored =>
            simp [readGlobal, entry] at readSuccess
            subst stored
            exact ⟨type, signatureEntry, slotType, Or.inl ⟨value,
              getter_call_reads_current_environment program store fuel index slot environment
                value getter entry, valueTyped⟩⟩
  · have uninitialized : store[slot]? = some none := by
      cases entry : store[slot]? with
      | none => simp [readGlobal, entry] at early
      | some cell =>
          cases cell with
          | none => rfl
          | some value => simp [readGlobal, entry] at early
    have earlyRead : evaluate program store (fuel + 2) environment
        (.app (.global index) []) = .error (.beforeInitialization slot) := by
      simp [evaluate, evaluateArgs, getter, readGlobal, uninitialized, List.isEmpty]
    exact ⟨type, signatureEntry, slotType, Or.inr earlyRead⟩

theorem evaluate_lambda_application_success_parts
    (program : List Definition) (store : Store) (fuel : Nat) (environment : List Value)
    (arity : Nat) (body : Term) (arguments : List Term) (value : Value)
    (fuelPositive : 0 < fuel)
    (success : evaluate program store (fuel + 1) environment
      (.app (.lam arity body) arguments) = .ok value) :
    ∃ values, evaluateArgs program store fuel environment arguments = .ok values ∧
      values.length = arity ∧
      evaluate program store fuel (values ++ environment) body = .ok value := by
  cases fuel with
  | zero => omega
  | succ fuel =>
      have functionSuccess : evaluate program store (fuel + 1) environment
          (.lam arity body) = .ok (.closure arity body environment) := by
        simp [evaluate, pure, Except.pure]
      cases argumentsSuccess : evaluateArgs program store (fuel + 1) environment arguments with
      | error fault =>
          simp [evaluate, functionSuccess, argumentsSuccess, bind, Except.bind] at success
      | ok values =>
          by_cases arityEq : values.length = arity
          · refine ⟨values, rfl, arityEq, ?_⟩
            simpa [evaluate, functionSuccess, argumentsSuccess, arityEq, bind, Except.bind]
              using success
          · simp [evaluate, functionSuccess, argumentsSuccess, arityEq, bind, Except.bind]
              at success

/-- Successful evaluation preserves types for the contextual runtime fragment
that includes lowered getter reads. The getter case uses the typed store
layout to rule out an untyped returned value; an uninitialized cell is
reported as a fault and therefore cannot satisfy the success premise. -/
theorem evaluate_contextualGlobalRuntimeTerm_preserves_type
    (globals : List Surface.Signature) (assignment : Nat → Surface.Ty)
    (definitions : Surface.Definitions) (slotTypes : List Surface.Ty)
    (functionSources : List (Nat × Nat)) (program : List Definition)
    (programTyped : GlobalProgramTyped globals definitions slotTypes functionSources program)
    (store : Store) (storeLayout : store.length = slotTypes.length)
    (storeTyped : StoreWellTyped globals slotTypes store)
    (context : List Surface.Ty) (fuel : Nat) (environment : List Value)
    (environmentTyped : ValuesTyped globals environment
      (Surface.interpretTypes assignment context))
    (term : Term) (type : Surface.Ty)
    (typing : ContextualGlobalRuntimeTerm globals assignment definitions slotTypes
      functionSources program context term type)
    (value : Value) (success : evaluate program store fuel environment term = .ok value) :
    PolyIR.ValueTyped globals value type := by
  cases typing with
  | arithmetic arithmeticTyping =>
      exact evaluate_contextualGlobalArithmeticTerm_preserves_type globals assignment
        definitions slotTypes functionSources program programTyped store context fuel
        environment environmentTyped term type arithmeticTyping value success
  | @getter index slot resultType getterEntry signatureEntry =>
      obtain ⟨getterType, getterSignature, _wellFormed, _slotType⟩ :=
        getter_layout_typed globals definitions slotTypes functionSources program programTyped
          index slot getterEntry
      have sameSignature := Option.some.inj (signatureEntry.symm.trans getterSignature)
      have getterTypeEq : getterType = type := by
        have resultEq := congrArg Surface.Signature.result sameSignature
        exact resultEq.symm
      cases getterTypeEq
      cases fuel with
      | zero => simp [evaluate] at success
      | succ fuel =>
          cases fuel with
          | zero => simp [evaluate, evaluateArgs, bind, Except.bind, pure, Except.pure] at success
          | succ remaining =>
              obtain ⟨helperType, helperSignature, _helperSlotType, getterResult⟩ :=
                typed_getter_call_type_safe_or_early_read_in_environment
                  program globals definitions slotTypes functionSources store remaining index slot
                  environment programTyped getterEntry storeLayout storeTyped
              have helperTypeEq : helperType = type := by
                have signatureEq := Option.some.inj (signatureEntry.symm.trans helperSignature)
                have resultEq := congrArg Surface.Signature.result signatureEq
                exact resultEq.symm
              cases helperTypeEq
              rcases getterResult with typedResult | earlyRead
              · rcases typedResult with ⟨result, getterSuccess, resultTyped⟩
                rw [getterSuccess] at success
                cases success
                exact resultTyped
              · rw [earlyRead] at success
                cases success
  | @lambdaApplication parameters arguments argumentTypes body resultType
      argumentsTyping arityAgreement bodyTyping =>
      cases fuel with
      | zero => simp [evaluate] at success
      | succ fuel =>
        cases fuel with
        | zero => simp [evaluate, bind, Except.bind] at success
        | succ fuel =>
          obtain ⟨values, argumentsSuccess, valuesArity, bodySuccess⟩ :=
            evaluate_lambda_application_success_parts program store (fuel + 1) environment
              parameters.length body arguments value (by omega) success
          have functionSuccess : evaluate program store (fuel + 1) environment
              (.lam parameters.length body) =
                .ok (.closure parameters.length body environment) := by
            simp [evaluate, pure, Except.pure]
          have argumentsTyped := evaluate_contextualGlobalArithmeticTerms_preserves_type
            globals assignment definitions slotTypes functionSources program programTyped store
            context (fuel + 1) environment environmentTyped arguments argumentTypes
            argumentsTyping values argumentsSuccess
          have bodyEnvironmentTyped : ValuesTyped globals (values ++ environment)
              (Surface.interpretTypes assignment (argumentTypes ++ context)) := by
            simpa [Surface.interpretTypes_append] using
              (ValuesTyped.append argumentsTyped environmentTyped)
          have bodyResultTyped := evaluate_contextualGlobalArithmeticTerm_preserves_type
            globals assignment definitions slotTypes functionSources program programTyped store
            (argumentTypes ++ context) (fuel + 1) (values ++ environment) bodyEnvironmentTyped
            body (Surface.interpret assignment resultType) bodyTyping value bodySuccess
          exact (evaluate_closure_application_preserves_type_from_body_result globals program
            store (fuel + 1) environment environment (.lam parameters.length body)
            parameters.length body functionSuccess arguments values argumentsSuccess valuesArity
            value (Surface.interpret assignment resultType) bodySuccess bodyResultTyped).2

theorem evaluate_contextualGlobalRuntimeIntegerOptionalCall_preserves_type
    (globals : List Surface.Signature) (assignment : Nat → Surface.Ty)
    (definitions : Surface.Definitions) (slotTypes : List Surface.Ty)
    (functionSources : List (Nat × Nat)) (program : List Definition)
    (programTyped : GlobalProgramTyped globals definitions slotTypes functionSources program)
    (store : Store) (context : List Surface.Ty) (fuel : Nat)
    (environment : List Value)
    (environmentTyped : ValuesTyped globals environment
      (Surface.interpretTypes assignment context))
    (operation : IntegerOptionalOperation) (left right : Term)
    (typing : ContextualGlobalRuntimeIntegerOptionalCall globals assignment definitions slotTypes
      functionSources program context operation left right)
    (storeLayout : store.length = slotTypes.length)
    (storeTyped : StoreWellTyped globals slotTypes store)
    (result : Value)
    (success : evaluateIntegerOptionalCall program store operation fuel environment left right =
      .ok result) :
    PolyIR.ValueTyped globals result (.option .integer) ∧
      ∃ leftValue rightValue,
        evaluate program store (fuel - 1) environment left = .ok leftValue ∧
        evaluate program store (fuel - 1) environment right = .ok rightValue ∧
        PolyIR.ValueTyped globals leftValue .integer ∧
        PolyIR.ValueTyped globals rightValue .integer := by
  cases fuel with
  | zero => simp [evaluateIntegerOptionalCall] at success
  | succ fuel =>
      obtain ⟨leftInteger, rightInteger, leftEval, rightEval, resultEq⟩ :=
        (evaluateIntegerOptionalCall_success_iff program store operation fuel environment
          left right result).mp (by simpa using success)
      cases typing with
      | mk leftTyping rightTyping =>
          have leftTyped := evaluate_contextualGlobalRuntimeTerm_preserves_type
            globals assignment definitions slotTypes functionSources program programTyped store
            storeLayout storeTyped context fuel environment environmentTyped left .integer leftTyping
            (.int leftInteger) leftEval
          have rightTyped := evaluate_contextualGlobalRuntimeTerm_preserves_type
            globals assignment definitions slotTypes functionSources program programTyped store
            storeLayout storeTyped context fuel environment environmentTyped right .integer rightTyping
            (.int rightInteger) rightEval
          refine ⟨?_, .int leftInteger, .int rightInteger, ?_, ?_, ?_, ?_⟩
          · rw [resultEq]
            exact integerOptionalRuntimeValue_typed globals operation.toPrimitive
              leftInteger rightInteger
          · exact leftEval
          · exact rightEval
          · exact leftTyped
          · exact rightTyped

/-- A successful Float comparison over runtime-typed operands (including
getter reads) returns a Boolean. The proof also exposes the two Float child
evaluations so the exact evaluation/fault order remains available to callers. -/
theorem evaluate_contextualGlobalRuntimeFloatComparisonCall_preserves_type
    (globals : List Surface.Signature) (assignment : Nat → Surface.Ty)
    (definitions : Surface.Definitions) (slotTypes : List Surface.Ty)
    (functionSources : List (Nat × Nat)) (program : List Definition)
    (programTyped : GlobalProgramTyped globals definitions slotTypes functionSources program)
    (store : Store) (context : List Surface.Ty) (fuel : Nat)
    (environment : List Value)
    (environmentTyped : ValuesTyped globals environment
      (Surface.interpretTypes assignment context))
    (operation : FloatComparisonOperation) (left right : Term)
    (typing : ContextualGlobalRuntimeFloatComparisonCall globals assignment definitions slotTypes
      functionSources program context operation left right)
    (storeLayout : store.length = slotTypes.length)
    (storeTyped : StoreWellTyped globals slotTypes store)
    (result : Value)
    (success : evaluateFloatComparisonCall program store operation fuel environment left right =
      .ok result) :
    PolyIR.ValueTyped globals result .boolean ∧
      ∃ leftValue rightValue,
        evaluate program store (fuel - 1) environment left = .ok leftValue ∧
        evaluate program store (fuel - 1) environment right = .ok rightValue ∧
        PolyIR.ValueTyped globals leftValue .float ∧
        PolyIR.ValueTyped globals rightValue .float := by
  cases fuel with
  | zero => simp [evaluateFloatComparisonCall] at success
  | succ fuel =>
      obtain ⟨leftFloat, rightFloat, leftEval, rightEval, resultEq⟩ :=
        (evaluateFloatComparisonCall_success_iff program store operation fuel environment
          left right result).mp (by simpa using success)
      cases typing with
      | mk leftTyping rightTyping =>
          have leftTyped := evaluate_contextualGlobalRuntimeTerm_preserves_type
            globals assignment definitions slotTypes functionSources program programTyped store
            storeLayout storeTyped context fuel environment environmentTyped left .float leftTyping
            (.float leftFloat) leftEval
          have rightTyped := evaluate_contextualGlobalRuntimeTerm_preserves_type
            globals assignment definitions slotTypes functionSources program programTyped store
            storeLayout storeTyped context fuel environment environmentTyped right .float rightTyping
            (.float rightFloat) rightEval
          refine ⟨?_, .float leftFloat, .float rightFloat, ?_, ?_, ?_, ?_⟩
          · rw [resultEq]
            exact floatComparisonRuntimeValue_typed globals operation leftFloat rightFloat
          · exact leftEval
          · exact rightEval
          · exact leftTyped
          · exact rightTyped

/-- Getter-aware type preservation for GlobalIR Float arithmetic terms. -/
theorem evaluate_contextualGlobalRuntimeFloatBinCall_preserves_type
    (globals : List Surface.Signature) (assignment : Nat → Surface.Ty)
    (definitions : Surface.Definitions) (slotTypes : List Surface.Ty)
    (functionSources : List (Nat × Nat)) (program : List Definition)
    (programTyped : GlobalProgramTyped globals definitions slotTypes functionSources program)
    (store : Store) (context : List Surface.Ty) (fuel : Nat)
    (environment : List Value)
    (environmentTyped : ValuesTyped globals environment
      (Surface.interpretTypes assignment context))
    (operation : Surface.FloatBinOp) (left right : Term)
    (typing : ContextualGlobalRuntimeFloatBinCall globals assignment definitions slotTypes
      functionSources program context operation left right)
    (storeLayout : store.length = slotTypes.length)
    (storeTyped : StoreWellTyped globals slotTypes store)
    (result : Value)
    (success : evaluate program store fuel environment (.floatBin operation left right) =
      .ok result) :
    PolyIR.ValueTyped globals result .float ∧
      ∃ leftValue rightValue,
        evaluate program store (fuel - 1) environment left = .ok leftValue ∧
        evaluate program store (fuel - 1) environment right = .ok rightValue ∧
        PolyIR.ValueTyped globals leftValue .float ∧
        PolyIR.ValueTyped globals rightValue .float := by
  cases fuel with
  | zero => simp [evaluate] at success
  | succ fuel =>
      have successParts := (evaluate_floatBin_success_iff program store operation fuel environment
        left right result).mp (by simpa using success)
      obtain ⟨leftFloat, rightFloat, leftEval, rightEval, resultEq⟩ := successParts
      cases typing with
      | mk leftTyping rightTyping =>
          have leftTyped := evaluate_contextualGlobalRuntimeTerm_preserves_type
            globals assignment definitions slotTypes functionSources program programTyped store
            storeLayout storeTyped context fuel environment environmentTyped left .float leftTyping
            (.float leftFloat) leftEval
          have rightTyped := evaluate_contextualGlobalRuntimeTerm_preserves_type
            globals assignment definitions slotTypes functionSources program programTyped store
            storeLayout storeTyped context fuel environment environmentTyped right .float rightTyping
            (.float rightFloat) rightEval
          refine ⟨?_, .float leftFloat, .float rightFloat, ?_, ?_, ?_, ?_⟩
          · rw [resultEq]
            exact .float
          · exact leftEval
          · exact rightEval
          · exact leftTyped
          · exact rightTyped

theorem evaluate_contextualGlobalRuntimeSequence_preserves_type
    (globals : List Surface.Signature) (assignment : Nat → Surface.Ty)
    (definitions : Surface.Definitions) (slotTypes : List Surface.Ty)
    (functionSources : List (Nat × Nat)) (program : List Definition)
    (programTyped : GlobalProgramTyped globals definitions slotTypes functionSources program)
    (store : Store) (context : List Surface.Ty) (fuel : Nat)
    (environment : List Value) (previous : Value) (terms : List Term)
    (resultType : Surface.Ty)
    (typing : ContextualGlobalRuntimeSequence globals assignment definitions slotTypes
      functionSources program context terms resultType)
    (storeLayout : store.length = slotTypes.length)
    (storeTyped : StoreWellTyped globals slotTypes store)
    (environmentTyped : ValuesTyped globals environment
      (Surface.interpretTypes assignment context))
    (value : Value)
    (success : evaluateSequence program store fuel environment previous terms = .ok value) :
    PolyIR.ValueTyped globals value resultType := by
  induction typing generalizing fuel environment previous value with
  | last expressionTyped =>
      rename_i term type
      cases fuel with
      | zero => simp [evaluateSequence] at success
      | succ fuel =>
          cases fuel with
          | zero => simp [evaluateSequence, evaluate, bind, Except.bind] at success
          | succ fuel =>
              cases expressionResult : evaluate program store (fuel + 1) environment term with
              | error fault => simp [evaluateSequence, expressionResult, bind, Except.bind] at success
              | ok expressionValue =>
                  have expressionValueTyped := evaluate_contextualGlobalRuntimeTerm_preserves_type
                    globals assignment definitions slotTypes functionSources program programTyped
                    store storeLayout storeTyped context (fuel + 1) environment environmentTyped
                    term type expressionTyped expressionValue expressionResult
                  have valueEq : value = expressionValue := by
                    simpa [evaluateSequence, expressionResult, bind, Except.bind,
                      Except.pure, Pure.pure] using success.symm
                  cases valueEq
                  exact expressionValueTyped
  | skip firstTyped restTyped restIH =>
      rename_i firstTerm firstType restTerms resultType
      cases fuel with
      | zero => simp [evaluateSequence] at success
      | succ fuel =>
          cases firstResult : evaluate program store fuel environment firstTerm with
          | error fault => simp [evaluateSequence, firstResult, bind, Except.bind] at success
          | ok firstValue =>
              have restSuccess : evaluateSequence program store fuel environment
                  firstValue restTerms = .ok value := by
                simpa [evaluateSequence, firstResult, bind, Except.bind] using success
              exact restIH fuel environment firstValue environmentTyped value restSuccess

/-- `begin` carries the getter-aware sequence guarantee through evaluation. -/
theorem evaluate_contextualGlobalRuntimeBegin_preserves_type
    (globals : List Surface.Signature) (assignment : Nat → Surface.Ty)
    (definitions : Surface.Definitions) (slotTypes : List Surface.Ty)
    (functionSources : List (Nat × Nat)) (program : List Definition)
    (programTyped : GlobalProgramTyped globals definitions slotTypes functionSources program)
    (store : Store) (context : List Surface.Ty) (fuel : Nat)
    (environment : List Value) (first : Term) (firstType : Surface.Ty)
    (rest : List Term) (resultType : Surface.Ty)
    (firstTyped : ContextualGlobalRuntimeTerm globals assignment definitions slotTypes
      functionSources program context first firstType)
    (restTyped : ContextualGlobalRuntimeSequence globals assignment definitions slotTypes
      functionSources program context rest resultType)
    (storeLayout : store.length = slotTypes.length)
    (storeTyped : StoreWellTyped globals slotTypes store)
    (environmentTyped : ValuesTyped globals environment
      (Surface.interpretTypes assignment context))
    (value : Value)
    (success : evaluate program store fuel environment (.begin first rest) = .ok value) :
    PolyIR.ValueTyped globals value resultType := by
  cases fuel with
  | zero => simp [evaluate] at success
  | succ fuel =>
      change (do
        let firstValue ← evaluate program store fuel environment first
        evaluateSequence program store fuel environment firstValue rest) = .ok value at success
      cases firstResult : evaluate program store fuel environment first with
      | error fault => simp [firstResult, bind, Except.bind] at success
      | ok firstValue =>
          have restSuccess : evaluateSequence program store fuel environment
              firstValue rest = .ok value := by
            simpa [firstResult, bind, Except.bind] using success
          exact evaluate_contextualGlobalRuntimeSequence_preserves_type
            globals assignment definitions slotTypes functionSources program programTyped store
            context fuel environment firstValue rest resultType restTyped storeLayout storeTyped
            environmentTyped value restSuccess

theorem evaluate_contextualGlobalRuntimeTerms_preserves_type
    (globals : List Surface.Signature) (assignment : Nat → Surface.Ty)
    (definitions : Surface.Definitions) (slotTypes : List Surface.Ty)
    (functionSources : List (Nat × Nat)) (program : List Definition)
    (programTyped : GlobalProgramTyped globals definitions slotTypes functionSources program)
    (store : Store) (context : List Surface.Ty) (fuel : Nat)
    (environment : List Value) (environmentTyped : ValuesTyped globals environment
      (Surface.interpretTypes assignment context)) (terms : List Term) (types : List Surface.Ty)
    (typing : ContextualGlobalRuntimeTerms globals assignment definitions slotTypes
      functionSources program context types terms)
    (storeLayout : store.length = slotTypes.length)
    (storeTyped : StoreWellTyped globals slotTypes store)
    (values : List Value)
    (success : evaluateArgs program store fuel environment terms = .ok values) :
    ValuesTyped globals values (Surface.interpretTypes assignment types) := by
  induction typing generalizing fuel values with
  | nil =>
      cases fuel with
      | zero => simp [evaluateArgs] at success
      | succ fuel =>
          have valuesEmpty : values = [] := by
            simpa [evaluateArgs, pure, Except.pure] using success.symm
          subst values
          exact .nil
  | cons headTyped tailTyped tailIH =>
      rename_i headTerm headType tailTypes tailTerms
      cases fuel with
      | zero => simp [evaluateArgs] at success
      | succ fuel =>
          cases headResult : evaluate program store fuel environment headTerm with
          | error fault => simp [evaluateArgs, headResult, bind, Except.bind] at success
          | ok headValue =>
              cases tailResult : evaluateArgs program store fuel environment tailTerms with
              | error fault =>
                  simp [evaluateArgs, headResult, tailResult, bind, Except.bind] at success
              | ok tailValues =>
                  have headTypedValue := evaluate_contextualGlobalRuntimeTerm_preserves_type
                    globals assignment definitions slotTypes functionSources program programTyped
                    store storeLayout storeTyped context fuel environment environmentTyped
                    headTerm (Surface.interpret assignment headType) headTyped headValue headResult
                  have tailTypedValues := tailIH fuel tailValues tailResult
                  have valuesEq : values = headValue :: tailValues := by
                    simpa [evaluateArgs, headResult, tailResult, bind, Except.bind,
                      Except.pure, Pure.pure, List.cons.injEq] using success.symm
                  subst values
                  simpa [Surface.interpretTypes] using
                    (ValuesTyped.cons headTypedValue tailTypedValues)

/-- A global function call preserves its declared result type when both its
argument expressions and its body may read initialized top-level value
slots. The argument row is evaluated in the caller environment, while the
body is evaluated in the argument-value environment, matching the evaluator's
call-by-value rule. -/
theorem evaluate_contextualGlobalRuntimeCall_preserves_type
    (globals : List Surface.Signature) (assignment : Nat → Surface.Ty)
    (definitions : Surface.Definitions) (slotTypes : List Surface.Ty)
    (functionSources : List (Nat × Nat)) (program : List Definition)
    (programTyped : GlobalProgramTyped globals definitions slotTypes functionSources program)
    (store : Store) (storeLayout : store.length = slotTypes.length)
    (storeTyped : StoreWellTyped globals slotTypes store)
    (callerContext : List Surface.Ty) (callerEnvironment : List Value)
    (callerEnvironmentTyped : ValuesTyped globals callerEnvironment
      (Surface.interpretTypes assignment callerContext))
    (fuel index : Nat) (runtime : RuntimeDefinition)
    (fuelPositive : 0 < fuel)
    (runtimeEntry : program[index]? = some (.function runtime))
    (terms : List Term) (argumentTypes : List Surface.Ty)
    (argumentsTyping : ContextualGlobalRuntimeTerms globals assignment definitions slotTypes
      functionSources program callerContext argumentTypes terms)
    (values : List Value)
    (argumentsSuccess : evaluateArgs program store fuel callerEnvironment terms = .ok values)
    (arity : runtime.arity = values.length) (resultType : Surface.Ty)
    (bodyTyping : ContextualGlobalRuntimeTerm globals assignment definitions slotTypes
      functionSources program argumentTypes runtime.body resultType)
    (result : Value)
    (bodySuccess : evaluate program store fuel values runtime.body = .ok result)
    (callSuccess : evaluate program store (fuel + 1) callerEnvironment
      (.app (.global index) terms) = .ok result) :
    PolyIR.ValueTyped globals result resultType := by
  have functionSuccess : evaluate program store fuel callerEnvironment (.global index) =
      .ok (.global index) := by
    cases fuel with
    | zero => omega
    | succ remaining => simp [evaluate, runtimeEntry, pure, Except.pure]
  have callEq : evaluate program store (fuel + 1) callerEnvironment
      (.app (.global index) terms) = evaluate program store fuel values runtime.body := by
    simp [evaluate, functionSuccess, argumentsSuccess, runtimeEntry, arity,
      bind, Except.bind, Except.pure, pure]
  have argumentsTyped := evaluate_contextualGlobalRuntimeTerms_preserves_type
    globals assignment definitions slotTypes functionSources program programTyped store
    callerContext fuel callerEnvironment callerEnvironmentTyped terms argumentTypes
    argumentsTyping storeLayout storeTyped values argumentsSuccess
  have bodyTyped := evaluate_contextualGlobalRuntimeTerm_preserves_type
    globals assignment definitions slotTypes functionSources program programTyped store
    storeLayout storeTyped argumentTypes fuel values argumentsTyped runtime.body resultType
    bodyTyping result bodySuccess
  rw [callEq, bodySuccess] at callSuccess
  cases callSuccess
  exact bodyTyped

/-- Closure calls also preserve their result type when their arguments and
captured body use top-level getters. Argument values and captured values are
typed independently, then appended in the exact order used by the evaluator. -/
theorem evaluate_contextualGlobalRuntimeClosureCall_preserves_type
    (globals : List Surface.Signature) (assignment : Nat → Surface.Ty)
    (definitions : Surface.Definitions) (slotTypes : List Surface.Ty)
    (functionSources : List (Nat × Nat)) (program : List Definition)
    (programTyped : GlobalProgramTyped globals definitions slotTypes functionSources program)
    (store : Store) (storeLayout : store.length = slotTypes.length)
    (storeTyped : StoreWellTyped globals slotTypes store)
    (callerContext argumentTypes capturedTypes : List Surface.Ty)
    (callerEnvironment captured : List Value)
    (callerEnvironmentTyped : ValuesTyped globals callerEnvironment
      (Surface.interpretTypes assignment callerContext))
    (capturedTyped : ValuesTyped globals captured
      (Surface.interpretTypes assignment capturedTypes))
    (fuel : Nat) (function : Term) (arity : Nat) (body : Term)
    (functionSuccess : evaluate program store fuel callerEnvironment function =
      .ok (.closure arity body captured))
    (terms : List Term)
    (argumentsTyping : ContextualGlobalRuntimeTerms globals assignment definitions slotTypes
      functionSources program callerContext argumentTypes terms)
    (values : List Value)
    (argumentsSuccess : evaluateArgs program store fuel callerEnvironment terms = .ok values)
    (arityAgreement : argumentTypes.length = arity)
    (resultType : Surface.Ty)
    (bodyTyping : ContextualGlobalRuntimeTerm globals assignment definitions slotTypes
      functionSources program (argumentTypes ++ capturedTypes) body resultType)
    (result : Value)
    (bodySuccess : evaluate program store fuel (values ++ captured) body = .ok result)
    (callSuccess : evaluate program store (fuel + 1) callerEnvironment
      (.app function terms) = .ok result) :
    PolyIR.ValueTyped globals result resultType := by
  have argumentsTyped := evaluate_contextualGlobalRuntimeTerms_preserves_type
    globals assignment definitions slotTypes functionSources program programTyped store
    callerContext fuel callerEnvironment callerEnvironmentTyped terms argumentTypes
    argumentsTyping storeLayout storeTyped values argumentsSuccess
  have bodyEnvironmentTyped : ValuesTyped globals (values ++ captured)
      (Surface.interpretTypes assignment (argumentTypes ++ capturedTypes)) := by
    simpa [Surface.interpretTypes_append] using
      (ValuesTyped.append argumentsTyped capturedTyped)
  have bodyResultTyped := evaluate_contextualGlobalRuntimeTerm_preserves_type
    globals assignment definitions slotTypes functionSources program programTyped store
    storeLayout storeTyped (argumentTypes ++ capturedTypes) fuel (values ++ captured)
    bodyEnvironmentTyped body resultType bodyTyping result bodySuccess
  obtain ⟨_callEvaluates, callTyped⟩ :=
    evaluate_closure_application_preserves_type_from_body_result globals program store fuel
      callerEnvironment captured function arity body functionSuccess terms values argumentsSuccess
      (by
        calc
          values.length = (Surface.interpretTypes assignment argumentTypes).length :=
            argumentsTyped.length
          _ = argumentTypes.length := by simp [Surface.interpretTypes]
          _ = arity := arityAgreement)
      result resultType bodySuccess bodyResultTyped
  rw [_callEvaluates] at callSuccess
  cases callSuccess
  exact callTyped

theorem evaluate_contextualGlobalRuntimeLetMany_preserves_type
    (globals : List Surface.Signature) (assignment : Nat → Surface.Ty)
    (definitions : Surface.Definitions) (slotTypes : List Surface.Ty)
    (functionSources : List (Nat × Nat)) (program : List Definition)
    (programTyped : GlobalProgramTyped globals definitions slotTypes functionSources program)
    (store : Store) (context types : List Surface.Ty) (fuel : Nat)
    (environment : List Value) (initializers : List Term) (body : Term)
    (resultType : Surface.Ty)
    (initializersTyped : ContextualGlobalRuntimeTerms globals assignment definitions
      slotTypes functionSources program context types initializers)
    (bodyTyped : ContextualGlobalRuntimeTerm globals assignment definitions slotTypes
      functionSources program (types ++ context) body resultType)
    (storeLayout : store.length = slotTypes.length)
    (storeTyped : StoreWellTyped globals slotTypes store)
    (environmentTyped : ValuesTyped globals environment
      (Surface.interpretTypes assignment context))
    (value : Value)
    (success : evaluate program store fuel environment
      (.letMany initializers body) = .ok value) :
    PolyIR.ValueTyped globals value resultType := by
  cases fuel with
  | zero => simp [evaluate] at success
  | succ fuel =>
      change (do
        let bindings ← evaluateArgs program store fuel environment initializers
        evaluate program store fuel (bindings ++ environment) body) = .ok value at success
      cases initializersResult : evaluateArgs program store fuel environment initializers with
      | error fault => simp [initializersResult, bind, Except.bind] at success
      | ok bindings =>
          have bindingsTyped := evaluate_contextualGlobalRuntimeTerms_preserves_type
            globals assignment definitions slotTypes functionSources program programTyped
            store context fuel environment environmentTyped initializers types initializersTyped
            storeLayout storeTyped bindings initializersResult
          have bodyEnvironmentTyped : ValuesTyped globals (bindings ++ environment)
              (Surface.interpretTypes assignment (types ++ context)) := by
            simpa [Surface.interpretTypes_append] using
              (ValuesTyped.append bindingsTyped environmentTyped)
          have bodySuccess : evaluate program store fuel (bindings ++ environment) body =
              .ok value := by
            simpa [initializersResult, bind, Except.bind, Except.pure] using success
          exact evaluate_contextualGlobalRuntimeTerm_preserves_type globals assignment
            definitions slotTypes functionSources program programTyped store storeLayout storeTyped
            (types ++ context) fuel (bindings ++ environment) bodyEnvironmentTyped body resultType
            bodyTyped value bodySuccess

theorem read_initialized {store : Store} {slot : Nat} {value : Value}
    (entry : store[slot]? = some (some value)) : readGlobal store slot = .ok value := by
  simp [readGlobal, entry]

theorem read_uninitialized {store : Store} {slot : Nat} (entry : store[slot]? = some none) :
    readGlobal store slot = .error (.beforeInitialization slot) := by simp [readGlobal, entry]

theorem initialization_length {fuel : Nat}
    (success : initializeValues program fuel store slot expressions = .ok result) : result.length = store.length := by
  induction fuel generalizing store slot expressions with
  | zero => simp [initializeValues] at success
  | succ fuel ih =>
    cases expressions with
    | nil =>
      have same : store = result := by simpa [initializeValues, pure, Except.pure] using success
      simp [same]
    | cons head tail =>
      cases step : evaluate program store fuel [] head with
      | error fault => simp [initializeValues, step, bind, Except.bind] at success
      | ok value =>
        have rest : initializeValues program fuel (store.set slot (some value)) (slot + 1) tail = .ok result := by
          simpa [initializeValues, step, bind, Except.bind] using success
        simpa using ih rest

theorem initializeValues_preserves_layout_length {fuel : Nat}
    (initialStore result : Store) (slotTypes : List Surface.Ty)
    (slot : Nat) (expressions : List Term)
    (success : initializeValues program fuel initialStore slot expressions = .ok result)
    (initialLayout : initialStore.length = slotTypes.length) :
    result.length = slotTypes.length := by
  rw [initialization_length success, initialLayout]

theorem set_other_lookup (store : Store) (slot index : Nat) (value : Option Value) (different : index ≠ slot) :
    (store.set slot value)[index]? = store[index]? := by
  induction store generalizing slot index with
  | nil => simp [getElem?_def, Nat.not_lt_zero]
  | cons head tail ih =>
    cases slot <;> cases index
    · exact False.elim (different rfl)
    · simp [getElem?_def, Nat.succ_lt_succ_iff]
    · simp [getElem?_def]
    · simpa [getElem?_def, Nat.succ_lt_succ_iff] using ih _ _ (by omega)

/-- Successfully evaluating an initializer prefix only writes the consecutive
slots assigned to that prefix. Every later in-range store position keeps its
previous cell, which lets source-level forward references be shown
uninitialized after an arbitrary successful prefix. -/
theorem initializeValues_success_preserves_slots_after
    (program : List Definition) (fuel : Nat) (store : Store) (start : Nat)
    (expressions : List Term) (result : Store) (index : Nat)
    (success : initializeValues program fuel store start expressions = .ok result)
    (afterPrefix : start + expressions.length ≤ index) :
    result[index]? = store[index]? := by
  induction fuel generalizing store start expressions with
  | zero => simp [initializeValues] at success
  | succ fuel ih =>
      cases expressions with
      | nil =>
          have same : store = result := by
            simpa [initializeValues, pure, Except.pure] using success
          simpa [same]
      | cons head tail =>
          cases step : evaluate program store fuel [] head with
          | error fault => simp [initializeValues, step, bind, Except.bind] at success
          | ok value =>
              have restSuccess :
                  initializeValues program fuel (store.set start (some value))
                    (start + 1) tail = .ok result := by
                simpa [initializeValues, step, bind, Except.bind] using success
              have afterRest : (start + 1) + tail.length ≤ index := by
                simp only [List.length_cons] at afterPrefix
                omega
              have restAgreement := ih (store := store.set start (some value))
                (start := start + 1) (expressions := tail) restSuccess afterRest
              have different : index ≠ start := by omega
              rw [restAgreement]
              exact set_other_lookup store start index (some value) different

theorem StoreWellTyped.set (globals : List Surface.Signature) (slotTypes : List Surface.Ty)
    (store : Store) (slot : Nat) (value : PolyIR.Value) (type : Surface.Ty)
    (storeTyped : StoreWellTyped globals slotTypes store)
    (slotFits : slot < store.length)
    (slotType : slotTypes.get? slot = some type)
    (valueTyped : PolyIR.ValueTyped globals value type) :
    StoreWellTyped globals slotTypes (store.set slot (some value)) := by
  intro index oldValue oldType lookup typeLookup
  by_cases same : index = slot
  · subst index
    have changedLookup : (store.set slot (some value))[slot]? = some (some oldValue) := by
      rw [indexed_lookup_eq_get?]
      exact lookup
    have valueEq : value = oldValue := by
      have slotFits' : slot < (store.set slot (some value)).length := by
        simpa only [List.length_set] using slotFits
      have optionEq : some ((store.set slot (some value))[slot]'slotFits') =
          some (some oldValue) := by
        simpa only [getElem?_def, dif_pos slotFits'] using changedLookup
      have elementEq : (store.set slot (some value))[slot]'slotFits' = some oldValue :=
        Option.some.inj optionEq
      have setValue : (store.set slot (some value))[slot]'slotFits' = some value :=
        List.get_set_eq store slot (some value) slotFits'
      exact Option.some.inj (setValue.symm.trans elementEq)
    have typeEq : type = oldType := Option.some.inj (slotType.symm.trans typeLookup)
    subst oldValue
    subst oldType
    exact valueTyped
  · have changedLookup : (store.set slot (some value))[index]? = some (some oldValue) := by
      rw [indexed_lookup_eq_get?]
      exact lookup
    have oldLookup : store[index]? = some (some oldValue) := by
      calc
        store[index]? = (store.set slot (some value))[index]? :=
          (set_other_lookup store slot index (some value) same).symm
        _ = some (some oldValue) := changedLookup
    have oldLookup' : store.get? index = some (some oldValue) := by
      rw [← indexed_lookup_eq_get?]
      exact oldLookup
    exact storeTyped index oldValue oldType oldLookup' typeLookup

def InitializerTypesAgree (slotTypes : List Surface.Ty) : Nat → List Term → Prop
  | _, [] => True
  | slot, _ :: tail =>
      ∃ type, slotTypes.get? slot = some type ∧ InitializerTypesAgree slotTypes (slot + 1) tail

theorem InitializerTypesAgree.slot_type_at (slotTypes : List Surface.Ty)
    (slot : Nat) (expressions : List Term)
    (agreed : InitializerTypesAgree slotTypes slot expressions)
    (offset : Nat) (within : offset < expressions.length) :
    ∃ type, slotTypes.get? (slot + offset) = some type := by
  induction expressions generalizing slot offset with
  | nil => exact False.elim (Nat.not_lt_zero _ within)
  | cons head tail ih =>
      cases offset with
      | zero =>
          rcases agreed with ⟨type, slotType, _⟩
          exact ⟨type, by simpa using slotType⟩
      | succ offset =>
          rcases agreed with ⟨_, _, tailAgreed⟩
          have withinTail : offset < tail.length := by
            simpa only [List.length_cons, Nat.add_one, Nat.succ_lt_succ_iff] using within
          obtain ⟨type, found⟩ := ih (slot := slot + 1) (offset := offset) tailAgreed withinTail
          have indexEq : slot + Nat.succ offset = (slot + 1) + offset := by omega
          exact ⟨type, by rw [indexEq]; exact found⟩

/- A stronger row invariant identifies each initializer with both its slot
type and the arithmetic fragment whose evaluator has already been proved
type safe. -/
def ArithmeticInitializerTypesAgree (slotTypes : List Surface.Ty) :
    Nat → List Term → Prop
  | _, [] => True
  | slot, expression :: tail =>
      ∃ type, slotTypes.get? slot = some type ∧ ArithmeticTerm expression type ∧
        ArithmeticInitializerTypesAgree slotTypes (slot + 1) tail

theorem initializeValues_arithmetic_preserves_typed
    (globals : List Surface.Signature) (program : List Definition)
    (slotTypes : List Surface.Ty) (fuel : Nat) (store : Store) (slot : Nat)
    (expressions : List Term) (result : Store)
    (storeTyped : StoreWellTyped globals slotTypes store)
    (typesAgree : ArithmeticInitializerTypesAgree slotTypes slot expressions)
    (slotsFit : ∀ offset, offset < expressions.length → slot + offset < store.length)
    (success : initializeValues program fuel store slot expressions = .ok result) :
    StoreWellTyped globals slotTypes result := by
  induction fuel generalizing store slot expressions with
  | zero => simp [initializeValues] at success
  | succ fuel ih =>
      cases expressions with
      | nil =>
          have same : store = result := by
            simpa [initializeValues, pure, Except.pure] using success
          simpa [same] using storeTyped
      | cons head tail =>
          rcases typesAgree with ⟨type, typeAtSlot, headArithmetic, tailTypesAgree⟩
          cases step : evaluate program store fuel [] head with
          | error fault => simp [initializeValues, step, bind, Except.bind] at success
          | ok value =>
              have valueTyped := evaluate_arithmetic_preserves_type globals program store
                fuel [] head type headArithmetic value step
              have slotFits : slot < store.length := slotsFit 0 (by simp)
              have nextStoreTyped := StoreWellTyped.set globals slotTypes store slot value type
                storeTyped slotFits typeAtSlot valueTyped
              have restSuccess :
                  initializeValues program fuel (store.set slot (some value)) (slot + 1) tail =
                    .ok result := by
                simpa [initializeValues, step, bind, Except.bind] using success
              apply ih (store := store.set slot (some value)) (slot := slot + 1)
                (expressions := tail) nextStoreTyped tailTypesAgree
              · intro offset below
                have shifted := slotsFit (offset + 1) (by simp; omega)
                rw [List.length_set]
                omega
              · exact restSuccess

/- Initializer rows may refer to typed global functions as well as use the
local arithmetic/constructor fragment. Their declared cell type is carried
along with the term typing, so each successful write preserves the complete
GlobalIR store invariant. -/
def ContextualGlobalInitializerTypesAgree (globals : List Surface.Signature)
    (assignment : Nat → Surface.Ty) (slotTypes : List Surface.Ty) :
    Nat → List Term → Prop
  | _, [] => True
  | slot, expression :: tail =>
      ∃ type, slotTypes.get? slot = some type ∧
        ContextualGlobalArithmeticTerm globals assignment [] expression type ∧
        ContextualGlobalInitializerTypesAgree globals assignment slotTypes (slot + 1) tail

/-- A stronger initializer row invariant for lowered value declarations that
may read already initialized top-level slots through generated getters. -/
def ContextualGlobalRuntimeInitializerTypesAgree (globals : List Surface.Signature)
    (assignment : Nat → Surface.Ty) (definitions : Surface.Definitions)
    (slotTypes : List Surface.Ty) (functionSources : List (Nat × Nat))
    (program : List Definition) : Nat → List Term → Prop
  | _, [] => True
  | slot, expression :: tail =>
      ∃ type, slotTypes.get? slot = some type ∧
        ContextualGlobalRuntimeTerm globals assignment definitions slotTypes
          functionSources program [] expression type ∧
        ContextualGlobalRuntimeInitializerTypesAgree globals assignment definitions
          slotTypes functionSources program (slot + 1) tail

theorem initializeValues_contextualGlobal_preserves_typed
    (globals : List Surface.Signature) (assignment : Nat → Surface.Ty)
    (definitions : Surface.Definitions) (slotTypes : List Surface.Ty)
    (functionSources : List (Nat × Nat)) (program : List Definition)
    (programTyped : GlobalProgramTyped globals definitions slotTypes functionSources program)
    (fuel : Nat) (store : Store) (slot : Nat) (expressions : List Term) (result : Store)
    (storeTyped : StoreWellTyped globals slotTypes store)
    (typesAgree : ContextualGlobalInitializerTypesAgree globals assignment slotTypes
      slot expressions)
    (slotsFit : ∀ offset, offset < expressions.length → slot + offset < store.length)
    (success : initializeValues program fuel store slot expressions = .ok result) :
    StoreWellTyped globals slotTypes result := by
  induction fuel generalizing store slot expressions with
  | zero => simp [initializeValues] at success
  | succ fuel ih =>
      cases expressions with
      | nil =>
          have same : store = result := by
            simpa [initializeValues, pure, Except.pure] using success
          simpa [same] using storeTyped
      | cons head tail =>
          rcases typesAgree with ⟨type, typeAtSlot, headTyped, tailTypesAgree⟩
          cases step : evaluate program store fuel [] head with
          | error fault => simp [initializeValues, step, bind, Except.bind] at success
          | ok value =>
              have valueTyped := evaluate_contextualGlobalArithmeticTerm_preserves_type
                globals assignment definitions slotTypes functionSources program programTyped
                store [] fuel [] .nil head type headTyped value step
              have slotFits : slot < store.length := slotsFit 0 (by simp)
              have nextStoreTyped := StoreWellTyped.set globals slotTypes store slot value type
                storeTyped slotFits typeAtSlot valueTyped
              have restSuccess :
                  initializeValues program fuel (store.set slot (some value)) (slot + 1) tail =
                    .ok result := by
                simpa [initializeValues, step, bind, Except.bind] using success
              apply ih (store := store.set slot (some value)) (slot := slot + 1)
                (expressions := tail) nextStoreTyped tailTypesAgree
              · intro offset below
                have shifted := slotsFit (offset + 1) (by simp; omega)
                rw [List.length_set]
                omega
              · exact restSuccess

theorem initializeValues_contextualGlobalRuntime_preserves_typed
    (globals : List Surface.Signature) (assignment : Nat → Surface.Ty)
    (definitions : Surface.Definitions) (slotTypes : List Surface.Ty)
    (functionSources : List (Nat × Nat)) (program : List Definition)
    (programTyped : GlobalProgramTyped globals definitions slotTypes functionSources program)
    (fuel : Nat) (store : Store) (slot : Nat) (expressions : List Term) (result : Store)
    (storeLayout : store.length = slotTypes.length)
    (storeTyped : StoreWellTyped globals slotTypes store)
    (typesAgree : ContextualGlobalRuntimeInitializerTypesAgree globals assignment definitions
      slotTypes functionSources program slot expressions)
    (slotsFit : ∀ offset, offset < expressions.length → slot + offset < store.length)
    (success : initializeValues program fuel store slot expressions = .ok result) :
    StoreWellTyped globals slotTypes result := by
  induction fuel generalizing store slot expressions with
  | zero => simp [initializeValues] at success
  | succ fuel ih =>
      cases expressions with
      | nil =>
          have same : store = result := by
            simpa [initializeValues, pure, Except.pure] using success
          simpa [same] using storeTyped
      | cons head tail =>
          rcases typesAgree with ⟨type, typeAtSlot, headTyped, tailTypesAgree⟩
          cases step : evaluate program store fuel [] head with
          | error fault => simp [initializeValues, step, bind, Except.bind] at success
          | ok value =>
              have valueTyped := evaluate_contextualGlobalRuntimeTerm_preserves_type
                globals assignment definitions slotTypes functionSources program programTyped
                store storeLayout storeTyped [] fuel [] ValuesTyped.nil head type
                headTyped value step
              have slotFits : slot < store.length := slotsFit 0 (by simp)
              have nextStoreTyped := StoreWellTyped.set globals slotTypes store slot value type
                storeTyped slotFits typeAtSlot valueTyped
              have restSuccess :
                  initializeValues program fuel (store.set slot (some value)) (slot + 1) tail =
                    .ok result := by
                simpa [initializeValues, step, bind, Except.bind] using success
              apply ih (store := store.set slot (some value)) (slot := slot + 1)
                (expressions := tail) (by simpa using storeLayout) nextStoreTyped tailTypesAgree
              · intro offset below
                have shifted := slotsFit (offset + 1) (by simp; omega)
                rw [List.length_set]
                omega
              · exact restSuccess

theorem initializeValues_preserves_typed (globals : List Surface.Signature)
    (program : List Definition) (slotTypes : List Surface.Ty) (fuel : Nat)
    (store : Store) (slot : Nat) (expressions : List Term) (result : Store)
    (storeTyped : StoreWellTyped globals slotTypes store)
    (typesAgree : InitializerTypesAgree slotTypes slot expressions)
    (slotsFit : ∀ offset, offset < expressions.length → slot + offset < store.length)
    (evaluationTyped : ∀ currentStore remaining expression value type,
      evaluate program currentStore remaining [] expression = .ok value →
        PolyIR.ValueTyped globals value type)
    (success : initializeValues program fuel store slot expressions = .ok result) :
    StoreWellTyped globals slotTypes result := by
  induction fuel generalizing store slot expressions with
  | zero => simp [initializeValues] at success
  | succ fuel ih =>
      cases expressions with
      | nil =>
          have same : store = result := by
            simpa [initializeValues, pure, Except.pure] using success
          simpa [same] using storeTyped
      | cons head tail =>
          rcases typesAgree with ⟨type, typeAtSlot, tailTypesAgree⟩
          cases step : evaluate program store fuel [] head with
          | error fault => simp [initializeValues, step, bind, Except.bind] at success
          | ok value =>
              have valueTyped := evaluationTyped store fuel head value type step
              have slotFits : slot < store.length := slotsFit 0 (by simp)
              have nextStoreTyped := StoreWellTyped.set globals slotTypes store slot value type
                storeTyped slotFits typeAtSlot valueTyped
              have restSuccess :
                  initializeValues program fuel (store.set slot (some value)) (slot + 1) tail =
                    .ok result := by
                simpa [initializeValues, step, bind, Except.bind] using success
              apply ih (store := store.set slot (some value)) (slot := slot + 1)
                (expressions := tail) nextStoreTyped tailTypesAgree
              · intro offset below
                have shifted := slotsFit (offset + 1) (by simp; omega)
                rw [List.length_set]
                omega
              · exact restSuccess

private theorem replicate_none_lookup_ne_initialized (count index : Nat) (value : PolyIR.Value) :
    (List.replicate count (none : Option PolyIR.Value)).get? index ≠ some (some value) := by
  induction count generalizing index with
  | zero => cases index <;> simp
  | succ count ih =>
      cases index with
      | zero => simp
      | succ index => simpa [List.replicate] using ih index

theorem empty_store_well_typed (globals : List Surface.Signature)
    (slotTypes : List Surface.Ty) (slotCount : Nat) :
    StoreWellTyped globals slotTypes (List.replicate slotCount none) := by
  intro slot value type initialized _
  exact False.elim (replicate_none_lookup_ne_initialized slotCount slot value initialized)

theorem initializeValues_from_empty_preserves_typed (globals : List Surface.Signature)
    (program : List Definition) (slotTypes : List Surface.Ty) (fuel : Nat)
    (expressions : List Term) (result : Store)
    (typesAgree : InitializerTypesAgree slotTypes 0 expressions)
    (evaluationTyped : ∀ currentStore remaining expression value type,
      evaluate program currentStore remaining [] expression = .ok value →
        PolyIR.ValueTyped globals value type)
    (success : initializeValues program fuel
      (List.replicate expressions.length none) 0 expressions = .ok result) :
    StoreWellTyped globals slotTypes result := by
  apply initializeValues_preserves_typed globals program slotTypes fuel
    (List.replicate expressions.length none) 0 expressions result
    (empty_store_well_typed globals slotTypes expressions.length) typesAgree
  · intro offset below
    simpa [List.length_replicate] using below
  · exact evaluationTyped
  · exact success

/-- A successful typed initializer batch followed by a typed zero-argument
entry call preserves both the initialized-store invariant and the entry result
type. This composes the initializer loop with the observable `run` path; the
remaining evaluator premise is the contextual GlobalIR fragment for each
initializer and the entry body. -/
theorem run_zero_arity_entry_preserves_type
    (globals : List Surface.Signature) (assignment : Nat → Surface.Ty)
    (definitions : Surface.Definitions) (slotTypes : List Surface.Ty)
    (functionSources : List (Nat × Nat)) (runtimeDefinitions : List Definition)
    (programTyped : GlobalProgramTyped globals definitions slotTypes functionSources
      runtimeDefinitions)
    (program : Program) (fuel entry : Nat) (initializedStore : Store)
    (runtime : RuntimeDefinition) (resultType : Surface.Ty) (result : Value)
    (initializerTypes : ContextualGlobalInitializerTypesAgree globals assignment
      slotTypes 0 program.initializers)
    (entryRuntime : runtimeDefinitions[entry]? = some (.function runtime))
    (entryArity : runtime.arity = 0)
    (entryBodyTyped : ContextualGlobalArithmeticTerm globals assignment []
      runtime.body resultType)
    (initialization : initializeValues runtimeDefinitions (fuel + 1)
      (List.replicate program.initializers.length none) 0 program.initializers =
      .ok initializedStore)
    (runSuccess : run ⟨runtimeDefinitions, program.initializers, entry⟩ (fuel + 1) =
      .ok result)
    (fuelPositive : 0 < fuel) :
    StoreWellTyped globals slotTypes initializedStore ∧
      PolyIR.ValueTyped globals result resultType := by
  have initializedTyped := initializeValues_contextualGlobal_preserves_typed
    globals assignment definitions slotTypes functionSources runtimeDefinitions programTyped
    (fuel + 1) (List.replicate program.initializers.length none) 0 program.initializers
    initializedStore (empty_store_well_typed globals slotTypes program.initializers.length)
    initializerTypes (by
      intro offset below
      simpa [List.length_replicate] using below) initialization
  have entryStep : evaluate runtimeDefinitions initializedStore (fuel + 1) []
      (.app (.global entry) []) = .ok result := by
    have runExpanded : (initializeValues runtimeDefinitions (fuel + 1)
        (List.replicate program.initializers.length none) 0 program.initializers).bind
        (fun store => evaluate runtimeDefinitions store (fuel + 1) []
          (.app (.global entry) [])) = .ok result := by
      simpa [run] using runSuccess
    rw [initialization] at runExpanded
    exact runExpanded
  have globalSuccess : evaluate runtimeDefinitions initializedStore fuel []
      (.global entry) = .ok (.global entry) := by
    cases fuel with
    | zero => omega
    | succ remaining => simp [evaluate, entryRuntime, pure, Except.pure]
  have argumentsSuccess : evaluateArgs runtimeDefinitions initializedStore fuel [] [] =
      .ok [] := by
    cases fuel with
    | zero => omega
    | succ remaining => simp [evaluateArgs, pure, Except.pure]
  have bodySuccess : evaluate runtimeDefinitions initializedStore fuel [] runtime.body =
      .ok result := by
    have callEq : evaluate runtimeDefinitions initializedStore (fuel + 1) []
        (.app (.global entry) []) =
        evaluate runtimeDefinitions initializedStore fuel [] runtime.body := by
      simp [evaluate, globalSuccess, argumentsSuccess, entryRuntime, entryArity,
        bind, Except.bind, Except.pure, pure]
    rw [callEq] at entryStep
    exact entryStep
  have typedResult := evaluate_contextual_zero_arity_global_call_preserves_type
    globals assignment definitions slotTypes functionSources runtimeDefinitions programTyped
    initializedStore fuel entry runtime fuelPositive entryRuntime entryArity resultType
    entryBodyTyped bodySuccess entryStep
  exact ⟨initializedTyped, typedResult⟩

theorem initialized_prefix_unchanged {fuel : Nat}
    (success : initializeValues program fuel store slot expressions = .ok result)
    (earlier : index < slot) : result[index]? = store[index]? := by
  induction fuel generalizing store slot expressions with
  | zero => simp [initializeValues] at success
  | succ fuel ih =>
    cases expressions with
    | nil =>
      have same : store = result := by simpa [initializeValues, pure, Except.pure] using success
      simp [same]
    | cons head tail =>
      cases step : evaluate program store fuel [] head with
      | error fault => simp [initializeValues, step, bind, Except.bind] at success
      | ok value =>
        have rest : initializeValues program fuel (store.set slot (some value)) (slot + 1) tail = .ok result := by
          simpa [initializeValues, step, bind, Except.bind] using success
        exact (ih rest (by omega)).trans (set_other_lookup store slot index (some value) (by omega))

theorem initialized_cells_present {fuel : Nat}
    (success : initializeValues program fuel store slot expressions = .ok result)
    (fits : slot + expressions.length ≤ store.length)
    (selected : slot ≤ index ∧ index < slot + expressions.length) :
    ∃ value, result[index]? = some (some value) := by
  induction fuel generalizing store slot expressions with
  | zero => simp [initializeValues] at success
  | succ fuel ih =>
    cases expressions with
    | nil => simp only [List.length_nil, Nat.add_zero] at selected; omega
    | cons head tail =>
      cases step : evaluate program store fuel [] head with
      | error fault => simp [initializeValues, step, bind, Except.bind] at success
      | ok value =>
        have rest : initializeValues program fuel (store.set slot (some value)) (slot + 1) tail = .ok result := by
          simpa [initializeValues, step, bind, Except.bind] using success
        simp only [List.length_cons] at fits selected
        by_cases current : index = slot
        · subst index
          have earlier := initialized_prefix_unchanged rest (index := slot) (by omega)
          refine ⟨value, earlier.trans ?_⟩
          have bound : slot < store.length := by omega
          simp only [getElem?_def, List.length_set, dif_pos bound, Option.some.injEq]
          exact List.get_set_eq store slot (some value) (by simpa using bound)
        · apply ih rest
          · simpa only [List.length_set] using (show slot + 1 + tail.length ≤ store.length by omega)
          · constructor <;> omega

/-- A top-level getter can also be the program entry. If its slot occurs in the
successfully initialized batch, typed initializer preservation makes the
store well typed and the successful `run` result has the getter's declared
type. -/
theorem run_getter_entry_preserves_type
    (globals : List Surface.Signature) (assignment : Nat → Surface.Ty)
    (definitions : Surface.Definitions) (slotTypes : List Surface.Ty)
    (functionSources : List (Nat × Nat)) (runtimeDefinitions : List Definition)
    (programTyped : GlobalProgramTyped globals definitions slotTypes functionSources
      runtimeDefinitions)
    (program : Program) (fuel entry slot : Nat) (initializedStore : Store)
    (result : Value)
    (initializerTypes : ContextualGlobalInitializerTypesAgree globals assignment
      slotTypes 0 program.initializers)
    (entryGetter : runtimeDefinitions[entry]? = some (.getter slot))
    (slotInitializedByBatch : slot < program.initializers.length)
    (initialization : initializeValues runtimeDefinitions (fuel + 2)
      (List.replicate program.initializers.length none) 0 program.initializers =
      .ok initializedStore)
    (runSuccess : run ⟨runtimeDefinitions, program.initializers, entry⟩ (fuel + 2) =
      .ok result) :
    ∃ type, PolyIR.ValueTyped globals result type := by
  have initializedTyped := initializeValues_contextualGlobal_preserves_typed
    globals assignment definitions slotTypes functionSources runtimeDefinitions programTyped
    (fuel + 2) (List.replicate program.initializers.length none) 0 program.initializers
    initializedStore (empty_store_well_typed globals slotTypes program.initializers.length)
    initializerTypes (by
      intro offset below
      simpa [List.length_replicate] using below) initialization
  have slotPopulated : ∃ value,
      initializedStore[slot]? = some (some value) :=
    initialized_cells_present initialization (by simp) (by constructor <;> omega)
  obtain ⟨storedValue, populated⟩ := slotPopulated
  obtain ⟨type, getterResult, _signature, _wellFormed, _slotType,
      getterEvaluation, resultTyped⟩ :=
    typed_getter_call_preserves_type runtimeDefinitions globals definitions slotTypes
      functionSources initializedStore fuel entry slot storedValue programTyped entryGetter
      initializedTyped populated
  have runStep : evaluate runtimeDefinitions initializedStore (fuel + 2) []
      (.app (.global entry) []) = .ok result := by
    have runExpanded : (initializeValues runtimeDefinitions (fuel + 2)
        (List.replicate program.initializers.length none) 0 program.initializers).bind
        (fun store => evaluate runtimeDefinitions store (fuel + 2) []
          (.app (.global entry) [])) = .ok result := by
      simpa [run] using runSuccess
    rw [initialization] at runExpanded
    exact runExpanded
  rw [getterEvaluation] at runStep
  injection runStep with resultEq
  subst result
  exact ⟨type, resultTyped⟩

/-- With layout-aligned initializer and slot counts, a typed getter entry after
successful initialization either returns a value of its declared type or
reports exactly the `beforeInitialization` fault for its slot. -/
theorem run_getter_entry_type_safe_or_early_read
    (globals : List Surface.Signature) (assignment : Nat → Surface.Ty)
    (definitions : Surface.Definitions) (slotTypes : List Surface.Ty)
    (functionSources : List (Nat × Nat)) (runtimeDefinitions : List Definition)
    (programTyped : GlobalProgramTyped globals definitions slotTypes functionSources
      runtimeDefinitions)
    (program : Program) (fuel entry slot : Nat) (initializedStore : Store)
    (initializerTypes : ContextualGlobalInitializerTypesAgree globals assignment
      slotTypes 0 program.initializers)
    (initializerCount : program.initializers.length = slotTypes.length)
    (entryGetter : runtimeDefinitions[entry]? = some (.getter slot))
    (initialization : initializeValues runtimeDefinitions (fuel + 2)
      (List.replicate program.initializers.length none) 0 program.initializers =
      .ok initializedStore) :
    ∃ type, globals[entry]? = some ⟨0, [], type⟩ ∧ slotTypes[slot]? = some type ∧
      ((∃ value, run ⟨runtimeDefinitions, program.initializers, entry⟩ (fuel + 2) =
          .ok value ∧ PolyIR.ValueTyped globals value type) ∨
        run ⟨runtimeDefinitions, program.initializers, entry⟩ (fuel + 2) =
          .error (.beforeInitialization slot)) := by
  have initializedTyped := initializeValues_contextualGlobal_preserves_typed
    globals assignment definitions slotTypes functionSources runtimeDefinitions programTyped
    (fuel + 2) (List.replicate program.initializers.length none) 0 program.initializers
    initializedStore (empty_store_well_typed globals slotTypes program.initializers.length)
    initializerTypes (by
      intro offset below
      simpa [List.length_replicate] using below) initialization
  have storeLayout : initializedStore.length = slotTypes.length := by
    calc
      initializedStore.length = (List.replicate program.initializers.length
          (none : Option Value)).length := initialization_length initialization
      _ = program.initializers.length := List.length_replicate _ _
      _ = slotTypes.length := initializerCount
  obtain ⟨type, signature, slotType, result⟩ :=
    typed_getter_call_type_safe_or_early_read runtimeDefinitions globals definitions slotTypes
      functionSources initializedStore fuel entry slot programTyped entryGetter storeLayout
      initializedTyped
  have runEq : run ⟨runtimeDefinitions, program.initializers, entry⟩ (fuel + 2) =
      evaluate runtimeDefinitions initializedStore (fuel + 2) []
        (.app (.global entry) []) := by
    change (initializeValues runtimeDefinitions (fuel + 2)
      (List.replicate program.initializers.length none) 0 program.initializers).bind
      (fun store => evaluate runtimeDefinitions store (fuel + 2) []
        (.app (.global entry) [])) = _
    rw [initialization]
    rfl
  refine ⟨type, signature, slotType, ?_⟩
  rcases result with success | early
  · rcases success with ⟨value, evaluated, valueTyped⟩
    exact Or.inl ⟨value, by simpa [runEq] using evaluated, valueTyped⟩
  · exact Or.inr (by simpa [runEq] using early)

theorem initializeValues_contextualGlobal_then_getter_preserves_type
    (globals : List Surface.Signature) (assignment : Nat → Surface.Ty)
    (definitions : Surface.Definitions) (slotTypes : List Surface.Ty)
    (functionSources : List (Nat × Nat)) (program : List Definition)
    (programTyped : GlobalProgramTyped globals definitions slotTypes functionSources program)
    (fuel readFuel : Nat) (store : Store) (base slot : Nat)
    (expressions : List Term) (initializedStore : Store) (type : Surface.Ty)
    (getterIndex : Nat)
    (storeTyped : StoreWellTyped globals slotTypes store)
    (typesAgree : ContextualGlobalInitializerTypesAgree globals assignment slotTypes
      base expressions)
    (slotsFit : ∀ offset, offset < expressions.length → base + offset < store.length)
    (batchFits : base + expressions.length ≤ store.length)
    (selected : base ≤ slot ∧ slot < base + expressions.length)
    (slotType : slotTypes[slot]? = some type)
    (getter : program[getterIndex]? = some (.getter slot))
    (initialized : initializeValues program fuel store base expressions =
      .ok initializedStore) :
    ∃ result,
      evaluate program initializedStore (readFuel + 2) []
        (.app (.global getterIndex) []) = .ok result ∧
      PolyIR.ValueTyped globals result type := by
  have storeAfterTyped := initializeValues_contextualGlobal_preserves_typed
    globals assignment definitions slotTypes functionSources program programTyped fuel store
    base expressions initializedStore storeTyped typesAgree slotsFit initialized
  obtain ⟨storedValue, populated⟩ := initialized_cells_present initialized batchFits selected
  exact getter_call_preserves_type program globals slotTypes initializedStore readFuel
    getterIndex slot storedValue type getter slotType storeAfterTyped populated

/-- Successful initialization of a decoded mixed top-level program populates
every value slot in the layout established by the decoder. This connects the
decode-time initializer count to the executable GlobalIR store update loop. -/
theorem decodedProgram_successful_initialization_populates_slot
    (decodeFuel initFuel : Nat) (forms : List CBindingWalk.Node)
    (functions : Named.Definitions) (slotTypes : List Surface.Ty)
    (initializers : List Named.Expr) (entry slot : Nat) (result : Store)
    (decoded : Named.decodeTopLevelProgram decodeFuel forms =
      some (functions, slotTypes, initializers))
    (slotBound : slot < slotTypes.length)
    (initialized : initializeValues
      (programOfNamed functions slotTypes initializers entry).definitions
      initFuel (List.replicate
        (programOfNamed functions slotTypes initializers entry).initializers.length none)
      0 (programOfNamed functions slotTypes initializers entry).initializers = .ok result) :
    ∃ value, result[slot]? = some (some value) := by
  have initializerCount := decodedProgram_initializer_count decodeFuel forms functions
    slotTypes initializers entry decoded
  have fits : 0 + (programOfNamed functions slotTypes initializers entry).initializers.length ≤
      (List.replicate
        (programOfNamed functions slotTypes initializers entry).initializers.length
        (none : Option Value)).length := by
    simp
  have selected : 0 ≤ slot ∧ slot <
      0 + (programOfNamed functions slotTypes initializers entry).initializers.length := by
    constructor
    · omega
    · omega
  exact initialized_cells_present initialized fits selected

/-- Decode success fixes the getter's mixed-program index, and successful
initialization makes that getter return the value committed to its slot. -/
theorem decodedProgram_successful_initialization_getter_reads_slot
    (decodeFuel initFuel readFuel : Nat) (forms : List CBindingWalk.Node)
    (functions : Named.Definitions) (slotTypes : List Surface.Ty)
    (initializers : List Named.Expr) (entry slot : Nat) (result : Store)
    (decoded : Named.decodeTopLevelProgram decodeFuel forms =
      some (functions, slotTypes, initializers))
    (slotBound : slot < slotTypes.length)
    (initialized : initializeValues
      (programOfNamed functions slotTypes initializers entry).definitions initFuel
      (List.replicate
        (programOfNamed functions slotTypes initializers entry).initializers.length
        (none : Option Value))
      0 (programOfNamed functions slotTypes initializers entry).initializers = .ok result) :
    ∃ value,
      result[slot]? = some (some value) ∧
      evaluate (programOfNamed functions slotTypes initializers entry).definitions result
        (readFuel + 2) [] (.app (.global (functions.length + slot)) []) = .ok value := by
  obtain ⟨value, stored⟩ := decodedProgram_successful_initialization_populates_slot
    decodeFuel initFuel forms functions slotTypes initializers entry slot result decoded
    slotBound initialized
  obtain ⟨_definitionsLength, _initializerLength, getter⟩ :=
    decodedProgram_layout decodeFuel forms functions slotTypes initializers entry slot decoded slotBound
  exact ⟨value, stored, getter_call_reads_current_store
    (programOfNamed functions slotTypes initializers entry).definitions result readFuel
    (functions.length + slot) slot value getter stored⟩


end NLisp.GlobalIR
