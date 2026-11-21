import NLisp.PolymorphicSafety
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
def functionSourcesFor (functionCount : Nat) : List (Nat × Nat) :=
  (List.range functionCount).map (fun index => (index, index))

theorem mem_functionSourcesFor_iff (functionCount runtimeIndex sourceIndex : Nat) :
    (runtimeIndex, sourceIndex) ∈ functionSourcesFor functionCount ↔
      runtimeIndex = sourceIndex ∧ sourceIndex < functionCount := by
  simp only [functionSourcesFor, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨index, bound, pairEq⟩
    have fields := Prod.mk.inj pairEq
    rcases fields with ⟨runtimeEq, sourceEq⟩
    subst runtimeIndex
    subst sourceIndex
    exact ⟨rfl, bound⟩
  · rintro ⟨sameIndex, bound⟩
    subst runtimeIndex
    exact ⟨sourceIndex, bound, rfl⟩

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

theorem getterFor_getterMappingsFrom (firstIndex index : Nat) (types : List Surface.Ty)
    (bound : index < types.length) :
    getterFor (getterMappingsFrom firstIndex types) (firstIndex + index) =
      some (firstIndex + index) := by
  induction types generalizing firstIndex index with
  | nil => simp at bound
  | cons type tail ih =>
      cases index with
      | zero => simp [getterMappingsFrom, getterFor]
      | succ index =>
          have tailBound : index < tail.length := by simpa using bound
          have different : firstIndex ≠ firstIndex + Nat.succ index := by omega
          have tailMapped := ih (firstIndex + 1) index tailBound
          have slotEq : firstIndex + Nat.succ index = firstIndex + 1 + index := by omega
          simpa [getterMappingsFrom, getterFor, different, slotEq] using tailMapped

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
  | .unit => .unit
  | .lam arity body => .lam arity (lowerGlobalReads getters body)
  | .app (.global index) arguments =>
      let arguments' := lowerGlobalReadsMany getters arguments
      match getterFor getters index with
      | some getter => .app (.app (.global getter) []) arguments'
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
def namedFunctionEntries (functions : Named.Definitions) (slotTypes : List Surface.Ty) :
    List Definition :=
  (Named.lowerDefinitions functions).map (fun runtime =>
    .function ⟨runtime.arity,
      lowerGlobalReads (getterMappings functions.length slotTypes) runtime.body⟩)

@[simp] theorem namedFunctionEntries_length (functions : Named.Definitions)
    (slotTypes : List Surface.Ty) :
    (namedFunctionEntries functions slotTypes).length = functions.length := by
  simp [namedFunctionEntries]

def assembleNamedProgram (functions : Named.Definitions) (slotTypes : List Surface.Ty) :
    List Definition :=
  namedFunctionEntries functions slotTypes ++ getterEntries slotTypes

@[simp] theorem assembleNamedProgram_length (functions : Named.Definitions)
    (slotTypes : List Surface.Ty) :
    (assembleNamedProgram functions slotTypes).length = functions.length + slotTypes.length := by
  simp [assembleNamedProgram, getterEntries]

def lowerNamedInitializers (functions : Named.Definitions) (slotTypes : List Surface.Ty)
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
  simp [assembleProgram, getterEntries]

@[simp] theorem functionEntries_length (definitions : Surface.Definitions)
    (slotTypes : List Surface.Ty) :
    (functionEntries definitions slotTypes).length = definitions.length := by
  simp [functionEntries]

theorem getterEntriesFrom_lookup (firstSlot index : Nat) (types : List Surface.Ty)
    (bound : index < types.length) :
    (getterEntriesFrom firstSlot types)[index]? = some (.getter (firstSlot + index)) := by
  induction types generalizing firstSlot index with
  | nil => simp at bound
  | cons type tail ih =>
      cases index with
      | zero => simp [getterEntriesFrom, getElem?_def]
      | succ index =>
          have tailBound : index < tail.length := by simpa using bound
          have slotEq : firstSlot + Nat.succ index = firstSlot + 1 + index := by omega
          simpa [getterEntriesFrom, getElem?_def, slotEq] using
            ih (firstSlot + 1) index tailBound

theorem getterEntriesFrom_entry (firstSlot index slot : Nat) (types : List Surface.Ty)
    (entry : (getterEntriesFrom firstSlot types)[index]? = some (.getter slot)) :
    index < types.length ∧ slot = firstSlot + index := by
  induction types generalizing firstSlot index slot with
  | nil => simp [getterEntriesFrom, getElem?_def] at entry
  | cons type tail ih =>
      cases index with
      | zero =>
          simp [getterEntriesFrom, getElem?_def] at entry
          subst slot
          simp
      | succ index =>
          have tailEntry :
              (getterEntriesFrom (firstSlot + 1) tail)[index]? = some (.getter slot) := by
            simpa [getterEntriesFrom, getElem?_def] using entry
          obtain ⟨tailBound, slotEq⟩ := ih (firstSlot + 1) index slot tailEntry
          have indexEq : firstSlot + Nat.succ index = firstSlot + 1 + index := by omega
          exact ⟨Nat.succ_lt_succ tailBound, slotEq.trans indexEq.symm⟩

theorem append_lookup_right (left right : List α) (index : Nat) :
    (left ++ right)[left.length + index]? = right[index]? := by
  induction left with
  | nil => simp [getElem?_def]
  | cons head tail ih =>
      simpa [List.length_cons, Nat.succ_add, getElem?_def] using ih index

theorem append_lookup_left (left right : List α) (index : Nat)
    (bound : index < left.length) :
    (left ++ right)[index]? = left[index]? := by
  induction left generalizing index with
  | nil => simp at bound
  | cons head tail ih =>
      cases index with
      | zero => simp [getElem?_def]
      | succ index =>
          have tailBound : index < tail.length := by simpa using bound
          simpa [getElem?_def] using ih right index tailBound

theorem lookup_some_lt {α : Type} (values : List α) (index : Nat) (value : α)
    (entry : values[index]? = some value) : index < values.length := by
  induction values generalizing index with
  | nil => cases index <;> simp [getElem?_def] at entry
  | cons head tail ih =>
      cases index with
      | zero => simp [getElem?_def]
      | succ index =>
          have tailEntry : tail[index]? = some value := by
            simpa [getElem?_def] using entry
          have tailBound := ih index tailEntry
          simpa [List.length_cons] using Nat.succ_lt_succ tailBound

theorem lookup_exists_of_lt {α : Type} (values : List α) (index : Nat)
    (bound : index < values.length) : ∃ value, values[index]? = some value := by
  induction values generalizing index with
  | nil => simp at bound
  | cons head tail ih =>
      cases index with
      | zero => exact ⟨head, by simp [getElem?_def]⟩
      | succ index =>
          have tailBound : index < tail.length := by simpa using bound
          obtain ⟨value, entry⟩ := ih index tailBound
          exact ⟨value, by simpa [getElem?_def] using entry⟩

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
  induction definitions generalizing index with
  | nil => cases index <;> simp [functionEntries, getElem?_def]
  | cons definition tail ih =>
      cases index with
      | zero => simp [functionEntries, getElem?_def]
      | succ index => simpa [functionEntries, getElem?_def] using ih slotTypes index

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
  | [] => []
  | type :: types => ⟨0, [], type⟩ :: getterSignaturesFrom types

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

theorem sourceSignatures_lookup (definitions : Surface.Definitions) (index : Nat) :
    (definitions.map Prod.fst)[index]? = (definitions[index]?).map Prod.fst := by
  induction definitions generalizing index with
  | nil => cases index <;> simp [getElem?_def]
  | cons definition tail ih =>
      cases index with
      | zero => simp [getElem?_def]
      | succ index => simpa [getElem?_def] using ih index

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
  induction types generalizing index with
  | nil => cases index <;> simp [getterSignaturesFrom, getElem?_def]
  | cons type tail ih =>
      cases index with
      | zero => simp [getterSignaturesFrom, getElem?_def]
      | succ index => simpa [getterSignaturesFrom, getElem?_def] using ih index

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
  have runtimeEntry := assembleProgram_getter_lookup definitions slotTypes slot
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
      simp at runtimeEntry
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

mutual
def evaluate (program : List Definition) (store : Store) : Nat → List Value → Term → Except Fault Value
  | 0, _, _ => .error (.core .outOfFuel)
  | fuel + 1, env, term => do
    match term with
    | .var i => match env[i]? with | some value => pure value | none => .error (.core .unbound)
    | .global i => match program[i]? with | some _ => pure (.global i) | none => .error (.core .unbound)
    | .bool b => pure (.bool b)
    | .int n => pure (.int n)
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

theorem initializeValues_stops_on_error (program : List Definition) (fuel : Nat)
    (store : Store) (slot : Nat) (head : Term) (tail : List Term) (fault : Fault)
    (step : evaluate program store fuel [] head = .error fault) :
    initializeValues program (fuel + 1) store slot (head :: tail) = .error fault := by
  simp [initializeValues, step, bind, Except.bind]

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

def programOfNamed (functions : Named.Definitions) (slotTypes : List Surface.Ty)
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
  induction expressions generalizing slot offset agreed with
  | nil => simp at within
  | cons head tail ih =>
      cases offset with
      | zero =>
          rcases agreed with ⟨type, slotType, _⟩
          exact ⟨type, by simpa using slotType⟩
      | succ offset =>
          rcases agreed with ⟨_, _, tailAgreed⟩
          have withinTail : offset < tail.length := by simpa using within
          obtain ⟨type, found⟩ := ih (slot := slot + 1) (offset := offset) tailAgreed withinTail
          have indexEq : slot + Nat.succ offset = (slot + 1) + offset := by omega
          exact ⟨type, by rw [indexEq]; exact found⟩

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

end NLisp.GlobalIR
