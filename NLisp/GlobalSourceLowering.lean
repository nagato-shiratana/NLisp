import NLisp.GlobalIR
import NLisp.ExpansionLowering
import NLisp.GlobalProgramEntry
import NLisp.NameLowering
import NLisp.GlobalIRErrorCorrespondence
import NLisp.ProcessCertificate

namespace NLisp.GlobalSourceLowering

open CBindingWalk ExpansionLowering Surface GlobalIR

/- Interpret the abstract C shared-cell store through GlobalIR's dense value
slots. The mixed declaration table supplies the identity-to-slot translation;
the payload type is the evaluator's actual PolyIR value type. -/
private theorem sourceGetElem?_eq_get? {α : Type} (items : List α) (index : Nat) :
    items[index]? = items.get? index := by
  by_cases bound : index < items.length
  · simp only [getElem?_def, dif_pos bound]
    exact (List.get?_eq_some).2 ⟨bound, rfl⟩ |>.symm
  · have outside : items.length ≤ index := Nat.le_of_not_gt bound
    simp only [getElem?_def, dif_neg bound]
    exact (List.get?_eq_none).2 outside |>.symm

def identityCellStore (entries : List GlobalProgramEntry.Entry) (store : GlobalIR.Store) :
    CNameResolution.CellStore PolyIR.Value := fun identity =>
  (GlobalProgramEntry.valueSlotOf identity 0 entries).bind
    (fun slot => (store[slot]?).join)

theorem identityCellStore_update_matches_C_cell_write
    (entries : List GlobalProgramEntry.Entry) (store : GlobalIR.Store)
    (identity slot : Nat) (value : PolyIR.Value)
    (mapped : GlobalProgramEntry.valueSlotOf identity 0 entries = some slot)
    (slotFits : slot < store.length)
    (slotUnique : ∀ other,
      GlobalProgramEntry.valueSlotOf other 0 entries = some slot → other = identity) :
    identityCellStore entries (store.set slot (some value)) =
      CNameResolution.writeCell (identityCellStore entries store) identity value := by
  funext queried
  by_cases sameIdentity : queried = identity
  · subst queried
    have slotFits' : slot < (store.set slot (some value)).length := by
      simpa only [List.length_set] using slotFits
    have setValue : (store.set slot (some value))[slot]'slotFits' = some value :=
      List.get_set_eq store slot (some value) slotFits'
    have lookupUpdated : (store.set slot (some value))[slot]? = some (some value) := by
      simp only [getElem?_def, dif_pos slotFits']
      simp [setValue]
    simp [identityCellStore, mapped, CNameResolution.writeCell, lookupUpdated]
  · unfold identityCellStore CNameResolution.writeCell
    cases slotLookup : GlobalProgramEntry.valueSlotOf queried 0 entries with
    | none => simp [slotLookup, sameIdentity]
    | some queriedSlot =>
        by_cases sameSlot : queriedSlot = slot
        · subst queriedSlot
          have sameResolvedIdentity := slotUnique queried slotLookup
          have contradiction : queried = identity := sameResolvedIdentity
          exact False.elim (sameIdentity contradiction)
        · have unchanged := GlobalIR.set_other_lookup store slot queriedSlot
            (some value) sameSlot
          simp [slotLookup, sameSlot, sameIdentity, unchanged]

theorem declaredValueCell_update_matches_C_cell_write
    (entries : List GlobalProgramEntry.Entry) (store : GlobalIR.Store)
    (sourceIndex identity slot : Nat) (type : Surface.Ty)
    (valid : type.wellFormed 0) (initializer : Surface.Expr)
    (value : PolyIR.Value)
    (entryAt : entries.get? sourceIndex =
      some (.value identity type valid initializer))
    (unique : GlobalProgramEntry.DistinctIds (GlobalProgramEntry.identities entries))
    (ordinal : GlobalProgramEntry.sourceValueSlotOrdinal entries sourceIndex = some slot)
    (slotFits : slot < store.length) :
    identityCellStore entries (store.set slot (some value)) =
      CNameResolution.writeCell (identityCellStore entries store) identity value := by
  have slotTranslation := GlobalProgramEntry.sourceValueSlotOrdinal_matches_identity_lookup
    entries sourceIndex identity type valid initializer entryAt unique
  have identitySlot : GlobalProgramEntry.valueSlotOf identity 0 entries = some slot := by
    rw [← slotTranslation]
    exact ordinal
  have slotUnique : ∀ other,
      GlobalProgramEntry.valueSlotOf other 0 entries = some slot → other = identity := by
    intro other otherSlot
    exact GlobalProgramEntry.valueSlotOf_injective entries 0 other identity slot unique
      otherSlot identitySlot
  exact identityCellStore_update_matches_C_cell_write entries store identity slot value
    identitySlot slotFits slotUnique

theorem resolvedCellName_reads_globalIR_slot
    (entries : List GlobalProgramEntry.Entry) (environment : List CNameResolution.Entry)
    (store : GlobalIR.Store) (name : String) (binding : CNameResolution.Entry)
    (slot : Nat) (value : PolyIR.Value)
    (resolved : CNameResolution.findName environment name = some binding)
    (identitySlot : GlobalProgramEntry.valueSlotOf binding.identity 0 entries = some slot)
    (stored : store[slot]? = some (some value)) :
    CNameResolution.readName environment (identityCellStore entries store) name = some value := by
  simp [CNameResolution.readName, identityCellStore, resolved, identitySlot, stored]

theorem resolvedValueName_reads_declared_globalIR_slot
    (entries : List GlobalProgramEntry.Entry) (environment : List CNameResolution.Entry)
    (store : GlobalIR.Store) (name : String) (binding : CNameResolution.Entry)
    (sourceIndex slot : Nat) (identity : Nat) (type : Surface.Ty)
    (valid : type.wellFormed 0) (initializer : Surface.Expr) (value : PolyIR.Value)
    (resolved : CNameResolution.findName environment name = some binding)
    (identityMatches : binding.identity = identity)
    (entryAt : entries.get? sourceIndex =
      some (.value identity type valid initializer))
    (unique : GlobalProgramEntry.DistinctIds (GlobalProgramEntry.identities entries))
    (ordinal : GlobalProgramEntry.sourceValueSlotOrdinal entries sourceIndex = some slot)
    (stored : store[slot]? = some (some value)) :
    CNameResolution.readName environment (identityCellStore entries store) name = some value := by
  have slotTranslation := GlobalProgramEntry.sourceValueSlotOrdinal_matches_identity_lookup
    entries sourceIndex identity type valid initializer entryAt unique
  have identitySlot : GlobalProgramEntry.valueSlotOf binding.identity 0 entries = some slot := by
    rw [identityMatches, ← slotTranslation]
    exact ordinal
  exact resolvedCellName_reads_globalIR_slot entries environment store name binding slot value
    resolved identitySlot stored

theorem resolvedCValueName_agrees_with_compiled_globalIR_getter
    (entries : List GlobalProgramEntry.Entry) (environment : List CNameResolution.Entry)
    (store : GlobalIR.Store) (name : String) (binding : CNameResolution.Entry)
    (sourceIndex slot : Nat) (identity : Nat) (type : Surface.Ty)
    (valid : type.wellFormed 0) (initializer : Surface.Expr) (value : PolyIR.Value)
    (fuel : Nat)
    (resolved : CNameResolution.findName environment name = some binding)
    (identityMatches : binding.identity = identity)
    (entryAt : entries.get? sourceIndex =
      some (.value identity type valid initializer))
    (unique : GlobalProgramEntry.DistinctIds (GlobalProgramEntry.identities entries))
    (ordinal : GlobalProgramEntry.sourceValueSlotOrdinal entries sourceIndex = some slot)
    (stored : store[slot]? = some (some value)) :
    CNameResolution.readName environment (identityCellStore entries store) name = some value ∧
      GlobalIR.evaluate (GlobalProgramEntry.toDefinitions 0 entries) store (fuel + 2) []
        (.app (.global sourceIndex) []) = .ok value := by
  have nameReads := resolvedValueName_reads_declared_globalIR_slot entries environment store
    name binding sourceIndex slot identity type valid initializer value resolved identityMatches
    entryAt unique ordinal stored
  obtain ⟨_type, getterLayout⟩ := GlobalProgramEntry.sourceValueSlotOrdinal_layout
    entries sourceIndex 0 slot ordinal
  have getterLookup := GlobalProgramEntry.toDefinitions_getter_of_layout 0 entries sourceIndex
    ⟨0, [], _type⟩ slot (by simpa using getterLayout)
  have getter : (GlobalProgramEntry.toDefinitions 0 entries)[sourceIndex]? =
      some (.getter slot) := by
    rw [sourceGetElem?_eq_get?]
    exact getterLookup
  exact ⟨nameReads, GlobalIR.getter_call_reads_current_store
    (GlobalProgramEntry.toDefinitions 0 entries) store fuel sourceIndex slot value getter stored⟩

/-- If C-style name lookup reports a mixed declaration index, the
position-preserving named layout supplies the identity correspondence needed
to connect that lookup directly to the value's GlobalIR getter. -/
theorem resolvedCValueName_from_namedLayout_agrees_with_compiled_globalIR_getter
    (entries : List GlobalProgramEntry.Entry) (environment : List CNameResolution.Entry)
    (layout : GlobalProgramEntry.NamedGlobalLayout environment entries)
    (store : GlobalIR.Store) (name : String) (binding : CNameResolution.Entry)
    (sourceIndex slot identity : Nat) (type : Surface.Ty)
    (valid : type.wellFormed 0) (initializer : Surface.Expr) (value : PolyIR.Value)
    (fuel : Nat)
    (resolved : CNameResolution.findName environment name = some binding)
    (indexResolved : CNameResolution.findNameIndex environment name = some sourceIndex)
    (entryAt : entries.get? sourceIndex =
      some (.value identity type valid initializer))
    (unique : GlobalProgramEntry.DistinctIds (GlobalProgramEntry.identities entries))
    (ordinal : GlobalProgramEntry.sourceValueSlotOrdinal entries sourceIndex = some slot)
    (stored : store[slot]? = some (some value)) :
    CNameResolution.readName environment
        (identityCellStore entries store) name = some value ∧
      GlobalIR.evaluate (GlobalProgramEntry.toDefinitions 0 entries) store (fuel + 2) []
        (.app (.global sourceIndex) []) = .ok value := by
  obtain ⟨indexedBinding, indexedFound, namedAt⟩ :=
    CNameResolution.findNameIndex_sound environment name sourceIndex indexResolved
  have bindingEq : indexedBinding = binding := by
    rw [resolved] at indexedFound
    exact (Option.some.inj indexedFound).symm
  subst indexedBinding
  have identityMatches : binding.identity = identity :=
    layout.2 sourceIndex binding (.value identity type valid initializer) namedAt entryAt
  exact resolvedCValueName_agrees_with_compiled_globalIR_getter entries environment store name
    binding sourceIndex slot identity type valid initializer value fuel resolved identityMatches
    entryAt unique ordinal stored

/-- A write to a declared mixed-layout value slot is observed identically by
C's shared-cell name lookup and by the corresponding compiled GlobalIR
getter. This composes source-order index translation, dense-slot mutation,
the C cell-store interpretation, and getter evaluation. -/
theorem declaredValue_write_agrees_with_C_name_and_globalIR_getter
    (entries : List GlobalProgramEntry.Entry) (environment : List CNameResolution.Entry)
    (store : GlobalIR.Store) (name : String) (binding : CNameResolution.Entry)
    (sourceIndex slot identity : Nat) (type : Surface.Ty)
    (valid : type.wellFormed 0) (initializer : Surface.Expr) (value : PolyIR.Value)
    (fuel : Nat)
    (resolved : CNameResolution.findName environment name = some binding)
    (identityMatches : binding.identity = identity)
    (entryAt : entries.get? sourceIndex =
      some (.value identity type valid initializer))
    (unique : GlobalProgramEntry.DistinctIds (GlobalProgramEntry.identities entries))
    (ordinal : GlobalProgramEntry.sourceValueSlotOrdinal entries sourceIndex = some slot)
    (slotFits : slot < store.length) :
    CNameResolution.readName environment
        (CNameResolution.writeCell (identityCellStore entries store) identity value) name =
        some value ∧
      GlobalIR.evaluate (GlobalProgramEntry.toDefinitions 0 entries) (store.set slot (some value))
        (fuel + 2) [] (.app (.global sourceIndex) []) = .ok value := by
  have slotFits' : slot < (store.set slot (some value)).length := by
    simpa only [List.length_set] using slotFits
  have updated : (store.set slot (some value))[slot]? = some (some value) := by
    simp only [getElem?_def, dif_pos slotFits']
    have setValue : (store.set slot (some value))[slot]'slotFits' = some value :=
      List.get_set_eq store slot (some value) slotFits'
    simp [setValue]
  have observed := resolvedCValueName_agrees_with_compiled_globalIR_getter entries environment
    (store.set slot (some value)) name binding sourceIndex slot identity type valid initializer
    value fuel resolved identityMatches entryAt unique ordinal updated
  have cellWrite := declaredValueCell_update_matches_C_cell_write entries store sourceIndex
    identity slot type valid initializer value entryAt unique ordinal slotFits
  rw [cellWrite] at observed
  exact observed

/-- A closure that retains C's linked global name environment observes a
later shared-cell write, while the corresponding GlobalIR closure reads the
same newly populated dense slot through its getter body. -/
theorem declaredValue_shared_closure_observes_later_cell_write
    (entries : List GlobalProgramEntry.Entry) (environment : List CNameResolution.Entry)
    (before : GlobalIR.Store) (name : String) (binding : CNameResolution.Entry)
    (sourceIndex slot identity : Nat) (type : Surface.Ty)
    (valid : type.wellFormed 0) (initializer : Surface.Expr)
    (value : PolyIR.Value) (fuel : Nat)
    (resolved : CNameResolution.findName environment name = some binding)
    (identityMatches : binding.identity = identity)
    (entryAt : entries.get? sourceIndex =
      some (.value identity type valid initializer))
    (unique : GlobalProgramEntry.DistinctIds (GlobalProgramEntry.identities entries))
    (ordinal : GlobalProgramEntry.sourceValueSlotOrdinal entries sourceIndex = some slot)
    (slotFits : slot < before.length)
    (beforeEmpty : before[slot]? = some none) :
    CNameResolution.readName environment
        (identityCellStore entries (before.set slot (some value))) name = some value ∧
      GlobalIR.evaluate (GlobalProgramEntry.toDefinitions 0 entries)
        (before.set slot (some value)) (fuel + 4)
        [.closure 0 (.app (.global sourceIndex) []) []] (.app (.var 0) []) = .ok value := by
  have cObserved := CNameResolution.readName_after_cell_write environment
    (identityCellStore entries before) name binding value resolved
  have cObserved' : CNameResolution.readName environment
      (CNameResolution.writeCell (identityCellStore entries before) identity value) name =
      some value := by
    rw [← identityMatches]
    exact cObserved
  have cellWrite := declaredValueCell_update_matches_C_cell_write entries before sourceIndex
    identity slot type valid initializer value entryAt unique ordinal slotFits
  have cReadAfterStore : CNameResolution.readName environment
      (identityCellStore entries (before.set slot (some value))) name = some value := by
    rw [cellWrite]
    exact cObserved'
  have slotFits' : slot < (before.set slot (some value)).length := by
    simpa only [List.length_set] using slotFits
  have afterInitialized : (before.set slot (some value))[slot]? = some (some value) := by
    simp only [getElem?_def, dif_pos slotFits']
    have setValue : (before.set slot (some value))[slot]'slotFits' = some value :=
      List.get_set_eq before slot (some value) slotFits'
    simp [setValue]
  obtain ⟨getterType, getterLayout⟩ :=
    GlobalProgramEntry.sourceValueSlotOrdinal_layout entries sourceIndex 0 slot ordinal
  have layout : (GlobalProgramEntry.compiledLayout 0 entries).get? sourceIndex =
      some (⟨0, [], getterType⟩, GlobalIR.Definition.getter slot) := by
    simpa [Nat.zero_add] using getterLayout
  have getterLookup := GlobalProgramEntry.toDefinitions_getter_of_layout 0 entries
    sourceIndex ⟨0, [], getterType⟩ slot layout
  have getter : (GlobalProgramEntry.toDefinitions 0 entries)[sourceIndex]? =
      some (GlobalIR.Definition.getter slot) := by
    rw [sourceGetElem?_eq_get?]
    exact getterLookup
  obtain ⟨_closureBefore, _earlyRead, closureAfter⟩ :=
    GlobalIR.closure_created_before_initialization_reads_later_store
      (GlobalProgramEntry.toDefinitions 0 entries) before (before.set slot (some value))
      fuel sourceIndex slot value getter beforeEmpty afterInitialized
  exact ⟨cReadAfterStore, closureAfter⟩

/-- The same shared-cell/closure simulation also preserves the declared value
type when the pre-write store is well typed and the initializer result has its
slot type. -/
theorem declaredValue_shared_closure_observes_later_cell_write_typed
    (entries : List GlobalProgramEntry.Entry) (environment : List CNameResolution.Entry)
    (globals : List Surface.Signature) (slotTypes : List Surface.Ty)
    (before : GlobalIR.Store) (name : String) (binding : CNameResolution.Entry)
    (sourceIndex slot identity : Nat) (type : Surface.Ty)
    (valid : type.wellFormed 0) (initializer : Surface.Expr)
    (value : PolyIR.Value) (fuel : Nat)
    (resolved : CNameResolution.findName environment name = some binding)
    (identityMatches : binding.identity = identity)
    (entryAt : entries.get? sourceIndex =
      some (.value identity type valid initializer))
    (unique : GlobalProgramEntry.DistinctIds (GlobalProgramEntry.identities entries))
    (ordinal : GlobalProgramEntry.sourceValueSlotOrdinal entries sourceIndex = some slot)
    (slotFits : slot < before.length)
    (beforeEmpty : before[slot]? = some none)
    (slotType : slotTypes[slot]? = some type)
    (beforeTyped : GlobalIR.StoreWellTyped globals slotTypes before)
    (valueTyped : PolyIR.ValueTyped globals value type) :
    CNameResolution.readName environment
        (identityCellStore entries (before.set slot (some value))) name = some value ∧
      GlobalIR.evaluate (GlobalProgramEntry.toDefinitions 0 entries)
        (before.set slot (some value)) (fuel + 4)
        [.closure 0 (.app (.global sourceIndex) []) []] (.app (.var 0) []) = .ok value ∧
      PolyIR.ValueTyped globals value type := by
  have observed := declaredValue_shared_closure_observes_later_cell_write entries
    environment before name binding sourceIndex slot identity type valid initializer value fuel
    resolved identityMatches entryAt unique ordinal slotFits beforeEmpty
  have slotTypeGet : slotTypes.get? slot = some type := by
    simpa only [sourceGetElem?_eq_get?] using slotType
  have updatedTyped : GlobalIR.StoreWellTyped globals slotTypes
      (before.set slot (some value)) :=
    GlobalIR.StoreWellTyped.set globals slotTypes before slot value type beforeTyped
      slotFits slotTypeGet valueTyped
  have updatedStored : (before.set slot (some value)).get? slot = some (some value) := by
    have slotFits' : slot < (before.set slot (some value)).length := by
      simpa only [List.length_set] using slotFits
    have updatedIndexed : (before.set slot (some value))[slot]? = some (some value) := by
      simp only [getElem?_def, dif_pos slotFits']
      have setValue : (before.set slot (some value))[slot]'slotFits' = some value :=
        List.get_set_eq before slot (some value) slotFits'
      simp [setValue]
    simpa only [sourceGetElem?_eq_get?] using updatedIndexed
  exact ⟨observed.1, observed.2, updatedTyped slot value type updatedStored slotTypeGet⟩

/-- A successful complete GlobalIR initializer run populates the value slot
selected by a mixed source declaration index. The resulting store is observed
as the same value by C-style name lookup and the compiled GlobalIR getter. -/
theorem declaredValue_successful_initialization_agrees_with_C_name_and_getter
    (entries : List GlobalProgramEntry.Entry) (environment : List CNameResolution.Entry)
    (result : GlobalIR.Store) (name : String) (binding : CNameResolution.Entry)
    (sourceIndex slot identity fuel getterFuel : Nat) (type : Surface.Ty)
    (valid : type.wellFormed 0) (initializer : Surface.Expr)
    (resolved : CNameResolution.findName environment name = some binding)
    (identityMatches : binding.identity = identity)
    (entryAt : entries.get? sourceIndex =
      some (.value identity type valid initializer))
    (unique : GlobalProgramEntry.DistinctIds (GlobalProgramEntry.identities entries))
    (ordinal : GlobalProgramEntry.sourceValueSlotOrdinal entries sourceIndex = some slot)
    (initialized : GlobalIR.initializeValues (GlobalProgramEntry.toDefinitions 0 entries) fuel
      (List.replicate (GlobalProgramEntry.initializerTerms entries).length
        (none : Option PolyIR.Value)) 0 (GlobalProgramEntry.initializerTerms entries) =
          .ok result) :
    ∃ value,
      CNameResolution.readName environment (identityCellStore entries result) name = some value ∧
      GlobalIR.evaluate (GlobalProgramEntry.toDefinitions 0 entries) result
        (getterFuel + 2) [] (.app (.global sourceIndex) []) = .ok value := by
  obtain ⟨value, stored⟩ := GlobalProgramEntry.sourceValueSlotOrdinal_successful_initialization_populates
    entries sourceIndex slot identity type valid initializer entryAt ordinal
    (GlobalProgramEntry.toDefinitions 0 entries) fuel result initialized
  have observed := resolvedCValueName_agrees_with_compiled_globalIR_getter entries environment
    result name binding sourceIndex slot identity type valid initializer value getterFuel
    resolved identityMatches entryAt unique ordinal stored
  exact ⟨value, observed.1, observed.2⟩

/-- Successful mixed-entry initialization also preserves the declared type of
the value observed through C-style name lookup and the generated GlobalIR
getter. This combines the initializer/source-index correspondence with the
typed-store getter theorem, so both observations refer to one runtime value. -/
theorem declaredValue_successful_initialization_agrees_with_C_name_and_typed_getter
    (entries : List GlobalProgramEntry.Entry) (environment : List CNameResolution.Entry)
    (globals : List Surface.Signature) (slotTypes : List Surface.Ty)
    (result : GlobalIR.Store) (name : String) (binding : CNameResolution.Entry)
    (sourceIndex slot identity fuel getterFuel : Nat) (type : Surface.Ty)
    (valid : type.wellFormed 0) (initializer : Surface.Expr)
    (resolved : CNameResolution.findName environment name = some binding)
    (identityMatches : binding.identity = identity)
    (entryAt : entries.get? sourceIndex =
      some (.value identity type valid initializer))
    (unique : GlobalProgramEntry.DistinctIds (GlobalProgramEntry.identities entries))
    (ordinal : GlobalProgramEntry.sourceValueSlotOrdinal entries sourceIndex = some slot)
    (slotType : slotTypes[slot]? = some type)
    (storeTyped : GlobalIR.StoreWellTyped globals slotTypes result)
    (initialized : GlobalIR.initializeValues (GlobalProgramEntry.toDefinitions 0 entries) fuel
      (List.replicate (GlobalProgramEntry.initializerTerms entries).length
        (none : Option PolyIR.Value)) 0 (GlobalProgramEntry.initializerTerms entries) =
          .ok result) :
    ∃ value,
      CNameResolution.readName environment (identityCellStore entries result) name = some value ∧
      GlobalIR.evaluate (GlobalProgramEntry.toDefinitions 0 entries) result
        (getterFuel + 2) [] (.app (.global sourceIndex) []) = .ok value ∧
      PolyIR.ValueTyped globals value type := by
  obtain ⟨value, nameReads, getterReads⟩ :=
    declaredValue_successful_initialization_agrees_with_C_name_and_getter
      entries environment result name binding sourceIndex slot identity fuel getterFuel type
      valid initializer resolved identityMatches entryAt unique ordinal initialized
  obtain ⟨storedValue, stored⟩ :=
    GlobalProgramEntry.sourceValueSlotOrdinal_successful_initialization_populates
      entries sourceIndex slot identity type valid initializer entryAt ordinal
      (GlobalProgramEntry.toDefinitions 0 entries) fuel result initialized
  obtain ⟨typedValue, getterTyped, valueTyped⟩ := GlobalIR.getter_call_preserves_type
    (GlobalProgramEntry.toDefinitions 0 entries) globals slotTypes result getterFuel
    sourceIndex slot storedValue type
    (by
      obtain ⟨_type, getterLayout⟩ := GlobalProgramEntry.sourceValueSlotOrdinal_layout
        entries sourceIndex 0 slot ordinal
      have lookup := GlobalProgramEntry.toDefinitions_getter_of_layout 0 entries sourceIndex
        ⟨0, [], _type⟩ slot (by simpa using getterLayout)
      rw [sourceGetElem?_eq_get?]
      exact lookup)
    slotType storeTyped
    stored
  have valuesEqual : typedValue = value := by
    have sameResults := getterTyped.symm.trans getterReads
    exact Except.ok.inj sameResults
  subst typedValue
  exact ⟨value, nameReads, getterReads, valueTyped⟩

/-- Compose the executable initializer checker with arithmetic initializer
preservation, mixed-entry slot initialization, C-style shared-cell lookup,
and the generated GlobalIR getter. The same typed value is observed through
the C name environment and the compiled getter. -/
theorem checkedArithmeticInitializer_agrees_with_C_name_and_typed_getter
    (checkerFuel : Nat) (entries : List GlobalProgramEntry.Entry)
    (environment : List CNameResolution.Entry) (globals : List Surface.Signature)
    (result : GlobalIR.Store) (name : String) (binding : CNameResolution.Entry)
    (sourceIndex slot identity initializerFuel getterFuel : Nat) (type : Surface.Ty)
    (valid : type.wellFormed 0) (initializer : Surface.Expr)
    (resolved : CNameResolution.findName environment name = some binding)
    (identityMatches : binding.identity = identity)
    (entryAt : entries.get? sourceIndex =
      some (.value identity type valid initializer))
    (unique : GlobalProgramEntry.DistinctIds (GlobalProgramEntry.identities entries))
    (ordinal : GlobalProgramEntry.sourceValueSlotOrdinal entries sourceIndex = some slot)
    (slotType : (GlobalProgramEntry.valueTypes entries)[slot]? = some type)
    (accepted : GlobalProgramEntry.checkInitializerRows checkerFuel entries
      (GlobalProgramEntry.valueTypes entries) 0 entries = true)
    (arithmeticRows : GlobalProgramEntry.ArithmeticInitializerRows
      (GlobalProgramEntry.valueTypes entries) 0 entries)
    (initialized : GlobalIR.initializeValues (GlobalProgramEntry.toDefinitions 0 entries)
      initializerFuel
      (List.replicate (GlobalProgramEntry.initializerTerms entries).length
        (none : Option PolyIR.Value)) 0 (GlobalProgramEntry.initializerTerms entries) =
        .ok result) :
    ∃ value,
      CNameResolution.readName environment (identityCellStore entries result) name = some value ∧
      GlobalIR.evaluate (GlobalProgramEntry.toDefinitions 0 entries) result
        (getterFuel + 2) [] (.app (.global sourceIndex) []) = .ok value ∧
      PolyIR.ValueTyped globals value type := by
  have checkerRows := GlobalProgramEntry.checkInitializerRows_sound checkerFuel entries
    (GlobalProgramEntry.valueTypes entries) 0 entries accepted
  have typedRows := checkerRows.toTypedInitializerRows checkerFuel entries
    (GlobalProgramEntry.valueTypes entries) 0 entries
  have storeTyped := typedRows.initialization_preserves_store_arithmetic entries globals
    (GlobalProgramEntry.valueTypes entries) (GlobalProgramEntry.toDefinitions 0 entries)
    initializerFuel entries result arithmeticRows initialized
  exact declaredValue_successful_initialization_agrees_with_C_name_and_typed_getter
    entries environment globals (GlobalProgramEntry.valueTypes entries) result name binding
    sourceIndex slot identity initializerFuel getterFuel type valid initializer resolved
    identityMatches entryAt unique ordinal slotType storeTyped initialized

/-- General initializer-row version of the C-name/getter composition. The
only semantic premise is GlobalIR evaluation type preservation for the
initializers; this isolates that remaining global safety result from the
source-index, shared-cell, and getter bookkeeping. -/
theorem checkedInitializer_agrees_with_C_name_and_typed_getter
    (checkerFuel : Nat) (entries : List GlobalProgramEntry.Entry)
    (environment : List CNameResolution.Entry) (globals : List Surface.Signature)
    (initializerFuel getterFuel : Nat) (result : GlobalIR.Store)
    (name : String) (binding : CNameResolution.Entry)
    (sourceIndex slot identity : Nat) (type : Surface.Ty)
    (valid : type.wellFormed 0) (initializer : Surface.Expr)
    (resolved : CNameResolution.findName environment name = some binding)
    (identityMatches : binding.identity = identity)
    (entryAt : entries.get? sourceIndex =
      some (.value identity type valid initializer))
    (unique : GlobalProgramEntry.DistinctIds (GlobalProgramEntry.identities entries))
    (ordinal : GlobalProgramEntry.sourceValueSlotOrdinal entries sourceIndex = some slot)
    (slotType : (GlobalProgramEntry.valueTypes entries)[slot]? = some type)
    (accepted : GlobalProgramEntry.checkInitializerRows checkerFuel entries
      (GlobalProgramEntry.valueTypes entries) 0 entries = true)
    (evaluationTyped : ∀ currentStore remaining expression value expected,
      GlobalIR.evaluate (GlobalProgramEntry.toDefinitions 0 entries)
        currentStore remaining [] expression = .ok value →
          PolyIR.ValueTyped globals value expected)
    (initialization : GlobalIR.initializeValues (GlobalProgramEntry.toDefinitions 0 entries)
      initializerFuel
      (List.replicate (GlobalProgramEntry.initializerTerms entries).length
        (none : Option PolyIR.Value)) 0 (GlobalProgramEntry.initializerTerms entries) =
        .ok result) :
    ∃ value,
      CNameResolution.readName environment (identityCellStore entries result) name = some value ∧
      GlobalIR.evaluate (GlobalProgramEntry.toRuntimeProgram entries entryIndex).definitions result
        (getterFuel + 2) [] (.app (.global sourceIndex) []) = .ok value ∧
      PolyIR.ValueTyped globals value type := by
  have checkerRows := GlobalProgramEntry.checkInitializerRows_sound checkerFuel entries
    (GlobalProgramEntry.valueTypes entries) 0 entries accepted
  have typedRows := checkerRows.toTypedInitializerRows checkerFuel entries
    (GlobalProgramEntry.valueTypes entries) 0 entries
  have storeTyped := typedRows.initialization_preserves_store entries globals
    (GlobalProgramEntry.valueTypes entries) (GlobalProgramEntry.toDefinitions 0 entries)
    initializerFuel entries result evaluationTyped initialization
  have initialized := declaredValue_successful_initialization_agrees_with_C_name_and_typed_getter
    entries environment globals (GlobalProgramEntry.valueTypes entries) result name binding
    sourceIndex slot identity initializerFuel getterFuel type valid initializer resolved
    identityMatches entryAt unique ordinal slotType storeTyped initialization
  exact initialized

theorem resolvedCValueName_uninitialized_matches_globalIR_early_read
    (entries : List GlobalProgramEntry.Entry) (environment : List CNameResolution.Entry)
    (store : GlobalIR.Store) (name : String) (binding : CNameResolution.Entry)
    (sourceIndex slot : Nat) (identity : Nat) (type : Surface.Ty)
    (valid : type.wellFormed 0) (initializer : Surface.Expr)
    (fuel : Nat)
    (resolved : CNameResolution.findName environment name = some binding)
    (identityMatches : binding.identity = identity)
    (entryAt : entries.get? sourceIndex =
      some (.value identity type valid initializer))
    (unique : GlobalProgramEntry.DistinctIds (GlobalProgramEntry.identities entries))
    (ordinal : GlobalProgramEntry.sourceValueSlotOrdinal entries sourceIndex = some slot)
    (uninitialized : store[slot]? = some none) :
    CNameResolution.readName environment (identityCellStore entries store) name = none ∧
      GlobalIR.evaluate (GlobalProgramEntry.toDefinitions 0 entries) store (fuel + 2) []
        (.app (.global sourceIndex) []) = .error (.beforeInitialization slot) := by
  have slotTranslation := GlobalProgramEntry.sourceValueSlotOrdinal_matches_identity_lookup
    entries sourceIndex identity type valid initializer entryAt unique
  have identitySlot : GlobalProgramEntry.valueSlotOf binding.identity 0 entries = some slot := by
    rw [identityMatches, ← slotTranslation]
    exact ordinal
  have cRead : CNameResolution.readName environment
      (identityCellStore entries store) name = none := by
    simp [CNameResolution.readName, resolved, identityCellStore, identitySlot, uninitialized]
  obtain ⟨_type, getterLayout⟩ := GlobalProgramEntry.sourceValueSlotOrdinal_layout
    entries sourceIndex 0 slot ordinal
  have getterLookup := GlobalProgramEntry.toDefinitions_getter_of_layout 0 entries sourceIndex
    ⟨0, [], _type⟩ slot (by simpa using getterLayout)
  have getter : (GlobalProgramEntry.toDefinitions 0 entries)[sourceIndex]? =
      some (.getter slot) := by
    rw [sourceGetElem?_eq_get?]
    exact getterLookup
  exact ⟨cRead, GlobalIR.getter_call_reports_early_read
    (GlobalProgramEntry.toDefinitions 0 entries) store fuel sourceIndex slot getter uninitialized⟩



def localPosition (selected : Nat) : List Nat → Nat
  | [] => 0
  | identity :: rest =>
      if identity == selected then 0 else localPosition selected rest + 1

theorem localPosition_eq_namedPosition (selected : Nat) (locals : List Nat) :
    localPosition selected locals = Named.position selected locals := by
  induction locals with
  | nil => rfl
  | cons head tail ih =>
      by_cases same : head = selected
      · simp [localPosition, Named.position, same]
      · simp [localPosition, Named.position, same, ih]

theorem localPosition_lookup (selected : Nat) (locals : List Nat)
    (member : selected ∈ locals) :
    locals.get? (localPosition selected locals) = some selected := by
  induction locals with
  | nil => simp at member
  | cons head tail ih =>
      by_cases same : head = selected
      · subst selected
        simp [localPosition]
      · have tailMember : selected ∈ tail := by
          rcases List.mem_cons.mp member with headMember | tailMember
          · exact False.elim (same headMember.symm)
          · exact tailMember
        have tailLookup := ih tailMember
        simpa [localPosition, same] using tailLookup

theorem localPosition_lt_length (selected : Nat) (locals : List Nat)
    (member : selected ∈ locals) :
    localPosition selected locals < locals.length := by
  induction locals with
  | nil => simp at member
  | cons head tail ih =>
      by_cases same : head = selected
      · subst selected
        simp [localPosition]
      · have tailMember : selected ∈ tail := by
          rcases List.mem_cons.mp member with headMember | tailMember
          · exact False.elim (same headMember.symm)
          · exact tailMember
        have tailBound := ih tailMember
        simp [localPosition, same, List.length_cons]
        omega

def visibleFunctionIndex (entries visible : List GlobalProgramEntry.Entry)
    (selected : Nat) : Option Nat :=
  if selected ∈ GlobalProgramEntry.functionIdentities visible &&
      selected ∈ GlobalProgramEntry.functionIdentities entries &&
      GlobalProgramEntry.identitiesUniqueCheck entries then
    GlobalProgramEntry.globalIndexOf selected entries
  else none

theorem visibleFunctionIndex_sound (entries visible : List GlobalProgramEntry.Entry)
    (selected index : Nat) (resolved : visibleFunctionIndex entries visible selected = some index) :
    selected ∈ GlobalProgramEntry.functionIdentities visible ∧
    selected ∈ GlobalProgramEntry.functionIdentities entries ∧
    GlobalProgramEntry.identitiesUniqueCheck entries = true ∧
    GlobalProgramEntry.globalIndexOf selected entries = some index := by
  unfold visibleFunctionIndex at resolved
  by_cases visibleMember : selected ∈ GlobalProgramEntry.functionIdentities visible
  · by_cases entryMember : selected ∈ GlobalProgramEntry.functionIdentities entries
    · by_cases unique : GlobalProgramEntry.identitiesUniqueCheck entries = true
      · simp [visibleMember, entryMember, unique] at resolved
        exact ⟨visibleMember, entryMember, unique, resolved⟩
      · simp [visibleMember, entryMember, unique] at resolved
    · simp [visibleMember, entryMember] at resolved
  · simp [visibleMember] at resolved

theorem visibleFunctionIndex_compiledFunction_sound
    (entries visible : List GlobalProgramEntry.Entry) (selected index : Nat)
    (resolved : visibleFunctionIndex entries visible selected = some index) :
    ∃ signature definition,
      (GlobalProgramEntry.compiledLayout 0 entries).get? index =
        some (signature, GlobalIR.Definition.function definition) := by
  obtain ⟨_visibleMember, entryMember, uniqueCheck, globalFound⟩ :=
    visibleFunctionIndex_sound entries visible selected index resolved
  have distinct := GlobalProgramEntry.identitiesUniqueCheck_sound entries uniqueCheck
  obtain ⟨signature, definition, actualIndex, actualFound, layoutFound⟩ :=
    GlobalProgramEntry.functionIdentity_function_at_globalIndex selected 0 entries
      distinct entryMember
  have sameIndex : actualIndex = index :=
    Option.some.inj (actualFound.symm.trans globalFound)
  subst actualIndex
  exact ⟨signature, definition, layoutFound⟩

mutual
def readClosedType : Nat → Node → Option { type : Surface.Ty // type.wellFormed 0 }
  | 0, _ => none
  | _fuel + 1, .atom atom _ =>
      match atom.name with
      | "Boolean" => some ⟨.boolean, trivial⟩
      | "Integer" => some ⟨.integer, trivial⟩
      | "Float" => some ⟨.float, trivial⟩
      | "String" => some ⟨.string, trivial⟩
      | "Character" => some ⟨.character, trivial⟩
      | "Unit" => some ⟨.unit, trivial⟩
      | _ => none
  | fuel + 1, .list [head, element] => do
      let element ← readClosedType fuel element
      if name head = some "List" then
        some ⟨.list element.val, by simpa [Surface.Ty.wellFormed] using element.property⟩
      else if name head = some "Option" then
        some ⟨.option element.val, by simpa [Surface.Ty.wellFormed] using element.property⟩
      else none
  | fuel + 1, .list [head, .list arguments, result] => do
      if name head != some "Function" then none else
      let arguments ← readClosedTypes fuel arguments
      let result ← readClosedType fuel result
      some ⟨.fn arguments.val result.val, by
        simp only [Surface.Ty.wellFormed]
        exact ⟨arguments.property, result.property⟩⟩
  | _fuel + 1, _ => none

def readClosedTypes : Nat → List Node →
    Option { types : List Surface.Ty // ∀ type ∈ types, type.wellFormed 0 }
  | 0, _ => none
  | _fuel + 1, [] => some ⟨[], by simp⟩
  | fuel + 1, head :: tail => do
      let head ← readClosedType fuel head
      let tail ← readClosedTypes fuel tail
      some ⟨head.val :: tail.val, by
        intro type member
        simp only [List.mem_cons] at member
        rcases member with same | inTail
        · simpa [same] using head.property
        · exact tail.property type inTail⟩
end

theorem readClosedTypes_length (fuel : Nat) (nodes : List Node)
    (decoded : { types : List Surface.Ty //
      ∀ type ∈ types, type.wellFormed 0 })
    (accepted : readClosedTypes fuel nodes = some decoded) :
    decoded.val.length = nodes.length := by
  induction nodes generalizing fuel decoded with
  | nil =>
      cases fuel with
      | zero => simp [readClosedTypes] at accepted
      | succ fuel =>
          simp only [readClosedTypes] at accepted
          have decodedEq := Option.some.inj accepted
          cases decodedEq
          rfl
  | cons node tail ih =>
      cases fuel with
      | zero => simp [readClosedTypes] at accepted
      | succ fuel =>
          cases head : readClosedType fuel node with
          | none => simp [readClosedTypes, head] at accepted
          | some typedHead =>
              cases rest : readClosedTypes fuel tail with
              | none => simp [readClosedTypes, head, rest] at accepted
              | some typedTail =>
                  have decodedEq :
                      (⟨typedHead.val :: typedTail.val, by
                        intro type member
                        simp only [List.mem_cons] at member
                        rcases member with same | inTail
                        · simpa [same] using typedHead.property
                        · exact typedTail.property type inTail⟩ :
                        { types : List Surface.Ty //
                          ∀ type ∈ types, type.wellFormed 0 }) = decoded :=
                    Option.some.inj (by
                      simpa [readClosedTypes, head, rest] using accepted)
                  have lengths := congrArg
                    (fun result : { types : List Surface.Ty //
                      ∀ type ∈ types, type.wellFormed 0 } => result.val.length) decodedEq
                  have tailLength := ih fuel typedTail rest
                  calc
                    decoded.val.length = (typedHead.val :: typedTail.val).length := lengths.symm
                    _ = (node :: tail).length := by simp [tailLength]

/- Decode the initializer subset supported by the source-order lowering pass.
Nonzero atoms resolve to visible local binders, function references, or value
getters. Global visibility is restricted to declarations preceding the
initializer, and function lookup requires a unique source declaration. -/
def floatBuiltinOperator : Nat → String → Option FloatBinOp
  | 39, "float+" => some .add
  | 42, "float-" => some .sub
  | 45, "float*" => some .mul
  | 48, "float/" => some .div
  | _, _ => none

def readClosedInitializer (entries visible : List GlobalProgramEntry.Entry)
    (forbidden : List Nat) :
    Nat → Node → Option Surface.Expr
  | 0, _ => none
  | _fuel + 1, .atom atom selected =>
      if selected != 0 then
        if selected ∈ forbidden then some (.var (localPosition selected forbidden))
        else if selected ∈ GlobalProgramEntry.functionIdentities visible then
          (visibleFunctionIndex entries visible selected).map (fun index => .global index [])
        else if selected ∈ GlobalProgramEntry.valueIdentities visible then
          if selected ∈ GlobalProgramEntry.valueIdentities entries then
            if GlobalProgramEntry.identitiesUniqueCheck entries then
              match GlobalProgramEntry.globalIndexOf selected entries with
              | some index => some (.app (.global index []) [])
              | none => none
            else none
          else none
        else none
      else if atom.name == "true" then some (.bool true)
      else if atom.name == "false" then some (.bool false)
      else if atom.name == "unit" then some .unit
      else if Lexical.integerLiteral atom.name.toList then
        atom.name.toInt?.map Surface.Expr.int
      else if Lexical.floatLiteral atom.name.toList then
        (Lexical.readFloatLiteral atom.name).map Surface.Expr.float
      else none
  | fuel + 1, .list (head :: tail) =>
      if name head = some "type-app" then
        match tail with
        | reference :: typeNodes =>
            match reference with
            | .atom _ selected =>
                if selected != 0 && selected ∉ forbidden then do
                  let arguments ← readClosedTypes fuel typeNodes
                  let index ← visibleFunctionIndex entries visible selected
                  pure (.global index arguments.val)
                else none
            | _ => none
        | [] => none
      else if match head with
        | .atom operator selected =>
            selected ∉ forbidden && (floatBuiltinOperator selected operator.name).isSome
        | _ => false then
        match head, tail with
        | .atom operator selected, [leftNode, rightNode] => do
            let operation ← floatBuiltinOperator selected operator.name
            let left ← readClosedInitializer entries visible forbidden fuel leftNode
            let right ← readClosedInitializer entries visible forbidden fuel rightNode
            pure (.floatBin operation left right)
        | _, _ => none
      else if name head = some "if" then
        match tail with
        | [condition, yes, no] => do
            let condition ← readClosedInitializer entries visible forbidden fuel condition
            let yes ← readClosedInitializer entries visible forbidden fuel yes
            let no ← readClosedInitializer entries visible forbidden fuel no
            pure (.ite condition yes no)
        | _ => none
      else if name head = some "begin" then
        match tail with
        | first :: rest => do
            let first ← readClosedInitializer entries visible forbidden fuel first
            let rest ← rest.mapM (readClosedInitializer entries visible forbidden fuel)
            pure (.begin first rest)
        | [] => none
      else if name head = some "lambda" then
        match tail with
        | [.list parameters, resultNode, bodyNode] => do
            let parameters ← readParameters fuel [] parameters
            let result ← readClosedType fuel resultNode
            let body ← readClosedInitializer entries visible
              (parameters.map Prod.fst ++ forbidden) fuel bodyNode
            pure (.lam (parameters.map Prod.snd) result.val body)
        | _ => none
      else if name head = some "let" then
        match tail with
        | [.list bindings, bodyNode] => do
            let (parameters, inputs) ← readBindings fuel [] bindings
            let initializers ← inputs.mapM
              (readClosedInitializer entries visible forbidden fuel)
            let body ← readClosedInitializer entries visible
              (parameters.map Prod.fst ++ forbidden) fuel bodyNode
            pure (.letMany (parameters.map Prod.snd) initializers body)
        | _ => none
      else if name head = some "Nil" then
        match tail with
        | [type] => (readClosedType fuel type).map (fun type => .nil type.val)
        | _ => none
      else if name head = some "None" then
        match tail with
        | [type] => (readClosedType fuel type).map (fun type => .none type.val)
        | _ => none
      else if name head = some "Some" then
        match tail with
        | [type, value] => do
            let type ← readClosedType fuel type
            let value ← readClosedInitializer entries visible forbidden fuel value
            pure (.some type.val value)
        | _ => none
      else if name head = some "Cons" then
        match tail with
        | [type, value, rest] => do
            let type ← readClosedType fuel type
            let value ← readClosedInitializer entries visible forbidden fuel value
            let rest ← readClosedInitializer entries visible forbidden fuel rest
            pure (.cons type.val value rest)
        | _ => none
      else if name head = some "match" then
        match tail with
        | target :: cases => do
            let target ← readClosedInitializer entries visible forbidden fuel target
            match casesParts "Nil" "Cons" cases with
            | some (empty, [headBinder, tailBinder], full) =>
                match binder headBinder, binder tailBinder with
                | some headIdentity, some tailIdentity =>
                    if headIdentity == tailIdentity then none else do
                      let empty ← readClosedInitializer entries visible forbidden fuel empty
                      let full ← readClosedInitializer entries visible
                        (headIdentity :: tailIdentity :: forbidden) fuel full
                      pure (.matchList target empty full)
                | _, _ => none
            | _ =>
                match casesParts "None" "Some" cases with
                | some (empty, [valueBinder], full) =>
                    match binder valueBinder with
                    | some valueIdentity => do
                        let empty ← readClosedInitializer entries visible forbidden fuel empty
                        let full ← readClosedInitializer entries visible
                          (valueIdentity :: forbidden) fuel full
                        pure (.matchOption target empty full)
                    | none => none
                | _ => none
        | _ => none
      else
        let ordinaryApplication := do
          let function ← readClosedInitializer entries visible forbidden fuel head
          let arguments ← tail.mapM (readClosedInitializer entries visible forbidden fuel)
          pure (.app function arguments)
        match head, tail with
        | .atom operator selected, arguments =>
          match if selected != 0 && selected ∉ forbidden then
              visibleFunctionIndex entries visible selected else none with
          | some index => do
              let arguments ← arguments.mapM
                (readClosedInitializer entries visible forbidden fuel)
              pure (.app (.global index []) arguments)
          | none =>
            match arguments with
            | [left, right] => do
                let left ← readClosedInitializer entries visible forbidden fuel left
                let right ← readClosedInitializer entries visible forbidden fuel right
                match selected, operator.name with
                | 3, "+" => pure (.add left right)
                | 6, "-" => pure (.sub left right)
                | 9, "*" => pure (.mul left right)
                | 15, "<=" => pure (.le left right)
                | 24, "integer=" => pure (.intEq left right)
                | _, _ => ordinaryApplication
            | _ => ordinaryApplication
        | _, _ => ordinaryApplication
  | _fuel + 1, .list [] => none

/-- The annotated C `integer=` builtin node is decoded as the corresponding
Surface integer equality once its operands are decoded and name resolution
does not select a user function. -/
theorem readClosedInitializer_intEq
    (entries visible : List GlobalProgramEntry.Entry) (forbidden : List Nat)
    (fuel selected : Nat) (operator : CMacroCopy.Atom)
    (leftNode rightNode : CBindingWalk.Node) (left right : Surface.Expr)
    (selectedEq : selected = 24) (operatorName : operator.name = "integer=")
    (notForbidden : selected ∉ forbidden)
    (notVisibleFunction : visibleFunctionIndex entries visible selected = none)
    (leftDecoded : readClosedInitializer entries visible forbidden fuel leftNode = some left)
    (rightDecoded : readClosedInitializer entries visible forbidden fuel rightNode = some right) :
    readClosedInitializer entries visible forbidden (fuel + 1)
      (.list [.atom operator selected, leftNode, rightNode]) = some (.intEq left right) := by
  have noForbiddenBuiltin : 24 ∉ forbidden := by simpa [selectedEq] using notForbidden
  have noVisibleBuiltin : visibleFunctionIndex entries visible 24 = none := by
    simpa [selectedEq] using notVisibleFunction
  have notTypeApp : "integer=" ≠ "type-app" := by decide
  have notIf : "integer=" ≠ "if" := by decide
  have notBegin : "integer=" ≠ "begin" := by decide
  have notLambda : "integer=" ≠ "lambda" := by decide
  have notLet : "integer=" ≠ "let" := by decide
  have notNil : "integer=" ≠ "Nil" := by decide
  have notNone : "integer=" ≠ "None" := by decide
  have notSome : "integer=" ≠ "Some" := by decide
  have notCons : "integer=" ≠ "Cons" := by decide
  have notMatch : "integer=" ≠ "match" := by decide
  simp [readClosedInitializer, ExpansionLowering.name, selectedEq, operatorName, notForbidden,
    notVisibleFunction, noForbiddenBuiltin, noVisibleBuiltin, notTypeApp, notIf, notBegin,
    notLambda, notLet, notNil, notNone, notSome, notCons, notMatch,
    leftDecoded, rightDecoded, floatBuiltinOperator]

/- Turn the type and evaluation evidence for one decoded initializer into the
checked initializer object consumed by the mixed-declaration row builder. The
evaluator result remains explicit; this connects evidence without claiming
that arbitrary decoding already preserves evaluation. -/
theorem initializerRow_of_typed_evaluation
    (entries : List GlobalProgramEntry.Entry) (slotTypes : List Surface.Ty)
    (slot identity : Nat) (type : Surface.Ty)
    (valid : type.wellFormed 0) (expression : Surface.Expr)
    (tail : List GlobalProgramEntry.Entry)
    (rest : GlobalProgramEntry.TypedInitializerRows entries slotTypes (slot + 1) tail)
    (slotType : slotTypes.get? slot = some type)
    (globals : List Surface.Signature)
    (globalsAgree : GlobalProgramEntry.signatures entries = globals)
    (typing : Surface.HasType globals 0 [] expression type)
    (program : List GlobalIR.Definition) (store : GlobalIR.Store)
    (fuel : Nat) (environment : List PolyIR.Value) (value : PolyIR.Value)
    (evaluated : GlobalIR.evaluate program store fuel environment
      (PolyIR.erase expression) = .ok value) :
    ∃ checked : GlobalProgramEntry.TypedInitializer entries type expression,
      checked.expression = expression ∧
      GlobalProgramEntry.TypedInitializerRows entries slotTypes slot
        (.value identity type valid checked.expression :: tail) ∧
      GlobalIR.evaluate program store fuel environment (PolyIR.erase expression) = .ok value := by
  have sourceTyping : Surface.HasType (GlobalProgramEntry.signatures entries) 0 []
      expression type := by
    rw [globalsAgree]
    exact typing
  let checked : GlobalProgramEntry.TypedInitializer entries type expression :=
    ⟨expression, sourceTyping, PolyIR.erase expression, rfl, rfl⟩
  refine ⟨checked, rfl, ?_, evaluated⟩
  exact GlobalProgramEntry.TypedInitializerRows.value_of_checked_initializer
    entries slotTypes slot identity type valid expression tail rest slotType checked

/-- A successful initializer type-check certificate plus its successful
GlobalIR evaluation constructs the mixed-program typed initializer row. This
composes checker output with runtime evidence instead of asking the caller to
restate the `HasType` derivation carried by the certificate. -/
theorem initializerRow_of_checker_and_evaluation
    (entries : List GlobalProgramEntry.Entry) (slotTypes : List Surface.Ty)
    (slot identity : Nat) (type : Surface.Ty) (valid : type.wellFormed 0)
    (expression : Surface.Expr) (tail : List GlobalProgramEntry.Entry)
    (rest : GlobalProgramEntry.TypedInitializerRows entries slotTypes (slot + 1) tail)
    (slotType : slotTypes.get? slot = some type) (checkerFuel : Nat)
    (checkerAccepted : (GlobalProgramEntry.checkInitializer checkerFuel entries
      expression type).isSome = true)
    (globals : List Surface.Signature)
    (globalsAgree : GlobalProgramEntry.signatures entries = globals)
    (program : List GlobalIR.Definition) (store : GlobalIR.Store)
    (evaluationFuel : Nat) (environment : List PolyIR.Value) (value : PolyIR.Value)
    (evaluated : GlobalIR.evaluate program store evaluationFuel environment
      (PolyIR.erase expression) = .ok value) :
    ∃ checked : GlobalProgramEntry.TypedInitializer entries type expression,
      checked.expression = expression ∧
      GlobalProgramEntry.TypedInitializerRows entries slotTypes slot
        (.value identity type valid checked.expression :: tail) ∧
      GlobalIR.evaluate program store evaluationFuel environment
        (PolyIR.erase expression) = .ok value := by
  obtain ⟨certified, _accepted, certifiedTyping, sourceExact, _erasure⟩ :=
    GlobalProgramEntry.checkInitializer_sound checkerFuel entries expression type checkerAccepted
  have expressionTyping : Surface.HasType (GlobalProgramEntry.signatures entries) 0 []
      expression type := by
    rw [← sourceExact]
    exact certifiedTyping
  have expressionTypingGlobals : Surface.HasType globals 0 [] expression type := by
    rw [← globalsAgree]
    exact expressionTyping
  exact initializerRow_of_typed_evaluation entries slotTypes slot identity type valid expression
    tail rest slotType globals globalsAgree expressionTypingGlobals program store evaluationFuel
    environment value evaluated

/-- End-to-end single-row bridge from the source initializer reader through
the executable type checker and successful GlobalIR evaluation. -/
theorem readClosedInitializer_typedRow_of_checker_and_evaluation
    (entries visible : List GlobalProgramEntry.Entry) (forbidden : List Nat)
    (slotTypes : List Surface.Ty)
    (readerFuel checkerFuel slot identity : Nat) (node : Node) (type : Surface.Ty)
    (valid : type.wellFormed 0) (expression : Surface.Expr)
    (tail : List GlobalProgramEntry.Entry)
    (rest : GlobalProgramEntry.TypedInitializerRows entries slotTypes (slot + 1) tail)
    (slotType : slotTypes.get? slot = some type)
    (decoded : readClosedInitializer entries visible forbidden readerFuel node =
      some expression)
    (checkerAccepted : (GlobalProgramEntry.checkInitializer checkerFuel entries
      expression type).isSome = true)
    (globals : List Surface.Signature)
    (globalsAgree : GlobalProgramEntry.signatures entries = globals)
    (program : List GlobalIR.Definition) (store : GlobalIR.Store)
    (evaluationFuel : Nat) (environment : List PolyIR.Value) (value : PolyIR.Value)
    (evaluated : GlobalIR.evaluate program store evaluationFuel environment
      (PolyIR.erase expression) = .ok value) :
    ∃ checked : GlobalProgramEntry.TypedInitializer entries type expression,
      readClosedInitializer entries visible forbidden readerFuel node =
        some checked.expression ∧ checked.expression = expression ∧
      GlobalProgramEntry.TypedInitializerRows entries slotTypes slot
        (.value identity type valid checked.expression :: tail) ∧
      GlobalIR.evaluate program store evaluationFuel environment
        (PolyIR.erase expression) = .ok value := by
  obtain ⟨checked, expressionEq, rows, evaluation⟩ :=
    initializerRow_of_checker_and_evaluation entries slotTypes slot identity type valid
      expression tail rest slotType checkerFuel checkerAccepted globals globalsAgree program store
      evaluationFuel environment value evaluated
  exact ⟨checked, by rw [expressionEq]; exact decoded, expressionEq, rows, evaluation⟩

/-- Generic row constructor for any expression in the proved arithmetic
fragment. The caller supplies its evaluation result; typing follows from the
fragment derivation and the same expression is retained in both row systems. -/
theorem arithmeticInitializerRow_of_evaluation
    (entries : List GlobalProgramEntry.Entry) (slotTypes : List Surface.Ty)
    (slot identity : Nat) (type : Surface.Ty) (valid : type.wellFormed 0)
    (expression : Surface.Expr) (tail : List GlobalProgramEntry.Entry)
    (rest : GlobalProgramEntry.TypedInitializerRows entries slotTypes (slot + 1) tail)
    (arithmeticTail : GlobalProgramEntry.ArithmeticInitializerRows slotTypes (slot + 1) tail)
    (slotType : slotTypes.get? slot = some type)
    (arithmetic : GlobalProgramEntry.ArithmeticSurfaceExpr expression type)
    (globals : List Surface.Signature)
    (globalsAgree : GlobalProgramEntry.signatures entries = globals)
    (program : List GlobalIR.Definition) (store : GlobalIR.Store) (fuel : Nat)
    (environment : List PolyIR.Value) (value : PolyIR.Value)
    (evaluated : GlobalIR.evaluate program store fuel environment (PolyIR.erase expression) = .ok value) :
    ∃ checked : GlobalProgramEntry.TypedInitializer entries type expression,
      checked.expression = expression ∧
      GlobalProgramEntry.TypedInitializerRows entries slotTypes slot
        (.value identity type valid checked.expression :: tail) ∧
      GlobalProgramEntry.ArithmeticInitializerRows slotTypes slot
        (.value identity type valid checked.expression :: tail) ∧
      GlobalIR.evaluate program store fuel environment (PolyIR.erase expression) = .ok value := by
  obtain ⟨checked, exactExpression, typedRows, evaluation⟩ :=
    initializerRow_of_typed_evaluation entries slotTypes slot identity type valid expression
      tail rest slotType globals globalsAgree arithmetic.hasType program store fuel environment
      value evaluated
  have checkedArithmetic : GlobalProgramEntry.ArithmeticSurfaceExpr checked.expression type := by
    rw [exactExpression]
    exact arithmetic
  exact ⟨checked, exactExpression, typedRows,
    ⟨slotType, checkedArithmetic, arithmeticTail⟩, evaluation⟩

/-- A lexically valid integer atom decodes to the matching typed Surface
literal, and erasure produces the corresponding GlobalIR integer term. -/
theorem readClosedInitializer_true
    (entries visible : List GlobalProgramEntry.Entry) (forbidden : List Nat)
    (fuel selected : Nat) (atom : CMacroCopy.Atom)
    (selectedZero : selected = 0) (spelling : atom.name = "true") :
    readClosedInitializer entries visible forbidden (fuel + 1)
      (.atom atom selected) = some (.bool true) := by
  simp [readClosedInitializer, selectedZero, spelling] <;> decide

theorem readClosedInitializer_false
    (entries visible : List GlobalProgramEntry.Entry) (forbidden : List Nat)
    (fuel selected : Nat) (atom : CMacroCopy.Atom)
    (selectedZero : selected = 0) (spelling : atom.name = "false") :
    readClosedInitializer entries visible forbidden (fuel + 1)
      (.atom atom selected) = some (.bool false) := by
  simp [readClosedInitializer, selectedZero, spelling] <;> decide

theorem readClosedInitializer_unit
    (entries visible : List GlobalProgramEntry.Entry) (forbidden : List Nat)
    (fuel selected : Nat) (atom : CMacroCopy.Atom)
    (selectedZero : selected = 0) (spelling : atom.name = "unit") :
    readClosedInitializer entries visible forbidden (fuel + 1)
      (.atom atom selected) = some .unit := by
  have notTrue : ("unit" == "true") = false := by decide
  have notFalse : ("unit" == "false") = false := by decide
  simp [readClosedInitializer, selectedZero, spelling, notTrue, notFalse]

theorem readClosedInitializer_floatLiteral
    (entries visible : List GlobalProgramEntry.Entry) (forbidden : List Nat)
    (fuel selected : Nat) (atom : CMacroCopy.Atom) (value : Float)
    (selectedZero : selected = 0)
    (lexical : Lexical.floatLiteral atom.name.toList = true)
    (notInteger : Lexical.integerLiteral atom.name.toList = false)
    (parsed : Lexical.parseFloatLiteral atom.name = some value) :
    readClosedInitializer entries visible forbidden (fuel + 1)
      (.atom atom selected) = some (.float value) := by
  have notTrue : atom.name ≠ "true" := by
    intro same
    have invalid : Lexical.floatLiteral "true".toList = false := by decide
    rw [same, invalid] at lexical
    contradiction
  have notFalse : atom.name ≠ "false" := by
    intro same
    have invalid : Lexical.floatLiteral "false".toList = false := by decide
    rw [same, invalid] at lexical
    contradiction
  have notUnit : atom.name ≠ "unit" := by
    intro same
    have invalid : Lexical.floatLiteral "unit".toList = false := by decide
    rw [same, invalid] at lexical
    contradiction
  simp [readClosedInitializer, Lexical.readFloatLiteral, selectedZero,
    notTrue, notFalse, notUnit, lexical, notInteger, parsed]

/-- The reserved C builtin identities decode to the matching Surface Float
operator through the dedicated reader branch. -/
theorem readClosedInitializer_floatBin
    (entries visible : List GlobalProgramEntry.Entry) (forbidden : List Nat)
    (fuel selected : Nat) (operator : CMacroCopy.Atom)
    (leftNode rightNode : CBindingWalk.Node) (operation : Surface.FloatBinOp)
    (left right : Surface.Expr)
    (builtin : (selected = 39 ∧ operator.name = "float+" ∧ operation = .add) ∨
      (selected = 42 ∧ operator.name = "float-" ∧ operation = .sub) ∨
      (selected = 45 ∧ operator.name = "float*" ∧ operation = .mul) ∨
      (selected = 48 ∧ operator.name = "float/" ∧ operation = .div))
    (notForbidden : selected ∉ forbidden)
    (leftDecoded : readClosedInitializer entries visible forbidden fuel leftNode = some left)
    (rightDecoded : readClosedInitializer entries visible forbidden fuel rightNode = some right) :
    readClosedInitializer entries visible forbidden (fuel + 1)
      (.list [.atom operator selected, leftNode, rightNode]) =
        some (.floatBin operation left right) := by
  rcases builtin with ⟨selectedEq, spelling, operationEq⟩ |
    ⟨selectedEq, spelling, operationEq⟩ |
    ⟨selectedEq, spelling, operationEq⟩ |
    ⟨selectedEq, spelling, operationEq⟩
  all_goals
    have notTypeApp : operator.name ≠ "type-app" := by rw [spelling]; decide
    have notIf : operator.name ≠ "if" := by rw [spelling]; decide
    have notBegin : operator.name ≠ "begin" := by rw [spelling]; decide
    have notLambda : operator.name ≠ "lambda" := by rw [spelling]; decide
    have notLet : operator.name ≠ "let" := by rw [spelling]; decide
    have notNil : operator.name ≠ "Nil" := by rw [spelling]; decide
    have notNone : operator.name ≠ "None" := by rw [spelling]; decide
    have notSome : operator.name ≠ "Some" := by rw [spelling]; decide
    have notCons : operator.name ≠ "Cons" := by rw [spelling]; decide
    have notMatch : operator.name ≠ "match" := by rw [spelling]; decide
    have operatorDecoded : floatBuiltinOperator selected operator.name = some operation := by
      rw [selectedEq, spelling, operationEq]
      rfl
    rw [readClosedInitializer]
    simp only [ExpansionLowering.name, Option.some.injEq, selectedEq, operationEq, notTypeApp, notIf,
      notBegin, notLambda, notLet, notNil, notNone, notSome, notCons, notMatch]
    simp only [if_false]
    have dispatch : selected ∉ forbidden ∧
        (floatBuiltinOperator selected operator.name).isSome = true := by
      exact ⟨notForbidden, by rw [operatorDecoded]; rfl⟩
    have dispatchAtId : _ ∧ _ := by simpa [selectedEq] using dispatch
    simp [selectedEq, operationEq, dispatchAtId, operatorDecoded, leftDecoded,
      rightDecoded, Option.bind]
    rw [← selectedEq, ← operationEq, operatorDecoded]

theorem readClosedInitializer_floatLiteral_evaluates
    (entries visible : List GlobalProgramEntry.Entry) (forbidden : List Nat)
    (fuel selected : Nat) (atom : CMacroCopy.Atom) (value : Float)
    (program : List GlobalIR.Definition) (store : GlobalIR.Store)
    (globals : List Surface.Signature) (environment : List PolyIR.Value)
    (selectedZero : selected = 0)
    (lexical : Lexical.floatLiteral atom.name.toList = true)
    (notInteger : Lexical.integerLiteral atom.name.toList = false)
    (parsed : Lexical.parseFloatLiteral atom.name = some value) :
    ∃ expression,
      readClosedInitializer entries visible forbidden (fuel + 1)
        (.atom atom selected) = some expression ∧
      GlobalIR.evaluate program store 1 environment (PolyIR.erase expression) =
        .ok (.float value) ∧ PolyIR.ValueTyped globals (.float value) .float := by
  refine ⟨.float value, readClosedInitializer_floatLiteral entries visible forbidden
    fuel selected atom value selectedZero lexical notInteger parsed, ?_, .float⟩
  rfl

theorem readClosedInitializer_floatLiteral_builds_typed_row
    (entries visible : List GlobalProgramEntry.Entry) (forbidden : List Nat)
    (slotTypes : List Surface.Ty) (slot identity fuel selected : Nat) (value : Float)
    (tail : List GlobalProgramEntry.Entry)
    (typedTail : GlobalProgramEntry.TypedInitializerRows entries slotTypes (slot + 1) tail)
    (arithmeticTail : GlobalProgramEntry.ArithmeticInitializerRows slotTypes (slot + 1) tail)
    (slotType : slotTypes.get? slot = some .float)
    (valid : Surface.Ty.float.wellFormed 0) (atom : CMacroCopy.Atom)
    (program : List GlobalIR.Definition) (store : GlobalIR.Store)
    (globals : List Surface.Signature) (environment : List PolyIR.Value)
    (globalsAgree : GlobalProgramEntry.signatures entries = globals)
    (selectedZero : selected = 0)
    (lexical : Lexical.floatLiteral atom.name.toList = true)
    (notInteger : Lexical.integerLiteral atom.name.toList = false)
    (parsed : Lexical.parseFloatLiteral atom.name = some value) :
    ∃ expression : Surface.Expr,
      ∃ checked : GlobalProgramEntry.TypedInitializer entries .float expression,
      readClosedInitializer entries visible forbidden (fuel + 1)
        (.atom atom selected) = some expression ∧ checked.expression = expression ∧
      GlobalProgramEntry.TypedInitializerRows entries slotTypes slot
        (.value identity .float valid checked.expression :: tail) ∧
      GlobalProgramEntry.ArithmeticInitializerRows slotTypes slot
        (.value identity .float valid checked.expression :: tail) ∧
      GlobalIR.evaluate program store 1 environment (PolyIR.erase expression) =
        .ok (.float value) := by
  have decoder := readClosedInitializer_floatLiteral entries visible forbidden fuel selected atom
    value selectedZero lexical notInteger parsed
  have arithmetic : GlobalProgramEntry.ArithmeticSurfaceExpr (.float value) .float := .float
  have evaluated : GlobalIR.evaluate program store 1 environment
      (PolyIR.erase (.float value)) = .ok (.float value) := rfl
  obtain ⟨checked, exactExpression, typedRows, arithmeticRows, evaluation⟩ :=
    arithmeticInitializerRow_of_evaluation entries slotTypes slot identity .float valid
      (.float value) tail typedTail arithmeticTail slotType arithmetic globals globalsAgree program
      store 1 environment (.float value) evaluated
  exact ⟨.float value, checked, decoder, exactExpression, typedRows, arithmeticRows, evaluation⟩

theorem readClosedInitializer_floatLiteral_initializes_store_typed
    (entries visible : List GlobalProgramEntry.Entry) (forbidden : List Nat)
    (slotTypes : List Surface.Ty) (identity fuel selected initFuel entryIndex : Nat)
    (value : Float) (tail : List GlobalProgramEntry.Entry)
    (typedTail : GlobalProgramEntry.TypedInitializerRows entries slotTypes 1 tail)
    (arithmeticTail : GlobalProgramEntry.ArithmeticInitializerRows slotTypes 1 tail)
    (slotType : slotTypes.get? 0 = some .float)
    (valid : Surface.Ty.float.wellFormed 0) (atom : CMacroCopy.Atom)
    (globals : List Surface.Signature)
    (globalsAgree : GlobalProgramEntry.signatures entries = globals)
    (selectedZero : selected = 0)
    (lexical : Lexical.floatLiteral atom.name.toList = true)
    (notInteger : Lexical.integerLiteral atom.name.toList = false)
    (parsed : Lexical.parseFloatLiteral atom.name = some value) (result : GlobalIR.Store)
    (initialization : GlobalIR.initializeValues
      (GlobalProgramEntry.toRuntimeProgram
        (.value identity .float valid (.float value) :: tail) entryIndex).definitions initFuel
      (List.replicate
        (GlobalProgramEntry.toRuntimeProgram
          (.value identity .float valid (.float value) :: tail) entryIndex).initializers.length none)
      0 (GlobalProgramEntry.toRuntimeProgram
        (.value identity .float valid (.float value) :: tail) entryIndex).initializers = .ok result) :
    ∃ expression : Surface.Expr,
      ∃ checked : GlobalProgramEntry.TypedInitializer entries .float expression,
      readClosedInitializer entries visible forbidden (fuel + 1)
        (.atom atom selected) = some expression ∧ checked.expression = expression ∧
      GlobalProgramEntry.TypedInitializerRows entries slotTypes 0
        (.value identity .float valid checked.expression :: tail) ∧
      GlobalProgramEntry.ArithmeticInitializerRows slotTypes 0
        (.value identity .float valid checked.expression :: tail) ∧
      GlobalIR.StoreWellTyped globals slotTypes result := by
  obtain ⟨expression, checked, decoded, expressionExact, typedRows, arithmeticRows, _eval⟩ :=
    readClosedInitializer_floatLiteral_builds_typed_row entries visible forbidden slotTypes 0
      identity fuel selected value tail typedTail arithmeticTail slotType valid atom
      (GlobalProgramEntry.toRuntimeProgram
        (.value identity .float valid (.float value) :: tail) entryIndex).definitions
      (List.replicate
        (GlobalProgramEntry.toRuntimeProgram
          (.value identity .float valid (.float value) :: tail) entryIndex).initializers.length none)
      globals [] globalsAgree selectedZero lexical notInteger parsed
  have decoder := readClosedInitializer_floatLiteral entries visible forbidden fuel selected atom
    value selectedZero lexical notInteger parsed
  have expressionIsLiteral : expression = .float value := Option.some.inj (decoded.symm.trans decoder)
  have checkedIsLiteral : checked.expression = .float value := expressionExact.trans expressionIsLiteral
  have initializedRows : GlobalIR.initializeValues
      (GlobalProgramEntry.toRuntimeProgram
        (.value identity .float valid checked.expression :: tail) entryIndex).definitions initFuel
      (List.replicate
        (GlobalProgramEntry.toRuntimeProgram
          (.value identity .float valid checked.expression :: tail) entryIndex).initializers.length none)
      0 (GlobalProgramEntry.toRuntimeProgram
        (.value identity .float valid checked.expression :: tail) entryIndex).initializers = .ok result := by
    simpa [GlobalProgramEntry.toRuntimeProgram, checkedIsLiteral] using initialization
  have storeTyped := GlobalProgramEntry.TypedInitializerRows.initialization_preserves_store_arithmetic
    entries globals slotTypes
    (GlobalProgramEntry.toRuntimeProgram
      (.value identity .float valid checked.expression :: tail) entryIndex).definitions
    initFuel (.value identity .float valid checked.expression :: tail) result
    typedRows arithmeticRows initializedRows
  exact ⟨expression, checked, decoded, expressionExact, typedRows, arithmeticRows, storeTyped⟩

theorem readClosedInitializer_true_typed_evaluates
    (entries visible : List GlobalProgramEntry.Entry) (forbidden : List Nat)
    (fuel selected : Nat) (atom : CMacroCopy.Atom)
    (program : List GlobalIR.Definition) (store : GlobalIR.Store)
    (globals : List Surface.Signature) (environment : List PolyIR.Value)
    (selectedZero : selected = 0) (spelling : atom.name = "true") :
    ∃ expression,
      readClosedInitializer entries visible forbidden (fuel + 1)
        (.atom atom selected) = some expression ∧
      Surface.HasType globals 0 [] expression .boolean ∧
      GlobalIR.evaluate program store 1 environment (PolyIR.erase expression) =
        .ok (.bool true) ∧ PolyIR.ValueTyped globals (.bool true) .boolean := by
  refine ⟨.bool true, readClosedInitializer_true entries visible forbidden fuel selected
    atom selectedZero spelling, .bool, ?_, .bool⟩
  rfl

theorem readClosedInitializer_true_builds_typed_row
    (entries visible : List GlobalProgramEntry.Entry) (forbidden : List Nat)
    (slotTypes : List Surface.Ty) (slot identity fuel selected : Nat)
    (tail : List GlobalProgramEntry.Entry)
    (rest : GlobalProgramEntry.TypedInitializerRows entries slotTypes (slot + 1) tail)
    (arithmeticTail : GlobalProgramEntry.ArithmeticInitializerRows slotTypes (slot + 1) tail)
    (slotType : slotTypes.get? slot = some .boolean)
    (valid : Surface.Ty.boolean.wellFormed 0)
    (atom : CMacroCopy.Atom) (program : List GlobalIR.Definition)
    (store : GlobalIR.Store) (globals : List Surface.Signature)
    (environment : List PolyIR.Value)
    (globalsAgree : GlobalProgramEntry.signatures entries = globals)
    (selectedZero : selected = 0) (spelling : atom.name = "true") :
    ∃ expression : Surface.Expr,
      ∃ checked : GlobalProgramEntry.TypedInitializer entries .boolean expression,
      readClosedInitializer entries visible forbidden (fuel + 1)
        (.atom atom selected) = some expression ∧ checked.expression = expression ∧
      GlobalProgramEntry.TypedInitializerRows entries slotTypes slot
        (.value identity .boolean valid checked.expression :: tail) ∧
      GlobalProgramEntry.ArithmeticInitializerRows slotTypes slot
        (.value identity .boolean valid checked.expression :: tail) ∧
      GlobalIR.evaluate program store 1 environment (PolyIR.erase expression) =
        .ok (.bool true) := by
  have decodedTrue := readClosedInitializer_true entries visible forbidden fuel selected atom
    selectedZero spelling
  obtain ⟨expression, decoded, typing, evaluated, _valueTyped⟩ :=
    readClosedInitializer_true_typed_evaluates entries visible forbidden fuel selected atom
      program store globals environment selectedZero spelling
  obtain ⟨checked, expressionExact, row, evaluation⟩ :=
    initializerRow_of_typed_evaluation entries slotTypes slot identity .boolean valid expression
      tail rest slotType globals globalsAgree typing program store 1 environment (.bool true)
      evaluated
  have expressionIsTrue : expression = .bool true :=
    Option.some.inj (decoded.symm.trans decodedTrue)
  have checkedIsTrue : checked.expression = .bool true :=
    expressionExact.trans expressionIsTrue
  have arithmetic : GlobalProgramEntry.ArithmeticSurfaceExpr checked.expression .boolean := by
    rw [checkedIsTrue]
    exact .bool
  exact ⟨expression, checked, decoded, expressionExact, row,
    ⟨slotType, arithmetic, arithmeticTail⟩, evaluation⟩

/-- End-to-end Boolean initializer fragment: a raw `true` atom is decoded,
turned into a typed/arithmetic value row, and a successful run of the generated
mixed-entry initializer list leaves a well-typed global store. The tail may
contain further checked arithmetic-fragment value rows and function entries. -/
theorem readClosedInitializer_true_initializes_store_typed
    (entries visible : List GlobalProgramEntry.Entry) (forbidden : List Nat)
    (slotTypes : List Surface.Ty) (identity fuel selected initFuel entryIndex : Nat)
    (tail : List GlobalProgramEntry.Entry)
    (typedTail : GlobalProgramEntry.TypedInitializerRows entries slotTypes 1 tail)
    (arithmeticTail : GlobalProgramEntry.ArithmeticInitializerRows slotTypes 1 tail)
    (slotType : slotTypes.get? 0 = some .boolean)
    (valid : Surface.Ty.boolean.wellFormed 0) (atom : CMacroCopy.Atom)
    (globals : List Surface.Signature)
    (globalsAgree : GlobalProgramEntry.signatures entries = globals)
    (selectedZero : selected = 0) (spelling : atom.name = "true")
    (result : GlobalIR.Store)
    (initialization : GlobalIR.initializeValues
      (GlobalProgramEntry.toRuntimeProgram
        (.value identity .boolean valid (.bool true) :: tail) entryIndex).definitions initFuel
      (List.replicate
        (GlobalProgramEntry.toRuntimeProgram
          (.value identity .boolean valid (.bool true) :: tail) entryIndex).initializers.length none)
      0 (GlobalProgramEntry.toRuntimeProgram
        (.value identity .boolean valid (.bool true) :: tail) entryIndex).initializers = .ok result) :
    ∃ expression : Surface.Expr,
      ∃ checked : GlobalProgramEntry.TypedInitializer entries .boolean expression,
      readClosedInitializer entries visible forbidden (fuel + 1)
        (.atom atom selected) = some expression ∧
      checked.expression = expression ∧
      GlobalProgramEntry.TypedInitializerRows entries slotTypes 0
        (.value identity .boolean valid checked.expression :: tail) ∧
      GlobalProgramEntry.ArithmeticInitializerRows slotTypes 0
        (.value identity .boolean valid checked.expression :: tail) ∧
      GlobalIR.StoreWellTyped globals slotTypes result := by
  obtain ⟨expression, checked, decoded, expressionExact, typedRows, arithmeticRows, _eval⟩ :=
    readClosedInitializer_true_builds_typed_row entries visible forbidden slotTypes 0 identity
      fuel selected tail typedTail arithmeticTail slotType valid atom
      (GlobalProgramEntry.toRuntimeProgram
        (.value identity .boolean valid (.bool true) :: tail) entryIndex).definitions
      (List.replicate
        (GlobalProgramEntry.toRuntimeProgram
          (.value identity .boolean valid (.bool true) :: tail) entryIndex).initializers.length none)
      globals [] globalsAgree selectedZero spelling
  have decoderTrue := readClosedInitializer_true entries visible forbidden fuel selected atom
    selectedZero spelling
  have expressionTrue : expression = .bool true :=
    Option.some.inj (decoded.symm.trans decoderTrue)
  have checkedTrue : checked.expression = .bool true := expressionExact.trans expressionTrue
  have initializedRows : GlobalIR.initializeValues
      (GlobalProgramEntry.toRuntimeProgram
        (.value identity .boolean valid checked.expression :: tail) entryIndex).definitions initFuel
      (List.replicate
        (GlobalProgramEntry.toRuntimeProgram
          (.value identity .boolean valid checked.expression :: tail) entryIndex).initializers.length none)
      0 (GlobalProgramEntry.toRuntimeProgram
        (.value identity .boolean valid checked.expression :: tail) entryIndex).initializers = .ok result := by
    simpa [GlobalProgramEntry.toRuntimeProgram, checkedTrue] using initialization
  have storeTyped := GlobalProgramEntry.TypedInitializerRows.initialization_preserves_store_arithmetic
    entries globals slotTypes
    (GlobalProgramEntry.toRuntimeProgram
      (.value identity .boolean valid checked.expression :: tail) entryIndex).definitions
    initFuel (.value identity .boolean valid checked.expression :: tail) result
    typedRows arithmeticRows initializedRows
  exact ⟨expression, checked, decoded, expressionExact, typedRows, arithmeticRows, storeTyped⟩

/-- A decoded boolean literal can be assembled into the same typed initializer
row for either boolean value, independently of the atom spelling proof. -/
theorem booleanInitializer_typed_row
    (entries : List GlobalProgramEntry.Entry) (slotTypes : List Surface.Ty)
    (slot identity : Nat) (tail : List GlobalProgramEntry.Entry)
    (rest : GlobalProgramEntry.TypedInitializerRows entries slotTypes (slot + 1) tail)
    (arithmeticTail : GlobalProgramEntry.ArithmeticInitializerRows slotTypes (slot + 1) tail)
    (slotType : slotTypes.get? slot = some .boolean)
    (valid : Surface.Ty.boolean.wellFormed 0) (expression : Surface.Expr)
    (globals : List Surface.Signature)
    (globalsAgree : GlobalProgramEntry.signatures entries = globals)
    (decoded : expression = .bool true ∨ expression = .bool false)
    (program : List GlobalIR.Definition) (store : GlobalIR.Store)
    (environment : List PolyIR.Value) (result : PolyIR.Value)
    (typing : Surface.HasType globals 0 [] expression .boolean)
    (evaluated : GlobalIR.evaluate program store 1 environment (PolyIR.erase expression) = .ok result) :
    ∃ checked : GlobalProgramEntry.TypedInitializer entries .boolean expression,
      checked.expression = expression ∧
      GlobalProgramEntry.TypedInitializerRows entries slotTypes slot
        (.value identity .boolean valid checked.expression :: tail) ∧
      GlobalProgramEntry.ArithmeticInitializerRows slotTypes slot
        (.value identity .boolean valid checked.expression :: tail) ∧
      GlobalIR.evaluate program store 1 environment (PolyIR.erase expression) = .ok result := by
  obtain ⟨checked, expressionExact, row, evaluation⟩ :=
    initializerRow_of_typed_evaluation entries slotTypes slot identity .boolean valid expression
      tail rest slotType globals globalsAgree typing program store 1 environment result evaluated
  have arithmeticExpr : GlobalProgramEntry.ArithmeticSurfaceExpr checked.expression .boolean := by
    rcases decoded with isTrue | isFalse
    · rw [expressionExact, isTrue]
      exact .bool
    · rw [expressionExact, isFalse]
      exact .bool
  exact ⟨checked, expressionExact, row,
    ⟨slotType, arithmeticExpr, arithmeticTail⟩, evaluation⟩

/-- Unit initializers participate in the typed-row invariant even though they
do not use an arithmetic operator. -/
theorem unitInitializer_typed_row
    (entries : List GlobalProgramEntry.Entry) (slotTypes : List Surface.Ty)
    (slot identity : Nat) (tail : List GlobalProgramEntry.Entry)
    (rest : GlobalProgramEntry.TypedInitializerRows entries slotTypes (slot + 1) tail)
    (arithmeticTail : GlobalProgramEntry.ArithmeticInitializerRows slotTypes (slot + 1) tail)
    (slotType : slotTypes.get? slot = some .unit)
    (valid : Surface.Ty.unit.wellFormed 0) (expression : Surface.Expr)
    (globals : List Surface.Signature)
    (globalsAgree : GlobalProgramEntry.signatures entries = globals)
    (decoded : expression = .unit)
    (program : List GlobalIR.Definition) (store : GlobalIR.Store)
    (environment : List PolyIR.Value)
    (typing : Surface.HasType globals 0 [] expression .unit)
    (evaluated : GlobalIR.evaluate program store 1 environment (PolyIR.erase expression) = .ok .unit) :
    ∃ checked : GlobalProgramEntry.TypedInitializer entries .unit expression,
      checked.expression = expression ∧
      GlobalProgramEntry.TypedInitializerRows entries slotTypes slot
        (.value identity .unit valid checked.expression :: tail) ∧
      GlobalProgramEntry.ArithmeticInitializerRows slotTypes slot
        (.value identity .unit valid checked.expression :: tail) ∧
      GlobalIR.evaluate program store 1 environment (PolyIR.erase expression) = .ok .unit := by
  obtain ⟨checked, expressionExact, row, evaluation⟩ :=
    initializerRow_of_typed_evaluation entries slotTypes slot identity .unit valid expression
      tail rest slotType globals globalsAgree typing program store 1 environment .unit evaluated
  have arithmeticExpr : GlobalProgramEntry.ArithmeticSurfaceExpr checked.expression .unit := by
    rw [expressionExact, decoded]
    exact .unit
  exact ⟨checked, expressionExact, row,
    ⟨slotType, arithmeticExpr, arithmeticTail⟩, evaluation⟩

theorem readClosedInitializer_false_typed_evaluates
    (entries visible : List GlobalProgramEntry.Entry) (forbidden : List Nat)
    (fuel selected : Nat) (atom : CMacroCopy.Atom)
    (program : List GlobalIR.Definition) (store : GlobalIR.Store)
    (globals : List Surface.Signature) (environment : List PolyIR.Value)
    (selectedZero : selected = 0) (spelling : atom.name = "false") :
    ∃ expression,
      readClosedInitializer entries visible forbidden (fuel + 1)
        (.atom atom selected) = some expression ∧
      Surface.HasType globals 0 [] expression .boolean ∧
      GlobalIR.evaluate program store 1 environment (PolyIR.erase expression) =
        .ok (.bool false) ∧ PolyIR.ValueTyped globals (.bool false) .boolean := by
  refine ⟨.bool false, readClosedInitializer_false entries visible forbidden fuel selected
    atom selectedZero spelling, .bool, ?_, .bool⟩
  rfl

theorem readClosedInitializer_unit_typed_evaluates
    (entries visible : List GlobalProgramEntry.Entry) (forbidden : List Nat)
    (fuel selected : Nat) (atom : CMacroCopy.Atom)
    (program : List GlobalIR.Definition) (store : GlobalIR.Store)
    (globals : List Surface.Signature) (environment : List PolyIR.Value)
    (selectedZero : selected = 0) (spelling : atom.name = "unit") :
    ∃ expression,
      readClosedInitializer entries visible forbidden (fuel + 1)
        (.atom atom selected) = some expression ∧
      Surface.HasType globals 0 [] expression .unit ∧
      GlobalIR.evaluate program store 1 environment (PolyIR.erase expression) =
        .ok .unit ∧ PolyIR.ValueTyped globals .unit .unit := by
  refine ⟨.unit, readClosedInitializer_unit entries visible forbidden fuel selected
    atom selectedZero spelling, .unit, ?_, .unit⟩
  rfl

theorem readClosedInitializer_false_builds_typed_row
    (entries visible : List GlobalProgramEntry.Entry) (forbidden : List Nat)
    (slotTypes : List Surface.Ty) (slot identity fuel selected : Nat)
    (tail : List GlobalProgramEntry.Entry)
    (rest : GlobalProgramEntry.TypedInitializerRows entries slotTypes (slot + 1) tail)
    (arithmeticTail : GlobalProgramEntry.ArithmeticInitializerRows slotTypes (slot + 1) tail)
    (slotType : slotTypes.get? slot = some .boolean)
    (valid : Surface.Ty.boolean.wellFormed 0) (atom : CMacroCopy.Atom)
    (program : List GlobalIR.Definition) (store : GlobalIR.Store)
    (globals : List Surface.Signature) (environment : List PolyIR.Value)
    (globalsAgree : GlobalProgramEntry.signatures entries = globals)
    (selectedZero : selected = 0) (spelling : atom.name = "false") :
    ∃ expression : Surface.Expr,
      ∃ checked : GlobalProgramEntry.TypedInitializer entries .boolean expression,
      readClosedInitializer entries visible forbidden (fuel + 1)
        (.atom atom selected) = some expression ∧ checked.expression = expression ∧
      GlobalProgramEntry.TypedInitializerRows entries slotTypes slot
        (.value identity .boolean valid checked.expression :: tail) ∧
      GlobalProgramEntry.ArithmeticInitializerRows slotTypes slot
        (.value identity .boolean valid checked.expression :: tail) ∧
      GlobalIR.evaluate program store 1 environment (PolyIR.erase expression) =
        .ok (.bool false) := by
  obtain ⟨expression, decoded, typing, evaluated, _typed⟩ :=
    readClosedInitializer_false_typed_evaluates entries visible forbidden fuel selected atom
      program store globals environment selectedZero spelling
  have isFalse : expression = .bool false := by
    have decoder := readClosedInitializer_false entries visible forbidden fuel selected atom
      selectedZero spelling
    exact Option.some.inj (decoded.symm.trans decoder)
  obtain ⟨checked, exactExpression, typedRow, arithmeticRow, evaluation⟩ :=
    booleanInitializer_typed_row entries slotTypes slot identity tail rest arithmeticTail
      slotType valid expression globals globalsAgree (Or.inr isFalse) program store environment
      (.bool false) typing evaluated
  exact ⟨expression, checked, decoded, exactExpression, typedRow, arithmeticRow, evaluation⟩

theorem readClosedInitializer_unit_builds_typed_row
    (entries visible : List GlobalProgramEntry.Entry) (forbidden : List Nat)
    (slotTypes : List Surface.Ty) (slot identity fuel selected : Nat)
    (tail : List GlobalProgramEntry.Entry)
    (rest : GlobalProgramEntry.TypedInitializerRows entries slotTypes (slot + 1) tail)
    (arithmeticTail : GlobalProgramEntry.ArithmeticInitializerRows slotTypes (slot + 1) tail)
    (slotType : slotTypes.get? slot = some .unit)
    (valid : Surface.Ty.unit.wellFormed 0) (atom : CMacroCopy.Atom)
    (program : List GlobalIR.Definition) (store : GlobalIR.Store)
    (globals : List Surface.Signature) (environment : List PolyIR.Value)
    (globalsAgree : GlobalProgramEntry.signatures entries = globals)
    (selectedZero : selected = 0) (spelling : atom.name = "unit") :
    ∃ expression : Surface.Expr,
      ∃ checked : GlobalProgramEntry.TypedInitializer entries .unit expression,
      readClosedInitializer entries visible forbidden (fuel + 1)
        (.atom atom selected) = some expression ∧ checked.expression = expression ∧
      GlobalProgramEntry.TypedInitializerRows entries slotTypes slot
        (.value identity .unit valid checked.expression :: tail) ∧
      GlobalProgramEntry.ArithmeticInitializerRows slotTypes slot
        (.value identity .unit valid checked.expression :: tail) ∧
      GlobalIR.evaluate program store 1 environment (PolyIR.erase expression) = .ok .unit := by
  obtain ⟨expression, decoded, typing, evaluated, _typed⟩ :=
    readClosedInitializer_unit_typed_evaluates entries visible forbidden fuel selected atom
      program store globals environment selectedZero spelling
  have isUnit : expression = .unit := by
    have decoder := readClosedInitializer_unit entries visible forbidden fuel selected atom
      selectedZero spelling
    exact Option.some.inj (decoded.symm.trans decoder)
  obtain ⟨checked, exactExpression, typedRow, arithmeticRow, evaluation⟩ :=
    unitInitializer_typed_row entries slotTypes slot identity tail rest arithmeticTail
      slotType valid expression globals globalsAgree isUnit program store environment typing evaluated
  exact ⟨expression, checked, decoded, exactExpression, typedRow, arithmeticRow, evaluation⟩

/-- The false-atom counterpart of the true initializer execution theorem. -/
theorem readClosedInitializer_false_initializes_store_typed
    (entries visible : List GlobalProgramEntry.Entry) (forbidden : List Nat)
    (slotTypes : List Surface.Ty) (identity fuel selected initFuel entryIndex : Nat)
    (tail : List GlobalProgramEntry.Entry)
    (typedTail : GlobalProgramEntry.TypedInitializerRows entries slotTypes 1 tail)
    (arithmeticTail : GlobalProgramEntry.ArithmeticInitializerRows slotTypes 1 tail)
    (slotType : slotTypes.get? 0 = some .boolean)
    (valid : Surface.Ty.boolean.wellFormed 0) (atom : CMacroCopy.Atom)
    (globals : List Surface.Signature)
    (globalsAgree : GlobalProgramEntry.signatures entries = globals)
    (selectedZero : selected = 0) (spelling : atom.name = "false")
    (result : GlobalIR.Store)
    (initialization : GlobalIR.initializeValues
      (GlobalProgramEntry.toRuntimeProgram
        (.value identity .boolean valid (.bool false) :: tail) entryIndex).definitions initFuel
      (List.replicate
        (GlobalProgramEntry.toRuntimeProgram
          (.value identity .boolean valid (.bool false) :: tail) entryIndex).initializers.length none)
      0 (GlobalProgramEntry.toRuntimeProgram
        (.value identity .boolean valid (.bool false) :: tail) entryIndex).initializers = .ok result) :
    ∃ expression : Surface.Expr,
      ∃ checked : GlobalProgramEntry.TypedInitializer entries .boolean expression,
      readClosedInitializer entries visible forbidden (fuel + 1)
        (.atom atom selected) = some expression ∧
      checked.expression = expression ∧
      GlobalProgramEntry.TypedInitializerRows entries slotTypes 0
        (.value identity .boolean valid checked.expression :: tail) ∧
      GlobalProgramEntry.ArithmeticInitializerRows slotTypes 0
        (.value identity .boolean valid checked.expression :: tail) ∧
      GlobalIR.StoreWellTyped globals slotTypes result := by
  obtain ⟨expression, checked, decoded, expressionExact, typedRows, arithmeticRows, _eval⟩ :=
    readClosedInitializer_false_builds_typed_row entries visible forbidden slotTypes 0 identity
      fuel selected tail typedTail arithmeticTail slotType valid atom
      (GlobalProgramEntry.toRuntimeProgram
        (.value identity .boolean valid (.bool false) :: tail) entryIndex).definitions
      (List.replicate
        (GlobalProgramEntry.toRuntimeProgram
          (.value identity .boolean valid (.bool false) :: tail) entryIndex).initializers.length none)
      globals [] globalsAgree selectedZero spelling
  have decoderFalse := readClosedInitializer_false entries visible forbidden fuel selected atom
    selectedZero spelling
  have expressionFalse : expression = .bool false :=
    Option.some.inj (decoded.symm.trans decoderFalse)
  have checkedFalse : checked.expression = .bool false := expressionExact.trans expressionFalse
  have initializedRows : GlobalIR.initializeValues
      (GlobalProgramEntry.toRuntimeProgram
        (.value identity .boolean valid checked.expression :: tail) entryIndex).definitions initFuel
      (List.replicate
        (GlobalProgramEntry.toRuntimeProgram
          (.value identity .boolean valid checked.expression :: tail) entryIndex).initializers.length none)
      0 (GlobalProgramEntry.toRuntimeProgram
        (.value identity .boolean valid checked.expression :: tail) entryIndex).initializers = .ok result := by
    simpa [GlobalProgramEntry.toRuntimeProgram, checkedFalse] using initialization
  have storeTyped := GlobalProgramEntry.TypedInitializerRows.initialization_preserves_store_arithmetic
    entries globals slotTypes
    (GlobalProgramEntry.toRuntimeProgram
      (.value identity .boolean valid checked.expression :: tail) entryIndex).definitions
    initFuel (.value identity .boolean valid checked.expression :: tail) result
    typedRows arithmeticRows initializedRows
  exact ⟨expression, checked, decoded, expressionExact, typedRows, arithmeticRows, storeTyped⟩

/-- Unit atom initialization also reaches the generated runtime program and
the post-initialization store typing theorem. -/
theorem readClosedInitializer_unit_initializes_store_typed
    (entries visible : List GlobalProgramEntry.Entry) (forbidden : List Nat)
    (slotTypes : List Surface.Ty) (identity fuel selected initFuel entryIndex : Nat)
    (tail : List GlobalProgramEntry.Entry)
    (typedTail : GlobalProgramEntry.TypedInitializerRows entries slotTypes 1 tail)
    (arithmeticTail : GlobalProgramEntry.ArithmeticInitializerRows slotTypes 1 tail)
    (slotType : slotTypes.get? 0 = some .unit)
    (valid : Surface.Ty.unit.wellFormed 0) (atom : CMacroCopy.Atom)
    (globals : List Surface.Signature)
    (globalsAgree : GlobalProgramEntry.signatures entries = globals)
    (selectedZero : selected = 0) (spelling : atom.name = "unit")
    (result : GlobalIR.Store)
    (initialization : GlobalIR.initializeValues
      (GlobalProgramEntry.toRuntimeProgram
        (.value identity .unit valid .unit :: tail) entryIndex).definitions initFuel
      (List.replicate
        (GlobalProgramEntry.toRuntimeProgram
          (.value identity .unit valid .unit :: tail) entryIndex).initializers.length none)
      0 (GlobalProgramEntry.toRuntimeProgram
        (.value identity .unit valid .unit :: tail) entryIndex).initializers = .ok result) :
    ∃ expression : Surface.Expr,
      ∃ checked : GlobalProgramEntry.TypedInitializer entries .unit expression,
      readClosedInitializer entries visible forbidden (fuel + 1)
        (.atom atom selected) = some expression ∧
      checked.expression = expression ∧
      GlobalProgramEntry.TypedInitializerRows entries slotTypes 0
        (.value identity .unit valid checked.expression :: tail) ∧
      GlobalProgramEntry.ArithmeticInitializerRows slotTypes 0
        (.value identity .unit valid checked.expression :: tail) ∧
      GlobalIR.StoreWellTyped globals slotTypes result := by
  obtain ⟨expression, checked, decoded, expressionExact, typedRows, arithmeticRows, _eval⟩ :=
    readClosedInitializer_unit_builds_typed_row entries visible forbidden slotTypes 0 identity
      fuel selected tail typedTail arithmeticTail slotType valid atom
      (GlobalProgramEntry.toRuntimeProgram
        (.value identity .unit valid .unit :: tail) entryIndex).definitions
      (List.replicate
        (GlobalProgramEntry.toRuntimeProgram
          (.value identity .unit valid .unit :: tail) entryIndex).initializers.length none)
      globals [] globalsAgree selectedZero spelling
  have decoderUnit := readClosedInitializer_unit entries visible forbidden fuel selected atom
    selectedZero spelling
  have expressionUnit : expression = .unit :=
    Option.some.inj (decoded.symm.trans decoderUnit)
  have checkedUnit : checked.expression = .unit := expressionExact.trans expressionUnit
  have initializedRows : GlobalIR.initializeValues
      (GlobalProgramEntry.toRuntimeProgram
        (.value identity .unit valid checked.expression :: tail) entryIndex).definitions initFuel
      (List.replicate
        (GlobalProgramEntry.toRuntimeProgram
          (.value identity .unit valid checked.expression :: tail) entryIndex).initializers.length none)
      0 (GlobalProgramEntry.toRuntimeProgram
        (.value identity .unit valid checked.expression :: tail) entryIndex).initializers = .ok result := by
    simpa [GlobalProgramEntry.toRuntimeProgram, checkedUnit] using initialization
  have storeTyped := GlobalProgramEntry.TypedInitializerRows.initialization_preserves_store_arithmetic
    entries globals slotTypes
    (GlobalProgramEntry.toRuntimeProgram
      (.value identity .unit valid checked.expression :: tail) entryIndex).definitions
    initFuel (.value identity .unit valid checked.expression :: tail) result
    typedRows arithmeticRows initializedRows
  exact ⟨expression, checked, decoded, expressionExact, typedRows, arithmeticRows, storeTyped⟩

theorem readClosedInitializer_integerLiteral
    (entries visible : List GlobalProgramEntry.Entry) (forbidden : List Nat)
    (fuel selected : Nat) (atom : CMacroCopy.Atom) (value : Int)
    (selectedZero : selected = 0)
    (lexical : Lexical.integerLiteral atom.name.toList = true)
    (parsed : atom.name.toInt? = some value) :
    readClosedInitializer entries visible forbidden (fuel + 1)
      (.atom atom selected) = some (.int value) := by
  have notTrue : atom.name ≠ "true" := by
    intro same
    have invalid : Lexical.integerLiteral "true".toList = false := by decide
    rw [same, invalid] at lexical
    contradiction
  have notFalse : atom.name ≠ "false" := by
    intro same
    have invalid : Lexical.integerLiteral "false".toList = false := by decide
    rw [same, invalid] at lexical
    contradiction
  have notUnit : atom.name ≠ "unit" := by
    intro same
    have invalid : Lexical.integerLiteral "unit".toList = false := by decide
    rw [same, invalid] at lexical
    contradiction
  simp [readClosedInitializer, selectedZero, notTrue, notFalse, notUnit,
    lexical, parsed]

theorem readClosedInitializer_integerLiteral_evaluates
    (entries visible : List GlobalProgramEntry.Entry) (forbidden : List Nat)
    (fuel selected : Nat) (atom : CMacroCopy.Atom) (value : Int)
    (program : List GlobalIR.Definition) (store : GlobalIR.Store)
    (globals : List Surface.Signature)
    (environment : List PolyIR.Value)
    (selectedZero : selected = 0)
    (lexical : Lexical.integerLiteral atom.name.toList = true)
    (parsed : atom.name.toInt? = some value) :
    ∃ expression,
      readClosedInitializer entries visible forbidden (fuel + 1)
        (.atom atom selected) = some expression ∧
      GlobalIR.evaluate program store 1 environment (PolyIR.erase expression) =
        .ok (.int value) ∧ PolyIR.ValueTyped globals (.int value) .integer := by
  refine ⟨.int value, readClosedInitializer_integerLiteral entries visible forbidden
    fuel selected atom value selectedZero lexical parsed, ?_, .int⟩
  rfl

theorem readClosedInitializer_integerLiteral_builds_typed_row
    (entries visible : List GlobalProgramEntry.Entry) (forbidden : List Nat)
    (slotTypes : List Surface.Ty) (slot identity fuel selected : Nat) (value : Int)
    (tail : List GlobalProgramEntry.Entry)
    (typedTail : GlobalProgramEntry.TypedInitializerRows entries slotTypes (slot + 1) tail)
    (arithmeticTail : GlobalProgramEntry.ArithmeticInitializerRows slotTypes (slot + 1) tail)
    (slotType : slotTypes.get? slot = some .integer)
    (valid : Surface.Ty.integer.wellFormed 0) (atom : CMacroCopy.Atom)
    (program : List GlobalIR.Definition) (store : GlobalIR.Store)
    (globals : List Surface.Signature) (environment : List PolyIR.Value)
    (globalsAgree : GlobalProgramEntry.signatures entries = globals)
    (selectedZero : selected = 0)
    (lexical : Lexical.integerLiteral atom.name.toList = true)
    (parsed : atom.name.toInt? = some value) :
    ∃ expression : Surface.Expr,
      ∃ checked : GlobalProgramEntry.TypedInitializer entries .integer expression,
      readClosedInitializer entries visible forbidden (fuel + 1)
        (.atom atom selected) = some expression ∧ checked.expression = expression ∧
      GlobalProgramEntry.TypedInitializerRows entries slotTypes slot
        (.value identity .integer valid checked.expression :: tail) ∧
      GlobalProgramEntry.ArithmeticInitializerRows slotTypes slot
        (.value identity .integer valid checked.expression :: tail) ∧
      GlobalIR.evaluate program store 1 environment (PolyIR.erase expression) =
        .ok (.int value) := by
  obtain ⟨expression, decoded, evaluated, _typed⟩ :=
    readClosedInitializer_integerLiteral_evaluates entries visible forbidden fuel selected atom
      value program store globals environment selectedZero lexical parsed
  have decoder := readClosedInitializer_integerLiteral entries visible forbidden fuel selected atom
    value selectedZero lexical parsed
  have expressionIsInt : expression = .int value := Option.some.inj (decoded.symm.trans decoder)
  have arithmetic : GlobalProgramEntry.ArithmeticSurfaceExpr expression .integer := by
    rw [expressionIsInt]
    exact .int
  obtain ⟨checked, exactExpression, typedRows, arithmeticRows, evaluation⟩ :=
    arithmeticInitializerRow_of_evaluation entries slotTypes slot identity .integer valid
      expression tail typedTail arithmeticTail slotType arithmetic globals globalsAgree program
      store 1 environment (.int value) evaluated
  exact ⟨expression, checked, decoded, exactExpression, typedRows, arithmeticRows, evaluation⟩

/-- A raw integer-literal value declaration reaches the generated runtime
initializer and leaves a well-typed store after any successful initialization
of the declaration and its arithmetic-fragment tail. -/
theorem readClosedInitializer_integerLiteral_initializes_store_typed
    (entries visible : List GlobalProgramEntry.Entry) (forbidden : List Nat)
    (slotTypes : List Surface.Ty) (identity fuel selected initFuel entryIndex : Nat)
    (value : Int) (tail : List GlobalProgramEntry.Entry)
    (typedTail : GlobalProgramEntry.TypedInitializerRows entries slotTypes 1 tail)
    (arithmeticTail : GlobalProgramEntry.ArithmeticInitializerRows slotTypes 1 tail)
    (slotType : slotTypes.get? 0 = some .integer)
    (valid : Surface.Ty.integer.wellFormed 0) (atom : CMacroCopy.Atom)
    (globals : List Surface.Signature)
    (globalsAgree : GlobalProgramEntry.signatures entries = globals)
    (selectedZero : selected = 0)
    (lexical : Lexical.integerLiteral atom.name.toList = true)
    (parsed : atom.name.toInt? = some value) (result : GlobalIR.Store)
    (initialization : GlobalIR.initializeValues
      (GlobalProgramEntry.toRuntimeProgram
        (.value identity .integer valid (.int value) :: tail) entryIndex).definitions initFuel
      (List.replicate
        (GlobalProgramEntry.toRuntimeProgram
          (.value identity .integer valid (.int value) :: tail) entryIndex).initializers.length none)
      0 (GlobalProgramEntry.toRuntimeProgram
        (.value identity .integer valid (.int value) :: tail) entryIndex).initializers = .ok result) :
    ∃ expression : Surface.Expr,
      ∃ checked : GlobalProgramEntry.TypedInitializer entries .integer expression,
      readClosedInitializer entries visible forbidden (fuel + 1)
        (.atom atom selected) = some expression ∧
      checked.expression = expression ∧
      GlobalProgramEntry.TypedInitializerRows entries slotTypes 0
        (.value identity .integer valid checked.expression :: tail) ∧
      GlobalProgramEntry.ArithmeticInitializerRows slotTypes 0
        (.value identity .integer valid checked.expression :: tail) ∧
      GlobalIR.StoreWellTyped globals slotTypes result := by
  obtain ⟨expression, checked, decoded, expressionExact, typedRows, arithmeticRows, _eval⟩ :=
    readClosedInitializer_integerLiteral_builds_typed_row entries visible forbidden slotTypes 0
      identity fuel selected value tail typedTail arithmeticTail slotType valid atom
      (GlobalProgramEntry.toRuntimeProgram
        (.value identity .integer valid (.int value) :: tail) entryIndex).definitions
      (List.replicate
        (GlobalProgramEntry.toRuntimeProgram
          (.value identity .integer valid (.int value) :: tail) entryIndex).initializers.length none)
      globals [] globalsAgree selectedZero lexical parsed
  have decoder := readClosedInitializer_integerLiteral entries visible forbidden fuel selected atom
    value selectedZero lexical parsed
  have expressionIsLiteral : expression = .int value :=
    Option.some.inj (decoded.symm.trans decoder)
  have checkedIsLiteral : checked.expression = .int value := expressionExact.trans expressionIsLiteral
  have initializedRows : GlobalIR.initializeValues
      (GlobalProgramEntry.toRuntimeProgram
        (.value identity .integer valid checked.expression :: tail) entryIndex).definitions initFuel
      (List.replicate
        (GlobalProgramEntry.toRuntimeProgram
          (.value identity .integer valid checked.expression :: tail) entryIndex).initializers.length none)
      0 (GlobalProgramEntry.toRuntimeProgram
        (.value identity .integer valid checked.expression :: tail) entryIndex).initializers = .ok result := by
    simpa [GlobalProgramEntry.toRuntimeProgram, checkedIsLiteral] using initialization
  have storeTyped := GlobalProgramEntry.TypedInitializerRows.initialization_preserves_store_arithmetic
    entries globals slotTypes
    (GlobalProgramEntry.toRuntimeProgram
      (.value identity .integer valid checked.expression :: tail) entryIndex).definitions
    initFuel (.value identity .integer valid checked.expression :: tail) result
    typedRows arithmeticRows initializedRows
  exact ⟨expression, checked, decoded, expressionExact, typedRows, arithmeticRows, storeTyped⟩

/-- The decoder's arithmetic constructor preserves the evaluated result when
the already-decoded operands evaluate to integers. The recursive operand
correspondence is explicit in the hypotheses. -/
theorem readClosedInitializer_add_evaluates
    (entries visible : List GlobalProgramEntry.Entry) (forbidden : List Nat)
    (decodeFuel evalFuel : Nat) (node : CBindingWalk.Node)
    (left right : Surface.Expr) (program : List GlobalIR.Definition)
    (store : GlobalIR.Store) (globals : List Surface.Signature)
    (environment : List PolyIR.Value) (x y : Int)
    (decoded : readClosedInitializer entries visible forbidden decodeFuel node =
      some (.add left right))
    (leftArithmetic : GlobalProgramEntry.ArithmeticSurfaceExpr left .integer)
    (rightArithmetic : GlobalProgramEntry.ArithmeticSurfaceExpr right .integer)
    (leftEvaluates : GlobalIR.evaluate program store evalFuel environment
      (PolyIR.erase left) = .ok (.int x))
    (rightEvaluates : GlobalIR.evaluate program store evalFuel environment
      (PolyIR.erase right) = .ok (.int y)) :
    ∃ expression,
      readClosedInitializer entries visible forbidden decodeFuel node = some expression ∧
      GlobalIR.evaluate program store (evalFuel + 1) environment (PolyIR.erase expression) =
        .ok (.int (x + y)) ∧ PolyIR.ValueTyped globals (.int (x + y)) .integer ∧
      GlobalProgramEntry.ArithmeticSurfaceExpr expression .integer ∧
      Surface.HasType globals 0 [] expression .integer := by
  refine ⟨.add left right, decoded, ?_, .int, .add leftArithmetic rightArithmetic,
    GlobalProgramEntry.ArithmeticSurfaceExpr.hasType (.add leftArithmetic rightArithmetic)⟩
  simpa [PolyIR.erase] using GlobalIR.evaluate_add_of_children program store environment
    evalFuel (PolyIR.erase left) (PolyIR.erase right) x y leftEvaluates rightEvaluates

theorem readClosedInitializer_sub_evaluates
    (entries visible : List GlobalProgramEntry.Entry) (forbidden : List Nat)
    (decodeFuel evalFuel : Nat) (node : CBindingWalk.Node)
    (left right : Surface.Expr) (program : List GlobalIR.Definition)
    (store : GlobalIR.Store) (globals : List Surface.Signature)
    (environment : List PolyIR.Value) (x y : Int)
    (decoded : readClosedInitializer entries visible forbidden decodeFuel node =
      some (.sub left right))
    (leftArithmetic : GlobalProgramEntry.ArithmeticSurfaceExpr left .integer)
    (rightArithmetic : GlobalProgramEntry.ArithmeticSurfaceExpr right .integer)
    (leftEvaluates : GlobalIR.evaluate program store evalFuel environment
      (PolyIR.erase left) = .ok (.int x))
    (rightEvaluates : GlobalIR.evaluate program store evalFuel environment
      (PolyIR.erase right) = .ok (.int y)) :
    ∃ expression,
      readClosedInitializer entries visible forbidden decodeFuel node = some expression ∧
      GlobalIR.evaluate program store (evalFuel + 1) environment (PolyIR.erase expression) =
        .ok (.int (x - y)) ∧ PolyIR.ValueTyped globals (.int (x - y)) .integer ∧
      GlobalProgramEntry.ArithmeticSurfaceExpr expression .integer ∧
      Surface.HasType globals 0 [] expression .integer := by
  refine ⟨.sub left right, decoded, ?_, .int, .sub leftArithmetic rightArithmetic,
    GlobalProgramEntry.ArithmeticSurfaceExpr.hasType (.sub leftArithmetic rightArithmetic)⟩
  simpa [PolyIR.erase] using GlobalIR.evaluate_sub_of_children program store environment
    evalFuel (PolyIR.erase left) (PolyIR.erase right) x y leftEvaluates rightEvaluates

theorem readClosedInitializer_mul_evaluates
    (entries visible : List GlobalProgramEntry.Entry) (forbidden : List Nat)
    (decodeFuel evalFuel : Nat) (node : CBindingWalk.Node)
    (left right : Surface.Expr) (program : List GlobalIR.Definition)
    (store : GlobalIR.Store) (globals : List Surface.Signature)
    (environment : List PolyIR.Value) (x y : Int)
    (decoded : readClosedInitializer entries visible forbidden decodeFuel node =
      some (.mul left right))
    (leftArithmetic : GlobalProgramEntry.ArithmeticSurfaceExpr left .integer)
    (rightArithmetic : GlobalProgramEntry.ArithmeticSurfaceExpr right .integer)
    (leftEvaluates : GlobalIR.evaluate program store evalFuel environment
      (PolyIR.erase left) = .ok (.int x))
    (rightEvaluates : GlobalIR.evaluate program store evalFuel environment
      (PolyIR.erase right) = .ok (.int y)) :
    ∃ expression,
      readClosedInitializer entries visible forbidden decodeFuel node = some expression ∧
      GlobalIR.evaluate program store (evalFuel + 1) environment (PolyIR.erase expression) =
        .ok (.int (x * y)) ∧ PolyIR.ValueTyped globals (.int (x * y)) .integer ∧
      GlobalProgramEntry.ArithmeticSurfaceExpr expression .integer ∧
      Surface.HasType globals 0 [] expression .integer := by
  refine ⟨.mul left right, decoded, ?_, .int, .mul leftArithmetic rightArithmetic,
    GlobalProgramEntry.ArithmeticSurfaceExpr.hasType (.mul leftArithmetic rightArithmetic)⟩
  simpa [PolyIR.erase] using GlobalIR.evaluate_mul_of_children program store environment
    evalFuel (PolyIR.erase left) (PolyIR.erase right) x y leftEvaluates rightEvaluates

theorem readClosedInitializer_le_evaluates
    (entries visible : List GlobalProgramEntry.Entry) (forbidden : List Nat)
    (decodeFuel evalFuel : Nat) (node : CBindingWalk.Node)
    (left right : Surface.Expr) (program : List GlobalIR.Definition)
    (store : GlobalIR.Store) (globals : List Surface.Signature)
    (environment : List PolyIR.Value) (x y : Int)
    (decoded : readClosedInitializer entries visible forbidden decodeFuel node =
      some (.le left right))
    (leftArithmetic : GlobalProgramEntry.ArithmeticSurfaceExpr left .integer)
    (rightArithmetic : GlobalProgramEntry.ArithmeticSurfaceExpr right .integer)
    (leftEvaluates : GlobalIR.evaluate program store evalFuel environment
      (PolyIR.erase left) = .ok (.int x))
    (rightEvaluates : GlobalIR.evaluate program store evalFuel environment
      (PolyIR.erase right) = .ok (.int y)) :
    ∃ expression,
      readClosedInitializer entries visible forbidden decodeFuel node = some expression ∧
      GlobalIR.evaluate program store (evalFuel + 1) environment (PolyIR.erase expression) =
        .ok (.bool (decide (x ≤ y))) ∧
      PolyIR.ValueTyped globals (.bool (decide (x ≤ y))) .boolean ∧
      GlobalProgramEntry.ArithmeticSurfaceExpr expression .boolean ∧
      Surface.HasType globals 0 [] expression .boolean := by
  refine ⟨.le left right, decoded, ?_, .bool, .le leftArithmetic rightArithmetic,
    GlobalProgramEntry.ArithmeticSurfaceExpr.hasType (.le leftArithmetic rightArithmetic)⟩
  simpa [PolyIR.erase] using GlobalIR.evaluate_le_of_children program store environment
    evalFuel (PolyIR.erase left) (PolyIR.erase right) x y leftEvaluates rightEvaluates

theorem readClosedInitializer_intEq_evaluates
    (entries visible : List GlobalProgramEntry.Entry) (forbidden : List Nat)
    (decodeFuel evalFuel : Nat) (node : CBindingWalk.Node)
    (left right : Surface.Expr) (program : List GlobalIR.Definition)
    (store : GlobalIR.Store) (globals : List Surface.Signature)
    (environment : List PolyIR.Value) (x y : Int)
    (decoded : readClosedInitializer entries visible forbidden decodeFuel node =
      some (.intEq left right))
    (leftArithmetic : GlobalProgramEntry.ArithmeticSurfaceExpr left .integer)
    (rightArithmetic : GlobalProgramEntry.ArithmeticSurfaceExpr right .integer)
    (leftEvaluates : GlobalIR.evaluate program store evalFuel environment
      (PolyIR.erase left) = .ok (.int x))
    (rightEvaluates : GlobalIR.evaluate program store evalFuel environment
      (PolyIR.erase right) = .ok (.int y)) :
    ∃ expression,
      readClosedInitializer entries visible forbidden decodeFuel node = some expression ∧
      GlobalIR.evaluate program store (evalFuel + 1) environment (PolyIR.erase expression) =
        .ok (.bool (x == y)) ∧ PolyIR.ValueTyped globals (.bool (x == y)) .boolean ∧
      GlobalProgramEntry.ArithmeticSurfaceExpr expression .boolean ∧
      Surface.HasType globals 0 [] expression .boolean := by
  refine ⟨.intEq left right, decoded, ?_, .bool, .intEq leftArithmetic rightArithmetic,
    GlobalProgramEntry.ArithmeticSurfaceExpr.hasType (.intEq leftArithmetic rightArithmetic)⟩
  simpa [PolyIR.erase] using GlobalIR.evaluate_intEq_of_children program store environment
    evalFuel (PolyIR.erase left) (PolyIR.erase right) x y leftEvaluates rightEvaluates

/-- Once a float binary expression has been decoded, its typed child
evaluations determine the same result in GlobalIR and provide the result's
value typing evidence. -/
theorem readClosedInitializer_floatBin_evaluates
    (entries visible : List GlobalProgramEntry.Entry) (forbidden : List Nat)
    (decodeFuel evalFuel : Nat) (node : CBindingWalk.Node)
    (operation : Surface.FloatBinOp) (left right : Surface.Expr)
    (program : List GlobalIR.Definition) (store : GlobalIR.Store)
    (globals : List Surface.Signature) (environment : List PolyIR.Value)
    (x y : Float)
    (decoded : readClosedInitializer entries visible forbidden decodeFuel node =
      some (.floatBin operation left right))
    (leftArithmetic : GlobalProgramEntry.ArithmeticSurfaceExpr left .float)
    (rightArithmetic : GlobalProgramEntry.ArithmeticSurfaceExpr right .float)
    (leftEvaluates : GlobalIR.evaluate program store evalFuel environment
      (PolyIR.erase left) = .ok (.float x))
    (rightEvaluates : GlobalIR.evaluate program store evalFuel environment
      (PolyIR.erase right) = .ok (.float y)) :
    ∃ expression,
      readClosedInitializer entries visible forbidden decodeFuel node = some expression ∧
      GlobalIR.evaluate program store (evalFuel + 1) environment (PolyIR.erase expression) =
        .ok (.float (floatBinValue operation x y)) ∧
      PolyIR.ValueTyped globals (.float (floatBinValue operation x y)) .float ∧
      GlobalProgramEntry.ArithmeticSurfaceExpr expression .float ∧
      Surface.HasType globals 0 [] expression .float := by
  have result := GlobalIR.evaluate_floatBin_typed_of_children globals program store
    environment evalFuel operation (PolyIR.erase left) (PolyIR.erase right) x y
    leftEvaluates rightEvaluates
  refine ⟨.floatBin operation left right, decoded, ?_, ?_,
    .floatBin leftArithmetic rightArithmetic,
    GlobalProgramEntry.ArithmeticSurfaceExpr.hasType (.floatBin leftArithmetic rightArithmetic)⟩
  · simpa [PolyIR.erase] using result.1
  · exact result.2

/-- A decoded Float builtin application with evaluated Float operands can be
inserted into a typed mixed-declaration initializer row. This composes the C
binding identity, source decoding, GlobalIR evaluation, and row invariants. -/
theorem readClosedInitializer_floatBin_builds_typed_row
    (entries visible : List GlobalProgramEntry.Entry) (forbidden : List Nat)
    (slotTypes : List Surface.Ty) (slot identity decodeFuel evalFuel selected : Nat)
    (operator : CMacroCopy.Atom) (leftNode rightNode : CBindingWalk.Node)
    (operation : Surface.FloatBinOp) (left right : Surface.Expr)
    (tail : List GlobalProgramEntry.Entry)
    (typedTail : GlobalProgramEntry.TypedInitializerRows entries slotTypes (slot + 1) tail)
    (arithmeticTail : GlobalProgramEntry.ArithmeticInitializerRows slotTypes (slot + 1) tail)
    (slotType : slotTypes.get? slot = some .float)
    (valid : Surface.Ty.float.wellFormed 0)
    (builtin : (selected = 39 ∧ operator.name = "float+" ∧ operation = .add) ∨
      (selected = 42 ∧ operator.name = "float-" ∧ operation = .sub) ∨
      (selected = 45 ∧ operator.name = "float*" ∧ operation = .mul) ∨
      (selected = 48 ∧ operator.name = "float/" ∧ operation = .div))
    (notForbidden : selected ∉ forbidden)
    (leftDecoded : readClosedInitializer entries visible forbidden decodeFuel leftNode = some left)
    (rightDecoded : readClosedInitializer entries visible forbidden decodeFuel rightNode = some right)
    (leftArithmetic : GlobalProgramEntry.ArithmeticSurfaceExpr left .float)
    (rightArithmetic : GlobalProgramEntry.ArithmeticSurfaceExpr right .float)
    (globals : List Surface.Signature)
    (globalsAgree : GlobalProgramEntry.signatures entries = globals)
    (program : List GlobalIR.Definition) (store : GlobalIR.Store)
    (environment : List PolyIR.Value) (x y : Float)
    (leftEvaluates : GlobalIR.evaluate program store evalFuel environment
      (PolyIR.erase left) = .ok (.float x))
    (rightEvaluates : GlobalIR.evaluate program store evalFuel environment
      (PolyIR.erase right) = .ok (.float y)) :
    ∃ expression,
      readClosedInitializer entries visible forbidden (decodeFuel + 1)
        (.list [.atom operator selected, leftNode, rightNode]) = some expression ∧
      GlobalProgramEntry.TypedInitializerRows entries slotTypes slot
        (.value identity .float valid expression :: tail) ∧
      GlobalProgramEntry.ArithmeticInitializerRows slotTypes slot
        (.value identity .float valid expression :: tail) ∧
      GlobalIR.evaluate program store (evalFuel + 1) environment (PolyIR.erase expression) =
        .ok (.float (floatBinValue operation x y)) := by
  have decoded := readClosedInitializer_floatBin entries visible forbidden decodeFuel selected
    operator leftNode rightNode operation left right builtin notForbidden
    leftDecoded rightDecoded
  obtain ⟨expression, sourceDecoded, evaluated, _valueTyped, arithmetic, _typing⟩ :=
    readClosedInitializer_floatBin_evaluates entries visible forbidden (decodeFuel + 1) evalFuel
      (.list [.atom operator selected, leftNode, rightNode]) operation left right program store
      globals environment x y decoded leftArithmetic rightArithmetic leftEvaluates rightEvaluates
  have row := arithmeticInitializerRow_of_evaluation entries slotTypes slot identity .float
    valid expression tail typedTail arithmeticTail slotType arithmetic globals globalsAgree
    program store (evalFuel + 1) environment (.float (floatBinValue operation x y)) evaluated
  rcases row with ⟨checked, checkedExact, typedRows, arithmeticRows, rowEvaluated⟩
  have typedRows' : GlobalProgramEntry.TypedInitializerRows entries slotTypes slot
      (.value identity .float valid expression :: tail) := by
    simpa [checkedExact] using typedRows
  have arithmeticRows' : GlobalProgramEntry.ArithmeticInitializerRows slotTypes slot
      (.value identity .float valid expression :: tail) := by
    simpa [checkedExact] using arithmeticRows
  exact ⟨expression, sourceDecoded, typedRows', arithmeticRows', rowEvaluated⟩

/-- A decoded Float builtin initializer in the first value slot, followed by
typed rows, gives a well-typed store after the actual generated GlobalIR
initializer program runs successfully. -/
theorem readClosedInitializer_floatBin_initialization_preserves_store
    (entries visible : List GlobalProgramEntry.Entry) (forbidden : List Nat)
    (slotTypes : List Surface.Ty) (identity decodeFuel initFuel entryIndex selected : Nat)
    (operator : CMacroCopy.Atom) (leftNode rightNode : CBindingWalk.Node)
    (operation : Surface.FloatBinOp) (left right : Surface.Expr)
    (tail : List GlobalProgramEntry.Entry)
    (typedTail : GlobalProgramEntry.TypedInitializerRows entries slotTypes 1 tail)
    (arithmeticTail : GlobalProgramEntry.ArithmeticInitializerRows slotTypes 1 tail)
    (slotType : slotTypes.get? 0 = some .float)
    (valid : Surface.Ty.float.wellFormed 0)
    (builtin : (selected = 39 ∧ operator.name = "float+" ∧ operation = .add) ∨
      (selected = 42 ∧ operator.name = "float-" ∧ operation = .sub) ∨
      (selected = 45 ∧ operator.name = "float*" ∧ operation = .mul) ∨
      (selected = 48 ∧ operator.name = "float/" ∧ operation = .div))
    (notForbidden : selected ∉ forbidden)
    (leftDecoded : readClosedInitializer entries visible forbidden decodeFuel leftNode = some left)
    (rightDecoded : readClosedInitializer entries visible forbidden decodeFuel rightNode = some right)
    (leftArithmetic : GlobalProgramEntry.ArithmeticSurfaceExpr left .float)
    (rightArithmetic : GlobalProgramEntry.ArithmeticSurfaceExpr right .float)
    (globals : List Surface.Signature)
    (globalsAgree : GlobalProgramEntry.signatures entries = globals)
    (result : GlobalIR.Store)
    (initialization : GlobalIR.initializeValues
      (GlobalProgramEntry.toRuntimeProgram
        (.value identity .float valid (.floatBin operation left right) :: tail) entryIndex).definitions
      initFuel
      (List.replicate
        (GlobalProgramEntry.toRuntimeProgram
          (.value identity .float valid (.floatBin operation left right) :: tail) entryIndex).initializers.length
        none)
      0
      (GlobalProgramEntry.toRuntimeProgram
        (.value identity .float valid (.floatBin operation left right) :: tail) entryIndex).initializers =
      .ok result) :
    readClosedInitializer entries visible forbidden (decodeFuel + 1)
      (.list [.atom operator selected, leftNode, rightNode]) =
        some (.floatBin operation left right) ∧
      GlobalIR.StoreWellTyped globals slotTypes result := by
  have decoded := readClosedInitializer_floatBin entries visible forbidden decodeFuel selected
    operator leftNode rightNode operation left right builtin notForbidden leftDecoded rightDecoded
  have arithmetic : GlobalProgramEntry.ArithmeticSurfaceExpr
      (.floatBin operation left right) .float := .floatBin leftArithmetic rightArithmetic
  have typing : Surface.HasType globals 0 [] (.floatBin operation left right) .float :=
    GlobalProgramEntry.ArithmeticSurfaceExpr.hasType arithmetic
  have sourceTyping : Surface.HasType (GlobalProgramEntry.signatures entries) 0 []
      (.floatBin operation left right) .float := by
    rw [globalsAgree]
    exact typing
  let checked : GlobalProgramEntry.TypedInitializer entries .float
      (.floatBin operation left right) :=
    ⟨.floatBin operation left right, sourceTyping, .floatBin operation (PolyIR.erase left)
      (PolyIR.erase right), by simp [PolyIR.erase], rfl⟩
  have typedRows := GlobalProgramEntry.TypedInitializerRows.value_of_checked_initializer
    entries slotTypes 0 identity .float valid (.floatBin operation left right) tail typedTail
    slotType checked
  have arithmeticRows : GlobalProgramEntry.ArithmeticInitializerRows slotTypes 0
      (.value identity .float valid (.floatBin operation left right) :: tail) :=
    ⟨slotType, arithmetic, arithmeticTail⟩
  have storeTyped := GlobalProgramEntry.TypedInitializerRows.initialization_preserves_store_arithmetic
    entries globals slotTypes
    (GlobalProgramEntry.toRuntimeProgram
      (.value identity .float valid (.floatBin operation left right) :: tail) entryIndex).definitions
    initFuel (.value identity .float valid (.floatBin operation left right) :: tail) result
    typedRows arithmeticRows initialization
  exact ⟨decoded, storeTyped⟩

/-- Compose annotated-node Float builtin decoding with the Surface/GlobalIR
wrong-shape correspondence, retaining the explicit child-evaluation
simulation premises. -/
theorem readClosedInitializer_floatBin_wrong_shape_fault_corresponds_to_globalIR
    (entries visible : List GlobalProgramEntry.Entry) (forbidden : List Nat)
    (decodeFuel fuel selected : Nat) (operator : CMacroCopy.Atom)
    (leftNode rightNode : CBindingWalk.Node) (operation : Surface.FloatBinOp)
    (left right : Surface.Expr) (sourceProgram : Surface.Definitions)
    (runtimeProgram : List GlobalIR.Definition) (store : GlobalIR.Store)
    (environment : List Surface.Value) (leftValue rightValue : Surface.Value)
    (builtin : (selected = 39 ∧ operator.name = "float+" ∧ operation = .add) ∨
      (selected = 42 ∧ operator.name = "float-" ∧ operation = .sub) ∨
      (selected = 45 ∧ operator.name = "float*" ∧ operation = .mul) ∨
      (selected = 48 ∧ operator.name = "float/" ∧ operation = .div))
    (notForbidden : selected ∉ forbidden)
    (leftDecoded : readClosedInitializer entries visible forbidden decodeFuel leftNode = some left)
    (rightDecoded : readClosedInitializer entries visible forbidden decodeFuel rightNode = some right)
    (sourceLeft : Surface.evaluate sourceProgram fuel environment left = .ok leftValue)
    (sourceRight : Surface.evaluate sourceProgram fuel environment right = .ok rightValue)
    (runtimeLeft : GlobalIR.evaluate runtimeProgram store fuel (PolyIR.eraseValues environment)
      (PolyIR.erase left) = .ok (PolyIR.eraseValue leftValue))
    (runtimeRight : GlobalIR.evaluate runtimeProgram store fuel (PolyIR.eraseValues environment)
      (PolyIR.erase right) = .ok (PolyIR.eraseValue rightValue))
    (notBothFloats : ¬ ∃ x y, leftValue = .float x ∧ rightValue = .float y) :
    readClosedInitializer entries visible forbidden (decodeFuel + 1)
      (.list [.atom operator selected, leftNode, rightNode]) =
        some (.floatBin operation left right) ∧
      (Surface.evaluate sourceProgram (fuel + 1) environment
          (.floatBin operation left right) = .error .wrongShape ↔
        GlobalIR.evaluate runtimeProgram store (fuel + 1) (PolyIR.eraseValues environment)
          (.floatBin operation (PolyIR.erase left) (PolyIR.erase right)) =
            .error (.core .wrongShape)) := by
  have decoded := readClosedInitializer_floatBin entries visible forbidden decodeFuel selected
    operator leftNode rightNode operation left right builtin notForbidden leftDecoded rightDecoded
  exact ⟨decoded,
    NLisp.floatBin_wrong_shape_fault_corresponds_to_globalIR sourceProgram runtimeProgram store
      fuel environment operation left right leftValue rightValue sourceLeft sourceRight
      runtimeLeft runtimeRight notBothFloats⟩

/-- A decoded conditional initializer preserves the selected branch's value,
type, and arithmetic-fragment certificate when its condition evaluates true. -/
theorem readClosedInitializer_if_true_evaluates
    (entries visible : List GlobalProgramEntry.Entry) (forbidden : List Nat)
    (decodeFuel evalFuel : Nat) (node : CBindingWalk.Node)
    (condition yes no : Surface.Expr) (resultType : Surface.Ty)
    (program : List GlobalIR.Definition) (store : GlobalIR.Store)
    (globals : List Surface.Signature) (environment : List PolyIR.Value)
    (value : PolyIR.Value)
    (decoded : readClosedInitializer entries visible forbidden decodeFuel node =
      some (.ite condition yes no))
    (conditionArithmetic : GlobalProgramEntry.ArithmeticSurfaceExpr condition .boolean)
    (yesArithmetic : GlobalProgramEntry.ArithmeticSurfaceExpr yes resultType)
    (noArithmetic : GlobalProgramEntry.ArithmeticSurfaceExpr no resultType)
    (conditionEvaluates : GlobalIR.evaluate program store evalFuel environment
      (PolyIR.erase condition) = .ok (.bool true))
    (yesEvaluates : GlobalIR.evaluate program store evalFuel environment
      (PolyIR.erase yes) = .ok value)
    (valueTyped : PolyIR.ValueTyped globals value resultType) :
    ∃ expression,
      readClosedInitializer entries visible forbidden decodeFuel node = some expression ∧
      GlobalIR.evaluate program store (evalFuel + 1) environment
        (PolyIR.erase expression) = .ok value ∧
      PolyIR.ValueTyped globals value resultType ∧
      GlobalProgramEntry.ArithmeticSurfaceExpr expression resultType ∧
      Surface.HasType globals 0 [] expression resultType := by
  refine ⟨.ite condition yes no, decoded, ?_, valueTyped,
    .ite conditionArithmetic yesArithmetic noArithmetic,
    GlobalProgramEntry.ArithmeticSurfaceExpr.hasType
      (.ite conditionArithmetic yesArithmetic noArithmetic)⟩
  simpa [PolyIR.erase, GlobalIR.evaluate, conditionEvaluates, yesEvaluates,
    bind, Except.bind, Except.pure]

theorem readClosedInitializer_if_false_evaluates
    (entries visible : List GlobalProgramEntry.Entry) (forbidden : List Nat)
    (decodeFuel evalFuel : Nat) (node : CBindingWalk.Node)
    (condition yes no : Surface.Expr) (resultType : Surface.Ty)
    (program : List GlobalIR.Definition) (store : GlobalIR.Store)
    (globals : List Surface.Signature) (environment : List PolyIR.Value)
    (value : PolyIR.Value)
    (decoded : readClosedInitializer entries visible forbidden decodeFuel node =
      some (.ite condition yes no))
    (conditionArithmetic : GlobalProgramEntry.ArithmeticSurfaceExpr condition .boolean)
    (yesArithmetic : GlobalProgramEntry.ArithmeticSurfaceExpr yes resultType)
    (noArithmetic : GlobalProgramEntry.ArithmeticSurfaceExpr no resultType)
    (conditionEvaluates : GlobalIR.evaluate program store evalFuel environment
      (PolyIR.erase condition) = .ok (.bool false))
    (noEvaluates : GlobalIR.evaluate program store evalFuel environment
      (PolyIR.erase no) = .ok value)
    (valueTyped : PolyIR.ValueTyped globals value resultType) :
    ∃ expression,
      readClosedInitializer entries visible forbidden decodeFuel node = some expression ∧
      GlobalIR.evaluate program store (evalFuel + 1) environment
        (PolyIR.erase expression) = .ok value ∧
      PolyIR.ValueTyped globals value resultType ∧
      GlobalProgramEntry.ArithmeticSurfaceExpr expression resultType ∧
      Surface.HasType globals 0 [] expression resultType := by
  refine ⟨.ite condition yes no, decoded, ?_, valueTyped,
    .ite conditionArithmetic yesArithmetic noArithmetic,
    GlobalProgramEntry.ArithmeticSurfaceExpr.hasType
      (.ite conditionArithmetic yesArithmetic noArithmetic)⟩
  simpa [PolyIR.erase, GlobalIR.evaluate, conditionEvaluates, noEvaluates,
    bind, Except.bind, Except.pure]

/-- The true-branch evaluation theorem feeds directly into the checked mixed
initializer row used by `GlobalProgramEntry`'s sequential store proof. -/
theorem readClosedInitializer_if_true_builds_typed_row
    (entries : List GlobalProgramEntry.Entry) (slotTypes : List Surface.Ty)
    (slot identity : Nat) (type : Surface.Ty) (valid : type.wellFormed 0)
    (tail : List GlobalProgramEntry.Entry)
    (rest : GlobalProgramEntry.TypedInitializerRows entries slotTypes (slot + 1) tail)
    (arithmeticTail : GlobalProgramEntry.ArithmeticInitializerRows slotTypes (slot + 1) tail)
    (slotType : slotTypes.get? slot = some type)
    (visible : List GlobalProgramEntry.Entry) (forbidden : List Nat)
    (decodeFuel evalFuel : Nat) (node : CBindingWalk.Node)
    (condition yes no : Surface.Expr) (program : List GlobalIR.Definition)
    (store : GlobalIR.Store) (globals : List Surface.Signature)
    (globalsAgree : GlobalProgramEntry.signatures entries = globals)
    (environment : List PolyIR.Value) (value : PolyIR.Value)
    (decoded : readClosedInitializer entries visible forbidden decodeFuel node =
      some (.ite condition yes no))
    (conditionArithmetic : GlobalProgramEntry.ArithmeticSurfaceExpr condition .boolean)
    (yesArithmetic : GlobalProgramEntry.ArithmeticSurfaceExpr yes type)
    (noArithmetic : GlobalProgramEntry.ArithmeticSurfaceExpr no type)
    (conditionEvaluates : GlobalIR.evaluate program store evalFuel environment
      (PolyIR.erase condition) = .ok (.bool true))
    (yesEvaluates : GlobalIR.evaluate program store evalFuel environment
      (PolyIR.erase yes) = .ok value)
    (valueTyped : PolyIR.ValueTyped globals value type) :
    ∃ checked : GlobalProgramEntry.TypedInitializer entries type (.ite condition yes no),
      checked.expression = .ite condition yes no ∧
      GlobalProgramEntry.TypedInitializerRows entries slotTypes slot
        (.value identity type valid checked.expression :: tail) ∧
      GlobalProgramEntry.ArithmeticInitializerRows slotTypes slot
        (.value identity type valid checked.expression :: tail) ∧
      GlobalIR.evaluate program store (evalFuel + 1) environment
        (PolyIR.erase checked.expression) = .ok value := by
  obtain ⟨expression, decodedExpression, evaluated, _valueType, arithmetic, _typing⟩ :=
    readClosedInitializer_if_true_evaluates entries visible forbidden decodeFuel evalFuel node
      condition yes no type program store globals environment value decoded
      conditionArithmetic yesArithmetic noArithmetic conditionEvaluates yesEvaluates valueTyped
  have expressionExact : expression = .ite condition yes no :=
    Option.some.inj (decodedExpression.symm.trans decoded)
  subst expression
  obtain ⟨checked, exactExpression, typedRows, arithmeticRows, checkedEvaluation⟩ :=
    arithmeticInitializerRow_of_evaluation entries slotTypes slot identity type valid
      (.ite condition yes no) tail rest arithmeticTail slotType
      (.ite conditionArithmetic yesArithmetic noArithmetic) globals globalsAgree
      program store (evalFuel + 1) environment value evaluated
  exact ⟨checked, exactExpression, typedRows, arithmeticRows, by
    simpa [exactExpression] using checkedEvaluation⟩

/-- The false-branch case produces the same row evidence for sequential
initialization, using the selected `no` initializer evaluation. -/
theorem readClosedInitializer_if_false_builds_typed_row
    (entries : List GlobalProgramEntry.Entry) (slotTypes : List Surface.Ty)
    (slot identity : Nat) (type : Surface.Ty) (valid : type.wellFormed 0)
    (tail : List GlobalProgramEntry.Entry)
    (rest : GlobalProgramEntry.TypedInitializerRows entries slotTypes (slot + 1) tail)
    (arithmeticTail : GlobalProgramEntry.ArithmeticInitializerRows slotTypes (slot + 1) tail)
    (slotType : slotTypes.get? slot = some type)
    (visible : List GlobalProgramEntry.Entry) (forbidden : List Nat)
    (decodeFuel evalFuel : Nat) (node : CBindingWalk.Node)
    (condition yes no : Surface.Expr) (program : List GlobalIR.Definition)
    (store : GlobalIR.Store) (globals : List Surface.Signature)
    (globalsAgree : GlobalProgramEntry.signatures entries = globals)
    (environment : List PolyIR.Value) (value : PolyIR.Value)
    (decoded : readClosedInitializer entries visible forbidden decodeFuel node =
      some (.ite condition yes no))
    (conditionArithmetic : GlobalProgramEntry.ArithmeticSurfaceExpr condition .boolean)
    (yesArithmetic : GlobalProgramEntry.ArithmeticSurfaceExpr yes type)
    (noArithmetic : GlobalProgramEntry.ArithmeticSurfaceExpr no type)
    (conditionEvaluates : GlobalIR.evaluate program store evalFuel environment
      (PolyIR.erase condition) = .ok (.bool false))
    (noEvaluates : GlobalIR.evaluate program store evalFuel environment
      (PolyIR.erase no) = .ok value)
    (valueTyped : PolyIR.ValueTyped globals value type) :
    ∃ checked : GlobalProgramEntry.TypedInitializer entries type (.ite condition yes no),
      checked.expression = .ite condition yes no ∧
      GlobalProgramEntry.TypedInitializerRows entries slotTypes slot
        (.value identity type valid checked.expression :: tail) ∧
      GlobalProgramEntry.ArithmeticInitializerRows slotTypes slot
        (.value identity type valid checked.expression :: tail) ∧
      GlobalIR.evaluate program store (evalFuel + 1) environment
        (PolyIR.erase checked.expression) = .ok value := by
  obtain ⟨expression, decodedExpression, evaluated, _valueType, arithmetic, _typing⟩ :=
    readClosedInitializer_if_false_evaluates entries visible forbidden decodeFuel evalFuel node
      condition yes no type program store globals environment value decoded
      conditionArithmetic yesArithmetic noArithmetic conditionEvaluates noEvaluates valueTyped
  have expressionExact : expression = .ite condition yes no :=
    Option.some.inj (decodedExpression.symm.trans decoded)
  subst expression
  obtain ⟨checked, exactExpression, typedRows, arithmeticRows, checkedEvaluation⟩ :=
    arithmeticInitializerRow_of_evaluation entries slotTypes slot identity type valid
      (.ite condition yes no) tail rest arithmeticTail slotType
      (.ite conditionArithmetic yesArithmetic noArithmetic) globals globalsAgree
      program store (evalFuel + 1) environment value evaluated
  exact ⟨checked, exactExpression, typedRows, arithmeticRows, by
    simpa [exactExpression] using checkedEvaluation⟩

/-- Execute a true-branch conditional value initializer in the actual generated
GlobalIR program. The successful run and the typed mixed row together preserve
the slot store invariant. -/
theorem readClosedInitializer_if_true_initializes_store_typed
    (entries : List GlobalProgramEntry.Entry) (slotTypes : List Surface.Ty)
    (identity initFuel entryIndex : Nat) (type : Surface.Ty)
    (valid : type.wellFormed 0) (tail : List GlobalProgramEntry.Entry)
    (typedTail : GlobalProgramEntry.TypedInitializerRows entries slotTypes 1 tail)
    (arithmeticTail : GlobalProgramEntry.ArithmeticInitializerRows slotTypes 1 tail)
    (slotType : slotTypes.get? 0 = some type)
    (visible : List GlobalProgramEntry.Entry) (forbidden : List Nat)
    (decodeFuel : Nat) (node : CBindingWalk.Node)
    (condition yes no : Surface.Expr) (program : List GlobalIR.Definition)
    (globals : List Surface.Signature)
    (globalsAgree : GlobalProgramEntry.signatures entries = globals)
    (environment : List PolyIR.Value) (value : PolyIR.Value)
    (decoded : readClosedInitializer entries visible forbidden decodeFuel node =
      some (.ite condition yes no))
    (conditionArithmetic : GlobalProgramEntry.ArithmeticSurfaceExpr condition .boolean)
    (yesArithmetic : GlobalProgramEntry.ArithmeticSurfaceExpr yes type)
    (noArithmetic : GlobalProgramEntry.ArithmeticSurfaceExpr no type)
    (conditionEvaluates : GlobalIR.evaluate program
      (List.replicate (GlobalProgramEntry.initializerTerms
        (.value identity type valid (.ite condition yes no) :: tail)).length none)
      initFuel [] (PolyIR.erase condition) = .ok (.bool true))
    (yesEvaluates : GlobalIR.evaluate program
      (List.replicate (GlobalProgramEntry.initializerTerms
        (.value identity type valid (.ite condition yes no) :: tail)).length none)
      initFuel [] (PolyIR.erase yes) = .ok value)
    (valueTyped : PolyIR.ValueTyped globals value type)
    (result : GlobalIR.Store)
    (initialization : GlobalIR.initializeValues
      (GlobalProgramEntry.toRuntimeProgram
        (.value identity type valid (.ite condition yes no) :: tail) entryIndex).definitions
      (initFuel + 1)
      (List.replicate
        (GlobalProgramEntry.toRuntimeProgram
          (.value identity type valid (.ite condition yes no) :: tail) entryIndex).initializers.length none)
      0 (GlobalProgramEntry.toRuntimeProgram
        (.value identity type valid (.ite condition yes no) :: tail) entryIndex).initializers =
      .ok result) :
    GlobalIR.StoreWellTyped globals slotTypes result := by
  let sourceEntries : List GlobalProgramEntry.Entry :=
    .value identity type valid (.ite condition yes no) :: tail
  let initialStore : GlobalIR.Store :=
    List.replicate (GlobalProgramEntry.initializerTerms sourceEntries).length none
  obtain ⟨checked, expressionExact, typedRows, arithmeticRows, _evaluated⟩ :=
    readClosedInitializer_if_true_builds_typed_row entries slotTypes 0 identity type valid
      tail typedTail arithmeticTail slotType visible forbidden decodeFuel initFuel node
      condition yes no program initialStore globals globalsAgree [] value
      (by simpa [sourceEntries] using decoded)
      conditionArithmetic yesArithmetic noArithmetic
      (by simpa [sourceEntries, initialStore, GlobalProgramEntry.initializerTerms] using conditionEvaluates)
      (by simpa [sourceEntries, initialStore, GlobalProgramEntry.initializerTerms] using yesEvaluates)
      valueTyped
  have checkedInitializer : checked.expression = .ite condition yes no := expressionExact
  have initializedRows : GlobalIR.initializeValues
      (GlobalProgramEntry.toRuntimeProgram
        (.value identity type valid checked.expression :: tail) entryIndex).definitions (initFuel + 1)
      (List.replicate
        (GlobalProgramEntry.toRuntimeProgram
          (.value identity type valid checked.expression :: tail) entryIndex).initializers.length none)
      0 (GlobalProgramEntry.toRuntimeProgram
        (.value identity type valid checked.expression :: tail) entryIndex).initializers =
      .ok result := by
    simpa [GlobalProgramEntry.toRuntimeProgram, checkedInitializer] using initialization
  exact GlobalProgramEntry.TypedInitializerRows.initialization_preserves_store_arithmetic
    entries globals slotTypes
    (GlobalProgramEntry.toRuntimeProgram
      (.value identity type valid checked.expression :: tail) entryIndex).definitions
    (initFuel + 1) (.value identity type valid checked.expression :: tail) result
    typedRows arithmeticRows initializedRows

/-- The false branch of a conditional initializer also preserves the slot
store invariant through successful execution of the generated initializer. -/
theorem readClosedInitializer_if_false_initializes_store_typed
    (entries : List GlobalProgramEntry.Entry) (slotTypes : List Surface.Ty)
    (identity initFuel entryIndex : Nat) (type : Surface.Ty)
    (valid : type.wellFormed 0) (tail : List GlobalProgramEntry.Entry)
    (typedTail : GlobalProgramEntry.TypedInitializerRows entries slotTypes 1 tail)
    (arithmeticTail : GlobalProgramEntry.ArithmeticInitializerRows slotTypes 1 tail)
    (slotType : slotTypes.get? 0 = some type)
    (visible : List GlobalProgramEntry.Entry) (forbidden : List Nat)
    (decodeFuel : Nat) (node : CBindingWalk.Node)
    (condition yes no : Surface.Expr) (program : List GlobalIR.Definition)
    (globals : List Surface.Signature)
    (globalsAgree : GlobalProgramEntry.signatures entries = globals)
    (value : PolyIR.Value)
    (decoded : readClosedInitializer entries visible forbidden decodeFuel node =
      some (.ite condition yes no))
    (conditionArithmetic : GlobalProgramEntry.ArithmeticSurfaceExpr condition .boolean)
    (yesArithmetic : GlobalProgramEntry.ArithmeticSurfaceExpr yes type)
    (noArithmetic : GlobalProgramEntry.ArithmeticSurfaceExpr no type)
    (conditionEvaluates : GlobalIR.evaluate program
      (List.replicate (GlobalProgramEntry.initializerTerms
        (.value identity type valid (.ite condition yes no) :: tail)).length none)
      initFuel [] (PolyIR.erase condition) = .ok (.bool false))
    (noEvaluates : GlobalIR.evaluate program
      (List.replicate (GlobalProgramEntry.initializerTerms
        (.value identity type valid (.ite condition yes no) :: tail)).length none)
      initFuel [] (PolyIR.erase no) = .ok value)
    (valueTyped : PolyIR.ValueTyped globals value type)
    (result : GlobalIR.Store)
    (initialization : GlobalIR.initializeValues
      (GlobalProgramEntry.toRuntimeProgram
        (.value identity type valid (.ite condition yes no) :: tail) entryIndex).definitions
      (initFuel + 1)
      (List.replicate
        (GlobalProgramEntry.toRuntimeProgram
          (.value identity type valid (.ite condition yes no) :: tail) entryIndex).initializers.length none)
      0 (GlobalProgramEntry.toRuntimeProgram
        (.value identity type valid (.ite condition yes no) :: tail) entryIndex).initializers =
      .ok result) :
    GlobalIR.StoreWellTyped globals slotTypes result := by
  let sourceEntries : List GlobalProgramEntry.Entry :=
    .value identity type valid (.ite condition yes no) :: tail
  let initialStore : GlobalIR.Store :=
    List.replicate (GlobalProgramEntry.initializerTerms sourceEntries).length none
  obtain ⟨checked, expressionExact, typedRows, arithmeticRows, _evaluated⟩ :=
    readClosedInitializer_if_false_builds_typed_row entries slotTypes 0 identity type valid
      tail typedTail arithmeticTail slotType visible forbidden decodeFuel initFuel node
      condition yes no program initialStore globals globalsAgree [] value
      (by simpa [sourceEntries] using decoded)
      conditionArithmetic yesArithmetic noArithmetic
      (by simpa [sourceEntries, initialStore, GlobalProgramEntry.initializerTerms] using conditionEvaluates)
      (by simpa [sourceEntries, initialStore, GlobalProgramEntry.initializerTerms] using noEvaluates)
      valueTyped
  have checkedInitializer : checked.expression = .ite condition yes no := expressionExact
  have initializedRows : GlobalIR.initializeValues
      (GlobalProgramEntry.toRuntimeProgram
        (.value identity type valid checked.expression :: tail) entryIndex).definitions (initFuel + 1)
      (List.replicate
        (GlobalProgramEntry.toRuntimeProgram
          (.value identity type valid checked.expression :: tail) entryIndex).initializers.length none)
      0 (GlobalProgramEntry.toRuntimeProgram
        (.value identity type valid checked.expression :: tail) entryIndex).initializers =
      .ok result := by
    simpa [GlobalProgramEntry.toRuntimeProgram, checkedInitializer] using initialization
  exact GlobalProgramEntry.TypedInitializerRows.initialization_preserves_store_arithmetic
    entries globals slotTypes
    (GlobalProgramEntry.toRuntimeProgram
      (.value identity type valid checked.expression :: tail) entryIndex).definitions
    (initFuel + 1) (.value identity type valid checked.expression :: tail) result
    typedRows arithmeticRows initializedRows

theorem readClosedInitializer_resolves_local_identity
    (entries visible : List GlobalProgramEntry.Entry) (forbidden : List Nat)
    (fuel selected : Nat) (atom : CMacroCopy.Atom)
    (selectedNonzero : selected ≠ 0)
    (forbiddenMember : selected ∈ forbidden) :
    readClosedInitializer entries visible forbidden (fuel + 1)
      (.atom atom selected) = some (.var (localPosition selected forbidden)) := by
  simp [readClosedInitializer, selectedNonzero, forbiddenMember]

theorem readClosedInitializer_globalFunction_reference
    (entries visible : List GlobalProgramEntry.Entry) (forbidden : List Nat)
    (fuel selected index : Nat) (atom : CMacroCopy.Atom)
    (selectedNonzero : selected ≠ 0) (notForbidden : selected ∉ forbidden)
    (visibleFunction : selected ∈ GlobalProgramEntry.functionIdentities visible)
    (resolved : visibleFunctionIndex entries visible selected = some index) :
    readClosedInitializer entries visible forbidden (fuel + 1)
      (.atom atom selected) = some (.global index []) := by
  simp [readClosedInitializer, selectedNonzero, notForbidden, visibleFunction, resolved]

theorem readClosedInitializer_globalReference_sound
    (entries visible : List GlobalProgramEntry.Entry) (forbidden : List Nat)
    (fuel selected index : Nat)
    (atom : CMacroCopy.Atom) (selectedNonzero : selected ≠ 0)
    (notFunction : selected ∉ GlobalProgramEntry.functionIdentities visible)
    (decoded : readClosedInitializer entries visible forbidden (fuel + 1)
      (.atom atom selected) = some (.app (.global index []) [])) :
    selected ∈ GlobalProgramEntry.valueIdentities visible ∧
    selected ∈ GlobalProgramEntry.valueIdentities entries ∧
    GlobalProgramEntry.globalIndexOf selected entries = some index ∧
    ∃ type denseSlot,
      (GlobalProgramEntry.compiledLayout 0 entries).get? index =
        some (⟨0, [], type⟩, Definition.getter denseSlot) := by
  have notForbidden : selected ∉ forbidden := by
    by_cases member : selected ∈ forbidden
    · simp [readClosedInitializer, selectedNonzero, member] at decoded
    · exact member
  have visibleMember : selected ∈ GlobalProgramEntry.valueIdentities visible := by
    by_cases member : selected ∈ GlobalProgramEntry.valueIdentities visible
    · exact member
    · simp [readClosedInitializer, selectedNonzero, notForbidden, member,
        notFunction] at decoded
  have entryMember : selected ∈ GlobalProgramEntry.valueIdentities entries := by
    by_cases member : selected ∈ GlobalProgramEntry.valueIdentities entries
    · exact member
    · simp [readClosedInitializer, selectedNonzero, notForbidden, visibleMember, member,
        notFunction] at decoded
  have uniqueCheck : GlobalProgramEntry.identitiesUniqueCheck entries = true := by
    by_cases accepted : GlobalProgramEntry.identitiesUniqueCheck entries = true
    · exact accepted
    · simp [readClosedInitializer, selectedNonzero, notForbidden, visibleMember, entryMember,
        notFunction, accepted] at decoded
  have globalFound : GlobalProgramEntry.globalIndexOf selected entries = some index := by
    cases lookup : GlobalProgramEntry.globalIndexOf selected entries with
    | none => simp [readClosedInitializer, selectedNonzero, notForbidden,
        visibleMember, entryMember, uniqueCheck, notFunction, lookup] at decoded
    | some actual =>
        have same : actual = index := by
          simpa [readClosedInitializer, selectedNonzero, notForbidden,
            visibleMember, entryMember, uniqueCheck, notFunction, lookup] using decoded
        simp [lookup, same]
  have unique := GlobalProgramEntry.identitiesUniqueCheck_sound entries uniqueCheck
  obtain ⟨type, actualIndex, denseSlot, actualGlobal, _slotFound, getterAt⟩ :=
    GlobalProgramEntry.valueIdentity_getter_at_globalIndex selected 0 entries unique entryMember
  have indicesSame : actualIndex = index := Option.some.inj (actualGlobal.symm.trans globalFound)
  subst actualIndex
  exact ⟨visibleMember, entryMember, globalFound, type, denseSlot, getterAt⟩

/- A decoded top-level value declaration. The primitive grammar above can
produce values in any well-formed closed type supported by GlobalIR. -/
structure ClosedValueDefinition where
  identity : Nat
  type : Surface.Ty
  typeValid : type.wellFormed 0
  expression : Surface.Expr

def ClosedValueDefinition.toGlobalProgramEntry (value : ClosedValueDefinition) :
    GlobalProgramEntry.Entry :=
  .value value.identity value.type value.typeValid value.expression

def matchesValueIdentityType (identity : Nat) (type : Surface.Ty)
    (entries : List GlobalProgramEntry.Entry) : Bool :=
  if GlobalProgramEntry.identitiesUniqueCheck entries then
    match GlobalProgramEntry.valueSlotOf identity 0 entries with
    | some slot => decide ((GlobalProgramEntry.valueTypes entries)[slot]? = some type)
    | none => false
  else false

theorem matchesValueIdentityType_true_unique (identity : Nat) (type : Surface.Ty)
    (entries : List GlobalProgramEntry.Entry)
    (accepted : matchesValueIdentityType identity type entries = true) :
    GlobalProgramEntry.identitiesUniqueCheck entries = true := by
  unfold matchesValueIdentityType at accepted
  by_cases unique : GlobalProgramEntry.identitiesUniqueCheck entries = true
  · exact unique
  · simp [unique] at accepted

def readClosedValueDefinition (fuel : Nat) (entries visible : List GlobalProgramEntry.Entry)
    (form : Node) :
    Option ClosedValueDefinition := do
  let (head, binding, typeNode, value) ← match form with
    | .list [head, .list [binding, type], value] => some (head, binding, type, value)
    | _ => none
  if name head != some "define" then none
  let identity ← binder binding
  let type ← readClosedType fuel typeNode
  let expression ← readClosedInitializer entries visible [] fuel value
  if matchesValueIdentityType identity type.val entries then
    pure ⟨identity, type.val, type.property, expression⟩
  else none

/- Reuse CBindingWalk's computed lexical environment at the declaration
position. This includes all function bindings and only prior value bindings. -/
def sourceVisibleIdentities (forms : List Node) (formIndex : Nat) : Option (List Nat) := do
  let globals ← CBindingWalk.globals forms CBindingWalk.builtinEnvironment
  let scopes ← CBindingWalk.definitionScopes forms globals
  let environment ← scopes[formIndex]?
  pure (environment.map CNameResolution.Entry.identity)

def sourceVisibleEntries (entries : List GlobalProgramEntry.Entry) (forms : List Node)
    (formIndex : Nat) : Option (List GlobalProgramEntry.Entry) := do
  let identities ← sourceVisibleIdentities forms formIndex
  pure (entries.filter fun declaration =>
    decide (declaration.bindingIdentity ∈ identities))

theorem sourceVisibleEntries_valueIdentities_subset (entries visible : List GlobalProgramEntry.Entry)
    (forms : List Node) (formIndex : Nat)
    (resolved : sourceVisibleEntries entries forms formIndex = some visible) :
    ∀ selected, selected ∈ GlobalProgramEntry.valueIdentities visible →
      selected ∈ GlobalProgramEntry.valueIdentities entries := by
  unfold sourceVisibleEntries at resolved
  cases idsFound : sourceVisibleIdentities forms formIndex with
  | none => simp [idsFound] at resolved
  | some visibleIds =>
      have visibleEq : visible = entries.filter (fun declaration =>
          decide (declaration.bindingIdentity ∈ visibleIds)) := by
        simpa [idsFound] using resolved.symm
      subst visible
      exact GlobalProgramEntry.valueIdentities_filter_subset entries
        (fun declaration => decide (declaration.bindingIdentity ∈ visibleIds))

theorem sourceVisibleEntries_functionIdentities_subset
    (entries visible : List GlobalProgramEntry.Entry) (forms : List Node)
    (formIndex : Nat)
    (resolved : sourceVisibleEntries entries forms formIndex = some visible) :
    ∀ selected, selected ∈ GlobalProgramEntry.functionIdentities visible →
      selected ∈ GlobalProgramEntry.functionIdentities entries := by
  unfold sourceVisibleEntries at resolved
  cases idsFound : sourceVisibleIdentities forms formIndex with
  | none => simp [idsFound] at resolved
  | some visibleIds =>
      have visibleEq : visible = entries.filter (fun declaration =>
          decide (declaration.bindingIdentity ∈ visibleIds)) := by
        simpa [idsFound] using resolved.symm
      subst visible
      exact GlobalProgramEntry.functionIdentities_filter_subset entries
        (fun declaration => decide (declaration.bindingIdentity ∈ visibleIds))

theorem sourceVisibleValue_notFunction (entries visible : List GlobalProgramEntry.Entry)
    (forms : List Node) (formIndex selected : Nat)
    (visibleResolved : sourceVisibleEntries entries forms formIndex = some visible)
    (uniqueCheck : GlobalProgramEntry.identitiesUniqueCheck entries = true)
    (valueMember : selected ∈ GlobalProgramEntry.valueIdentities visible) :
    selected ∉ GlobalProgramEntry.functionIdentities visible := by
  have valueEntries := sourceVisibleEntries_valueIdentities_subset entries visible forms
    formIndex visibleResolved selected valueMember
  have distinct := GlobalProgramEntry.identitiesUniqueCheck_sound entries uniqueCheck
  have notFunctionEntries := GlobalProgramEntry.value_function_identity_disjoint entries selected
    distinct valueEntries
  intro functionMember
  exact notFunctionEntries
    (sourceVisibleEntries_functionIdentities_subset entries visible forms formIndex
      visibleResolved selected functionMember)

theorem readClosedInitializer_sourceVisibleFunctionReference_sound
    (entries visible : List GlobalProgramEntry.Entry) (forms : List Node) (forbidden : List Nat)
    (formIndex fuel selected : Nat) (atom : CMacroCopy.Atom)
    (selectedNonzero : selected ≠ 0) (notForbidden : selected ∉ forbidden)
    (visibleResolved : sourceVisibleEntries entries forms formIndex = some visible)
    (uniqueCheck : GlobalProgramEntry.identitiesUniqueCheck entries = true)
    (functionMember : selected ∈ GlobalProgramEntry.functionIdentities visible) :
    ∃ index signature definition,
      readClosedInitializer entries visible forbidden (fuel + 1) (.atom atom selected) =
        some (.global index []) ∧
      (GlobalProgramEntry.compiledLayout 0 entries).get? index =
        some (signature, GlobalIR.Definition.function definition) := by
  have entryMember := sourceVisibleEntries_functionIdentities_subset entries visible forms
    formIndex visibleResolved selected functionMember
  have distinct := GlobalProgramEntry.identitiesUniqueCheck_sound entries uniqueCheck
  obtain ⟨signature, definition, index, globalFound, layoutFound⟩ :=
    GlobalProgramEntry.functionIdentity_function_at_globalIndex selected 0 entries
      distinct entryMember
  have resolved : visibleFunctionIndex entries visible selected = some index := by
    unfold visibleFunctionIndex
    simp [functionMember, entryMember, uniqueCheck, globalFound]
  have decoded := readClosedInitializer_globalFunction_reference entries visible forbidden
    fuel selected index atom selectedNonzero notForbidden functionMember resolved
  exact ⟨index, signature, definition, decoded, layoutFound⟩

/-- A source-visible function name decodes to the same mixed-table index that
the compiled GlobalIR program uses. Evaluating the erased reference returns
that global value, so source resolution and runtime indexing agree for this
reference case even when value getters are interleaved in the entry table. -/
theorem readClosedInitializer_sourceVisibleFunctionReference_runtime_evaluates
    (entries visible : List GlobalProgramEntry.Entry) (forms : List Node)
    (forbidden : List Nat) (formIndex fuel selected : Nat) (atom : CMacroCopy.Atom)
    (selectedNonzero : selected ≠ 0) (notForbidden : selected ∉ forbidden)
    (visibleResolved : sourceVisibleEntries entries forms formIndex = some visible)
    (uniqueCheck : GlobalProgramEntry.identitiesUniqueCheck entries = true)
    (functionMember : selected ∈ GlobalProgramEntry.functionIdentities visible)
    (program : GlobalIR.Program) (store : GlobalIR.Store)
    (programDefinitions : program.definitions = GlobalProgramEntry.toDefinitions 0 entries) :
    ∃ index signature definition,
      readClosedInitializer entries visible forbidden (fuel + 1) (.atom atom selected) =
        some (.global index []) ∧
      (GlobalProgramEntry.compiledLayout 0 entries).get? index =
        some (signature, GlobalIR.Definition.function definition) ∧
      program.definitions[index]? = some (.function definition) ∧
      GlobalIR.evaluate program.definitions store (fuel + 1) []
        (PolyIR.erase (.global index [])) = .ok (.global index) := by
  obtain ⟨index, signature, definition, decoded, layout⟩ :=
    readClosedInitializer_sourceVisibleFunctionReference_sound entries visible forms forbidden
      formIndex fuel selected atom selectedNonzero notForbidden visibleResolved uniqueCheck
      functionMember
  have runtimeLookup := GlobalProgramEntry.toDefinitions_function_of_layout
    0 entries index signature definition layout
  have runtimeFound : (program.definitions)[index]? = some (.function definition) := by
    rw [programDefinitions, sourceGetElem?_eq_get?]
    exact runtimeLookup
  refine ⟨index, signature, definition, decoded, layout, runtimeFound, ?_⟩
  have runtimeAt : (GlobalProgramEntry.toDefinitions 0 entries)[index]? =
      some (.function definition) := by
    rw [sourceGetElem?_eq_get?]
    exact runtimeLookup
  have evaluated : GlobalIR.evaluate (GlobalProgramEntry.toDefinitions 0 entries)
      store (fuel + 1) [] (.global index) = .ok (.global index) := by
    simp [GlobalIR.evaluate, runtimeAt, pure, Except.pure]
  simpa [programDefinitions, PolyIR.erase] using evaluated

/-- The runtime result of a decoded function reference is not only the right
global index: its `ValueTyped` witness is the polymorphic function type in
the mixed entry signature table. -/
theorem readClosedInitializer_sourceVisibleFunctionReference_runtime_typed
    (entries visible : List GlobalProgramEntry.Entry) (forms : List Node)
    (forbidden : List Nat) (formIndex fuel selected : Nat) (atom : CMacroCopy.Atom)
    (selectedNonzero : selected ≠ 0) (notForbidden : selected ∉ forbidden)
    (visibleResolved : sourceVisibleEntries entries forms formIndex = some visible)
    (uniqueCheck : GlobalProgramEntry.identitiesUniqueCheck entries = true)
    (functionMember : selected ∈ GlobalProgramEntry.functionIdentities visible)
    (program : GlobalIR.Program) (store : GlobalIR.Store)
    (assignment : Nat → Surface.Ty)
    (programDefinitions : program.definitions = GlobalProgramEntry.toDefinitions 0 entries) :
    ∃ index signature definition,
      readClosedInitializer entries visible forbidden (fuel + 1) (.atom atom selected) =
        some (.global index []) ∧
      (GlobalProgramEntry.compiledLayout 0 entries).get? index =
        some (signature, GlobalIR.Definition.function definition) ∧
      GlobalIR.evaluate program.definitions store (fuel + 1) []
        (PolyIR.erase (.global index [])) = .ok (.global index) ∧
      PolyIR.ValueTyped (GlobalProgramEntry.signatures entries) (.global index)
        (.fn (Surface.interpretTypes assignment signature.parameters)
          (Surface.interpret assignment signature.result)) := by
  obtain ⟨index, signature, definition, decoded, layout, _runtimeEntry, evaluated⟩ :=
    readClosedInitializer_sourceVisibleFunctionReference_runtime_evaluates entries visible forms
      forbidden formIndex fuel selected atom selectedNonzero notForbidden visibleResolved
      uniqueCheck functionMember program store programDefinitions
  have projected :
      ((GlobalProgramEntry.compiledLayout 0 entries).get? index).map Prod.fst =
        (GlobalProgramEntry.signatures entries).get? index := by
    rw [GlobalProgramEntry.signatures, List.get?_map]
  rw [layout] at projected
  have signatureGet : (GlobalProgramEntry.signatures entries).get? index = some signature :=
    projected.symm
  have signatureAt : (GlobalProgramEntry.signatures entries)[index]? = some signature := by
    rw [sourceGetElem?_eq_get?]
    exact signatureGet
  exact ⟨index, signature, definition, decoded, layout, evaluated,
    PolyIR.ValueTyped.global signatureAt⟩

theorem readClosedInitializer_sourceVisibleTypeAppFunction_sound
    (entries visible : List GlobalProgramEntry.Entry) (forms : List Node)
    (formIndex fuel selected : Nat) (tag reference : Node) (typeNodes : List Node)
    (typeArguments : { types : List Surface.Ty //
      ∀ type ∈ types, type.wellFormed 0 })
    (tagName : name tag = some "type-app")
    (referenceIsAtom : ∃ atom, reference = .atom atom selected)
    (selectedNonzero : selected ≠ 0)
    (visibleResolved : sourceVisibleEntries entries forms formIndex = some visible)
    (uniqueCheck : GlobalProgramEntry.identitiesUniqueCheck entries = true)
    (functionMember : selected ∈ GlobalProgramEntry.functionIdentities visible)
    (argumentsDecoded : readClosedTypes fuel typeNodes = some typeArguments) :
    ∃ index signature definition,
      readClosedInitializer entries visible [] (fuel + 1)
        (.list (tag :: reference :: typeNodes)) = some (.global index typeArguments.val) ∧
      (GlobalProgramEntry.compiledLayout 0 entries).get? index =
        some (signature, GlobalIR.Definition.function definition) := by
  obtain ⟨atom, rfl⟩ := referenceIsAtom
  have entryMember := sourceVisibleEntries_functionIdentities_subset entries visible forms
    formIndex visibleResolved selected functionMember
  have distinct := GlobalProgramEntry.identitiesUniqueCheck_sound entries uniqueCheck
  obtain ⟨signature, definition, index, globalFound, layoutFound⟩ :=
    GlobalProgramEntry.functionIdentity_function_at_globalIndex selected 0 entries
      distinct entryMember
  have resolved : visibleFunctionIndex entries visible selected = some index := by
    unfold visibleFunctionIndex
    simp [functionMember, entryMember, uniqueCheck, globalFound]
  refine ⟨index, signature, definition, ?_, layoutFound⟩
  simp [readClosedInitializer, tagName, selectedNonzero,
    argumentsDecoded, resolved]

/-- An explicitly type-applied, source-visible polymorphic function reference
keeps its mixed-table runtime index and has the instantiated type in the
GlobalIR signature table. -/
theorem readClosedInitializer_sourceVisibleTypeAppFunction_runtime_typed
    (entries visible : List GlobalProgramEntry.Entry) (forms : List Node)
    (formIndex fuel selected : Nat) (tag reference : Node) (typeNodes : List Node)
    (typeArguments : { types : List Surface.Ty //
      ∀ type ∈ types, type.wellFormed 0 })
    (tagName : name tag = some "type-app")
    (referenceIsAtom : ∃ atom, reference = .atom atom selected)
    (selectedNonzero : selected ≠ 0)
    (visibleResolved : sourceVisibleEntries entries forms formIndex = some visible)
    (uniqueCheck : GlobalProgramEntry.identitiesUniqueCheck entries = true)
    (functionMember : selected ∈ GlobalProgramEntry.functionIdentities visible)
    (argumentsDecoded : readClosedTypes fuel typeNodes = some typeArguments)
    (layoutTypes : ∀ index signature definition,
      (GlobalProgramEntry.compiledLayout 0 entries).get? index =
        some (signature, GlobalIR.Definition.function definition) →
      signature.wellFormed ∧ typeArguments.val.length = signature.typeArity)
    (program : GlobalIR.Program) (store : GlobalIR.Store)
    (assignment : Nat → Surface.Ty)
    (programDefinitions : program.definitions = GlobalProgramEntry.toDefinitions 0 entries) :
    ∃ index signature definition,
      readClosedInitializer entries visible [] (fuel + 1)
        (.list (tag :: reference :: typeNodes)) =
          some (.global index typeArguments.val) ∧
      (GlobalProgramEntry.compiledLayout 0 entries).get? index =
        some (signature, GlobalIR.Definition.function definition) ∧
      GlobalIR.evaluate program.definitions store (fuel + 1) []
        (PolyIR.erase (.global index typeArguments.val)) = .ok (.global index) ∧
      PolyIR.ValueTyped (GlobalProgramEntry.signatures entries) (.global index)
        (Surface.interpret assignment
          (.fn (signature.parameters.map (fun type => type.instantiate typeArguments.val))
            (signature.result.instantiate typeArguments.val))) := by
  obtain ⟨index, signature, definition, decoded, layout⟩ :=
    readClosedInitializer_sourceVisibleTypeAppFunction_sound entries visible forms formIndex
      fuel selected tag reference typeNodes typeArguments tagName referenceIsAtom selectedNonzero
      visibleResolved uniqueCheck functionMember argumentsDecoded
  obtain ⟨signatureValid, argumentsArity⟩ := layoutTypes index signature definition layout
  have projected :
      ((GlobalProgramEntry.compiledLayout 0 entries).get? index).map Prod.fst =
        (GlobalProgramEntry.signatures entries).get? index := by
    rw [GlobalProgramEntry.signatures, List.get?_map]
  rw [layout] at projected
  have signatureGet : (GlobalProgramEntry.signatures entries).get? index = some signature :=
    projected.symm
  have signatureAt : (GlobalProgramEntry.signatures entries)[index]? = some signature := by
    rw [sourceGetElem?_eq_get?]
    exact signatureGet
  have runtimeLookup := GlobalProgramEntry.toDefinitions_function_of_layout
    0 entries index signature definition layout
  have runtimeAt : (GlobalProgramEntry.toDefinitions 0 entries)[index]? =
      some (.function definition) := by
    rw [sourceGetElem?_eq_get?]
    exact runtimeLookup
  have evaluated : GlobalIR.evaluate (GlobalProgramEntry.toDefinitions 0 entries)
      store (fuel + 1) [] (.global index) = .ok (.global index) := by
    simp [GlobalIR.evaluate, runtimeAt, pure, Except.pure]
  refine ⟨index, signature, definition, decoded, layout, ?_, ?_⟩
  · simpa [programDefinitions, PolyIR.erase] using evaluated
  · exact PolyIR.generic_global_typed signatureAt argumentsArity signatureValid

theorem typedGlobalFunctionReference_arity
    (entries : List GlobalProgramEntry.Entry) (index : Nat)
    (arguments : List Surface.Ty) (result : Surface.Ty)
    (typed : Surface.HasType (GlobalProgramEntry.signatures entries) 0 []
      (.global index arguments) result)
    (compiledFunction : ∃ signature definition,
      (GlobalProgramEntry.compiledLayout 0 entries).get? index =
        some (signature, GlobalIR.Definition.function definition)) :
    ∃ signature definition,
      (GlobalProgramEntry.compiledLayout 0 entries).get? index =
        some (signature, GlobalIR.Definition.function definition) ∧
      arguments.length = signature.typeArity := by
  cases typed with
  | global globalFound arity _argumentsWellFormed _signatureWellFormed =>
      obtain ⟨signature, definition, layoutFound⟩ := compiledFunction
      have projected :
          ((GlobalProgramEntry.compiledLayout 0 entries).get? index).map Prod.fst =
            (GlobalProgramEntry.signatures entries).get? index := by
        rw [GlobalProgramEntry.signatures, List.get?_map]
      rw [layoutFound] at projected
      cases signatureAt : (GlobalProgramEntry.signatures entries).get? index with
      | none =>
          have bracketNone : (GlobalProgramEntry.signatures entries)[index]? = none := by
            rw [sourceGetElem?_eq_get?]
            exact signatureAt
          rw [bracketNone] at globalFound
          contradiction
      | some typedSignature =>
          have signatureEq : signature = typedSignature :=
            Option.some.inj (projected.trans signatureAt)
          have globalFoundGet :=
            (sourceGetElem?_eq_get? (GlobalProgramEntry.signatures entries) index).symm.trans
              globalFound
          have typedSignatureEq := Option.some.inj (signatureAt.symm.trans globalFoundGet)
          have arityForLayout : arguments.length = signature.typeArity := by
            rw [signatureEq, typedSignatureEq]
            exact arity
          exact ⟨signature, definition, layoutFound, arityForLayout⟩

theorem readClosedInitializer_sourceVisibleValueReference_sound
    (entries visible : List GlobalProgramEntry.Entry) (forms : List Node)
    (formIndex fuel selected index : Nat) (atom : CMacroCopy.Atom)
    (selectedNonzero : selected ≠ 0)
    (visibleResolved : sourceVisibleEntries entries forms formIndex = some visible)
    (uniqueCheck : GlobalProgramEntry.identitiesUniqueCheck entries = true)
    (valueMember : selected ∈ GlobalProgramEntry.valueIdentities visible)
    (decoded : readClosedInitializer entries visible [] (fuel + 1)
      (.atom atom selected) = some (.app (.global index []) [])) :
    selected ∈ GlobalProgramEntry.valueIdentities entries ∧
    GlobalProgramEntry.globalIndexOf selected entries = some index ∧
    ∃ type denseSlot,
      (GlobalProgramEntry.compiledLayout 0 entries).get? index =
        some (⟨0, [], type⟩, Definition.getter denseSlot) := by
  have notFunction := sourceVisibleValue_notFunction entries visible forms formIndex selected
    visibleResolved uniqueCheck valueMember
  obtain ⟨_visibleValue, entryValue, globalFound, type, denseSlot, getterAt⟩ :=
    readClosedInitializer_globalReference_sound entries visible [] fuel selected index atom
      selectedNonzero notFunction decoded
  exact ⟨entryValue, globalFound, type, denseSlot, getterAt⟩

theorem readClosedInitializer_valueReference_runtime_reads_current_store
    (entries visible : List GlobalProgramEntry.Entry) (forms : List Node)
    (formIndex fuel selected index : Nat) (atom : CMacroCopy.Atom)
    (selectedNonzero : selected ≠ 0)
    (visibleResolved : sourceVisibleEntries entries forms formIndex = some visible)
    (uniqueCheck : GlobalProgramEntry.identitiesUniqueCheck entries = true)
    (valueMember : selected ∈ GlobalProgramEntry.valueIdentities visible)
    (decoded : readClosedInitializer entries visible [] (fuel + 1)
      (.atom atom selected) = some (.app (.global index []) []))
    (program : GlobalIR.Program) (value : PolyIR.Value)
    (store : GlobalIR.Store)
    (programDefinitions : program.definitions = GlobalProgramEntry.toDefinitions 0 entries)
    (initialized : ∀ type slot,
      (GlobalProgramEntry.compiledLayout 0 entries).get? index =
        some (⟨0, [], type⟩, GlobalIR.Definition.getter slot) →
      store[slot]? = some (some value)) :
    ∃ type slot,
      (GlobalProgramEntry.compiledLayout 0 entries).get? index =
        some (⟨0, [], type⟩, GlobalIR.Definition.getter slot) ∧
      program.definitions[index]? = some (.getter slot) ∧
      GlobalIR.evaluate program.definitions store (fuel + 2) []
        (PolyIR.erase (.app (.global index []) [])) = .ok value := by
  obtain ⟨_entryValue, _globalFound, type, slot, layout⟩ :=
    readClosedInitializer_sourceVisibleValueReference_sound entries visible forms formIndex
      fuel selected index atom selectedNonzero visibleResolved uniqueCheck valueMember decoded
  have runtimeGetterLookup :
      (GlobalProgramEntry.toDefinitions 0 entries).get? index = some (.getter slot) :=
    GlobalProgramEntry.toDefinitions_getter_of_layout 0 entries index
      ⟨0, [], type⟩ slot layout
  have runtimeGetter :
      (GlobalProgramEntry.toDefinitions 0 entries)[index]? = some (.getter slot) := by
    rw [sourceGetElem?_eq_get?]
    exact runtimeGetterLookup
  have initializedCell := initialized type slot layout
  have evaluated := GlobalIR.getter_call_reads_current_store
    (GlobalProgramEntry.toDefinitions 0 entries) store fuel index slot value
    runtimeGetter initializedCell
  refine ⟨type, slot, layout, ?_, ?_⟩
  · simpa [programDefinitions] using runtimeGetter
  · simpa [programDefinitions, PolyIR.erase] using evaluated

theorem readClosedInitializer_valueReference_runtime_reports_early_read
    (entries visible : List GlobalProgramEntry.Entry) (forms : List Node)
    (formIndex fuel selected index : Nat) (atom : CMacroCopy.Atom)
    (selectedNonzero : selected ≠ 0)
    (visibleResolved : sourceVisibleEntries entries forms formIndex = some visible)
    (uniqueCheck : GlobalProgramEntry.identitiesUniqueCheck entries = true)
    (valueMember : selected ∈ GlobalProgramEntry.valueIdentities visible)
    (decoded : readClosedInitializer entries visible [] (fuel + 1)
      (.atom atom selected) = some (.app (.global index []) []))
    (program : GlobalIR.Program) (store : GlobalIR.Store)
    (programDefinitions : program.definitions = GlobalProgramEntry.toDefinitions 0 entries)
    (uninitialized : ∀ type slot,
      (GlobalProgramEntry.compiledLayout 0 entries).get? index =
        some (⟨0, [], type⟩, GlobalIR.Definition.getter slot) →
      store[slot]? = some none) :
    ∃ type slot,
      (GlobalProgramEntry.compiledLayout 0 entries).get? index =
        some (⟨0, [], type⟩, GlobalIR.Definition.getter slot) ∧
      program.definitions[index]? = some (.getter slot) ∧
      GlobalIR.evaluate program.definitions store (fuel + 2) []
        (PolyIR.erase (.app (.global index []) [])) =
          .error (.beforeInitialization slot) := by
  obtain ⟨_entryValue, _globalFound, type, slot, layout⟩ :=
    readClosedInitializer_sourceVisibleValueReference_sound entries visible forms formIndex
      fuel selected index atom selectedNonzero visibleResolved uniqueCheck valueMember decoded
  have runtimeGetterLookup :
      (GlobalProgramEntry.toDefinitions 0 entries).get? index = some (.getter slot) :=
    GlobalProgramEntry.toDefinitions_getter_of_layout 0 entries index
      ⟨0, [], type⟩ slot layout
  have runtimeGetter :
      (GlobalProgramEntry.toDefinitions 0 entries)[index]? = some (.getter slot) := by
    rw [sourceGetElem?_eq_get?]
    exact runtimeGetterLookup
  have earlyRead := GlobalIR.getter_call_reports_early_read
    (GlobalProgramEntry.toDefinitions 0 entries) store fuel index slot runtimeGetter
    (uninitialized type slot layout)
  refine ⟨type, slot, layout, ?_, ?_⟩
  · simpa [programDefinitions] using runtimeGetter
  · simpa [programDefinitions, PolyIR.erase] using earlyRead

/-- When a decoded top-level value reference is the first initializer and its
getter slot is still empty, the source-resolved reference's early-read fault
becomes the observable `GlobalIR.run` result. -/
theorem readClosedInitializer_fault_reports_run_fault_after_prefix
    (entries visible : List GlobalProgramEntry.Entry) (forbidden : List Nat)
    (decodeFuel fuel : Nat) (node : CBindingWalk.Node) (expression : Surface.Expr)
    (program : GlobalIR.Program) (initializersBefore tail : List PolyIR.Term)
    (after : GlobalIR.Store) (fault : GlobalIR.Fault)
    (decoded : readClosedInitializer entries visible forbidden decodeFuel node =
      some expression)
    (programLayout : program.initializers =
      initializersBefore ++ PolyIR.erase expression :: tail)
    (prefixSuccess : GlobalIR.initializeValues program.definitions
      (fuel + initializersBefore.length + 2)
      (List.replicate program.initializers.length none) 0 initializersBefore = .ok after)
    (runtimeFault : GlobalIR.evaluate program.definitions after (fuel + 1) []
      (PolyIR.erase expression) = .error fault) :
    readClosedInitializer entries visible forbidden decodeFuel node = some expression ∧
      GlobalIR.run program (fuel + initializersBefore.length + 2) = .error fault := by
  exact ⟨decoded, GlobalIR.run_reports_initializer_fault_after_prefix program fuel
    initializersBefore (PolyIR.erase expression) tail after fault programLayout
    prefixSuccess runtimeFault⟩

/-- Compose a C reader result at a node of an accepted finite expansion with
the source-to-GlobalIR call-fragment fault theorem. The checked expansion
retains the finite source/target syntax and scope certificate; source
evaluation and prefix success are explicit semantic premises. -/
theorem checkedExpansion_readClosedInitializer_fault_reports_run_after_prefix
    (expansion : ProcessCertificate.CheckedExpansion)
    (nodeIndex decodeFuel fuel : Nat) (entries visible : List GlobalProgramEntry.Entry)
    (forbidden : List Nat) (node : CBindingWalk.Node) (expression : Surface.Expr)
    (sourceProgram : Surface.Definitions) (initializersBefore tail : List PolyIR.Term)
    (entry : Nat) (after : GlobalIR.Store) (fault : PolyIR.Fault)
    (nodeFound : expansion.annotated[nodeIndex]? = some node)
    (decoded : readClosedInitializer entries visible forbidden decodeFuel node = some expression)
    (fragments : FunctionTableCallTerms (PolyIR.eraseDefinitions sourceProgram)
      (initializersBefore ++ PolyIR.erase expression :: tail))
    (prefixSuccess : initializeValuesCore (PolyIR.eraseDefinitions sourceProgram)
      (fuel + initializersBefore.length + 2)
      (List.replicate (initializersBefore ++ PolyIR.erase expression :: tail).length none)
      0 initializersBefore = .ok after)
    (sourceFault : Surface.evaluate sourceProgram (fuel + 1) [] expression = .error fault) :
    expansion.text.toUTF8.data.data = expansion.bytes ∧
      SourceReader.readWithFuel expansion.lexFuel expansion.parseFuel expansion.text =
        some expansion.parsed ∧
      SourceReader.normalize expansion.parsed = some expansion.normalized ∧
      CExpansion.Expands (CExpansion.sourceRules 0 expansion.normalized)
      (.list (CExpansion.programForms expansion.normalized)) (.list expansion.expanded) ∧
      CExpansion.disjointIntervals
        (ExpansionCertificate.freshIntervals expansion.localCertificate) = true ∧
      expansion.annotated.map CBindingWalk.Node.erase = expansion.expanded ∧
      (∃ sites, CBindingWalk.references expansion.scopeFuel expansion.annotated
        CBindingWalk.builtinEnvironment = some sites ∧
        ∀ site ∈ sites, CBindingWalk.Corresponds site) ∧
      expansion.annotated[nodeIndex]? = some node ∧
      readClosedInitializer entries visible forbidden decodeFuel node = some expression ∧
      GlobalIR.run
        ⟨(PolyIR.eraseDefinitions sourceProgram).map GlobalIR.Definition.function,
          initializersBefore ++ PolyIR.erase expression :: tail, entry⟩
        (fuel + initializersBefore.length + 2) = .error (.core fault) := by
  have certificateFacts := ProcessCertificate.source_expands_with_scopes_and_freshness expansion
  rcases certificateFacts with
    ⟨bytesMatch, parses, normalizes, finiteExpansion, fresh, syntaxCorr, scope⟩
  refine ⟨bytesMatch, parses, normalizes, finiteExpansion, fresh, syntaxCorr, scope,
    nodeFound, decoded, ?_⟩
  exact functionTable_sourceFault_run_reports_initializer_fault_after_prefix
    sourceProgram initializersBefore tail expression entry fuel after fault fragments
    prefixSuccess sourceFault

theorem readClosedInitializer_firstInitializer_reports_early_read
    (entries visible : List GlobalProgramEntry.Entry) (forms : List Node)
    (formIndex fuel selected index : Nat) (atom : CMacroCopy.Atom)
    (selectedNonzero : selected ≠ 0)
    (visibleResolved : sourceVisibleEntries entries forms formIndex = some visible)
    (uniqueCheck : GlobalProgramEntry.identitiesUniqueCheck entries = true)
    (valueMember : selected ∈ GlobalProgramEntry.valueIdentities visible)
    (decoded : readClosedInitializer entries visible [] (fuel + 1)
      (.atom atom selected) = some (.app (.global index []) []))
    (slotZero : ∃ type,
      (GlobalProgramEntry.compiledLayout 0 entries).get? index =
        some (⟨0, [], type⟩, GlobalIR.Definition.getter 0))
    (program : GlobalIR.Program)
    (programDefinitions : program.definitions = GlobalProgramEntry.toDefinitions 0 entries)
    (programInitializers : program.initializers =
      [PolyIR.erase (.app (.global index []) [])]) :
    GlobalIR.run program (fuel + 3) = .error (.beforeInitialization 0) := by
  obtain ⟨_entryValue, _globalFound, type, denseSlot, layout⟩ :=
    readClosedInitializer_sourceVisibleValueReference_sound entries visible forms formIndex
      fuel selected index atom selectedNonzero visibleResolved uniqueCheck valueMember decoded
  obtain ⟨slotType, zeroLayout⟩ := slotZero
  have layoutEqual :
      Prod.mk (⟨0, [], type⟩ : Surface.Signature) (GlobalIR.Definition.getter denseSlot) =
        Prod.mk (⟨0, [], slotType⟩ : Surface.Signature) (GlobalIR.Definition.getter 0) := by
    have equalSome := Option.some.inj (layout.symm.trans zeroLayout)
    exact equalSome
  have signatureEqual : (⟨0, [], type⟩ : Surface.Signature) = ⟨0, [], slotType⟩ :=
    congrArg Prod.fst layoutEqual
  have getterEqual : GlobalIR.Definition.getter denseSlot =
      GlobalIR.Definition.getter 0 := congrArg Prod.snd layoutEqual
  have denseSlotZero : denseSlot = 0 := GlobalIR.Definition.getter.inj getterEqual
  cases signatureEqual
  subst denseSlot
  have layout := zeroLayout
  have runtimeGetterLookup :
      (GlobalProgramEntry.toDefinitions 0 entries).get? index =
        some (.getter 0) :=
    GlobalProgramEntry.toDefinitions_getter_of_layout 0 entries index
      ⟨0, [], type⟩ 0 layout
  have runtimeGetter :
      (GlobalProgramEntry.toDefinitions 0 entries)[index]? = some (.getter 0) := by
    rw [sourceGetElem?_eq_get?]
    exact runtimeGetterLookup
  have earlyRead := GlobalIR.getter_call_reports_early_read
    (GlobalProgramEntry.toDefinitions 0 entries)
    (List.replicate 1 none) fuel index 0 runtimeGetter (by simp)
  have firstStep : GlobalIR.evaluate program.definitions
      (List.replicate program.initializers.length none) (fuel + 2) []
      (PolyIR.erase (.app (.global index []) [])) = .error (.beforeInitialization 0) := by
    simpa [programDefinitions, programInitializers, PolyIR.erase] using earlyRead
  apply GlobalIR.run_reports_first_initializer_fault program (fuel + 2)
    (.beforeInitialization 0) (PolyIR.erase (.app (.global index []) [])) []
  · exact programInitializers
  · exact firstStep

/-- A reader-produced initializer with a wrong-shaped integer equality
propagates the same source fault through the first GlobalIR initialization
step and becomes the observable `run` result. -/
theorem readClosedInitializer_intEq_wrong_shape_reports_run_fault
    (entries visible : List GlobalProgramEntry.Entry) (forbidden : List Nat)
    (decodeFuel fuel : Nat) (node : CBindingWalk.Node)
    (sourceProgram : Surface.Definitions) (program : GlobalIR.Program)
    (decoded : readClosedInitializer entries visible forbidden decodeFuel node =
      some (.intEq (.bool true) (.int 4)))
    (programDefinitions : program.definitions = [])
    (programInitializers : program.initializers =
      [PolyIR.erase (.intEq (.bool true) (.int 4))]) :
    readClosedInitializer entries visible forbidden decodeFuel node =
        some (.intEq (.bool true) (.int 4)) ∧
      Surface.evaluate sourceProgram (fuel + 2) [] (.intEq (.bool true) (.int 4)) =
        .error .wrongShape ∧
      GlobalIR.run program (fuel + 3) = .error (.core .wrongShape) := by
  have sourceLeft : Surface.evaluate sourceProgram (fuel + 1) [] (.bool true) =
      .ok (.bool true) := by rfl
  have sourceRight : Surface.evaluate sourceProgram (fuel + 1) [] (.int 4) =
      .ok (.int 4) := by rfl
  have runtimeLeft : GlobalIR.evaluate [] (List.replicate 1 none) (fuel + 1) [] (.bool true) =
      .ok (.bool true) := by rfl
  have runtimeRight : GlobalIR.evaluate [] (List.replicate 1 none) (fuel + 1) [] (.int 4) =
      .ok (.int 4) := by rfl
  have notBothIntegers : ¬ ∃ leftInt rightInt,
      Surface.Value.bool true = .int leftInt ∧ Surface.Value.int 4 = .int rightInt := by
    rintro ⟨_, _, hLeft, _⟩
    cases hLeft
  have correspondingFault := NLisp.intEq_wrong_shape_fault_corresponds_to_globalIR
    sourceProgram [] (List.replicate 1 none) (fuel + 1) [] (.bool true) (.int 4)
    (.bool true) (.int 4) sourceLeft sourceRight runtimeLeft runtimeRight notBothIntegers
  have runtimeFault : GlobalIR.evaluate [] (List.replicate 1 none) (fuel + 2) []
      (.intEq (.bool true) (.int 4)) = .error (.core .wrongShape) := by
    simp [GlobalIR.evaluate]
  have sourceFault := correspondingFault.2 runtimeFault
  have firstStep : GlobalIR.evaluate program.definitions
      (List.replicate program.initializers.length none) (fuel + 2) []
      (PolyIR.erase (.intEq (.bool true) (.int 4))) = .error (.core .wrongShape) := by
    simpa [programDefinitions, programInitializers, PolyIR.erase] using runtimeFault
  have runFault := GlobalIR.run_reports_first_initializer_fault program (fuel + 2)
    (.core .wrongShape) (PolyIR.erase (.intEq (.bool true) (.int 4))) [] programInitializers
    firstStep
  exact ⟨decoded, sourceFault, by simpa using runFault⟩

/-- Compose the concrete annotated-node reader rule for the reserved C
`integer=` builtin with the source-fault and GlobalIR run-fault correspondence. -/
theorem readClosedInitializer_intEq_builtin_wrong_shape_reports_run_fault
    (entries visible : List GlobalProgramEntry.Entry) (forbidden : List Nat)
    (decodeFuel fuel selected : Nat) (operator : CMacroCopy.Atom)
    (leftNode rightNode : CBindingWalk.Node)
    (sourceProgram : Surface.Definitions) (program : GlobalIR.Program)
    (selectedEq : selected = 24) (operatorName : operator.name = "integer=")
    (notForbidden : selected ∉ forbidden)
    (notVisibleFunction : visibleFunctionIndex entries visible selected = none)
    (leftDecoded : readClosedInitializer entries visible forbidden decodeFuel leftNode =
      some (.bool true))
    (rightDecoded : readClosedInitializer entries visible forbidden decodeFuel rightNode =
      some (.int 4))
    (programDefinitions : program.definitions = [])
    (programInitializers : program.initializers =
      [PolyIR.erase (.intEq (.bool true) (.int 4))]) :
    readClosedInitializer entries visible forbidden (decodeFuel + 1)
        (.list [.atom operator selected, leftNode, rightNode]) =
        some (.intEq (.bool true) (.int 4)) ∧
      Surface.evaluate sourceProgram (fuel + 2) [] (.intEq (.bool true) (.int 4)) =
        .error .wrongShape ∧
      GlobalIR.run program (fuel + 3) = .error (.core .wrongShape) := by
  have decoded := readClosedInitializer_intEq entries visible forbidden decodeFuel selected
    operator leftNode rightNode (.bool true) (.int 4) selectedEq operatorName notForbidden
    notVisibleFunction leftDecoded rightDecoded
  exact readClosedInitializer_intEq_wrong_shape_reports_run_fault entries visible forbidden
    (decodeFuel + 1) fuel (.list [.atom operator selected, leftNode, rightNode])
    sourceProgram program decoded programDefinitions programInitializers

/-- The concrete C reader's `integer=` wrong-shape fault remains observable
when it occurs after an arbitrary successfully initialized top-level prefix. -/
theorem readClosedInitializer_intEq_builtin_wrong_shape_reports_run_fault_after_prefix
    (entries visible : List GlobalProgramEntry.Entry) (forbidden : List Nat)
    (decodeFuel fuel selected : Nat) (operator : CMacroCopy.Atom)
    (leftNode rightNode : CBindingWalk.Node) (initializersBefore : List PolyIR.Term)
    (after : GlobalIR.Store) (sourceProgram : Surface.Definitions)
    (program : GlobalIR.Program)
    (selectedEq : selected = 24) (operatorName : operator.name = "integer=")
    (notForbidden : selected ∉ forbidden)
    (notVisibleFunction : visibleFunctionIndex entries visible selected = none)
    (leftDecoded : readClosedInitializer entries visible forbidden decodeFuel leftNode =
      some (.bool true))
    (rightDecoded : readClosedInitializer entries visible forbidden decodeFuel rightNode =
      some (.int 4))
    (programDefinitions : program.definitions = [])
    (programInitializers : program.initializers =
      initializersBefore ++ [PolyIR.erase (.intEq (.bool true) (.int 4))])
    (prefixSuccess : GlobalIR.initializeValues program.definitions
      (fuel + initializersBefore.length + 3)
      (List.replicate program.initializers.length none) 0 initializersBefore = .ok after) :
    readClosedInitializer entries visible forbidden (decodeFuel + 1)
        (.list [.atom operator selected, leftNode, rightNode]) =
        some (.intEq (.bool true) (.int 4)) ∧
      Surface.evaluate sourceProgram (fuel + 2) [] (.intEq (.bool true) (.int 4)) =
        .error .wrongShape ∧
      GlobalIR.run program (fuel + initializersBefore.length + 3) =
        .error (.core .wrongShape) := by
  have decoded := readClosedInitializer_intEq entries visible forbidden decodeFuel selected
    operator leftNode rightNode (.bool true) (.int 4) selectedEq operatorName notForbidden
    notVisibleFunction leftDecoded rightDecoded
  have sourceLeft : Surface.evaluate sourceProgram (fuel + 1) [] (.bool true) =
      .ok (.bool true) := by rfl
  have sourceRight : Surface.evaluate sourceProgram (fuel + 1) [] (.int 4) =
      .ok (.int 4) := by rfl
  have runtimeLeft : GlobalIR.evaluate [] after (fuel + 1) [] (.bool true) =
      .ok (.bool true) := by cases fuel <;> rfl
  have runtimeRight : GlobalIR.evaluate [] after (fuel + 1) [] (.int 4) =
      .ok (.int 4) := by cases fuel <;> rfl
  have mismatch : ¬ ∃ leftInt rightInt,
      Surface.Value.bool true = .int leftInt ∧ Surface.Value.int 4 = .int rightInt := by
    rintro ⟨_, _, hLeft, _⟩
    cases hLeft
  have correspondingFault := NLisp.intEq_wrong_shape_fault_corresponds_to_globalIR
    sourceProgram [] after (fuel + 1) [] (.bool true) (.int 4)
    (.bool true) (.int 4) sourceLeft sourceRight runtimeLeft runtimeRight mismatch
  have runtimeFault : GlobalIR.evaluate [] after (fuel + 2) []
      (.intEq (.bool true) (.int 4)) = .error (.core .wrongShape) := by
    cases fuel <;> simp [GlobalIR.evaluate]
  have sourceFault := correspondingFault.mpr (by
    simpa [PolyIR.erase] using runtimeFault)
  have runFault := GlobalIR.run_reports_initializer_fault_after_prefix program (fuel + 1)
    initializersBefore (PolyIR.erase (.intEq (.bool true) (.int 4))) [] after
    (.core .wrongShape) programInitializers
    (by simpa [programDefinitions, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
      using prefixSuccess)
    (by simpa [programDefinitions, PolyIR.erase] using runtimeFault)
  exact ⟨decoded, by simpa [Nat.add_assoc] using sourceFault,
    by simpa [programInitializers, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
      using runFault⟩

/-- The annotated C reader's Float builtin branch preserves a wrong-shape
fault through an arbitrary successful initializer prefix and exposes it as
the GlobalIR program result. -/
theorem readClosedInitializer_floatBin_builtin_wrong_shape_reports_run_fault_after_prefix
    (entries visible : List GlobalProgramEntry.Entry) (forbidden : List Nat)
    (decodeFuel fuel selected : Nat) (operator : CMacroCopy.Atom)
    (leftNode rightNode : CBindingWalk.Node) (operation : Surface.FloatBinOp)
    (initializersBefore : List PolyIR.Term) (after : GlobalIR.Store)
    (sourceProgram : Surface.Definitions) (program : GlobalIR.Program)
    (builtin : (selected = 39 ∧ operator.name = "float+" ∧ operation = .add) ∨
      (selected = 42 ∧ operator.name = "float-" ∧ operation = .sub) ∨
      (selected = 45 ∧ operator.name = "float*" ∧ operation = .mul) ∨
      (selected = 48 ∧ operator.name = "float/" ∧ operation = .div))
    (notForbidden : selected ∉ forbidden)
    (leftDecoded : readClosedInitializer entries visible forbidden decodeFuel leftNode =
      some (.bool true))
    (rightDecoded : readClosedInitializer entries visible forbidden decodeFuel rightNode =
      some (.int 4))
    (programDefinitions : program.definitions = [])
    (programInitializers : program.initializers = initializersBefore ++
      [PolyIR.erase (.floatBin operation (.bool true) (.int 4))])
    (prefixSuccess : GlobalIR.initializeValues program.definitions
      (fuel + initializersBefore.length + 3)
      (List.replicate program.initializers.length none) 0 initializersBefore = .ok after) :
    readClosedInitializer entries visible forbidden (decodeFuel + 1)
        (.list [.atom operator selected, leftNode, rightNode]) =
        some (.floatBin operation (.bool true) (.int 4)) ∧
      Surface.evaluate sourceProgram (fuel + 2) []
        (.floatBin operation (.bool true) (.int 4)) = .error .wrongShape ∧
      GlobalIR.run program (fuel + initializersBefore.length + 3) =
        .error (.core .wrongShape) := by
  have decoded := readClosedInitializer_floatBin entries visible forbidden decodeFuel selected
    operator leftNode rightNode operation (.bool true) (.int 4) builtin notForbidden
    leftDecoded rightDecoded
  have sourceLeft : Surface.evaluate sourceProgram (fuel + 1) [] (.bool true) =
      .ok (.bool true) := by rfl
  have sourceRight : Surface.evaluate sourceProgram (fuel + 1) [] (.int 4) =
      .ok (.int 4) := by rfl
  have runtimeLeft : GlobalIR.evaluate [] after (fuel + 1) [] (.bool true) =
      .ok (.bool true) := by cases fuel <;> rfl
  have runtimeRight : GlobalIR.evaluate [] after (fuel + 1) [] (.int 4) =
      .ok (.int 4) := by cases fuel <;> rfl
  have notBothFloats : ¬ ∃ x y, Surface.Value.bool true = .float x ∧
      Surface.Value.int 4 = .float y := by
    rintro ⟨_, _, leftIsFloat, _⟩
    cases leftIsFloat
  have correspondingFault := readClosedInitializer_floatBin_wrong_shape_fault_corresponds_to_globalIR
    entries visible forbidden decodeFuel (fuel + 1) selected operator leftNode rightNode
    operation (.bool true) (.int 4) sourceProgram [] after [] (.bool true) (.int 4)
    builtin notForbidden leftDecoded rightDecoded sourceLeft sourceRight
    runtimeLeft runtimeRight notBothFloats
  have runtimeFault : GlobalIR.evaluate [] after (fuel + 2) []
      (.floatBin operation (.bool true) (.int 4)) = .error (.core .wrongShape) := by
    simp [GlobalIR.evaluate, runtimeLeft, runtimeRight, bind, Except.bind,
      Except.pure, pure]
  have sourceFault := correspondingFault.2.mpr runtimeFault
  have prefixSuccess' : GlobalIR.initializeValues program.definitions
      (fuel + 1 + initializersBefore.length + 2)
      (List.replicate program.initializers.length none) 0 initializersBefore = .ok after := by
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using prefixSuccess
  have runFault := GlobalIR.run_reports_initializer_fault_after_prefix program (fuel + 1)
    initializersBefore (PolyIR.erase (.floatBin operation (.bool true) (.int 4))) [] after
    (.core .wrongShape) programInitializers prefixSuccess'
    (by simpa [programDefinitions, PolyIR.erase] using runtimeFault)
  exact ⟨decoded, sourceFault, by
    simpa [programInitializers, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using runFault⟩

/-- A C-reader `if` whose condition decodes to an integer preserves the
source wrong-shape fault through a successful top-level initializer prefix
and exposes the same fault as `GlobalIR.run`. -/
theorem readClosedInitializer_if_wrong_condition_reports_run_fault_after_prefix
    (entries visible : List GlobalProgramEntry.Entry) (forbidden : List Nat)
    (decodeFuel fuel : Nat) (keyword : CMacroCopy.Atom) (keywordToken : Nat)
    (conditionNode yesNode noNode : CBindingWalk.Node)
    (initializersBefore : List PolyIR.Term) (after : GlobalIR.Store)
    (sourceProgram : Surface.Definitions) (program : GlobalIR.Program)
    (keywordName : keyword.name = "if")
    (conditionDecoded : readClosedInitializer entries visible forbidden decodeFuel
      conditionNode = some (.int 1))
    (yesDecoded : readClosedInitializer entries visible forbidden decodeFuel yesNode =
      some (.bool true))
    (noDecoded : readClosedInitializer entries visible forbidden decodeFuel noNode =
      some (.bool false))
    (programInitializers : program.initializers = initializersBefore ++
      [PolyIR.erase (.ite (.int 1) (.bool true) (.bool false))])
    (prefixSuccess : GlobalIR.initializeValues program.definitions
      (fuel + initializersBefore.length + 3)
      (List.replicate program.initializers.length none) 0 initializersBefore = .ok after) :
    readClosedInitializer entries visible forbidden (decodeFuel + 1)
        (.list [.atom keyword keywordToken, conditionNode, yesNode, noNode]) =
        some (.ite (.int 1) (.bool true) (.bool false)) ∧
      Surface.evaluate sourceProgram (fuel + 2) []
        (.ite (.int 1) (.bool true) (.bool false)) = .error .wrongShape ∧
      GlobalIR.run program (fuel + initializersBefore.length + 3) =
        .error (.core .wrongShape) := by
  have decoded : readClosedInitializer entries visible forbidden (decodeFuel + 1)
      (.list [.atom keyword keywordToken, conditionNode, yesNode, noNode]) =
      some (.ite (.int 1) (.bool true) (.bool false)) := by
    have noFloat : floatBuiltinOperator keywordToken "if" = none := by
      by_cases h39 : keywordToken = 39
      · subst keywordToken; rfl
      · by_cases h42 : keywordToken = 42
        · subst keywordToken; rfl
        · by_cases h45 : keywordToken = 45
          · subst keywordToken; rfl
          · by_cases h48 : keywordToken = 48
            · subst keywordToken; rfl
            · simp [floatBuiltinOperator, h39, h42, h45, h48]
    have ifNotTypeApp : "if" ≠ "type-app" := by decide
    simp [readClosedInitializer, ExpansionLowering.name, noFloat, keywordName,
      ifNotTypeApp,
      conditionDecoded, yesDecoded, noDecoded]
  have sourceFault : Surface.evaluate sourceProgram (fuel + 2) []
      (.ite (.int 1) (.bool true) (.bool false)) = .error .wrongShape := by
    simp [Surface.evaluate]
  have runtimeFault : GlobalIR.evaluate program.definitions after (fuel + 2) []
      (.ite (.int 1) (.bool true) (.bool false)) = .error (.core .wrongShape) := by
    cases fuel <;> simp [GlobalIR.evaluate]
  have prefixSuccess' : GlobalIR.initializeValues program.definitions
      (fuel + 1 + initializersBefore.length + 2)
      (List.replicate program.initializers.length none) 0 initializersBefore = .ok after := by
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using prefixSuccess
  have runFault := GlobalIR.run_reports_initializer_fault_after_prefix program (fuel + 1)
    initializersBefore (PolyIR.erase (.ite (.int 1) (.bool true) (.bool false))) [] after
    (.core .wrongShape) programInitializers prefixSuccess'
    (by simpa [PolyIR.erase] using runtimeFault)
  exact ⟨decoded, sourceFault, by
    simpa [programInitializers, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using runFault⟩

/-- General C-reader conditional fault correspondence. If the decoded
condition evaluates to corresponding non-Boolean values in Surface and
GlobalIR, then the reader-produced `if` reports `.wrongShape`; after any
successful initializer prefix, this remains the observable `run` fault. -/
theorem readClosedInitializer_if_nonboolean_condition_reports_run_fault_after_prefix
    (entries visible : List GlobalProgramEntry.Entry) (forbidden : List Nat)
    (decodeFuel fuel : Nat) (keyword : CMacroCopy.Atom) (keywordToken : Nat)
    (conditionNode yesNode noNode : CBindingWalk.Node)
    (condition yes no : Surface.Expr) (conditionValue : Surface.Value)
    (initializersBefore : List PolyIR.Term) (after : GlobalIR.Store)
    (sourceProgram : Surface.Definitions) (program : GlobalIR.Program)
    (keywordName : keyword.name = "if")
    (conditionDecoded : readClosedInitializer entries visible forbidden decodeFuel
      conditionNode = some condition)
    (yesDecoded : readClosedInitializer entries visible forbidden decodeFuel yesNode =
      some yes)
    (noDecoded : readClosedInitializer entries visible forbidden decodeFuel noNode =
      some no)
    (conditionEvaluates : Surface.evaluate sourceProgram (fuel + 1) [] condition =
      .ok conditionValue)
    (conditionRuntime : GlobalIR.evaluate program.definitions after (fuel + 1) []
      (PolyIR.erase condition) = .ok (PolyIR.eraseValue conditionValue))
    (conditionNotBoolean : ∀ boolean, conditionValue ≠ .bool boolean)
    (programInitializers : program.initializers = initializersBefore ++
      [PolyIR.erase (.ite condition yes no)])
    (prefixSuccess : GlobalIR.initializeValues program.definitions
      (fuel + initializersBefore.length + 3)
      (List.replicate program.initializers.length none) 0 initializersBefore = .ok after) :
    readClosedInitializer entries visible forbidden (decodeFuel + 1)
        (.list [.atom keyword keywordToken, conditionNode, yesNode, noNode]) =
        some (.ite condition yes no) ∧
      Surface.evaluate sourceProgram (fuel + 2) [] (.ite condition yes no) =
        .error .wrongShape ∧
      GlobalIR.run program (fuel + initializersBefore.length + 3) =
        .error (.core .wrongShape) := by
  have decoded : readClosedInitializer entries visible forbidden (decodeFuel + 1)
      (.list [.atom keyword keywordToken, conditionNode, yesNode, noNode]) =
      some (.ite condition yes no) := by
    have noFloat : floatBuiltinOperator keywordToken "if" = none := by
      by_cases h39 : keywordToken = 39
      · subst keywordToken; rfl
      · by_cases h42 : keywordToken = 42
        · subst keywordToken; rfl
        · by_cases h45 : keywordToken = 45
          · subst keywordToken; rfl
          · by_cases h48 : keywordToken = 48
            · subst keywordToken; rfl
            · simp [floatBuiltinOperator, h39, h42, h45, h48]
    have ifNotTypeApp : "if" ≠ "type-app" := by decide
    simp [readClosedInitializer, ExpansionLowering.name, noFloat, keywordName,
      ifNotTypeApp, conditionDecoded, yesDecoded, noDecoded]
  have sourceFault : Surface.evaluate sourceProgram (fuel + 2) []
      (.ite condition yes no) = .error .wrongShape := by
    simp only [Surface.evaluate]
    rw [conditionEvaluates]
    cases conditionValue <;> simp_all [bind, pure, Except.bind, Except.pure]
  have runtimeFault : GlobalIR.evaluate program.definitions after (fuel + 2) []
      (PolyIR.erase (.ite condition yes no)) = .error (.core .wrongShape) := by
    simp only [PolyIR.erase, GlobalIR.evaluate]
    rw [conditionRuntime]
    cases conditionValue <;>
      simp_all [PolyIR.eraseValue, bind, pure, Except.bind, Except.pure]
  have prefixSuccess' : GlobalIR.initializeValues program.definitions
      (fuel + 1 + initializersBefore.length + 2)
      (List.replicate program.initializers.length none) 0 initializersBefore = .ok after := by
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using prefixSuccess
  have runFault := GlobalIR.run_reports_initializer_fault_after_prefix program (fuel + 1)
    initializersBefore (PolyIR.erase (.ite condition yes no)) [] after (.core .wrongShape)
    programInitializers prefixSuccess'
    (by simpa [PolyIR.erase] using runtimeFault)
  exact ⟨decoded, sourceFault, by
    simpa [programInitializers, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using runFault⟩

theorem readClosedInitializer_valueReference_runtime_preserves_type
    (entries visible : List GlobalProgramEntry.Entry) (forms : List Node)
    (formIndex fuel selected index : Nat) (atom : CMacroCopy.Atom)
    (selectedNonzero : selected ≠ 0)
    (visibleResolved : sourceVisibleEntries entries forms formIndex = some visible)
    (uniqueCheck : GlobalProgramEntry.identitiesUniqueCheck entries = true)
    (valueMember : selected ∈ GlobalProgramEntry.valueIdentities visible)
    (decoded : readClosedInitializer entries visible [] (fuel + 1)
      (.atom atom selected) = some (.app (.global index []) []))
    (program : GlobalIR.Program) (globals : List Surface.Signature)
    (slotTypes : List Surface.Ty) (store : GlobalIR.Store) (value : PolyIR.Value)
    (programDefinitions : program.definitions = GlobalProgramEntry.toDefinitions 0 entries)
    (storeTyped : GlobalIR.StoreWellTyped globals slotTypes store)
    (initialized : ∀ type slot,
      (GlobalProgramEntry.compiledLayout 0 entries).get? index =
        some (⟨0, [], type⟩, GlobalIR.Definition.getter slot) →
      store[slot]? = some (some value))
    (layoutTyped : ∀ type slot,
      (GlobalProgramEntry.compiledLayout 0 entries).get? index =
        some (⟨0, [], type⟩, GlobalIR.Definition.getter slot) →
      globals[index]? = some ⟨0, [], type⟩ ∧ slotTypes[slot]? = some type) :
    ∃ type slot result,
      (GlobalProgramEntry.compiledLayout 0 entries).get? index =
        some (⟨0, [], type⟩, GlobalIR.Definition.getter slot) ∧
      program.definitions[index]? = some (.getter slot) ∧
      GlobalIR.evaluate program.definitions store (fuel + 2) []
        (PolyIR.erase (.app (.global index []) [])) = .ok result ∧
      PolyIR.ValueTyped globals result type := by
  obtain ⟨_entryValue, _globalFound, type, slot, layout⟩ :=
    readClosedInitializer_sourceVisibleValueReference_sound entries visible forms formIndex
      fuel selected index atom selectedNonzero visibleResolved uniqueCheck valueMember decoded
  have runtimeGetterLookup :
      (GlobalProgramEntry.toDefinitions 0 entries).get? index = some (.getter slot) :=
    GlobalProgramEntry.toDefinitions_getter_of_layout 0 entries index
      ⟨0, [], type⟩ slot layout
  have runtimeGetter :
      (GlobalProgramEntry.toDefinitions 0 entries)[index]? = some (.getter slot) := by
    rw [sourceGetElem?_eq_get?]
    exact runtimeGetterLookup
  obtain ⟨_signatureEntry, slotType⟩ := layoutTyped type slot layout
  obtain ⟨result, evaluated, resultTyped⟩ := GlobalIR.getter_call_preserves_type
    (GlobalProgramEntry.toDefinitions 0 entries) globals slotTypes store fuel index slot value type
    runtimeGetter slotType storeTyped (initialized type slot layout)
  refine ⟨type, slot, result, layout, ?_, ?_, resultTyped⟩
  · simpa [programDefinitions] using runtimeGetter
  · simpa [programDefinitions, PolyIR.erase] using evaluated

/-- A decoded source value reference is safe after it is translated through
the mixed-entry layout: with a well-typed, layout-sized store it either
returns a value of the declared slot type or reports the precise
before-initialization fault. -/
theorem readClosedInitializer_valueReference_runtime_type_safe_or_early_read
    (entries visible : List GlobalProgramEntry.Entry) (forms : List Node)
    (formIndex fuel selected index : Nat) (atom : CMacroCopy.Atom)
    (selectedNonzero : selected ≠ 0)
    (visibleResolved : sourceVisibleEntries entries forms formIndex = some visible)
    (uniqueCheck : GlobalProgramEntry.identitiesUniqueCheck entries = true)
    (valueMember : selected ∈ GlobalProgramEntry.valueIdentities visible)
    (decoded : readClosedInitializer entries visible [] (fuel + 1)
      (.atom atom selected) = some (.app (.global index []) []))
    (program : GlobalIR.Program) (globals : List Surface.Signature)
    (slotTypes : List Surface.Ty) (store : GlobalIR.Store)
    (programDefinitions : program.definitions = GlobalProgramEntry.toDefinitions 0 entries)
    (storeTyped : GlobalIR.StoreWellTyped globals slotTypes store)
    (storeLayout : store.length = slotTypes.length)
    (layoutTyped : ∀ type slot,
      (GlobalProgramEntry.compiledLayout 0 entries).get? index =
        some (⟨0, [], type⟩, GlobalIR.Definition.getter slot) →
      globals[index]? = some ⟨0, [], type⟩ ∧ slotTypes[slot]? = some type) :
    ∃ type slot,
      (GlobalProgramEntry.compiledLayout 0 entries).get? index =
        some (⟨0, [], type⟩, GlobalIR.Definition.getter slot) ∧
      program.definitions[index]? = some (.getter slot) ∧
      ((∃ result,
          GlobalIR.evaluate program.definitions store (fuel + 2) []
            (PolyIR.erase (.app (.global index []) [])) = .ok result ∧
          PolyIR.ValueTyped globals result type) ∨
        GlobalIR.evaluate program.definitions store (fuel + 2) []
          (PolyIR.erase (.app (.global index []) [])) =
            .error (.beforeInitialization slot)) := by
  obtain ⟨_entryValue, _globalFound, type, slot, layout⟩ :=
    readClosedInitializer_sourceVisibleValueReference_sound entries visible forms formIndex
      fuel selected index atom selectedNonzero visibleResolved uniqueCheck valueMember decoded
  have runtimeGetterLookup :
      (GlobalProgramEntry.toDefinitions 0 entries).get? index = some (.getter slot) :=
    GlobalProgramEntry.toDefinitions_getter_of_layout 0 entries index
      ⟨0, [], type⟩ slot layout
  have runtimeGetter :
      (GlobalProgramEntry.toDefinitions 0 entries)[index]? = some (.getter slot) := by
    rw [sourceGetElem?_eq_get?]
    exact runtimeGetterLookup
  obtain ⟨_signatureEntry, slotType⟩ := layoutTyped type slot layout
  have slotTypeGet : slotTypes.get? slot = some type := by
    rw [← sourceGetElem?_eq_get?]
    exact slotType
  have slotBound : slot < slotTypes.length := (List.get?_eq_some.mp slotTypeGet).1
  have storeBound : slot < store.length := by omega
  have slotPresent : (store[slot]?).isSome = true := by
    simp [getElem?_def, storeBound]
  refine ⟨type, slot, layout, ?_, ?_⟩
  · simpa [programDefinitions] using runtimeGetter
  · cases cell : store[slot]? with
    | none =>
        have contradiction : (store[slot]?).isSome = false := by simp [cell]
        rw [contradiction] at slotPresent
        cases slotPresent
    | some contents =>
        cases contents with
        | none =>
            right
            have early := GlobalIR.getter_call_reports_early_read
              (GlobalProgramEntry.toDefinitions 0 entries) store fuel index slot
              runtimeGetter (by simp [cell])
            simpa [programDefinitions, PolyIR.erase] using early
        | some value =>
            left
            have initialized : store[slot]? = some (some value) := by simp [cell]
            obtain ⟨result, evaluated, resultTyped⟩ := GlobalIR.getter_call_preserves_type
              (GlobalProgramEntry.toDefinitions 0 entries) globals slotTypes store fuel
              index slot value type runtimeGetter slotType storeTyped initialized
            exact ⟨result, by simpa [programDefinitions, PolyIR.erase] using evaluated,
              resultTyped⟩

theorem readClosedInitializer_valueReference_reads_current_store
    (entries visible : List GlobalProgramEntry.Entry)
    (fuel selected sourceIndex : Nat) (atom : CMacroCopy.Atom)
    (getters : List (Nat × Nat))
    (program : List GlobalIR.Definition) (store : GlobalIR.Store)
    (getterIndex slot : Nat) (value : PolyIR.Value)
    (decoded : readClosedInitializer entries visible [] (fuel + 1)
      (.atom atom selected) = some (.app (.global sourceIndex []) []))
    (mapped : GlobalIR.getterFor getters sourceIndex = some getterIndex)
    (getter : program[getterIndex]? = some (.getter slot))
    (initialized : store[slot]? = some (some value)) :
    readClosedInitializer entries visible [] (fuel + 1) (.atom atom selected) =
        some (.app (.global sourceIndex []) []) ∧
      GlobalIR.evaluate program store (fuel + 2) []
        (GlobalIR.lowerGlobalReads getters
          (PolyIR.erase (.app (.global sourceIndex []) []))) = .ok value := by
  exact ⟨decoded, GlobalIR.lowered_surface_value_reference_reads_current_store getters
    program store fuel sourceIndex getterIndex slot value mapped getter initialized⟩

/- The parsed Node, its decoding equation, and the erasure equation travel
together so the caller cannot detach the converted initializer from its input. -/
structure LoweredClosedValue (entries : List GlobalProgramEntry.Entry) where
  visibleEntries : List GlobalProgramEntry.Entry
  sourceForm : Node
  decodeFuel : Nat
  definition : ClosedValueDefinition
  source_decodes : readClosedValueDefinition decodeFuel entries visibleEntries
    sourceForm = some definition
  initializer : GlobalProgramEntry.TypedInitializer entries definition.type definition.expression
  checkerAccepted : GlobalProgramEntry.checkInitializer decodeFuel entries
    definition.expression definition.type = some initializer
  erasure : initializer.term = PolyIR.erase definition.expression

def LoweredClosedValue.toGlobalProgramEntry
    (value : LoweredClosedValue entries) : GlobalProgramEntry.Entry :=
  value.definition.toGlobalProgramEntry

def lowerClosedValueDefinition (fuel : Nat) (entries visible : List GlobalProgramEntry.Entry)
    (form : Node) : Option (LoweredClosedValue entries) :=
  match decoded : readClosedValueDefinition fuel entries visible form with
  | none => none
  | some definition =>
      match checked : GlobalProgramEntry.checkInitializer fuel entries
          definition.expression definition.type with
      | none => none
      | some initializer =>
          some ⟨visible, form, fuel, definition, decoded, initializer,
            checked, by rw [initializer.erasure, initializer.sourceExact]⟩

theorem lowerClosedValueDefinition_checker_sound
    (fuel : Nat) (entries visible : List GlobalProgramEntry.Entry) (form : Node)
    (lowered : LoweredClosedValue entries)
    (accepted : lowerClosedValueDefinition fuel entries visible form = some lowered) :
    GlobalProgramEntry.checkInitializer fuel entries
      lowered.definition.expression lowered.definition.type = some lowered.initializer := by
  simp only [lowerClosedValueDefinition] at accepted
  split at accepted
  · contradiction
  · split at accepted
    · contradiction
    · cases accepted
      assumption

def lowerClosedValueDefinitionAt (fuel : Nat) (entries : List GlobalProgramEntry.Entry)
    (forms : List Node) (formIndex : Nat) : Option (LoweredClosedValue entries) := do
  let form ← forms[formIndex]?
  let visible ← sourceVisibleEntries entries forms formIndex
  lowerClosedValueDefinition fuel entries visible form

/- Replace a declaration's initializer while retaining its source-order row.
The replacement must be a value entry with the same identity and cell type. -/
def replaceValueEntry (replacement : GlobalProgramEntry.Entry) :
    List GlobalProgramEntry.Entry → Option (List GlobalProgramEntry.Entry)
  | [] => none
  | .function identity signature signatureValid definition :: tail => do
      let replaced ← replaceValueEntry replacement tail
      pure (.function identity signature signatureValid definition :: replaced)
  | .value identity type typeValid expression :: tail =>
      match replacement with
      | .function _ _ _ _ => none
      | .value replacementIdentity replacementType _ _ =>
          if identity = replacementIdentity then
            if type = replacementType then
              some (replacement :: tail)
            else none
          else do
            let replaced ← replaceValueEntry replacement tail
            pure (.value identity type typeValid expression :: replaced)

theorem replaceValueEntry_replacement_identity_mem
    (replacement : GlobalProgramEntry.Entry) (entries result : List GlobalProgramEntry.Entry)
    (replaced : replaceValueEntry replacement entries = some result)
    (replacementIsValue : ∃ identity type valid expression,
      replacement = .value identity type valid expression) :
    ∃ type, GlobalProgramEntry.valueSlotOf
      (GlobalProgramEntry.identity replacement) 0 result = some type := by
  rcases replacementIsValue with ⟨wanted, replacementType, replacementValid,
    replacementExpression, rfl⟩
  induction entries generalizing result with
  | nil => simp [replaceValueEntry] at replaced
  | cons head tail ih =>
      cases head with
      | function identity signature valid definition =>
          cases tailResult : replaceValueEntry
              (.value wanted replacementType replacementValid replacementExpression) tail with
          | none => simp [replaceValueEntry, tailResult] at replaced
          | some tailOutput =>
              have outputEq :
                  .function identity signature valid definition :: tailOutput = result := by
                simpa [replaceValueEntry, tailResult] using replaced
              cases outputEq
              obtain ⟨slot, found⟩ := ih tailOutput tailResult
              exact ⟨slot, by simpa [GlobalProgramEntry.valueSlotOf] using found⟩
      | value identity type typeValid initializer =>
          by_cases same : identity = wanted
          · subst identity
            have resultInfo : type = replacementType ∧
                .value wanted replacementType replacementValid replacementExpression :: tail = result := by
              simpa [replaceValueEntry] using replaced
            have resultEq :
                .value wanted replacementType replacementValid replacementExpression :: tail = result := by
              exact resultInfo.2
            cases resultEq
            exact ⟨0, by simp [GlobalProgramEntry.valueSlotOf,
              GlobalProgramEntry.identity]⟩
          · cases tailResult : replaceValueEntry
                (.value wanted replacementType replacementValid replacementExpression) tail with
            | none => simp [replaceValueEntry, same, tailResult] at replaced
            | some tailOutput =>
                have outputEq :
                    .value identity type typeValid initializer :: tailOutput = result := by
                  simpa [replaceValueEntry, same, tailResult] using replaced
                cases outputEq
                obtain ⟨slot, found⟩ := ih tailOutput tailResult
                have found' : GlobalProgramEntry.valueSlotOf wanted 0 tailOutput = some slot := by
                  simpa [GlobalProgramEntry.identity] using found
                have shifted := GlobalProgramEntry.valueSlotOf_shift wanted 0 1 tailOutput
                rw [found'] at shifted
                exact ⟨slot + 1, by
                  simpa [GlobalProgramEntry.valueSlotOf, GlobalProgramEntry.identity,
                    same] using shifted⟩

/- Keep the proof-carrying decoded initializer attached to the updated table.
The ordinary entry list is useful to execute; this wrapper retains the source
form, typed Surface expression, and erasure equation that justify its update. -/
structure CertifiedValueReplacement (entries : List GlobalProgramEntry.Entry) where
  converted : LoweredClosedValue entries
  result : List GlobalProgramEntry.Entry
  replaced : replaceValueEntry converted.toGlobalProgramEntry entries = some result

structure TypedInitializerAtSlot (entries : List GlobalProgramEntry.Entry)
    (identity : Nat) (type : Surface.Ty) (source : Surface.Expr) where
  slot : Nat
  slot_found : GlobalProgramEntry.valueSlotOf identity 0 entries = some slot
  initializer : GlobalProgramEntry.TypedInitializer entries type source

def lowerAndReplaceValueAtCertified (fuel : Nat) (entries : List GlobalProgramEntry.Entry)
    (forms : List Node) (formIndex : Nat) : Option (CertifiedValueReplacement entries) := do
  let converted ← lowerClosedValueDefinitionAt fuel entries forms formIndex
  match h : replaceValueEntry converted.toGlobalProgramEntry entries with
  | none => none
  | some result => some ⟨converted, result, h⟩

theorem replaceValueEntry_preserves_length (replacement : GlobalProgramEntry.Entry)
    (entries result : List GlobalProgramEntry.Entry)
    (replaced : replaceValueEntry replacement entries = some result) :
    result.length = entries.length := by
  induction entries generalizing result with
  | nil => simp [replaceValueEntry] at replaced
  | cons entry tail ih =>
      cases entry with
      | function identity signature signatureValid definition =>
          cases tailResult : replaceValueEntry replacement tail with
          | none => simp [replaceValueEntry, tailResult] at replaced
          | some replacedTail =>
              simp [replaceValueEntry, tailResult] at replaced
              have sameResult : result = .function identity signature signatureValid definition :: replacedTail :=
                replaced.symm
              subst result
              have tailLength := ih replacedTail tailResult
              simp [tailLength]
      | value identity type typeValid expression =>
          cases replacement with
          | function replacementIdentity signature signatureValid definition =>
              simp [replaceValueEntry] at replaced
          | value replacementIdentity replacementType replacementValid replacementExpression =>
              by_cases sameIdentity : identity = replacementIdentity
              · by_cases sameType : type = replacementType
                · simp [replaceValueEntry, sameIdentity, sameType] at replaced
                  cases replaced
                  simp
                · simp [replaceValueEntry, sameIdentity, sameType] at replaced
              · cases tailResult : replaceValueEntry
                    (.value replacementIdentity replacementType replacementValid replacementExpression) tail with
                | none => simp [replaceValueEntry, sameIdentity, tailResult] at replaced
                | some replacedTail =>
                    simp [replaceValueEntry, sameIdentity, tailResult] at replaced
                    have sameResult : result = .value identity type typeValid expression :: replacedTail :=
                      replaced.symm
                    subst result
                    have tailLength := ih replacedTail tailResult
                    simp [tailLength]

theorem replaceValueEntry_preserves_identities (replacement : GlobalProgramEntry.Entry)
    (entries result : List GlobalProgramEntry.Entry)
    (replaced : replaceValueEntry replacement entries = some result) :
    GlobalProgramEntry.identities result = GlobalProgramEntry.identities entries := by
  induction entries generalizing result with
  | nil => simp [replaceValueEntry] at replaced
  | cons entry tail ih =>
      cases entry with
      | function identity signature signatureValid definition =>
          cases tailResult : replaceValueEntry replacement tail with
          | none => simp [replaceValueEntry, tailResult] at replaced
          | some replacedTail =>
              simp [replaceValueEntry, tailResult] at replaced
              have sameResult : result = .function identity signature signatureValid definition :: replacedTail :=
                replaced.symm
              subst result
              have tailIds := ih replacedTail tailResult
              change identity :: GlobalProgramEntry.identities replacedTail =
                identity :: GlobalProgramEntry.identities tail
              exact congrArg (List.cons identity) tailIds
      | value identity type typeValid expression =>
          cases replacement with
          | function replacementIdentity signature signatureValid definition =>
              simp [replaceValueEntry] at replaced
          | value replacementIdentity replacementType replacementValid replacementExpression =>
              by_cases sameIdentity : identity = replacementIdentity
              · by_cases sameType : type = replacementType
                · simp [replaceValueEntry, sameIdentity, sameType] at replaced
                  have headIdentity : replacementIdentity = identity := sameIdentity.symm
                  cases replaced
                  subst replacementType
                  subst replacementIdentity
                  rfl
                · simp [replaceValueEntry, sameIdentity, sameType] at replaced
              · cases tailResult : replaceValueEntry
                    (.value replacementIdentity replacementType replacementValid replacementExpression) tail with
                | none => simp [replaceValueEntry, sameIdentity, tailResult] at replaced
                | some replacedTail =>
                    simp [replaceValueEntry, sameIdentity, tailResult] at replaced
                    have sameResult : result = .value identity type typeValid expression :: replacedTail :=
                      replaced.symm
                    subst result
                    have tailIds := ih replacedTail tailResult
                    change identity :: GlobalProgramEntry.identities replacedTail =
                      identity :: GlobalProgramEntry.identities tail
                    exact congrArg (List.cons identity) tailIds

theorem replaceValueEntry_preserves_valueIdentities (replacement : GlobalProgramEntry.Entry)
    (entries result : List GlobalProgramEntry.Entry)
    (replaced : replaceValueEntry replacement entries = some result) :
    GlobalProgramEntry.valueIdentities result = GlobalProgramEntry.valueIdentities entries := by
  induction entries generalizing result with
  | nil => simp [replaceValueEntry] at replaced
  | cons entry tail ih =>
      cases entry with
      | function identity signature signatureValid definition =>
          cases tailResult : replaceValueEntry replacement tail with
          | none => simp [replaceValueEntry, tailResult] at replaced
          | some replacedTail =>
              simp [replaceValueEntry, tailResult] at replaced
              have sameResult : result = .function identity signature signatureValid definition :: replacedTail :=
                replaced.symm
              subst result
              have tailValues := ih replacedTail tailResult
              change GlobalProgramEntry.valueIdentities replacedTail =
                GlobalProgramEntry.valueIdentities tail
              exact tailValues
      | value identity type typeValid expression =>
          cases replacement with
          | function replacementIdentity signature signatureValid definition =>
              simp [replaceValueEntry] at replaced
          | value replacementIdentity replacementType replacementValid replacementExpression =>
              by_cases sameIdentity : identity = replacementIdentity
              · by_cases sameType : type = replacementType
                · simp [replaceValueEntry, sameIdentity, sameType] at replaced
                  cases replaced
                  subst replacementIdentity
                  subst replacementType
                  rfl
                · simp [replaceValueEntry, sameIdentity, sameType] at replaced
              · cases tailResult : replaceValueEntry
                    (.value replacementIdentity replacementType replacementValid replacementExpression) tail with
                | none => simp [replaceValueEntry, sameIdentity, tailResult] at replaced
                | some replacedTail =>
                    simp [replaceValueEntry, sameIdentity, tailResult] at replaced
                    have sameResult : result = .value identity type typeValid expression :: replacedTail :=
                      replaced.symm
                    subst result
                    have tailValues := ih replacedTail tailResult
                    change identity :: GlobalProgramEntry.valueIdentities replacedTail =
                      identity :: GlobalProgramEntry.valueIdentities tail
                    exact congrArg (List.cons identity) tailValues

theorem replaceValueEntry_preserves_compiledLayout (replacement : GlobalProgramEntry.Entry)
    (start : Nat) (entries result : List GlobalProgramEntry.Entry)
    (replaced : replaceValueEntry replacement entries = some result) :
    GlobalProgramEntry.compiledLayout start result =
      GlobalProgramEntry.compiledLayout start entries := by
  induction entries generalizing result start with
  | nil => simp [replaceValueEntry] at replaced
  | cons entry tail ih =>
      cases entry with
      | function identity signature signatureValid definition =>
          cases tailResult : replaceValueEntry replacement tail with
          | none => simp [replaceValueEntry, tailResult] at replaced
          | some replacedTail =>
              simp [replaceValueEntry, tailResult] at replaced
              have sameResult : result = .function identity signature signatureValid definition :: replacedTail :=
                replaced.symm
              subst result
              have tailLayout := ih start replacedTail tailResult
              simp [GlobalProgramEntry.compiledLayout, tailLayout]
      | value identity type typeValid expression =>
          cases replacement with
          | function replacementIdentity signature signatureValid definition =>
              simp [replaceValueEntry] at replaced
          | value replacementIdentity replacementType replacementValid replacementExpression =>
              by_cases sameIdentity : identity = replacementIdentity
              · by_cases sameType : type = replacementType
                · simp [replaceValueEntry, sameIdentity, sameType] at replaced
                  cases replaced
                  subst replacementIdentity
                  subst replacementType
                  simp [GlobalProgramEntry.compiledLayout]
                · simp [replaceValueEntry, sameIdentity, sameType] at replaced
              · cases tailResult : replaceValueEntry
                    (.value replacementIdentity replacementType replacementValid replacementExpression) tail with
                | none => simp [replaceValueEntry, sameIdentity, tailResult] at replaced
                | some replacedTail =>
                    simp [replaceValueEntry, sameIdentity, tailResult] at replaced
                    have sameResult : result = .value identity type typeValid expression :: replacedTail :=
                      replaced.symm
                    subst result
                    have tailLayout := ih (start + 1) replacedTail tailResult
                    simp [GlobalProgramEntry.compiledLayout, tailLayout]

theorem replaceValueEntry_preserves_valueTypes (replacement : GlobalProgramEntry.Entry)
    (entries result : List GlobalProgramEntry.Entry)
    (replaced : replaceValueEntry replacement entries = some result) :
    GlobalProgramEntry.valueTypes result = GlobalProgramEntry.valueTypes entries := by
  calc
    GlobalProgramEntry.valueTypes result =
        GlobalProgramEntry.compiledGetterTypes (GlobalProgramEntry.compiledLayout 0 result) :=
      (GlobalProgramEntry.compiledGetterTypes_compiledLayout 0 result).symm
    _ = GlobalProgramEntry.compiledGetterTypes (GlobalProgramEntry.compiledLayout 0 entries) :=
      congrArg GlobalProgramEntry.compiledGetterTypes
        (replaceValueEntry_preserves_compiledLayout replacement 0 entries result replaced)
    _ = GlobalProgramEntry.valueTypes entries :=
      GlobalProgramEntry.compiledGetterTypes_compiledLayout 0 entries

theorem CertifiedValueReplacement.preserves_layout
    (certificate : CertifiedValueReplacement entries) (start : Nat) :
    GlobalProgramEntry.compiledLayout start certificate.result =
      GlobalProgramEntry.compiledLayout start entries :=
  replaceValueEntry_preserves_compiledLayout certificate.converted.toGlobalProgramEntry
    start entries certificate.result certificate.replaced

/- Replacing an initializer changes only expression payloads: the compiled
signature layout is unchanged, so the initializer's type derivation can be
transported from the table used while decoding it to the resulting table. -/
def CertifiedValueReplacement.initializer_typed_in_result
    (certificate : CertifiedValueReplacement entries) :
    GlobalProgramEntry.TypedInitializer certificate.result
      certificate.converted.definition.type certificate.converted.definition.expression := by
  have sameResultLayout :
      GlobalProgramEntry.compiledLayout 0 certificate.result =
        GlobalProgramEntry.compiledLayout 0 entries := certificate.preserves_layout 0
  have sameSignatures : GlobalProgramEntry.signatures entries =
      GlobalProgramEntry.signatures certificate.result :=
    (GlobalProgramEntry.signatures_eq_of_compiledLayout_eq
      certificate.result entries sameResultLayout).symm
  exact GlobalProgramEntry.TypedInitializer.transport sameSignatures
    certificate.converted.initializer

noncomputable def CertifiedValueReplacement.initializer_at_slot
    (certificate : CertifiedValueReplacement entries) :
    TypedInitializerAtSlot certificate.result certificate.converted.definition.identity
      certificate.converted.definition.type certificate.converted.definition.expression := by
  let slotExists := replaceValueEntry_replacement_identity_mem
    certificate.converted.toGlobalProgramEntry entries certificate.result certificate.replaced
    ⟨certificate.converted.definition.identity, certificate.converted.definition.type,
      certificate.converted.definition.typeValid, certificate.converted.definition.expression,
      rfl⟩
  let slot := Classical.choose slotExists
  exact ⟨slot, Classical.choose_spec slotExists, certificate.initializer_typed_in_result⟩

theorem CertifiedValueReplacement.preserves_length
    (certificate : CertifiedValueReplacement entries) :
    certificate.result.length = entries.length :=
  replaceValueEntry_preserves_length certificate.converted.toGlobalProgramEntry
    entries certificate.result certificate.replaced

theorem CertifiedValueReplacement.preserves_identities
    (certificate : CertifiedValueReplacement entries) :
    GlobalProgramEntry.identities certificate.result = GlobalProgramEntry.identities entries :=
  replaceValueEntry_preserves_identities certificate.converted.toGlobalProgramEntry
    entries certificate.result certificate.replaced

theorem CertifiedValueReplacement.preserves_valueIdentities
    (certificate : CertifiedValueReplacement entries) :
    GlobalProgramEntry.valueIdentities certificate.result =
      GlobalProgramEntry.valueIdentities entries :=
  replaceValueEntry_preserves_valueIdentities certificate.converted.toGlobalProgramEntry
    entries certificate.result certificate.replaced

theorem CertifiedValueReplacement.preserves_value_types
    (certificate : CertifiedValueReplacement entries) :
    GlobalProgramEntry.valueTypes certificate.result = GlobalProgramEntry.valueTypes entries :=
  replaceValueEntry_preserves_valueTypes certificate.converted.toGlobalProgramEntry
    entries certificate.result certificate.replaced

def lowerAndReplaceValueAt (fuel : Nat) (entries : List GlobalProgramEntry.Entry)
    (forms : List Node) (formIndex : Nat) : Option (List GlobalProgramEntry.Entry) := do
  let lowered ← lowerClosedValueDefinitionAt fuel entries forms formIndex
  replaceValueEntry lowered.toGlobalProgramEntry entries

theorem lowerAndReplaceValueAt_preserves_length (fuel : Nat)
    (entries result : List GlobalProgramEntry.Entry) (forms : List Node) (formIndex : Nat)
    (accepted : lowerAndReplaceValueAt fuel entries forms formIndex = some result) :
    result.length = entries.length := by
  unfold lowerAndReplaceValueAt at accepted
  cases lowered : lowerClosedValueDefinitionAt fuel entries forms formIndex with
  | none => simp [lowered] at accepted
  | some value =>
      have replaced : replaceValueEntry value.toGlobalProgramEntry entries = some result := by
        simpa [lowered] using accepted
      exact replaceValueEntry_preserves_length value.toGlobalProgramEntry entries result replaced

theorem lowerAndReplaceValueAt_preserves_identities (fuel : Nat)
    (entries result : List GlobalProgramEntry.Entry) (forms : List Node) (formIndex : Nat)
    (accepted : lowerAndReplaceValueAt fuel entries forms formIndex = some result) :
    GlobalProgramEntry.identities result = GlobalProgramEntry.identities entries := by
  unfold lowerAndReplaceValueAt at accepted
  cases lowered : lowerClosedValueDefinitionAt fuel entries forms formIndex with
  | none => simp [lowered] at accepted
  | some value =>
      have replaced : replaceValueEntry value.toGlobalProgramEntry entries = some result := by
        simpa [lowered] using accepted
      exact replaceValueEntry_preserves_identities value.toGlobalProgramEntry entries result replaced

theorem lowerAndReplaceValueAt_preserves_valueIdentities (fuel : Nat)
    (entries result : List GlobalProgramEntry.Entry) (forms : List Node) (formIndex : Nat)
    (accepted : lowerAndReplaceValueAt fuel entries forms formIndex = some result) :
    GlobalProgramEntry.valueIdentities result = GlobalProgramEntry.valueIdentities entries := by
  unfold lowerAndReplaceValueAt at accepted
  cases lowered : lowerClosedValueDefinitionAt fuel entries forms formIndex with
  | none => simp [lowered] at accepted
  | some value =>
      have replaced : replaceValueEntry value.toGlobalProgramEntry entries = some result := by
        simpa [lowered] using accepted
      exact replaceValueEntry_preserves_valueIdentities value.toGlobalProgramEntry entries result replaced

theorem lowerAndReplaceValueAt_preserves_compiledLayout (fuel start : Nat)
    (entries result : List GlobalProgramEntry.Entry) (forms : List Node) (formIndex : Nat)
    (accepted : lowerAndReplaceValueAt fuel entries forms formIndex = some result) :
    GlobalProgramEntry.compiledLayout start result =
      GlobalProgramEntry.compiledLayout start entries := by
  unfold lowerAndReplaceValueAt at accepted
  cases lowered : lowerClosedValueDefinitionAt fuel entries forms formIndex with
  | none => simp [lowered] at accepted
  | some value =>
      have replaced : replaceValueEntry value.toGlobalProgramEntry entries = some result := by
        simpa [lowered] using accepted
      exact replaceValueEntry_preserves_compiledLayout value.toGlobalProgramEntry start
        entries result replaced

/- Convert all source value declarations in order. Each converted initializer
sees the declaration table produced by earlier conversions, while source
visibility is still taken from CBindingWalk at the original form position. -/
def lowerAndReplaceValuesFrom (fuel : Nat) (allForms : List Node) :
    List Node → Nat → List GlobalProgramEntry.Entry → Option (List GlobalProgramEntry.Entry)
  | [], _, entries => some entries
  | form :: tail, index, entries => do
      let next ← match CBindingWalk.valueParts form with
        | none => some entries
        | some _ => lowerAndReplaceValueAt fuel entries allForms index
      lowerAndReplaceValuesFrom fuel allForms tail (index + 1) next

theorem lowerAndReplaceValuesFrom_preserves_length (fuel : Nat) (allForms forms : List Node)
    (index : Nat) (entries result : List GlobalProgramEntry.Entry)
    (accepted : lowerAndReplaceValuesFrom fuel allForms forms index entries = some result) :
    result.length = entries.length := by
  induction forms generalizing index entries result with
  | nil => simp [lowerAndReplaceValuesFrom] at accepted; cases accepted; rfl
  | cons form tail ih =>
      cases formParts : CBindingWalk.valueParts form with
      | none =>
          have tailAccepted :
              lowerAndReplaceValuesFrom fuel allForms tail (index + 1) entries = some result := by
            simpa [lowerAndReplaceValuesFrom, formParts] using accepted
          exact ih (index + 1) entries result tailAccepted
      | some parts =>
          cases lowered : lowerAndReplaceValueAt fuel entries allForms index with
          | none => simp [lowerAndReplaceValuesFrom, formParts, lowered] at accepted
          | some next =>
              have tailAccepted :
                  lowerAndReplaceValuesFrom fuel allForms tail (index + 1) next = some result := by
                simpa [lowerAndReplaceValuesFrom, formParts, lowered] using accepted
              have tailLength := ih (index + 1) next result tailAccepted
              have currentLength := lowerAndReplaceValueAt_preserves_length fuel entries next
                allForms index lowered
              omega

theorem lowerAndReplaceValuesFrom_preserves_identities (fuel : Nat) (allForms forms : List Node)
    (index : Nat) (entries result : List GlobalProgramEntry.Entry)
    (accepted : lowerAndReplaceValuesFrom fuel allForms forms index entries = some result) :
    GlobalProgramEntry.identities result = GlobalProgramEntry.identities entries := by
  induction forms generalizing index entries result with
  | nil => simp [lowerAndReplaceValuesFrom] at accepted; cases accepted; rfl
  | cons form tail ih =>
      cases formParts : CBindingWalk.valueParts form with
      | none =>
          have tailAccepted :
              lowerAndReplaceValuesFrom fuel allForms tail (index + 1) entries = some result := by
            simpa [lowerAndReplaceValuesFrom, formParts] using accepted
          exact ih (index + 1) entries result tailAccepted
      | some parts =>
          cases lowered : lowerAndReplaceValueAt fuel entries allForms index with
          | none => simp [lowerAndReplaceValuesFrom, formParts, lowered] at accepted
          | some next =>
              have tailAccepted :
                  lowerAndReplaceValuesFrom fuel allForms tail (index + 1) next = some result := by
                simpa [lowerAndReplaceValuesFrom, formParts, lowered] using accepted
              have tailIds := ih (index + 1) next result tailAccepted
              have currentIds := lowerAndReplaceValueAt_preserves_identities fuel entries next
                allForms index lowered
              exact tailIds.trans currentIds

theorem lowerAndReplaceValuesFrom_preserves_valueIdentities (fuel : Nat)
    (allForms forms : List Node) (index : Nat)
    (entries result : List GlobalProgramEntry.Entry)
    (accepted : lowerAndReplaceValuesFrom fuel allForms forms index entries = some result) :
    GlobalProgramEntry.valueIdentities result = GlobalProgramEntry.valueIdentities entries := by
  induction forms generalizing index entries result with
  | nil => simp [lowerAndReplaceValuesFrom] at accepted; cases accepted; rfl
  | cons form tail ih =>
      cases formParts : CBindingWalk.valueParts form with
      | none =>
          have tailAccepted :
              lowerAndReplaceValuesFrom fuel allForms tail (index + 1) entries = some result := by
            simpa [lowerAndReplaceValuesFrom, formParts] using accepted
          exact ih (index + 1) entries result tailAccepted
      | some parts =>
          cases lowered : lowerAndReplaceValueAt fuel entries allForms index with
          | none => simp [lowerAndReplaceValuesFrom, formParts, lowered] at accepted
          | some next =>
              have tailAccepted :
                  lowerAndReplaceValuesFrom fuel allForms tail (index + 1) next = some result := by
                simpa [lowerAndReplaceValuesFrom, formParts, lowered] using accepted
              have tailIds := ih (index + 1) next result tailAccepted
              have currentIds := lowerAndReplaceValueAt_preserves_valueIdentities fuel entries next
                allForms index lowered
              exact tailIds.trans currentIds

theorem lowerAndReplaceValuesFrom_preserves_compiledLayout (fuel : Nat) (allForms forms : List Node)
    (index start : Nat) (entries result : List GlobalProgramEntry.Entry)
    (accepted : lowerAndReplaceValuesFrom fuel allForms forms index entries = some result) :
    GlobalProgramEntry.compiledLayout start result =
      GlobalProgramEntry.compiledLayout start entries := by
  induction forms generalizing index entries result with
  | nil => simp [lowerAndReplaceValuesFrom] at accepted; cases accepted; rfl
  | cons form tail ih =>
      cases formParts : CBindingWalk.valueParts form with
      | none =>
          have tailAccepted :
              lowerAndReplaceValuesFrom fuel allForms tail (index + 1) entries = some result := by
            simpa [lowerAndReplaceValuesFrom, formParts] using accepted
          exact ih (index + 1) entries result tailAccepted
      | some parts =>
          cases lowered : lowerAndReplaceValueAt fuel entries allForms index with
          | none => simp [lowerAndReplaceValuesFrom, formParts, lowered] at accepted
          | some next =>
              have tailAccepted :
                  lowerAndReplaceValuesFrom fuel allForms tail (index + 1) next = some result := by
                simpa [lowerAndReplaceValuesFrom, formParts, lowered] using accepted
              have tailLayout := ih (index + 1) next result tailAccepted
              have currentLayout := lowerAndReplaceValueAt_preserves_compiledLayout
                fuel start entries next allForms index lowered
              exact tailLayout.trans currentLayout

def lowerAndReplaceValues (fuel : Nat) (entries : List GlobalProgramEntry.Entry)
    (forms : List Node) : Option (List GlobalProgramEntry.Entry) := do
  let _ ← CBindingWalk.globals forms CBindingWalk.builtinEnvironment
  lowerAndReplaceValuesFrom fuel forms forms 0 entries

/- This pass retains the typed decode certificate for every initializer as
it replaces value entries in source order. -/
inductive CertifiedValueTrace : List GlobalProgramEntry.Entry →
    List GlobalProgramEntry.Entry → Type where
  | done (entries) : CertifiedValueTrace entries entries
  | skipped (rest : CertifiedValueTrace entries result) :
      CertifiedValueTrace entries result
  | replaced (certificate : CertifiedValueReplacement entries)
      (rest : CertifiedValueTrace certificate.result result) :
      CertifiedValueTrace entries result

def lowerAndReplaceValuesFromCertified (fuel : Nat) (allForms : List Node) :
    (forms : List Node) → Nat → (entries : List GlobalProgramEntry.Entry) →
    Option (Σ result, CertifiedValueTrace entries result)
  | [], _, entries => some ⟨entries, .done entries⟩
  | form :: tail, index, entries => do
      match CBindingWalk.valueParts form with
      | none =>
          let ⟨result, trace⟩ ← lowerAndReplaceValuesFromCertified fuel allForms
            tail (index + 1) entries
          pure ⟨result, .skipped trace⟩
      | some _ =>
          let certificate ← lowerAndReplaceValueAtCertified fuel entries allForms index
          let ⟨result, trace⟩ ← lowerAndReplaceValuesFromCertified fuel allForms
            tail (index + 1) certificate.result
          pure ⟨result, .replaced certificate trace⟩

def lowerAndReplaceValuesCertified (fuel : Nat) (entries : List GlobalProgramEntry.Entry)
    (forms : List Node) : Option (Σ result, CertifiedValueTrace entries result) := do
  let _ ← CBindingWalk.globals forms CBindingWalk.builtinEnvironment
  lowerAndReplaceValuesFromCertified fuel forms forms 0 entries

theorem CertifiedValueTrace.preserves_layout
    (trace : CertifiedValueTrace entries result) (start : Nat) :
    GlobalProgramEntry.compiledLayout start result =
      GlobalProgramEntry.compiledLayout start entries := by
  induction trace with
  | done => rfl
  | skipped _ ih => exact ih
  | replaced certificate _ ih => exact ih.trans (certificate.preserves_layout start)

/- Every replacement in the trace carries a checker-produced initializer.
Transport all of them to the final signature table; earlier replacements do
not change compiled signatures, even though they do change initializer ASTs. -/
def CertifiedValueTrace.typedInitializers
    (trace : CertifiedValueTrace entries result) :
    List (Σ identity : Nat, Σ type : Surface.Ty, Σ source : Surface.Expr,
      GlobalProgramEntry.TypedInitializer result type source) :=
  match trace with
  | .done _ => []
  | .skipped rest => rest.typedInitializers
  | .replaced certificate rest =>
      let layoutEq := rest.preserves_layout 0
      let signatureEq := GlobalProgramEntry.signatures_eq_of_compiledLayout_eq
        certificate.result result layoutEq.symm
      let typedAtStep := certificate.initializer_typed_in_result
      let typedAtEnd := GlobalProgramEntry.TypedInitializer.transport signatureEq typedAtStep
      ⟨certificate.converted.definition.identity,
        certificate.converted.definition.type,
        certificate.converted.definition.expression, typedAtEnd⟩ :: rest.typedInitializers

def CertifiedValueTrace.replacementCount : CertifiedValueTrace entries result → Nat
  | .done _ => 0
  | .skipped rest => rest.replacementCount
  | .replaced _ rest => rest.replacementCount + 1

theorem CertifiedValueTrace.typedInitializers_length
    (trace : CertifiedValueTrace entries result) :
    trace.typedInitializers.length = trace.replacementCount := by
  induction trace with
  | done => rfl
  | skipped rest ih => exact ih
  | replaced certificate rest ih => simp [typedInitializers, replacementCount, ih]

theorem CertifiedValueTrace.preserves_length
    (trace : CertifiedValueTrace entries result) : result.length = entries.length := by
  induction trace with
  | done => rfl
  | skipped _ ih => exact ih
  | replaced certificate _ ih => exact ih.trans certificate.preserves_length

theorem CertifiedValueTrace.preserves_identities
    (trace : CertifiedValueTrace entries result) :
    GlobalProgramEntry.identities result = GlobalProgramEntry.identities entries := by
  induction trace with
  | done => rfl
  | skipped _ ih => exact ih
  | replaced certificate _ ih => exact ih.trans certificate.preserves_identities

theorem CertifiedValueTrace.preserves_valueIdentities
    (trace : CertifiedValueTrace entries result) :
    GlobalProgramEntry.valueIdentities result = GlobalProgramEntry.valueIdentities entries := by
  induction trace with
  | done => rfl
  | skipped _ ih => exact ih
  | replaced certificate _ ih => exact ih.trans certificate.preserves_valueIdentities

theorem lowerAndReplaceValuesCertified_preserves_layout
    (entries : List GlobalProgramEntry.Entry)
    (converted : Σ result, CertifiedValueTrace entries result) :
    GlobalProgramEntry.compiledLayout 0 converted.1 =
      GlobalProgramEntry.compiledLayout 0 entries :=
  CertifiedValueTrace.preserves_layout converted.2 0

theorem lowerAndReplaceValuesCertified_preserves_length
    (entries : List GlobalProgramEntry.Entry)
    (converted : Σ result, CertifiedValueTrace entries result) :
    converted.1.length = entries.length :=
  CertifiedValueTrace.preserves_length converted.2

theorem lowerAndReplaceValuesCertified_preserves_identities
    (entries : List GlobalProgramEntry.Entry)
    (converted : Σ result, CertifiedValueTrace entries result) :
    GlobalProgramEntry.identities converted.1 = GlobalProgramEntry.identities entries :=
  CertifiedValueTrace.preserves_identities converted.2

theorem lowerAndReplaceValuesCertified_preserves_valueIdentities
    (entries : List GlobalProgramEntry.Entry)
    (converted : Σ result, CertifiedValueTrace entries result) :
    GlobalProgramEntry.valueIdentities converted.1 = GlobalProgramEntry.valueIdentities entries :=
  CertifiedValueTrace.preserves_valueIdentities converted.2

theorem lowerAndReplaceValuesCertified_preserves_valueTypes
    (entries : List GlobalProgramEntry.Entry)
    (converted : Σ result, CertifiedValueTrace entries result) :
    GlobalProgramEntry.valueTypes converted.1 = GlobalProgramEntry.valueTypes entries := by
  calc
    GlobalProgramEntry.valueTypes converted.1 =
        GlobalProgramEntry.compiledGetterTypes
          (GlobalProgramEntry.compiledLayout 0 converted.1) :=
      (GlobalProgramEntry.compiledGetterTypes_compiledLayout 0 converted.1).symm
    _ = GlobalProgramEntry.compiledGetterTypes
          (GlobalProgramEntry.compiledLayout 0 entries) := by
      rw [lowerAndReplaceValuesCertified_preserves_layout entries converted]
    _ = GlobalProgramEntry.valueTypes entries :=
      GlobalProgramEntry.compiledGetterTypes_compiledLayout 0 entries

theorem lowerAndReplaceValuesCertified_preserves_runtimeDefinitions
    (entries : List GlobalProgramEntry.Entry)
    (converted : Σ result, CertifiedValueTrace entries result) (start : Nat) :
    GlobalProgramEntry.toDefinitions start converted.1 =
      GlobalProgramEntry.toDefinitions start entries := by
  calc
    GlobalProgramEntry.toDefinitions start converted.1 =
        GlobalProgramEntry.compiledDefinitions
          (GlobalProgramEntry.compiledLayout start converted.1) :=
      GlobalProgramEntry.toDefinitions_eq_compiledDefinitions start converted.1
    _ = GlobalProgramEntry.compiledDefinitions
          (GlobalProgramEntry.compiledLayout start entries) :=
      congrArg GlobalProgramEntry.compiledDefinitions
        (CertifiedValueTrace.preserves_layout converted.2 start)
    _ = GlobalProgramEntry.toDefinitions start entries :=
      (GlobalProgramEntry.toDefinitions_eq_compiledDefinitions start entries).symm

theorem lowerAndReplaceValuesCertified_preserves_runtimeProgramLayout
    (entries : List GlobalProgramEntry.Entry)
    (converted : Σ result, CertifiedValueTrace entries result) (entryIndex : Nat) :
    (GlobalProgramEntry.toRuntimeProgram converted.1 entryIndex).definitions =
        (GlobalProgramEntry.toRuntimeProgram entries entryIndex).definitions ∧
      (GlobalProgramEntry.toRuntimeProgram converted.1 entryIndex).initializers.length =
        (GlobalProgramEntry.toRuntimeProgram entries entryIndex).initializers.length := by
  constructor
  · exact lowerAndReplaceValuesCertified_preserves_runtimeDefinitions entries converted 0
  · simp only [GlobalProgramEntry.toRuntimeProgram]
    rw [GlobalProgramEntry.initializerTerms_length, GlobalProgramEntry.initializerTerms_length,
      lowerAndReplaceValuesCertified_preserves_valueTypes entries converted]

theorem lowerAndReplaceValues_preserves_length (fuel : Nat) (entries result : List GlobalProgramEntry.Entry)
    (forms : List Node)
    (accepted : lowerAndReplaceValues fuel entries forms = some result) :
    result.length = entries.length := by
  unfold lowerAndReplaceValues at accepted
  cases parsed : CBindingWalk.globals forms CBindingWalk.builtinEnvironment with
  | none => simp [parsed] at accepted
  | some globals =>
      exact lowerAndReplaceValuesFrom_preserves_length fuel forms forms 0 entries result
        (by simpa [parsed] using accepted)

theorem lowerAndReplaceValues_preserves_identities (fuel : Nat)
    (entries result : List GlobalProgramEntry.Entry) (forms : List Node)
    (accepted : lowerAndReplaceValues fuel entries forms = some result) :
    GlobalProgramEntry.identities result = GlobalProgramEntry.identities entries := by
  unfold lowerAndReplaceValues at accepted
  cases parsed : CBindingWalk.globals forms CBindingWalk.builtinEnvironment with
  | none => simp [parsed] at accepted
  | some globals =>
      exact lowerAndReplaceValuesFrom_preserves_identities fuel forms forms 0 entries result
        (by simpa [parsed] using accepted)

theorem lowerAndReplaceValues_preserves_valueIdentities (fuel : Nat)
    (entries result : List GlobalProgramEntry.Entry) (forms : List Node)
    (accepted : lowerAndReplaceValues fuel entries forms = some result) :
    GlobalProgramEntry.valueIdentities result = GlobalProgramEntry.valueIdentities entries := by
  unfold lowerAndReplaceValues at accepted
  cases parsed : CBindingWalk.globals forms CBindingWalk.builtinEnvironment with
  | none => simp [parsed] at accepted
  | some globals =>
      exact lowerAndReplaceValuesFrom_preserves_valueIdentities fuel forms forms 0 entries result
        (by simpa [parsed] using accepted)

theorem lowerAndReplaceValues_preserves_compiledLayout (fuel start : Nat)
    (entries result : List GlobalProgramEntry.Entry) (forms : List Node)
    (accepted : lowerAndReplaceValues fuel entries forms = some result) :
    GlobalProgramEntry.compiledLayout start result =
      GlobalProgramEntry.compiledLayout start entries := by
  unfold lowerAndReplaceValues at accepted
  cases parsed : CBindingWalk.globals forms CBindingWalk.builtinEnvironment with
  | none => simp [parsed] at accepted
  | some globals =>
      exact lowerAndReplaceValuesFrom_preserves_compiledLayout fuel forms forms 0 start entries result
        (by simpa [parsed] using accepted)

theorem lowerAndReplaceValues_preserves_valueTypes (fuel : Nat)
    (entries result : List GlobalProgramEntry.Entry) (forms : List Node)
    (accepted : lowerAndReplaceValues fuel entries forms = some result) :
    GlobalProgramEntry.valueTypes result = GlobalProgramEntry.valueTypes entries := by
  calc
    GlobalProgramEntry.valueTypes result =
        GlobalProgramEntry.compiledGetterTypes (GlobalProgramEntry.compiledLayout 0 result) :=
      (GlobalProgramEntry.compiledGetterTypes_compiledLayout 0 result).symm
    _ = GlobalProgramEntry.compiledGetterTypes (GlobalProgramEntry.compiledLayout 0 entries) :=
      congrArg GlobalProgramEntry.compiledGetterTypes
        (lowerAndReplaceValues_preserves_compiledLayout fuel 0 entries result forms accepted)
    _ = GlobalProgramEntry.valueTypes entries :=
      GlobalProgramEntry.compiledGetterTypes_compiledLayout 0 entries

theorem lowerAndReplaceValues_preserves_runtimeDefinitions (fuel start : Nat)
    (entries result : List GlobalProgramEntry.Entry) (forms : List Node)
    (accepted : lowerAndReplaceValues fuel entries forms = some result) :
    GlobalProgramEntry.toDefinitions start result =
      GlobalProgramEntry.toDefinitions start entries := by
  calc
    GlobalProgramEntry.toDefinitions start result =
        GlobalProgramEntry.compiledDefinitions (GlobalProgramEntry.compiledLayout start result) :=
      GlobalProgramEntry.toDefinitions_eq_compiledDefinitions start result
    _ = GlobalProgramEntry.compiledDefinitions (GlobalProgramEntry.compiledLayout start entries) :=
      congrArg GlobalProgramEntry.compiledDefinitions
        (lowerAndReplaceValues_preserves_compiledLayout fuel start entries result forms accepted)
    _ = GlobalProgramEntry.toDefinitions start entries :=
      (GlobalProgramEntry.toDefinitions_eq_compiledDefinitions start entries).symm

theorem lowerAndReplaceValues_preserves_runtimeProgramLayout (fuel entryIndex : Nat)
    (entries result : List GlobalProgramEntry.Entry) (forms : List Node)
    (accepted : lowerAndReplaceValues fuel entries forms = some result) :
    (GlobalProgramEntry.toRuntimeProgram result entryIndex).definitions =
        (GlobalProgramEntry.toRuntimeProgram entries entryIndex).definitions ∧
      (GlobalProgramEntry.toRuntimeProgram result entryIndex).initializers.length =
        (GlobalProgramEntry.toRuntimeProgram entries entryIndex).initializers.length := by
  constructor
  · exact lowerAndReplaceValues_preserves_runtimeDefinitions fuel 0 entries result forms accepted
  · simp only [GlobalProgramEntry.toRuntimeProgram]
    rw [GlobalProgramEntry.initializerTerms_length, GlobalProgramEntry.initializerTerms_length,
      lowerAndReplaceValues_preserves_valueTypes fuel entries result forms accepted]

/-- Connect a successful mixed top-level decode and the checked initializer
rows of its corresponding source-order entry table to the concrete GlobalIR
runtime program. The correspondence equations expose the bridge from decoded
source initializers and slot types to the Entry representation. -/
theorem decodedTopLevelProgram_checkedRows_globalIR_layout
    (decodeFuel checkerFuel entryIndex : Nat) (forms : List Node)
    (definitions : NLisp.Named.Definitions) (slotTypes : List Surface.Ty)
    (initializers : List NLisp.Named.Expr) (entries : List GlobalProgramEntry.Entry)
    (decoded : NLisp.Named.decodeTopLevelProgram decodeFuel forms =
      some (definitions, slotTypes, initializers))
    (slotTypesAgree : slotTypes = GlobalProgramEntry.valueTypes entries)
    (rowsChecked : GlobalProgramEntry.checkInitializerRows checkerFuel entries
      (GlobalProgramEntry.valueTypes entries) 0 entries = true) :
    ∃ headers : ProgramHeaders,
      readProgramHeaders decodeFuel 0 forms = some headers ∧
      slotTypes = headers.globals.map GlobalHeader.type ∧
      slotTypes = GlobalProgramEntry.valueTypes entries ∧
      slotTypes.length = initializers.length ∧
      NLisp.Named.programWellScoped definitions ∧
      (∀ expression ∈ initializers,
        NLisp.Named.letLayoutsAligned expression = true) ∧
      GlobalProgramEntry.TypedInitializerRows entries
        (GlobalProgramEntry.valueTypes entries) 0 entries ∧
      GlobalIR.InitializerTypesAgree (GlobalProgramEntry.valueTypes entries) 0
        (GlobalProgramEntry.toRuntimeProgram entries entryIndex).initializers := by
  obtain ⟨headers, headersRead, headerTypesAgree, initializerCount,
    definitionsScoped, initializersAligned⟩ :=
    NLisp.Named.decodeTopLevelProgram_layout_and_initializer_conditions
      decodeFuel forms definitions slotTypes initializers decoded
  have checkedRows := GlobalProgramEntry.checkInitializerRows_sound checkerFuel
    entries (GlobalProgramEntry.valueTypes entries) 0 entries rowsChecked
  have typedRows := checkedRows.toTypedInitializerRows checkerFuel entries
    (GlobalProgramEntry.valueTypes entries) 0 entries
  have runtimeTypesAgree := typedRows.toRuntimeProgram_types_agree entries entryIndex
  exact ⟨headers, headersRead, headerTypesAgree, slotTypesAgree, initializerCount, definitionsScoped,
    initializersAligned, typedRows, runtimeTypesAgree⟩

/-- Executable-layout view of the decode/checker bridge. Besides the source
header and initializer conditions, it records the exact lengths and typing
invariant of the concrete GlobalIR program produced from the mixed entry
table. -/
theorem decodedTopLevelProgram_checkedRows_executable_layout
    (decodeFuel checkerFuel entryIndex : Nat) (forms : List Node)
    (definitions : NLisp.Named.Definitions) (slotTypes : List Surface.Ty)
    (initializers : List NLisp.Named.Expr) (entries : List GlobalProgramEntry.Entry)
    (decoded : NLisp.Named.decodeTopLevelProgram decodeFuel forms =
      some (definitions, slotTypes, initializers))
    (slotTypesAgree : slotTypes = GlobalProgramEntry.valueTypes entries)
    (rowsChecked : GlobalProgramEntry.checkInitializerRows checkerFuel entries
      (GlobalProgramEntry.valueTypes entries) 0 entries = true) :
    ∃ headers : ProgramHeaders,
      readProgramHeaders decodeFuel 0 forms = some headers ∧
      slotTypes = headers.globals.map GlobalHeader.type ∧
      slotTypes.length = initializers.length ∧
      (GlobalProgramEntry.toRuntimeProgram entries entryIndex).definitions.length =
        entries.length ∧
      (GlobalProgramEntry.toRuntimeProgram entries entryIndex).initializers.length =
        slotTypes.length ∧
      NLisp.Named.programWellScoped definitions ∧
      (∀ expression ∈ initializers, NLisp.Named.letLayoutsAligned expression = true) ∧
      GlobalProgramEntry.TypedInitializerRows entries
        (GlobalProgramEntry.valueTypes entries) 0 entries ∧
      GlobalIR.InitializerTypesAgree (GlobalProgramEntry.valueTypes entries) 0
        (GlobalProgramEntry.toRuntimeProgram entries entryIndex).initializers := by
  obtain ⟨headers, headersRead, headerTypesAgree, _slotTypesAgree, initializerCount,
    definitionsScoped, initializersAligned, typedRows, runtimeTypesAgree⟩ :=
    decodedTopLevelProgram_checkedRows_globalIR_layout decodeFuel checkerFuel entryIndex
      forms definitions slotTypes initializers entries decoded slotTypesAgree rowsChecked
  have runtimeLayout := GlobalProgramEntry.toRuntimeProgram_layout entries entryIndex
  have runtimeDefinitionCount :
      (GlobalProgramEntry.toRuntimeProgram entries entryIndex).definitions.length =
        entries.length := by
    rw [runtimeLayout.1]
    exact GlobalProgramEntry.toDefinitions_length 0 entries
  have runtimeInitializerCount :
      (GlobalProgramEntry.toRuntimeProgram entries entryIndex).initializers.length =
        slotTypes.length := by
    calc
      (GlobalProgramEntry.toRuntimeProgram entries entryIndex).initializers.length =
          (GlobalProgramEntry.valueTypes entries).length := runtimeLayout.2
      _ = slotTypes.length := by rw [← slotTypesAgree]
  exact ⟨headers, headersRead, headerTypesAgree, initializerCount, runtimeDefinitionCount,
    runtimeInitializerCount, definitionsScoped, initializersAligned, typedRows,
    runtimeTypesAgree⟩

/-- A successful mixed top-level decode, checked initializer rows, and the
actual GlobalIR initialization run compose to a well-typed initialized store.
The evaluator preservation premise is explicit: this theorem connects the
decoded source layout to the runtime store, while general initializer
evaluation safety is supplied separately. -/
theorem decodedTopLevelProgram_checkedRows_initialization_preserves_store
    (decodeFuel checkerFuel entryIndex initializerFuel : Nat) (forms : List Node)
    (definitions : NLisp.Named.Definitions) (slotTypes : List Surface.Ty)
    (initializers : List NLisp.Named.Expr) (entries : List GlobalProgramEntry.Entry)
    (globals : List Surface.Signature) (initializedStore : GlobalIR.Store)
    (decoded : NLisp.Named.decodeTopLevelProgram decodeFuel forms =
      some (definitions, slotTypes, initializers))
    (slotTypesAgree : slotTypes = GlobalProgramEntry.valueTypes entries)
    (rowsChecked : GlobalProgramEntry.checkInitializerRows checkerFuel entries
      (GlobalProgramEntry.valueTypes entries) 0 entries = true)
    (evaluationTyped : ∀ currentStore remaining expression value type,
      GlobalIR.evaluate (GlobalProgramEntry.toRuntimeProgram entries entryIndex).definitions
        currentStore remaining [] expression = .ok value →
        PolyIR.ValueTyped globals value type)
    (initialization : GlobalIR.initializeValues
      (GlobalProgramEntry.toRuntimeProgram entries entryIndex).definitions initializerFuel
      (List.replicate (GlobalProgramEntry.toRuntimeProgram entries entryIndex).initializers.length none)
      0 (GlobalProgramEntry.toRuntimeProgram entries entryIndex).initializers =
        .ok initializedStore) :
    initializers.length =
        (GlobalProgramEntry.toRuntimeProgram entries entryIndex).initializers.length ∧
      GlobalIR.StoreWellTyped globals slotTypes initializedStore ∧
      initializedStore.length = slotTypes.length := by
  obtain ⟨_headers, _headersRead, _headerTypes, _slotAgreement, initializerCount,
    _definitionsScoped, _initializersAligned, typedRows, _runtimeTypesAgree⟩ :=
    decodedTopLevelProgram_checkedRows_globalIR_layout decodeFuel checkerFuel entryIndex
      forms definitions slotTypes initializers entries decoded slotTypesAgree rowsChecked
  have initialized := GlobalProgramEntry.TypedInitializerRows.initialization_preserves_store_and_layout
    entries globals
    (GlobalProgramEntry.valueTypes entries)
    (GlobalProgramEntry.toRuntimeProgram entries entryIndex).definitions initializerFuel entries
    initializedStore typedRows (GlobalProgramEntry.initializerTerms_length entries)
    evaluationTyped (by
      simpa [GlobalProgramEntry.initializerTerms, GlobalProgramEntry.toRuntimeProgram] using initialization)
  have initializerLengths : initializers.length =
      (GlobalProgramEntry.toRuntimeProgram entries entryIndex).initializers.length := by
    calc
      initializers.length = slotTypes.length := initializerCount.symm
      _ = (GlobalProgramEntry.valueTypes entries).length := congrArg List.length slotTypesAgree
      _ = (GlobalProgramEntry.initializerTerms entries).length :=
        (GlobalProgramEntry.initializerTerms_length entries).symm
  exact ⟨initializerLengths, by simpa [slotTypesAgree] using initialized.1,
    by simpa [slotTypesAgree] using initialized.2⟩

/-- Combine successful mixed-source decoding, checker-accepted value rows,
the concrete GlobalIR layout, and a successful initialization run. Every
declared value slot is populated with a value of its declared type. The
evaluator-preservation premise remains explicit, so this theorem does not
silently assume general GlobalIR type safety. -/
theorem decodedTopLevelProgram_checkedRows_initialization_type_safe_and_populated
    (decodeFuel checkerFuel entryIndex initializerFuel : Nat) (forms : List Node)
    (definitions : NLisp.Named.Definitions) (slotTypes : List Surface.Ty)
    (initializers : List NLisp.Named.Expr) (entries : List GlobalProgramEntry.Entry)
    (globals : List Surface.Signature) (initializedStore : GlobalIR.Store)
    (decoded : NLisp.Named.decodeTopLevelProgram decodeFuel forms =
      some (definitions, slotTypes, initializers))
    (slotTypesAgree : slotTypes = GlobalProgramEntry.valueTypes entries)
    (rowsChecked : GlobalProgramEntry.checkInitializerRows checkerFuel entries
      (GlobalProgramEntry.valueTypes entries) 0 entries = true)
    (evaluationTyped : ∀ currentStore remaining expression value type,
      GlobalIR.evaluate (GlobalProgramEntry.toRuntimeProgram entries entryIndex).definitions
        currentStore remaining [] expression = .ok value →
        PolyIR.ValueTyped globals value type)
    (initialization : GlobalIR.initializeValues
      (GlobalProgramEntry.toRuntimeProgram entries entryIndex).definitions initializerFuel
      (List.replicate (GlobalProgramEntry.toRuntimeProgram entries entryIndex).initializers.length none)
      0 (GlobalProgramEntry.toRuntimeProgram entries entryIndex).initializers =
        .ok initializedStore) :
    (∃ headers : ProgramHeaders,
      readProgramHeaders decodeFuel 0 forms = some headers ∧
      slotTypes = headers.globals.map GlobalHeader.type ∧
      initializers.length = (GlobalProgramEntry.toRuntimeProgram entries entryIndex).initializers.length ∧
      (GlobalProgramEntry.toRuntimeProgram entries entryIndex).definitions.length = entries.length ∧
      (GlobalProgramEntry.toRuntimeProgram entries entryIndex).initializers.length = slotTypes.length ∧
      NLisp.Named.programWellScoped definitions ∧
      (∀ expression ∈ initializers, NLisp.Named.letLayoutsAligned expression = true) ∧
      GlobalIR.InitializerTypesAgree (GlobalProgramEntry.valueTypes entries) 0
        (GlobalProgramEntry.toRuntimeProgram entries entryIndex).initializers) ∧
    GlobalIR.StoreWellTyped globals slotTypes initializedStore ∧
    initializedStore.length = slotTypes.length ∧
    (∀ slot type, slotTypes.get? slot = some type →
      ∃ value, initializedStore.get? slot = some (some value) ∧
        PolyIR.ValueTyped globals value type) := by
  obtain ⟨headers, headersRead, headerTypes, initializerCount,
    definitionCount, runtimeInitializerCount, definitionsScoped, initializersAligned,
    _typedRows, runtimeTypesAgree⟩ :=
    decodedTopLevelProgram_checkedRows_executable_layout decodeFuel checkerFuel entryIndex
      forms definitions slotTypes initializers entries decoded slotTypesAgree rowsChecked
  have typedRows : GlobalProgramEntry.TypedInitializerRows entries
      (GlobalProgramEntry.valueTypes entries) 0 entries :=
    (GlobalProgramEntry.checkInitializerRows_sound checkerFuel entries
      (GlobalProgramEntry.valueTypes entries) 0 entries rowsChecked).toTypedInitializerRows
      checkerFuel entries (GlobalProgramEntry.valueTypes entries) 0 entries
  have runtimeEvaluationTyped : ∀ currentStore remaining expression value type,
      GlobalIR.evaluate (GlobalProgramEntry.toRuntimeProgram entries entryIndex).definitions
        currentStore remaining [] expression = .ok value →
        PolyIR.ValueTyped globals value type := evaluationTyped
  have sourceInitialization : GlobalIR.initializeValues
      (GlobalProgramEntry.toRuntimeProgram entries entryIndex).definitions initializerFuel
      (List.replicate (GlobalProgramEntry.initializerTerms entries).length none)
      0 (GlobalProgramEntry.initializerTerms entries) = .ok initializedStore := by
    simpa [GlobalProgramEntry.toRuntimeProgram, GlobalProgramEntry.initializerTerms] using initialization
  have initialized := typedRows.initialization_type_safe_and_populated entries globals
    (GlobalProgramEntry.valueTypes entries)
    (GlobalProgramEntry.toRuntimeProgram entries entryIndex).definitions initializerFuel entries
    initializedStore (GlobalProgramEntry.initializerTerms_length entries)
    runtimeEvaluationTyped sourceInitialization
  have sourceRuntimeInitializerCount : initializers.length =
      (GlobalProgramEntry.toRuntimeProgram entries entryIndex).initializers.length := by
    calc
      initializers.length = slotTypes.length := initializerCount.symm
      _ = (GlobalProgramEntry.toRuntimeProgram entries entryIndex).initializers.length :=
        runtimeInitializerCount.symm
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact ⟨headers, headersRead, headerTypes, sourceRuntimeInitializerCount, definitionCount,
      runtimeInitializerCount, definitionsScoped, initializersAligned, runtimeTypesAgree⟩
  · simpa [slotTypesAgree] using initialized.1
  · simpa [slotTypesAgree] using initialized.2.1
  · intro slot type slotType
    have slotType' : (GlobalProgramEntry.valueTypes entries).get? slot = some type := by
      simpa [slotTypesAgree] using slotType
    have slotTypeIndexed : (GlobalProgramEntry.valueTypes entries)[slot]? = some type := by
      rw [sourceGetElem?_eq_get?]
      exact slotType'
    obtain ⟨value, present, valueTyped⟩ := initialized.2.2 slot type slotTypeIndexed
    have presentGet : initializedStore.get? slot = some (some value) := by
      rw [← sourceGetElem?_eq_get?]
      exact present
    exact ⟨value, presentGet, valueTyped⟩

/-- Arithmetic initializer evidence itself supplies GlobalIR evaluator safety,
so the source decode/layout/init theorem can expose a typed populated store
without a separate theorem about every arbitrary initializer term. -/
theorem decodedTopLevelProgram_arithmeticRows_initialization_type_safe_and_populated
    (decodeFuel entryIndex initializerFuel : Nat) (forms : List Node)
    (definitions : NLisp.Named.Definitions) (slotTypes : List Surface.Ty)
    (initializers : List NLisp.Named.Expr) (entries : List GlobalProgramEntry.Entry)
    (globals : List Surface.Signature) (initializedStore : GlobalIR.Store)
    (decoded : NLisp.Named.decodeTopLevelProgram decodeFuel forms =
      some (definitions, slotTypes, initializers))
    (slotTypesAgree : slotTypes = GlobalProgramEntry.valueTypes entries)
    (arithmeticRows : GlobalProgramEntry.ArithmeticInitializerRows
      (GlobalProgramEntry.valueTypes entries) 0 entries)
    (initialization : GlobalIR.initializeValues
      (GlobalProgramEntry.toRuntimeProgram entries entryIndex).definitions initializerFuel
      (List.replicate (GlobalProgramEntry.toRuntimeProgram entries entryIndex).initializers.length none)
      0 (GlobalProgramEntry.toRuntimeProgram entries entryIndex).initializers =
        .ok initializedStore) :
    (∃ headers : ProgramHeaders,
      readProgramHeaders decodeFuel 0 forms = some headers ∧
      slotTypes = headers.globals.map GlobalHeader.type ∧
      initializers.length = (GlobalProgramEntry.toRuntimeProgram entries entryIndex).initializers.length ∧
      (GlobalProgramEntry.toRuntimeProgram entries entryIndex).definitions.length = entries.length ∧
      (GlobalProgramEntry.toRuntimeProgram entries entryIndex).initializers.length = slotTypes.length ∧
      NLisp.Named.programWellScoped definitions ∧
      (∀ expression ∈ initializers, NLisp.Named.letLayoutsAligned expression = true) ∧
      GlobalIR.InitializerTypesAgree (GlobalProgramEntry.valueTypes entries) 0
        (GlobalProgramEntry.toRuntimeProgram entries entryIndex).initializers) ∧
    GlobalIR.StoreWellTyped globals slotTypes initializedStore ∧
    initializedStore.length = slotTypes.length ∧
    (∀ slot type, slotTypes.get? slot = some type →
      ∃ value, initializedStore.get? slot = some (some value) ∧
        PolyIR.ValueTyped globals value type) := by
  have typedRows := arithmeticRows.toTypedInitializerRows entries
    (GlobalProgramEntry.valueTypes entries) 0 entries
  obtain ⟨checkerFuel, checkedRows⟩ := typedRows.toInitializerCheckerRows entries
    (GlobalProgramEntry.valueTypes entries) 0 entries
  have rowsChecked : GlobalProgramEntry.checkInitializerRows checkerFuel entries
      (GlobalProgramEntry.valueTypes entries) 0 entries = true := by
    exact (GlobalProgramEntry.checkInitializerRows_iff checkerFuel entries
      (GlobalProgramEntry.valueTypes entries) 0 entries).2 checkedRows
  obtain ⟨headers, headersRead, headerTypes, initializerCount, definitionCount,
    runtimeInitializerCount, definitionsScoped, initializersAligned, _typedRows,
    runtimeTypesAgree⟩ :=
    decodedTopLevelProgram_checkedRows_executable_layout decodeFuel checkerFuel entryIndex
      forms definitions slotTypes initializers entries decoded slotTypesAgree rowsChecked
  have storeTyped := GlobalProgramEntry.TypedInitializerRows.toRuntimeProgram_initialization_preserves_store_arithmetic
    entries globals entryIndex
    initializerFuel initializedStore typedRows arithmeticRows initialization
  have storeLength := GlobalIR.initializeValues_preserves_layout_length
    (List.replicate
      (GlobalProgramEntry.toRuntimeProgram entries entryIndex).initializers.length
      (none : Option PolyIR.Value)) initializedStore slotTypes 0
    (GlobalProgramEntry.toRuntimeProgram entries entryIndex).initializers
    initialization (by simpa using runtimeInitializerCount)
  have sourceRuntimeInitializerCount : initializers.length =
      (GlobalProgramEntry.toRuntimeProgram entries entryIndex).initializers.length := by
    calc
      initializers.length = slotTypes.length := initializerCount.symm
      _ = (GlobalProgramEntry.toRuntimeProgram entries entryIndex).initializers.length :=
        runtimeInitializerCount.symm
  have everySlotTyped : ∀ slot type, slotTypes.get? slot = some type →
      ∃ value, initializedStore.get? slot = some (some value) ∧
        PolyIR.ValueTyped globals value type := by
    intro slot type slotType
    have slotBound : slot < slotTypes.length := (List.get?_eq_some.mp slotType).1
    have runtimeBound : slot <
        (GlobalProgramEntry.toRuntimeProgram entries entryIndex).initializers.length := by
      rw [runtimeInitializerCount]
      exact slotBound
    have present := GlobalIR.initialized_cells_present initialization (by simp)
      ⟨Nat.zero_le _, by simpa using runtimeBound⟩
    obtain ⟨value, valuePresent⟩ := present
    have valueGet : initializedStore.get? slot = some (some value) := by
      rw [← sourceGetElem?_eq_get?]
      exact valuePresent
    exact ⟨value, valueGet, storeTyped slot value type valueGet
      (by simpa [slotTypesAgree] using slotType)⟩
  exact ⟨⟨headers, headersRead, headerTypes, sourceRuntimeInitializerCount, definitionCount,
      runtimeInitializerCount, definitionsScoped, initializersAligned, runtimeTypesAgree⟩,
    by simpa [slotTypesAgree] using storeTyped,
    by simpa [slotTypesAgree] using storeLength, everySlotTyped⟩

/-- Carry a successful mixed top-level decode and checker-accepted
initializer rows through the actual runtime initialization to a typed getter
call. Runtime table typing and initializer evaluation type safety remain
explicit premises; the decode bridge supplies the source-order slot layout and
the initializer-row typing evidence. -/
theorem decodedTopLevelProgram_checkedRows_initialization_supports_typed_getter_call
    (decodeFuel checkerFuel entryIndex initializerFuel getterFuel : Nat)
    (forms : List Node) (definitions : NLisp.Named.Definitions)
    (surfaceDefinitions : Surface.Definitions)
    (slotTypes : List Surface.Ty) (initializers : List NLisp.Named.Expr)
    (entries : List GlobalProgramEntry.Entry)
    (globals : List Surface.Signature) (functionSources : List (Nat × Nat))
    (initializedStore : GlobalIR.Store) (index slot : Nat)
    (decoded : NLisp.Named.decodeTopLevelProgram decodeFuel forms =
      some (definitions, slotTypes, initializers))
    (slotTypesAgree : slotTypes = GlobalProgramEntry.valueTypes entries)
    (rowsChecked : GlobalProgramEntry.checkInitializerRows checkerFuel entries
      (GlobalProgramEntry.valueTypes entries) 0 entries = true)
    (evaluationTyped : ∀ currentStore remaining expression value type,
      GlobalIR.evaluate (GlobalProgramEntry.toRuntimeProgram entries entryIndex).definitions
        currentStore remaining [] expression = .ok value →
        PolyIR.ValueTyped globals value type)
    (initialization : GlobalIR.initializeValues
      (GlobalProgramEntry.toRuntimeProgram entries entryIndex).definitions initializerFuel
      (List.replicate (GlobalProgramEntry.toRuntimeProgram entries entryIndex).initializers.length none)
      0 (GlobalProgramEntry.toRuntimeProgram entries entryIndex).initializers =
        .ok initializedStore)
    (programTyped : GlobalIR.GlobalProgramTyped globals surfaceDefinitions
      (GlobalProgramEntry.valueTypes entries) functionSources
      (GlobalProgramEntry.toRuntimeProgram entries entryIndex).definitions)
    (getter : (GlobalProgramEntry.toRuntimeProgram entries entryIndex).definitions[index]? =
      some (.getter slot)) :
    ∃ type value, globals[index]? = some ⟨0, [], type⟩ ∧ type.wellFormed 0 ∧
      (GlobalProgramEntry.valueTypes entries)[slot]? = some type ∧
      GlobalIR.evaluate (GlobalProgramEntry.toRuntimeProgram entries entryIndex).definitions
        initializedStore (getterFuel + 2) [] (.app (.global index) []) = .ok value ∧
      PolyIR.ValueTyped globals value type := by
  obtain ⟨_headers, _headersRead, _headerTypesAgree, _slotTypesAgree, _initializerCount,
    _definitionsScoped, _initializersAligned, typedRows, _runtimeTypesAgree⟩ :=
    decodedTopLevelProgram_checkedRows_globalIR_layout decodeFuel checkerFuel entryIndex
      forms definitions slotTypes initializers entries decoded slotTypesAgree rowsChecked
  exact typedRows.toRuntimeProgram_initialization_supports_typed_getter_call entries globals
    surfaceDefinitions functionSources entryIndex initializerFuel getterFuel initializedStore index slot
    evaluationTyped initialization programTyped getter

/-- End-to-end typed execution path for mixed programs whose value rows carry
the arithmetic initializer certificate. The row certificate constructs a
finite checker fuel, typed execution layout and post-initialization typed
getter result from the successful mixed decode. -/
theorem decodedTopLevelProgram_arithmeticRows_initialization_supports_typed_getter_call
    (decodeFuel entryIndex initializerFuel getterFuel : Nat) (forms : List Node)
    (definitions : NLisp.Named.Definitions) (slotTypes : List Surface.Ty)
    (initializers : List NLisp.Named.Expr) (entries : List GlobalProgramEntry.Entry)
    (globals : List Surface.Signature) (surfaceDefinitions : Surface.Definitions)
    (functionSources : List (Nat × Nat)) (initializedStore : GlobalIR.Store)
    (index slot : Nat)
    (decoded : NLisp.Named.decodeTopLevelProgram decodeFuel forms =
      some (definitions, slotTypes, initializers))
    (slotTypesAgree : slotTypes = GlobalProgramEntry.valueTypes entries)
    (arithmeticRows : GlobalProgramEntry.ArithmeticInitializerRows
      (GlobalProgramEntry.valueTypes entries) 0 entries)
    (initialization : GlobalIR.initializeValues
      (GlobalProgramEntry.toRuntimeProgram entries entryIndex).definitions initializerFuel
      (List.replicate (GlobalProgramEntry.toRuntimeProgram entries entryIndex).initializers.length none)
      0 (GlobalProgramEntry.toRuntimeProgram entries entryIndex).initializers =
        .ok initializedStore)
    (programTyped : GlobalIR.GlobalProgramTyped globals surfaceDefinitions
      (GlobalProgramEntry.valueTypes entries) functionSources
      (GlobalProgramEntry.toRuntimeProgram entries entryIndex).definitions)
    (getter : (GlobalProgramEntry.toRuntimeProgram entries entryIndex).definitions[index]? =
      some (.getter slot)) :
    ∃ checkerFuel,
      GlobalProgramEntry.checkInitializerRows checkerFuel entries
        (GlobalProgramEntry.valueTypes entries) 0 entries = true ∧
      (∃ headers : ProgramHeaders,
        readProgramHeaders decodeFuel 0 forms = some headers ∧
        slotTypes = headers.globals.map GlobalHeader.type ∧
        slotTypes.length = initializers.length ∧
        (GlobalProgramEntry.toRuntimeProgram entries entryIndex).definitions.length = entries.length ∧
        (GlobalProgramEntry.toRuntimeProgram entries entryIndex).initializers.length = slotTypes.length ∧
        NLisp.Named.programWellScoped definitions ∧
        (∀ expression ∈ initializers, NLisp.Named.letLayoutsAligned expression = true) ∧
        GlobalIR.InitializerTypesAgree (GlobalProgramEntry.valueTypes entries) 0
          (GlobalProgramEntry.toRuntimeProgram entries entryIndex).initializers) ∧
      (∃ type value, globals[index]? = some ⟨0, [], type⟩ ∧ type.wellFormed 0 ∧
        (GlobalProgramEntry.valueTypes entries)[slot]? = some type ∧
        GlobalIR.evaluate (GlobalProgramEntry.toRuntimeProgram entries entryIndex).definitions
          initializedStore (getterFuel + 2) [] (.app (.global index) []) = .ok value ∧
        PolyIR.ValueTyped globals value type) := by
  have typedRows : GlobalProgramEntry.TypedInitializerRows entries
      (GlobalProgramEntry.valueTypes entries) 0 entries :=
    arithmeticRows.toTypedInitializerRows entries (GlobalProgramEntry.valueTypes entries) 0 entries
  obtain ⟨checkerFuel, _checkedRows⟩ := typedRows.toInitializerCheckerRows
    entries (GlobalProgramEntry.valueTypes entries) 0 entries
  have rowsAccepted : GlobalProgramEntry.checkInitializerRows checkerFuel entries
      (GlobalProgramEntry.valueTypes entries) 0 entries = true := by
    exact (GlobalProgramEntry.checkInitializerRows_iff checkerFuel entries
      (GlobalProgramEntry.valueTypes entries) 0 entries).2 _checkedRows
  obtain ⟨headers, headersRead, headerTypesAgree, initializerCount,
    runtimeDefinitionCount, runtimeInitializerCount, definitionsScoped,
    initializersAligned, _typedRows, initializerTypesAgree⟩ :=
    decodedTopLevelProgram_checkedRows_executable_layout decodeFuel checkerFuel entryIndex
      forms definitions slotTypes initializers entries decoded slotTypesAgree rowsAccepted
  obtain ⟨type, value, globalSignature, typeValid, slotType, getterEvaluation, valueTyped⟩ :=
    GlobalProgramEntry.ArithmeticInitializerRows.toRuntimeProgram_initialization_supports_typed_getter_call
      entries globals surfaceDefinitions functionSources entryIndex initializerFuel getterFuel
      initializedStore index slot arithmeticRows initialization programTyped getter
  exact ⟨checkerFuel, rowsAccepted,
    ⟨headers, headersRead, headerTypesAgree, initializerCount, runtimeDefinitionCount,
      runtimeInitializerCount, definitionsScoped, initializersAligned, initializerTypesAgree⟩,
    ⟨type, value, globalSignature, typeValid, slotType, getterEvaluation, valueTyped⟩⟩

/-- The arithmetic initializer path also establishes the invariant for the
whole store, without choosing a getter. This combines successful mixed
top-level decoding, source-order slot agreement, arithmetic initializer rows,
and the actual runtime initialization run. -/
theorem decodedTopLevelProgram_arithmeticRows_initialization_preserves_store
    (decodeFuel entryIndex initializerFuel : Nat) (forms : List Node)
    (definitions : NLisp.Named.Definitions) (slotTypes : List Surface.Ty)
    (initializers : List NLisp.Named.Expr) (entries : List GlobalProgramEntry.Entry)
    (globals : List Surface.Signature) (initializedStore : GlobalIR.Store)
    (decoded : NLisp.Named.decodeTopLevelProgram decodeFuel forms =
      some (definitions, slotTypes, initializers))
    (slotTypesAgree : slotTypes = GlobalProgramEntry.valueTypes entries)
    (arithmeticRows : GlobalProgramEntry.ArithmeticInitializerRows
      (GlobalProgramEntry.valueTypes entries) 0 entries)
    (initialization : GlobalIR.initializeValues
      (GlobalProgramEntry.toRuntimeProgram entries entryIndex).definitions initializerFuel
      (List.replicate (GlobalProgramEntry.toRuntimeProgram entries entryIndex).initializers.length none)
      0 (GlobalProgramEntry.toRuntimeProgram entries entryIndex).initializers =
        .ok initializedStore) :
    ∃ checkerFuel,
      GlobalProgramEntry.checkInitializerRows checkerFuel entries
        (GlobalProgramEntry.valueTypes entries) 0 entries = true ∧
      (∃ headers : ProgramHeaders,
        readProgramHeaders decodeFuel 0 forms = some headers ∧
        slotTypes = headers.globals.map GlobalHeader.type ∧
        slotTypes.length = initializers.length ∧
        (GlobalProgramEntry.toRuntimeProgram entries entryIndex).definitions.length = entries.length ∧
        (GlobalProgramEntry.toRuntimeProgram entries entryIndex).initializers.length = slotTypes.length ∧
        NLisp.Named.programWellScoped definitions ∧
        (∀ expression ∈ initializers, NLisp.Named.letLayoutsAligned expression = true) ∧
        GlobalIR.InitializerTypesAgree (GlobalProgramEntry.valueTypes entries) 0
          (GlobalProgramEntry.toRuntimeProgram entries entryIndex).initializers) ∧
      GlobalIR.StoreWellTyped globals slotTypes initializedStore ∧
      initializedStore.length = slotTypes.length ∧
      (∀ slot type, slotTypes.get? slot = some type →
        ∃ value, initializedStore.get? slot = some (some value) ∧
          PolyIR.ValueTyped globals value type) := by
  have typedRows : GlobalProgramEntry.TypedInitializerRows entries
      (GlobalProgramEntry.valueTypes entries) 0 entries :=
    arithmeticRows.toTypedInitializerRows entries (GlobalProgramEntry.valueTypes entries) 0 entries
  obtain ⟨checkerFuel, checkedRows⟩ := typedRows.toInitializerCheckerRows
    entries (GlobalProgramEntry.valueTypes entries) 0 entries
  have rowsAccepted : GlobalProgramEntry.checkInitializerRows checkerFuel entries
      (GlobalProgramEntry.valueTypes entries) 0 entries = true := by
    exact (GlobalProgramEntry.checkInitializerRows_iff checkerFuel entries
      (GlobalProgramEntry.valueTypes entries) 0 entries).2 checkedRows
  obtain ⟨headers, headersRead, headerTypesAgree, initializerCount,
    runtimeDefinitionCount, runtimeInitializerCount, definitionsScoped,
    initializersAligned, _typedRows, initializerTypesAgree⟩ :=
    decodedTopLevelProgram_checkedRows_executable_layout decodeFuel checkerFuel entryIndex
      forms definitions slotTypes initializers entries decoded slotTypesAgree rowsAccepted
  have storeTyped := GlobalProgramEntry.TypedInitializerRows.toRuntimeProgram_initialization_preserves_store_arithmetic
    entries globals entryIndex initializerFuel initializedStore typedRows arithmeticRows initialization
  have runtimeInitialStoreLength :
      (List.replicate
        (GlobalProgramEntry.toRuntimeProgram entries entryIndex).initializers.length
        (none : Option PolyIR.Value)).length = slotTypes.length := by
    simp [runtimeInitializerCount]
  have initializedStoreLength := GlobalIR.initializeValues_preserves_layout_length
    (List.replicate
      (GlobalProgramEntry.toRuntimeProgram entries entryIndex).initializers.length
      (none : Option PolyIR.Value)) initializedStore slotTypes 0
    (GlobalProgramEntry.toRuntimeProgram entries entryIndex).initializers
    initialization runtimeInitialStoreLength
  have everySlotTyped : ∀ slot type, slotTypes.get? slot = some type →
      ∃ value, initializedStore.get? slot = some (some value) ∧
        PolyIR.ValueTyped globals value type := by
    intro slot type slotType
    have slotBound : slot < slotTypes.length := (List.get?_eq_some.mp slotType).1
    have runtimeBound : slot <
        (GlobalProgramEntry.toRuntimeProgram entries entryIndex).initializers.length := by
      rw [runtimeInitializerCount]
      exact slotBound
    have present := GlobalIR.initialized_cells_present initialization (by simp)
      ⟨Nat.zero_le _, by simpa using runtimeBound⟩
    obtain ⟨value, valuePresent⟩ := present
    have valueGet : initializedStore.get? slot = some (some value) := by
      rw [← sourceGetElem?_eq_get?]
      exact valuePresent
    exact ⟨value, valueGet, storeTyped slot value type valueGet
      (by simpa [slotTypesAgree] using slotType)⟩
  exact ⟨checkerFuel, rowsAccepted,
    ⟨headers, headersRead, headerTypesAgree, initializerCount, runtimeDefinitionCount,
      runtimeInitializerCount, definitionsScoped, initializersAligned, initializerTypesAgree⟩,
    by simpa [slotTypesAgree] using storeTyped,
    initializedStoreLength, everySlotTyped⟩

end NLisp.GlobalSourceLowering
