import NLisp.GlobalIR
import NLisp.ExpansionLowering
import NLisp.SurfaceChecker
import NLisp.CheckerCompleteness
import NLisp.CNameResolution

namespace NLisp.GlobalProgramEntry

open NLisp.GlobalIR NLisp.PolyIR NLisp.Surface

/- Source-order declarations used while lowering top-level values. The identity
is the scoped binding token; value expressions are retained until their
initializer has been lowered against the preceding declaration layout. -/
inductive Entry where
  | function (identity : Nat) (signature : Signature)
      (signatureValid : signature.wellFormed) (definition : RuntimeDefinition)
  | value (identity : Nat) (type : Ty) (typeValid : type.wellFormed 0)
      (initializer : Expr)

def identity : Entry → Nat
  | .function id _ _ _ => id
  | .value id _ _ _ => id

def bindingIdentity := identity

namespace Entry

def bindingIdentity (entry : GlobalProgramEntry.Entry) : Nat := identity entry

end Entry

def DistinctIds : List Nat → Prop
  | [] => True
  | id :: rest => id ∉ rest ∧ DistinctIds rest

def valueIdentities : List Entry → List Nat
  | [] => []
  | .function _ _ _ _ :: rest => valueIdentities rest
  | .value id _ _ _ :: rest => id :: valueIdentities rest

def functionIdentities : List Entry → List Nat
  | [] => []
  | .function id _ _ _ :: rest => id :: functionIdentities rest
  | .value _ _ _ _ :: rest => functionIdentities rest

/- Runtime-table positions count both functions and values, while Surface
Definitions contains functions only. This map records the correspondence. -/
def functionSourcesFromEntries (runtimeIndex sourceIndex : Nat) : List Entry →
    List (Nat × Nat)
  | [] => []
  | .function _ _ _ _ :: rest =>
      (runtimeIndex, sourceIndex) ::
        functionSourcesFromEntries (runtimeIndex + 1) (sourceIndex + 1) rest
  | .value _ _ _ _ :: rest =>
      functionSourcesFromEntries (runtimeIndex + 1) sourceIndex rest

theorem functionSourcesFromEntries_length (runtimeIndex sourceIndex : Nat)
    (entries : List Entry) :
    (functionSourcesFromEntries runtimeIndex sourceIndex entries).length =
      (functionIdentities entries).length := by
  induction entries generalizing runtimeIndex sourceIndex with
  | nil => rfl
  | cons entry rest ih =>
      cases entry <;> simp [functionSourcesFromEntries, functionIdentities, ih]

theorem functionSourcesFromEntries_mem_bounds
    (runtimeIndex sourceIndex : Nat) (entries : List Entry) (pair : Nat × Nat)
    (member : pair ∈ functionSourcesFromEntries runtimeIndex sourceIndex entries) :
    pair.1 < runtimeIndex + entries.length ∧
      pair.2 < sourceIndex + (functionIdentities entries).length := by
  induction entries generalizing runtimeIndex sourceIndex with
  | nil => simp [functionSourcesFromEntries] at member
  | cons entry rest ih =>
      cases entry with
      | function identity signature valid definition =>
          simp only [functionSourcesFromEntries, List.mem_cons] at member
          rcases member with head | tail
          · have pairEq : pair = (runtimeIndex, sourceIndex) := by
              exact head
            subst pair
            simp only [List.length_cons, functionIdentities]
            omega
          · have bounds := ih (runtimeIndex + 1) (sourceIndex + 1) tail
            simp only [List.length_cons, functionIdentities] at bounds ⊢
            omega
      | value identity type valid initializer =>
          have bounds := ih (runtimeIndex + 1) sourceIndex
            (by simpa [functionSourcesFromEntries] using member)
          simp only [List.length_cons, functionIdentities] at bounds ⊢
          omega

theorem functionSourcesFromEntries_mem_lower_bounds
    (runtimeIndex sourceIndex : Nat) (entries : List Entry) (pair : Nat × Nat)
    (member : pair ∈ functionSourcesFromEntries runtimeIndex sourceIndex entries) :
    runtimeIndex ≤ pair.1 ∧ sourceIndex ≤ pair.2 := by
  induction entries generalizing runtimeIndex sourceIndex with
  | nil => simp [functionSourcesFromEntries] at member
  | cons entry rest ih =>
      cases entry with
      | function identity signature valid definition =>
          simp only [functionSourcesFromEntries, List.mem_cons] at member
          rcases member with head | tail
          · have pairEq : pair = (runtimeIndex, sourceIndex) := head
            subst pair
            simp
          · have lower := ih (runtimeIndex + 1) (sourceIndex + 1) tail
            omega
      | value identity type valid initializer =>
          have lower := ih (runtimeIndex + 1) sourceIndex
            (by simpa [functionSourcesFromEntries] using member)
          omega

def identities : List Entry → List Nat
  := List.map identity

/- Position-preserving relation between the C-style named environment and
the mixed source declaration layout. The decoder must establish this relation
from parsed names and scoped identities. -/
def NamedGlobalLayout (named : List CNameResolution.Entry) (entries : List Entry) : Prop :=
  named.length = entries.length ∧
    ∀ index namedEntry sourceEntry,
      named.get? index = some namedEntry → entries.get? index = some sourceEntry →
        namedEntry.identity = identity sourceEntry

theorem namedGlobalLayout_of_identity_map
    (declarations : List ExpansionLowering.TopLevelDeclaration) (entries : List Entry)
    (aligned : declarations.map ExpansionLowering.TopLevelDeclaration.identity =
      identities entries) :
    NamedGlobalLayout
      (declarations.map ExpansionLowering.TopLevelDeclaration.toNameEntry) entries := by
  constructor
  · simpa [identities] using congrArg List.length aligned
  · intro index namedEntry sourceEntry namedAt sourceAt
    have namedIdentityAt :
        (declarations.map ExpansionLowering.TopLevelDeclaration.identity).get? index =
          some namedEntry.identity := by
      have mapped := congrArg (Option.map CNameResolution.Entry.identity) namedAt
      simpa [List.get?_map, ExpansionLowering.TopLevelDeclaration.toNameEntry] using mapped
    have sourceIdentityAt : (identities entries).get? index = some (identity sourceEntry) := by
      have mapped := congrArg (Option.map identity) sourceAt
      simpa [identities, List.get?_map] using mapped
    have atIndex := congrArg (fun values : List Nat => values.get? index) aligned
    have selectedIdentity : some namedEntry.identity = some (identity sourceEntry) := by
      calc
        some namedEntry.identity =
            (declarations.map ExpansionLowering.TopLevelDeclaration.identity).get? index :=
              namedIdentityAt.symm
        _ = (identities entries).get? index := atIndex
        _ = some (identity sourceEntry) := sourceIdentityAt
    exact Option.some.inj selectedIdentity

theorem programHeaders_namedGlobalLayout
    (headers : ExpansionLowering.ProgramHeaders) (entries : List Entry)
    (aligned : headers.declarations.map ExpansionLowering.TopLevelDeclaration.identity =
      identities entries) :
    NamedGlobalLayout headers.namedEnvironment entries := by
  simpa [ExpansionLowering.ProgramHeaders.namedEnvironment] using
    namedGlobalLayout_of_identity_map headers.declarations entries aligned

theorem decodedTopLevelProgram_namedGlobalLayout
    (fuel : Nat) (forms : List CBindingWalk.Node)
    (headers : ExpansionLowering.ProgramHeaders) (definitions : NLisp.Named.Definitions)
    (slotTypes : List Ty) (initializers : List NLisp.Named.Expr) (entries : List Entry)
    (decoded : NLisp.Named.decodeTopLevelProgramWithHeaders fuel forms =
      some (headers, definitions, slotTypes, initializers))
    (aligned : headers.declarations.map ExpansionLowering.TopLevelDeclaration.identity =
      identities entries) :
    NLisp.Named.decodeTopLevelProgramWithHeaders fuel forms =
        some (headers, definitions, slotTypes, initializers) ∧
      NamedGlobalLayout headers.namedEnvironment entries :=
  ⟨decoded, programHeaders_namedGlobalLayout headers entries aligned⟩

def valueTypes : List Entry → List Ty
  | [] => []
  | .function _ _ _ _ :: rest => valueTypes rest
  | .value _ type _ _ :: rest => type :: valueTypes rest

def identitiesUniqueCheck : List Entry → Bool
  | [] => true
  | entry :: rest =>
      !(rest.any fun other => identity other == identity entry) && identitiesUniqueCheck rest

theorem identitiesUniqueCheck_sound (entries : List Entry)
    (accepted : identitiesUniqueCheck entries = true) : DistinctIds (identities entries) := by
  induction entries with
  | nil => trivial
  | cons entry rest ih =>
      simp only [identitiesUniqueCheck, Bool.and_eq_true, Bool.not_eq_true'] at accepted
      rcases accepted with ⟨notRepeated, restAccepted⟩
      constructor
      · intro member
        change identity entry ∈ List.map identity rest at member
        obtain ⟨other, otherMember, sameIdentity⟩ := List.mem_map.mp member
        have repeated : (rest.any fun candidate => identity candidate == identity entry) = true :=
          List.any_eq_true.mpr ⟨other, otherMember, by simp [sameIdentity]⟩
        rw [repeated] at notRepeated
        contradiction
      · exact ih restAccepted

def globalIndexOf (target : Nat) : List Entry → Option Nat
  | [] => none
  | entry :: rest =>
      if identity entry == target then some 0
      else (globalIndexOf target rest).map Nat.succ

def valueSlotOf (target start : Nat) : List Entry → Option Nat
  | [] => none
  | .function _ _ _ _ :: rest => valueSlotOf target start rest
  | .value id _ _ _ :: rest =>
      if id == target then some start else valueSlotOf target (start + 1) rest

private theorem identity_mem_of_get?_some (entries : List Entry) (index : Nat)
    (entry : Entry) (found : entries.get? index = some entry) :
    identity entry ∈ identities entries := by
  induction entries generalizing index with
  | nil => simp at found
  | cons head tail ih =>
      cases index with
      | zero => simp at found; subst entry; simp [identities]
      | succ index =>
          have tailFound : tail.get? index = some entry := by simpa using found
          exact List.mem_cons_of_mem (identity head) (ih index tailFound)

/-- With unique binding identities, looking up an entry at a source-order
declaration index yields that same index from the identity-based global
lookup. This is the name-to-index half of the mixed Program.data layout
correspondence used by C. -/
theorem globalIndexOf_get?_unique (entries : List Entry) (index : Nat)
    (entry : Entry) (target : Nat)
    (unique : DistinctIds (identities entries))
    (found : entries.get? index = some entry)
    (identityMatches : identity entry = target) :
    globalIndexOf target entries = some index := by
  induction entries generalizing index with
  | nil => simp at found
  | cons head tail ih =>
      cases index with
      | zero =>
          simp only [List.get?] at found
          have entryEq : head = entry := Option.some.inj found
          subst entry
          simp [globalIndexOf, identityMatches]
      | succ index =>
          have tailFound : tail.get? index = some entry := by simpa using found
          have identityMem := identity_mem_of_get?_some tail index entry tailFound
          have targetMem : target ∈ identities tail := by
            simpa [identityMatches] using identityMem
          have headDifferent : identity head ≠ target := by
            intro same
            obtain ⟨candidate, candidateMem, candidateIdentity⟩ :=
              List.mem_map.mp targetMem
            apply unique.1
            apply List.mem_map.mpr
            exact ⟨candidate, candidateMem, candidateIdentity.trans same.symm⟩
          simp only [globalIndexOf, beq_iff_eq, if_neg headDifferent]
          simpa using ih index unique.2 tailFound

theorem findNameIndex_matches_globalIndexOf
    (named : List CNameResolution.Entry) (entries : List Entry)
    (name : String) (binding : CNameResolution.Entry)
    (layout : NamedGlobalLayout named entries)
    (unique : DistinctIds (identities entries))
    (found : CNameResolution.findName named name = some binding) :
    ∃ index, CNameResolution.findNameIndex named name = some index ∧
      globalIndexOf binding.identity entries = some index := by
  obtain ⟨index, indexFound, namedAtIndex⟩ :=
    CNameResolution.findNameIndex_complete named name binding found
  have indexBound : index < named.length := (List.get?_eq_some.mp namedAtIndex).1
  have sourceBound : index < entries.length := by rw [← layout.1]; exact indexBound
  let sourceEntry : Entry := entries[index]
  have sourceAtIndex : entries.get? index = some sourceEntry :=
    (List.get?_eq_some).mpr ⟨sourceBound, rfl⟩
  have identityAgreement := layout.2 index binding sourceEntry namedAtIndex sourceAtIndex
  have globalFound := globalIndexOf_get?_unique entries index sourceEntry binding.identity
    unique sourceAtIndex identityAgreement.symm
  exact ⟨index, indexFound, globalFound⟩

theorem decodedTopLevelProgram_resolves_name_to_globalIndex
    (fuel : Nat) (forms : List CBindingWalk.Node)
    (headers : ExpansionLowering.ProgramHeaders) (definitions : NLisp.Named.Definitions)
    (slotTypes : List Ty) (initializers : List NLisp.Named.Expr)
    (entries : List Entry) (name : String) (binding : CNameResolution.Entry)
    (decoded : NLisp.Named.decodeTopLevelProgramWithHeaders fuel forms =
      some (headers, definitions, slotTypes, initializers))
    (aligned : headers.declarations.map ExpansionLowering.TopLevelDeclaration.identity =
      identities entries)
    (unique : DistinctIds (identities entries))
    (nameFound : CNameResolution.findName headers.namedEnvironment name = some binding) :
    NLisp.Named.decodeTopLevelProgramWithHeaders fuel forms =
        some (headers, definitions, slotTypes, initializers) ∧
      ∃ index, CNameResolution.findNameIndex headers.namedEnvironment name = some index ∧
        globalIndexOf binding.identity entries = some index := by
  have namedLayout := programHeaders_namedGlobalLayout headers entries aligned
  exact ⟨decoded,
    findNameIndex_matches_globalIndexOf headers.namedEnvironment entries name binding
      namedLayout unique nameFound⟩

/- C indexes its `value_slots` pointer array by the original Program
declaration index. GlobalIR stores values densely, so this function translates
that mixed declaration index to the dense value-slot ordinal. -/
def sourceValueSlotOrdinal : List Entry → Nat → Option Nat
  | [], _ => none
  | .function _ _ _ _ :: _, 0 => none
  | .value _ _ _ _ :: _, 0 => some 0
  | .function _ _ _ _ :: rest, index + 1 => sourceValueSlotOrdinal rest index
  | .value _ _ _ _ :: rest, index + 1 =>
      (sourceValueSlotOrdinal rest index).map Nat.succ

/- C stores an RBind-cell pointer at each mixed Program.data index, leaving
function declarations empty. Assigning each allocated cell its dense ordinal
gives a small executable model of the `value_slots` pointer array. -/
def cValueSlotOrdinalsFrom (next : Nat) : List Entry → List (Option Nat)
  | [] => []
  | .function _ _ _ _ :: rest => none :: cValueSlotOrdinalsFrom next rest
  | .value _ _ _ _ :: rest => some next :: cValueSlotOrdinalsFrom (next + 1) rest

def cValueSlotOrdinals (entries : List Entry) : List (Option Nat) :=
  cValueSlotOrdinalsFrom 0 entries

/- Interpret a C `value_slots` pointer as an address in the abstract shared
cell heap. Both a missing pointer and a null `RBind.value` read as no value. -/
def cValueSlotCellRead (slots : List (Option Nat)) (cells : GlobalIR.Store)
    (sourceIndex : Nat) : Option PolyIR.Value :=
  match slots[sourceIndex]? with
  | some (some address) =>
      match cells[address]? with
      | some value => value
      | none => none
  | _ => none

/-- Once a mixed declaration's C `value_slots` entry points at a dense cell,
reading through that shared-cell pointer has exactly the successful behavior
of GlobalIR's getter read, for every store state. -/
theorem cValueSlotCellRead_success_iff_readGlobal
    (slots : List (Option Nat)) (cells : GlobalIR.Store)
    (sourceIndex slot : Nat) (pointer : slots[sourceIndex]? = some (some slot))
    (value : PolyIR.Value) :
    cValueSlotCellRead slots cells sourceIndex = some value ↔
      GlobalIR.readGlobal cells slot = .ok value := by
  cases cell : cells[slot]? with
  | none => simp [cValueSlotCellRead, pointer, GlobalIR.readGlobal, cell]
  | some stored =>
      cases stored with
      | none => simp [cValueSlotCellRead, pointer, GlobalIR.readGlobal, cell]
      | some storedValue =>
          simp [cValueSlotCellRead, pointer, GlobalIR.readGlobal, cell]

/-- A non-null C cell pointer observes the same early-initialization fault as
the corresponding GlobalIR getter when its shared cell has not been filled. -/
theorem cValueSlotCellRead_beforeInitialization_iff
    (slots : List (Option Nat)) (cells : GlobalIR.Store)
    (sourceIndex slot : Nat) (pointer : slots[sourceIndex]? = some (some slot)) :
    cells[slot]? = some none ↔
      GlobalIR.readGlobal cells slot = .error (.beforeInitialization slot) := by
  cases cell : cells[slot]? with
  | none => simp [GlobalIR.readGlobal, cell]
  | some stored =>
      cases stored with
      | none => simp [GlobalIR.readGlobal, cell]
      | some value => simp [GlobalIR.readGlobal, cell]

/-- In the mixed-table model, a live C `value_slots` pointer to an
uninitialized shared cell and the corresponding GlobalIR getter report the
same early-read state: C's cell read is empty and the getter raises the
slot-specific before-initialization fault. -/
theorem cValueSlotCellRead_and_getter_beforeInitialization
    (slots : List (Option Nat)) (cells : GlobalIR.Store)
    (sourceIndex slot fuel : Nat) (pointer : slots[sourceIndex]? = some (some slot))
    (program : List GlobalIR.Definition)
    (getter : program[sourceIndex]? = some (.getter slot))
    (uninitialized : cells[slot]? = some none) :
    cValueSlotCellRead slots cells sourceIndex = none ∧
      GlobalIR.evaluate program cells (fuel + 2) []
        (.app (.global sourceIndex) []) = .error (.beforeInitialization slot) := by
  constructor
  · simp [cValueSlotCellRead, pointer, uninitialized]
  · simp [GlobalIR.evaluate, GlobalIR.evaluateArgs, getter, GlobalIR.readGlobal,
      uninitialized, List.isEmpty]

/-- At an in-range mixed declaration index, the C `value_slots` array model
contains exactly the dense GlobalIR ordinal for a value declaration and an
empty cell for a function declaration. -/
theorem cValueSlotOrdinalsFrom_get (entries : List Entry) (index next : Nat)
    (inRange : index < entries.length) :
    (cValueSlotOrdinalsFrom next entries)[index]? =
      some ((sourceValueSlotOrdinal entries index).map (· + next)) := by
  induction entries generalizing index next with
  | nil =>
      have impossible : index < 0 := by simpa using inRange
      exact False.elim ((Nat.not_lt_zero index) impossible)
  | cons entry rest ih =>
      cases entry with
      | function identity signature signatureValid definition =>
          cases index with
          | zero => simp [cValueSlotOrdinalsFrom, sourceValueSlotOrdinal]
          | succ index =>
              have tailRange : index < rest.length := by simp at inRange; omega
              simpa [cValueSlotOrdinalsFrom, sourceValueSlotOrdinal] using
                ih index next tailRange
      | value identity type valid initializer =>
          cases index with
          | zero => simp [cValueSlotOrdinalsFrom, sourceValueSlotOrdinal]
          | succ index =>
              have tailRange : index < rest.length := by simp at inRange; omega
              simpa [cValueSlotOrdinalsFrom, sourceValueSlotOrdinal, Nat.add_comm,
                Nat.add_left_comm, Nat.add_assoc] using
                ih index (next + 1) tailRange

theorem cValueSlotOrdinals_get (entries : List Entry) (index : Nat)
    (inRange : index < entries.length) :
    (cValueSlotOrdinals entries)[index]? =
      some (sourceValueSlotOrdinal entries index) := by
  have mapped := cValueSlotOrdinalsFrom_get entries index 0 inRange
  simpa [cValueSlotOrdinals, Nat.zero_add] using mapped

theorem valueSlotOf_shift (target start offset : Nat) (entries : List Entry) :
    valueSlotOf target (start + offset) entries =
      (valueSlotOf target start entries).map (fun slot => slot + offset) := by
  induction entries generalizing start with
  | nil => rfl
  | cons entry rest ih =>
      cases entry with
      | function identity signature valid definition =>
          simpa [valueSlotOf] using ih start
      | value identity type valid initializer =>
          by_cases sameIdentity : identity = target
          · simp [valueSlotOf, sameIdentity]
          · simp only [valueSlotOf, beq_iff_eq]
            simp [sameIdentity]
            rw [show start + offset + 1 = (start + 1) + offset by omega,
              ih (start + 1)]

theorem valueSlotOf_result_ge_start (target start slot : Nat) (entries : List Entry)
    (found : valueSlotOf target start entries = some slot) : start ≤ slot := by
  induction entries generalizing start with
  | nil => simp [valueSlotOf] at found
  | cons entry rest ih =>
      cases entry with
      | function identity signature valid definition =>
          exact ih start (by simpa [valueSlotOf] using found)
      | value identity type valid initializer =>
          by_cases same : identity = target
          · simp [valueSlotOf, same] at found
            omega
          · have tailFound : valueSlotOf target (start + 1) rest = some slot := by
              simpa [valueSlotOf, same] using found
            have tailBound := ih (start + 1) tailFound
            omega

theorem valueSlotOf_injective (entries : List Entry) (start left right slot : Nat)
    (unique : DistinctIds (identities entries))
    (leftFound : valueSlotOf left start entries = some slot)
    (rightFound : valueSlotOf right start entries = some slot) : left = right := by
  induction entries generalizing start left right slot with
  | nil => simp [valueSlotOf] at leftFound
  | cons entry rest ih =>
      cases entry with
      | function identity signature valid definition =>
          apply ih start left right slot unique.2
            (by simpa [valueSlotOf] using leftFound)
            (by simpa [valueSlotOf] using rightFound)
      | value identity type valid initializer =>
          by_cases leftHead : identity = left
          · by_cases rightHead : identity = right
            · exact leftHead.symm.trans rightHead
            · have tailFound : valueSlotOf right (start + 1) rest = some slot := by
                simpa [valueSlotOf, rightHead] using rightFound
              have bound := valueSlotOf_result_ge_start right (start + 1) slot rest tailFound
              have startEqSlot : start = slot := by
                simpa [valueSlotOf, leftHead] using leftFound
              have leftSlot : slot = start := startEqSlot.symm
              omega
          · by_cases rightHead : identity = right
            · have tailFound : valueSlotOf left (start + 1) rest = some slot := by
                simpa [valueSlotOf, leftHead] using leftFound
              have bound := valueSlotOf_result_ge_start left (start + 1) slot rest tailFound
              have startEqSlot : start = slot := by
                simpa [valueSlotOf, rightHead] using rightFound
              have rightSlot : slot = start := startEqSlot.symm
              omega
            · have leftTail : valueSlotOf left (start + 1) rest = some slot := by
                simpa [valueSlotOf, leftHead] using leftFound
              have rightTail : valueSlotOf right (start + 1) rest = some slot := by
                simpa [valueSlotOf, rightHead] using rightFound
              exact ih (start + 1) left right slot unique.2 leftTail rightTail

theorem sourceValueSlotOrdinal_matches_identity_lookup (entries : List Entry)
    (sourceIndex identityValue : Nat) (type : Ty) (typeValid : type.wellFormed 0)
    (initializer : Expr)
    (entryAt : entries.get? sourceIndex = some (.value identityValue type typeValid initializer))
    (unique : DistinctIds (identities entries)) :
    sourceValueSlotOrdinal entries sourceIndex = valueSlotOf identityValue 0 entries := by
  induction entries generalizing sourceIndex with
  | nil => simp at entryAt
  | cons head tail ih =>
      cases head with
      | function headId signature signatureValid definition =>
          cases sourceIndex with
          | zero => simp at entryAt
          | succ sourceIndex =>
              have tailEntry : tail.get? sourceIndex =
                  some (.value identityValue type typeValid initializer) := by
                simpa using entryAt
              have tailUnique : DistinctIds (identities tail) := unique.2
              simpa [sourceValueSlotOrdinal, valueSlotOf] using ih sourceIndex tailEntry tailUnique
      | value headId headType headValid headInitializer =>
          cases sourceIndex with
          | zero =>
              have entryEq : Entry.value headId headType headValid headInitializer =
                  Entry.value identityValue type typeValid initializer := Option.some.inj entryAt
              have identityEq : headId = identityValue := congrArg identity entryEq
              simp [sourceValueSlotOrdinal, valueSlotOf, identityEq]
          | succ sourceIndex =>
              have tailEntry : tail.get? sourceIndex =
                  some (.value identityValue type typeValid initializer) := by
                simpa using entryAt
              have headNotIdentity : headId ≠ identityValue := by
                intro same
                subst identityValue
                have foundIdentity := identity_mem_of_get?_some tail sourceIndex
                  (.value headId type typeValid initializer) tailEntry
                have headNotMember : headId ∉ identities tail := by
                  simpa [identities] using unique.1
                exact headNotMember foundIdentity
              have tailUnique : DistinctIds (identities tail) := unique.2
              have tailOrdinal := ih sourceIndex tailEntry tailUnique
              rw [sourceValueSlotOrdinal, valueSlotOf]
              simp only [beq_iff_eq, headNotIdentity]
              rw [valueSlotOf_shift identityValue 0 1 tail]
              simpa [sourceValueSlotOrdinal, Nat.zero_add] using
                congrArg (Option.map Nat.succ) tailOrdinal

def initializerTerms : List Entry → List PolyIR.Term
  | [] => []
  | .function _ _ _ _ :: rest => initializerTerms rest
  | .value _ _ _ initializer :: rest => PolyIR.erase initializer :: initializerTerms rest

/-- The dense slot selected from C's mixed declaration index addresses the
same source initializer in GlobalIR's filtered initializer list. -/
theorem sourceValueSlotOrdinal_initializer_lookup (entries : List Entry)
    (sourceIndex slot identityValue : Nat) (type : Ty) (typeValid : type.wellFormed 0)
    (initializer : Expr)
    (entryAt : entries.get? sourceIndex =
      some (.value identityValue type typeValid initializer))
    (ordinal : sourceValueSlotOrdinal entries sourceIndex = some slot) :
    (initializerTerms entries).get? slot = some (PolyIR.erase initializer) := by
  induction entries generalizing sourceIndex slot with
  | nil => simp at entryAt
  | cons head tail ih =>
      cases head with
      | function functionId signature signatureValid definition =>
          cases sourceIndex with
          | zero => simp at entryAt
          | succ sourceIndex =>
              have tailEntry : tail.get? sourceIndex =
                  some (.value identityValue type typeValid initializer) := by
                simpa using entryAt
              have tailOrdinal : sourceValueSlotOrdinal tail sourceIndex = some slot := by
                simpa [sourceValueSlotOrdinal] using ordinal
              have tailInitializer := ih sourceIndex slot tailEntry tailOrdinal
              simpa [initializerTerms] using tailInitializer
      | value headId headType headValid headInitializer =>
          cases sourceIndex with
          | zero =>
              have entryEq :
                  Entry.value headId headType headValid headInitializer =
                    Entry.value identityValue type typeValid initializer :=
                Option.some.inj entryAt
              cases entryEq
              have slotEq : 0 = slot := Option.some.inj (by
                simpa [sourceValueSlotOrdinal] using ordinal)
              subst slot
              simp [initializerTerms]
          | succ sourceIndex =>
              have tailEntry : tail.get? sourceIndex =
                  some (.value identityValue type typeValid initializer) := by
                simpa using entryAt
              cases tailOrdinal : sourceValueSlotOrdinal tail sourceIndex with
              | none => simp [sourceValueSlotOrdinal, tailOrdinal] at ordinal
              | some tailSlot =>
                  have slotEq : tailSlot + 1 = slot := by
                    simpa [sourceValueSlotOrdinal, tailOrdinal] using ordinal
                  subst slot
                  have tailInitializer := ih sourceIndex tailSlot tailEntry tailOrdinal
                  simpa [initializerTerms] using tailInitializer

/-- A successful sequential GlobalIR initialization writes a value into the
dense store slot selected by a C-style mixed declaration index. The selected
initializer is shown to be the one belonging to that declaration. -/
theorem sourceValueSlotOrdinal_successful_initialization_populates
    (entries : List Entry) (sourceIndex slot identityValue : Nat) (type : Ty)
    (typeValid : type.wellFormed 0) (initializer : Expr)
    (entryAt : entries.get? sourceIndex =
      some (.value identityValue type typeValid initializer))
    (ordinal : sourceValueSlotOrdinal entries sourceIndex = some slot)
    (program : List GlobalIR.Definition) (fuel : Nat) (result : GlobalIR.Store)
    (initialized : GlobalIR.initializeValues program fuel
      (List.replicate (initializerTerms entries).length
        (none : Option PolyIR.Value)) 0 (initializerTerms entries) = .ok result) :
    ∃ value, result[slot]? = some (some value) := by
  have initializerFound := sourceValueSlotOrdinal_initializer_lookup entries sourceIndex
    slot identityValue type typeValid initializer entryAt ordinal
  have slotBound : slot < (initializerTerms entries).length :=
    (List.get?_eq_some.mp initializerFound).1
  have fits : 0 + (initializerTerms entries).length ≤
      (List.replicate (initializerTerms entries).length
        (none : Option PolyIR.Value)).length := by simp
  have selected : 0 ≤ slot ∧ slot < 0 + (initializerTerms entries).length :=
    ⟨Nat.zero_le _, by omega⟩
  exact GlobalIR.initialized_cells_present initialized fits selected

theorem sourceValueSlotOrdinal_refersToValueDeclaration (entries : List Entry)
    (sourceIndex slot : Nat)
    (resolved : sourceValueSlotOrdinal entries sourceIndex = some slot) :
    ∃ identity type initializer, ∃ valid : type.wellFormed 0,
      entries.get? sourceIndex = some (.value identity type valid initializer) := by
  induction entries generalizing sourceIndex slot with
  | nil => simp [sourceValueSlotOrdinal] at resolved
  | cons entry rest ih =>
      cases entry with
      | function identity signature valid definition =>
          cases sourceIndex with
          | zero => simp [sourceValueSlotOrdinal] at resolved
          | succ sourceIndex =>
              have tailResolved : sourceValueSlotOrdinal rest sourceIndex = some slot := by
                simpa [sourceValueSlotOrdinal] using resolved
              obtain ⟨valueIdentity, type, initializer, typeValid, found⟩ :=
                ih sourceIndex slot tailResolved
              exact ⟨valueIdentity, type, initializer, typeValid, by simpa using found⟩
      | value identity type valid initializer =>
          cases sourceIndex with
          | zero =>
              simp only [sourceValueSlotOrdinal] at resolved
              have slotEq : slot = 0 := (Option.some.inj resolved).symm
              subst slot
              exact ⟨identity, type, initializer, valid, by simp⟩
          | succ sourceIndex =>
              cases tailResolved : sourceValueSlotOrdinal rest sourceIndex with
              | none => simp [sourceValueSlotOrdinal, tailResolved] at resolved
              | some tailSlot =>
                  obtain ⟨valueIdentity, tailType, tailInitializer, typeValid, found⟩ :=
                    ih sourceIndex tailSlot tailResolved
                  exact ⟨valueIdentity, tailType, tailInitializer, typeValid, by simpa using found⟩

def compiledLayout (start : Nat) : List Entry → List (Signature × Definition)
  | [] => []
  | .function _ signature _ definition :: rest =>
      (signature, .function definition) :: compiledLayout start rest
  | .value _ type _ _ :: rest =>
      (⟨0, [], type⟩, .getter start) :: compiledLayout (start + 1) rest

theorem sourceValueSlotOrdinal_layout (entries : List Entry) (sourceIndex start slot : Nat)
    (resolved : sourceValueSlotOrdinal entries sourceIndex = some slot) :
    ∃ type,
      (compiledLayout start entries).get? sourceIndex =
        some (⟨0, [], type⟩, Definition.getter (start + slot)) := by
  induction entries generalizing sourceIndex start slot with
  | nil => simp [sourceValueSlotOrdinal] at resolved
  | cons entry rest ih =>
      cases entry with
      | function identity signature valid definition =>
          cases sourceIndex with
          | zero => simp [sourceValueSlotOrdinal] at resolved
          | succ sourceIndex =>
              have tailResolved : sourceValueSlotOrdinal rest sourceIndex = some slot := by
                simpa [sourceValueSlotOrdinal] using resolved
              obtain ⟨type, layout⟩ := ih sourceIndex start slot tailResolved
              exact ⟨type, by simpa [compiledLayout] using layout⟩
      | value identity type valid initializer =>
          cases sourceIndex with
          | zero =>
              simp only [sourceValueSlotOrdinal] at resolved
              have slotEq : slot = 0 := (Option.some.inj resolved).symm
              subst slot
              exact ⟨type, by simp [compiledLayout]⟩
          | succ sourceIndex =>
              cases tailResolved : sourceValueSlotOrdinal rest sourceIndex with
              | none => simp [sourceValueSlotOrdinal, tailResolved] at resolved
              | some tailSlot =>
                  have slotEq : Nat.succ tailSlot = slot := by
                    simpa [sourceValueSlotOrdinal, tailResolved] using resolved
                  obtain ⟨tailType, layout⟩ := ih sourceIndex (start + 1) tailSlot tailResolved
                  refine ⟨tailType, ?_⟩
                  have offset : start + 1 + tailSlot = start + slot := by omega
                  simpa [compiledLayout, offset] using layout

/-- The C-style mixed-indexed cell pointer and the compiled GlobalIR getter
at that same source declaration index select the same dense value slot. -/
theorem cValueSlotOrdinal_matches_compiledGetter
    (entries : List Entry) (sourceIndex start slot : Nat)
    (inRange : sourceIndex < entries.length)
    (ordinal : sourceValueSlotOrdinal entries sourceIndex = some slot) :
    (cValueSlotOrdinalsFrom start entries)[sourceIndex]? =
        some (some (start + slot)) ∧
      ∃ type,
        (compiledLayout start entries).get? sourceIndex =
          some (⟨0, [], type⟩, Definition.getter (start + slot)) := by
  have cSlot := cValueSlotOrdinalsFrom_get entries sourceIndex start inRange
  rw [ordinal] at cSlot
  have layout := sourceValueSlotOrdinal_layout entries sourceIndex start slot ordinal
  exact ⟨by simpa [Nat.add_comm] using cSlot, layout⟩

/-- Compose declaration lookup, generated getter layout, and successful
initializer storage: the same dense slot is selected by the declaration's
source index and contains a value after initialization. -/
theorem sourceValueSlotOrdinal_layout_and_initialized
    (entries : List Entry) (sourceIndex slot start identityValue : Nat) (type : Ty)
    (typeValid : type.wellFormed 0) (initializer : Expr)
    (entryAt : entries.get? sourceIndex =
      some (.value identityValue type typeValid initializer))
    (ordinal : sourceValueSlotOrdinal entries sourceIndex = some slot)
    (program : List GlobalIR.Definition) (fuel : Nat) (result : GlobalIR.Store)
    (initialized : GlobalIR.initializeValues program fuel
      (List.replicate (initializerTerms entries).length
        (none : Option PolyIR.Value)) 0 (initializerTerms entries) = .ok result) :
    ∃ getterType,
      (compiledLayout start entries).get? sourceIndex =
        some (⟨0, [], getterType⟩, GlobalIR.Definition.getter (start + slot)) ∧
      ∃ value, result[slot]? = some (some value) := by
  obtain ⟨getterType, getterLayout⟩ :=
    sourceValueSlotOrdinal_layout entries sourceIndex start slot ordinal
  obtain ⟨value, stored⟩ := sourceValueSlotOrdinal_successful_initialization_populates
    entries sourceIndex slot identityValue type typeValid initializer entryAt ordinal
    program fuel result initialized
  exact ⟨getterType, getterLayout, value, stored⟩

/-- A source-order value declaration's compiled getter reads the value in its
dense store slot after all initializers complete. -/
theorem sourceValueSlotOrdinal_getter_returns_initialized_value
    (entries : List Entry) (sourceIndex slot start identityValue fuel : Nat) (type : Ty)
    (typeValid : type.wellFormed 0) (initializer : Expr)
    (entryAt : entries.get? sourceIndex =
      some (.value identityValue type typeValid initializer))
    (ordinal : sourceValueSlotOrdinal entries sourceIndex = some slot)
    (startZero : start = 0)
    (program : List GlobalIR.Definition)
    (programLayout : program = (compiledLayout start entries).map Prod.snd)
    (result : GlobalIR.Store)
    (initialized : GlobalIR.initializeValues program fuel
      (List.replicate (initializerTerms entries).length
        (none : Option PolyIR.Value)) 0 (initializerTerms entries) = .ok result) :
    ∃ value,
      GlobalIR.evaluate program result (fuel + 2) [] (.app (.global sourceIndex) []) =
        .ok value ∧ result[slot]? = some (some value) := by
  obtain ⟨_, getterLayout, value, stored⟩ :=
    sourceValueSlotOrdinal_layout_and_initialized entries sourceIndex slot start
      identityValue type typeValid initializer entryAt ordinal program fuel result initialized
  obtain ⟨indexBound, getterAt⟩ := List.get?_eq_some.mp getterLayout
  have mappedBound : sourceIndex < ((compiledLayout start entries).map Prod.snd).length := by
    simpa using indexBound
  have getterMapped :
      ((compiledLayout start entries).map Prod.snd)[sourceIndex]? =
        some (GlobalIR.Definition.getter (start + slot)) := by
    simp only [getElem?_def, List.length_map, dif_pos indexBound]
    change some (((compiledLayout start entries).map Prod.snd).get
      ⟨sourceIndex, mappedBound⟩) = _
    rw [List.get_map]
    simpa using congrArg Prod.snd getterAt
  have getter : program[sourceIndex]? =
      some (GlobalIR.Definition.getter (start + slot)) := by
    rw [programLayout]
    exact getterMapped
  have getterStored : result[start + slot]? = some (some value) := by
    simpa [startZero] using stored
  exact ⟨value, GlobalIR.getter_call_reads_current_store program result fuel sourceIndex
    (start + slot) value getter getterStored, stored⟩

/-- Starting initializer stores at the same base offset used by compiled
getters aligns a source-order value declaration with its actual GlobalIR
store cell for every `start`. -/
theorem sourceValueSlotOrdinal_getter_returns_initialized_value_from_start
    (entries : List Entry) (sourceIndex slot start identityValue fuel : Nat) (type : Ty)
    (typeValid : type.wellFormed 0) (initializer : Expr)
    (entryAt : entries.get? sourceIndex =
      some (.value identityValue type typeValid initializer))
    (ordinal : sourceValueSlotOrdinal entries sourceIndex = some slot)
    (program : List GlobalIR.Definition)
    (programLayout : program = (compiledLayout start entries).map Prod.snd)
    (result : GlobalIR.Store)
    (initialized : GlobalIR.initializeValues program fuel
      (List.replicate (start + (initializerTerms entries).length)
        (none : Option PolyIR.Value)) start (initializerTerms entries) = .ok result) :
    ∃ value,
      GlobalIR.evaluate program result (fuel + 2) [] (.app (.global sourceIndex) []) =
        .ok value ∧ result[start + slot]? = some (some value) := by
  obtain ⟨layoutType, getterLayout⟩ :=
    sourceValueSlotOrdinal_layout entries sourceIndex start slot ordinal
  obtain ⟨indexBound, getterAt⟩ := List.get?_eq_some.mp getterLayout
  have getterBound : sourceIndex < ((compiledLayout start entries).map Prod.snd).length := by
    simpa using indexBound
  have getterMapped :
      ((compiledLayout start entries).map Prod.snd)[sourceIndex]? =
        some (GlobalIR.Definition.getter (start + slot)) := by
    simp only [getElem?_def, List.length_map, dif_pos indexBound]
    change some (((compiledLayout start entries).map Prod.snd).get
      ⟨sourceIndex, getterBound⟩) = _
    rw [List.get_map]
    simpa using congrArg Prod.snd getterAt
  have getter : program[sourceIndex]? =
      some (GlobalIR.Definition.getter (start + slot)) := by
    rw [programLayout]
    exact getterMapped
  have initializerFound := sourceValueSlotOrdinal_initializer_lookup entries sourceIndex
    slot identityValue type typeValid initializer entryAt ordinal
  have slotBound : slot < (initializerTerms entries).length :=
    (List.get?_eq_some.mp initializerFound).1
  have fits : start + (initializerTerms entries).length ≤
      (List.replicate (start + (initializerTerms entries).length)
        (none : Option PolyIR.Value)).length := by simp
  have selected : start ≤ start + slot ∧
      start + slot < start + (initializerTerms entries).length := by omega
  obtain ⟨value, stored⟩ := GlobalIR.initialized_cells_present initialized fits selected
  exact ⟨value, GlobalIR.getter_call_reads_current_store program result fuel sourceIndex
    (start + slot) value getter stored, stored⟩

theorem sourceValueSlotOrdinal_complete (entries : List Entry) (sourceIndex start : Nat)
    (signature : Signature) (globalSlot : Nat)
    (found : (compiledLayout start entries).get? sourceIndex =
      some (signature, Definition.getter globalSlot)) :
    ∃ slot, sourceValueSlotOrdinal entries sourceIndex = some slot ∧
      signature = ⟨0, [], (match entries[sourceIndex]? with
        | some (.value _ type _ _) => type
        | _ => .unit)⟩ ∧ globalSlot = start + slot := by
  induction entries generalizing sourceIndex start signature globalSlot with
  | nil => simp [compiledLayout] at found
  | cons entry rest ih =>
      cases entry with
      | function identity entrySignature valid definition =>
          cases sourceIndex with
          | zero => simp [compiledLayout] at found
          | succ sourceIndex =>
              have tailFound : (compiledLayout start rest).get? sourceIndex =
                  some (signature, Definition.getter globalSlot) := by
                simpa [compiledLayout] using found
              obtain ⟨slot, ordinal, typeEq, slotEq⟩ :=
                ih sourceIndex start signature globalSlot tailFound
              refine ⟨slot, ?_, ?_, slotEq⟩
              · simpa [sourceValueSlotOrdinal] using ordinal
              · simpa using typeEq
      | value identity type valid initializer =>
          cases sourceIndex with
          | zero =>
              simp [compiledLayout] at found
              rcases found with ⟨rfl, rfl⟩
              exact ⟨0, by simp [sourceValueSlotOrdinal], by simp, by omega⟩
          | succ sourceIndex =>
              have tailFound : (compiledLayout (start + 1) rest).get? sourceIndex =
                  some (signature, Definition.getter globalSlot) := by
                simpa [compiledLayout] using found
              obtain ⟨tailSlot, ordinal, typeEq, slotEq⟩ :=
                ih sourceIndex (start + 1) signature globalSlot tailFound
              refine ⟨tailSlot + 1, ?_, ?_, ?_⟩
              · simp [sourceValueSlotOrdinal, ordinal]
              · simpa using typeEq
              · omega

def toDefinitions (start : Nat) : List Entry → List Definition
  | [] => []
  | .function _ _ _ definition :: rest =>
      .function definition :: toDefinitions start rest
  | .value _ _ _ _ :: rest => .getter start :: toDefinitions (start + 1) rest

/-- Getter mappings for the actual mixed declaration table. Unlike the
function-prefix layout in `GlobalIR.getterMappings`, both the source global
index and runtime getter index advance through every declaration. -/
def getterMappingsFromEntries (globalIndex : Nat) : List Entry → List (Nat × Nat)
  | [] => []
  | .function _ _ _ _ :: rest => getterMappingsFromEntries (globalIndex + 1) rest
  | .value _ _ _ _ :: rest =>
      (globalIndex, globalIndex) :: getterMappingsFromEntries (globalIndex + 1) rest

theorem getterMappingsFromEntries_value_lookup (globalIndex : Nat) (entries : List Entry)
    (index identity : Nat) (type : Ty) (valid : type.wellFormed 0)
    (initializer : Surface.Expr)
    (found : entries.get? index = some (.value identity type valid initializer)) :
    GlobalIR.getterFor (getterMappingsFromEntries globalIndex entries)
      (globalIndex + index) = some (globalIndex + index) := by
  induction entries generalizing globalIndex index with
  | nil => simp at found
  | cons entry rest ih =>
      cases entry with
      | function functionId signature signatureValid definition =>
          cases index with
          | zero => simp at found
          | succ index =>
              have tailFound : rest.get? index =
                  some (.value identity type valid initializer) := by
                simpa using found
              have tailMapped := ih (globalIndex + 1) index tailFound
              simpa [getterMappingsFromEntries, GlobalIR.getterFor,
                Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using tailMapped
      | value valueId valueType valueValid valueInitializer =>
          cases index with
          | zero =>
              simp at found
              rcases found with ⟨rfl, rfl, rfl, rfl⟩
              simp [getterMappingsFromEntries, GlobalIR.getterFor]
          | succ index =>
              have tailFound : rest.get? index =
                  some (.value identity type valid initializer) := by
                simpa using found
              have tailMapped := ih (globalIndex + 1) index tailFound
              have queryDifferent : globalIndex ≠ globalIndex + Nat.succ index := by omega
              simp only [getterMappingsFromEntries, GlobalIR.getterFor, if_neg queryDifferent]
              rw [show globalIndex + Nat.succ index = globalIndex + 1 + index by omega]
              simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using tailMapped

/-- For a mixed declaration table with unique binding identities, a value
declaration's source index is preserved by both identity lookup and the
GlobalIR getter map. -/
theorem mixed_value_identity_and_getter_index (entries : List Entry) (index identity : Nat)
    (type : Ty) (valid : type.wellFormed 0) (initializer : Surface.Expr)
    (unique : DistinctIds (identities entries))
    (found : entries.get? index = some (.value identity type valid initializer)) :
    globalIndexOf identity entries = some index ∧
      GlobalIR.getterFor (getterMappingsFromEntries 0 entries) index = some index := by
  constructor
  · exact globalIndexOf_get?_unique entries index
      (.value identity type valid initializer) identity unique found rfl
  · have mapped := getterMappingsFromEntries_value_lookup 0 entries index identity type
      valid initializer found
    simpa using mapped

theorem lowerGlobalReads_mixed_value_reference (entries : List Entry) (index : Nat)
    (identity : Nat) (type : Ty) (valid : type.wellFormed 0)
    (initializer : Surface.Expr)
    (found : entries.get? index = some (.value identity type valid initializer)) :
    GlobalIR.lowerGlobalReads (getterMappingsFromEntries 0 entries)
      (.app (.global index) []) = .app (.global index) [] := by
  have mapping := getterMappingsFromEntries_value_lookup 0 entries index identity type valid
    initializer found
  have mapping' : GlobalIR.getterFor (getterMappingsFromEntries 0 entries) index = some index := by
    simpa using mapping
  exact GlobalIR.lowerGlobalReads_zero_arg_value_getter
    (getterMappingsFromEntries 0 entries) index index mapping'

/- Surface initializer forms supported by the proved arithmetic execution
fragment. -/
inductive ArithmeticSurfaceExpr : Surface.Expr → Ty → Prop where
  | bool : ArithmeticSurfaceExpr (.bool value) .boolean
  | int : ArithmeticSurfaceExpr (.int value) .integer
  | float : ArithmeticSurfaceExpr (.float value) .float
  | string : ArithmeticSurfaceExpr (.string value) .string
  | character : ArithmeticSurfaceExpr (.character value) .character
  | unit : ArithmeticSurfaceExpr .unit .unit
  | nil : type.wellFormed 0 → ArithmeticSurfaceExpr (.nil type) (.list type)
  | none : type.wellFormed 0 → ArithmeticSurfaceExpr (.none type) (.option type)
  | some : type.wellFormed 0 → ArithmeticSurfaceExpr value type →
      ArithmeticSurfaceExpr (.some type value) (.option type)
  | cons : type.wellFormed 0 → ArithmeticSurfaceExpr head type →
      ArithmeticSurfaceExpr tail (.list type) →
      ArithmeticSurfaceExpr (.cons type head tail) (.list type)
  | ite : ArithmeticSurfaceExpr condition .boolean →
      ArithmeticSurfaceExpr yes resultType → ArithmeticSurfaceExpr no resultType →
      ArithmeticSurfaceExpr (.ite condition yes no) resultType
  | matchOption : ArithmeticSurfaceExpr target (.option element) →
      ArithmeticSurfaceExpr empty resultType → ArithmeticSurfaceExpr full resultType →
      ArithmeticSurfaceExpr (.matchOption target empty full) resultType
  | matchList : ArithmeticSurfaceExpr target (.list element) →
      ArithmeticSurfaceExpr empty resultType → ArithmeticSurfaceExpr full resultType →
      ArithmeticSurfaceExpr (.matchList target empty full) resultType
  | add : ArithmeticSurfaceExpr left .integer → ArithmeticSurfaceExpr right .integer →
      ArithmeticSurfaceExpr (.add left right) .integer
  | sub : ArithmeticSurfaceExpr left .integer → ArithmeticSurfaceExpr right .integer →
      ArithmeticSurfaceExpr (.sub left right) .integer
  | mul : ArithmeticSurfaceExpr left .integer → ArithmeticSurfaceExpr right .integer →
      ArithmeticSurfaceExpr (.mul left right) .integer
  | le : ArithmeticSurfaceExpr left .integer → ArithmeticSurfaceExpr right .integer →
      ArithmeticSurfaceExpr (.le left right) .boolean
  | intEq : ArithmeticSurfaceExpr left .integer → ArithmeticSurfaceExpr right .integer →
      ArithmeticSurfaceExpr (.intEq left right) .boolean
  | floatBin : ArithmeticSurfaceExpr left .float → ArithmeticSurfaceExpr right .float →
      ArithmeticSurfaceExpr (.floatBin op left right) .float

theorem ArithmeticSurfaceExpr.hasType {globals : List Signature}
    {context : List Ty} {expression : Surface.Expr} {type : Ty}
    (arithmetic : ArithmeticSurfaceExpr expression type) :
    Surface.HasType globals 0 context expression type := by
  induction arithmetic generalizing context with
  | bool => exact .bool
  | int => exact .int
  | float => exact .float
  | string => exact .string
  | character => exact .character
  | unit => exact .unit
  | nil typeValid => exact .nil typeValid
  | none typeValid => exact .none typeValid
  | some typeValid valueTyped valueHasType => exact .some typeValid valueHasType
  | cons typeValid headTyped tailTyped headHasType tailHasType =>
      exact .cons typeValid headHasType tailHasType
  | ite conditionTyped yesTyped noTyped conditionHasType yesHasType noHasType =>
      exact .ite conditionHasType yesHasType noHasType
  | matchOption targetTyped emptyTyped fullTyped targetHasType emptyHasType fullHasType =>
      exact .matchOption targetHasType emptyHasType
        (fullHasType (context := _ :: context))
  | matchList targetTyped emptyTyped fullTyped targetHasType emptyHasType fullHasType =>
      exact .matchList targetHasType emptyHasType
        (fullHasType (context := _ :: _ :: context))
  | add left right leftTyped rightTyped => exact .add leftTyped rightTyped
  | sub left right leftTyped rightTyped => exact .sub leftTyped rightTyped
  | mul left right leftTyped rightTyped => exact .mul leftTyped rightTyped
  | le left right leftTyped rightTyped => exact .le leftTyped rightTyped
  | intEq left right leftTyped rightTyped => exact .intEq leftTyped rightTyped
  | floatBin left right leftTyped rightTyped => exact .floatBin leftTyped rightTyped

theorem ArithmeticSurfaceExpr.erase {expression : Surface.Expr} {type : Ty}
    (arithmetic : ArithmeticSurfaceExpr expression type) :
    GlobalIR.ArithmeticTerm (PolyIR.erase expression) type := by
  induction arithmetic with
  | bool => simpa [PolyIR.erase] using GlobalIR.ArithmeticTerm.bool
  | int => simpa [PolyIR.erase] using GlobalIR.ArithmeticTerm.int
  | float => simpa [PolyIR.erase] using GlobalIR.ArithmeticTerm.float
  | string => simpa [PolyIR.erase] using GlobalIR.ArithmeticTerm.string
  | character => simpa [PolyIR.erase] using GlobalIR.ArithmeticTerm.character
  | unit => simpa [PolyIR.erase] using GlobalIR.ArithmeticTerm.unit
  | nil _ => simpa [PolyIR.erase] using GlobalIR.ArithmeticTerm.nil
  | none _ => simpa [PolyIR.erase] using GlobalIR.ArithmeticTerm.none
  | some _ valueTyped valueErased =>
      simpa [PolyIR.erase] using GlobalIR.ArithmeticTerm.some valueErased
  | cons _ headTyped tailTyped headErased tailErased =>
      simpa [PolyIR.erase] using GlobalIR.ArithmeticTerm.cons headErased tailErased
  | ite conditionTyped yesTyped noTyped condition yes no =>
      simpa [PolyIR.erase] using GlobalIR.ArithmeticTerm.ite condition yes no
  | matchOption targetTyped emptyTyped fullTyped targetErased emptyErased fullErased =>
      simpa [PolyIR.erase] using
        GlobalIR.ArithmeticTerm.matchOption targetErased emptyErased fullErased
  | matchList targetTyped emptyTyped fullTyped targetErased emptyErased fullErased =>
      simpa [PolyIR.erase] using
        GlobalIR.ArithmeticTerm.matchList targetErased emptyErased fullErased
  | add left right leftErased rightErased =>
      simpa [PolyIR.erase] using GlobalIR.ArithmeticTerm.add leftErased rightErased
  | sub left right leftErased rightErased =>
      simpa [PolyIR.erase] using GlobalIR.ArithmeticTerm.sub leftErased rightErased
  | mul left right leftErased rightErased =>
      simpa [PolyIR.erase] using GlobalIR.ArithmeticTerm.mul leftErased rightErased
  | le left right leftErased rightErased =>
      simpa [PolyIR.erase] using GlobalIR.ArithmeticTerm.le leftErased rightErased
  | intEq left right leftErased rightErased =>
      simpa [PolyIR.erase] using GlobalIR.ArithmeticTerm.intEq leftErased rightErased
  | floatBin left right leftErased rightErased =>
      simpa [PolyIR.erase] using GlobalIR.ArithmeticTerm.floatBin leftErased rightErased

/- Source rows whose initializer forms belong to this arithmetic fragment.
The slot index advances only across value declarations. -/
def ArithmeticInitializerRows (slotTypes : List Ty) : Nat → List Entry → Prop
  | _, [] => True
  | slot, .function _ _ _ _ :: rest => ArithmeticInitializerRows slotTypes slot rest
  | slot, .value _ type _ initializer :: rest =>
      slotTypes.get? slot = some type ∧
        ArithmeticSurfaceExpr initializer type ∧
        ArithmeticInitializerRows slotTypes (slot + 1) rest

/- Source-order initializer rows typed by the contextual GlobalIR fragment.
This admits typed global function and getter references as well as the local
arithmetic fragment. -/
def ContextualGlobalInitializerRows (globals : List Signature)
    (assignment : Nat → Ty) (slotTypes : List Ty) : Nat → List Entry → Prop
  | _, [] => True
  | slot, .function _ _ _ _ :: rest =>
      ContextualGlobalInitializerRows globals assignment slotTypes slot rest
  | slot, .value _ type _ initializer :: rest =>
      slotTypes.get? slot = some type ∧
        GlobalIR.ContextualGlobalArithmeticTerm globals assignment []
          (PolyIR.erase initializer) type ∧
        ContextualGlobalInitializerRows globals assignment slotTypes (slot + 1) rest

/- Source-order initializer rows typed by the runtime GlobalIR fragment. This
includes generated getter reads, so later values may depend on earlier slots
while preserving the declared slot types. -/
def ContextualGlobalRuntimeInitializerRows (globals : List Signature)
    (assignment : Nat → Ty) (definitions : Surface.Definitions)
    (slotTypes : List Ty) (functionSources : List (Nat × Nat))
    (program : List Definition) : Nat → List Entry → Prop
  | _, [] => True
  | slot, .function _ _ _ _ :: rest =>
      ContextualGlobalRuntimeInitializerRows globals assignment definitions
        slotTypes functionSources program slot rest
  | slot, .value _ type _ initializer :: rest =>
      slotTypes.get? slot = some type ∧
        GlobalIR.ContextualGlobalRuntimeTerm globals assignment definitions slotTypes
          functionSources program [] (PolyIR.erase initializer) type ∧
        ContextualGlobalRuntimeInitializerRows globals assignment definitions
          slotTypes functionSources program (slot + 1) rest

theorem ContextualGlobalInitializerRows.toTypesAgree
    (globals : List Signature) (assignment : Nat → Ty) (slotTypes : List Ty)
    (slot : Nat) (rows : List Entry)
    (contextual : ContextualGlobalInitializerRows globals assignment slotTypes slot rows) :
    GlobalIR.ContextualGlobalInitializerTypesAgree globals assignment slotTypes slot
      (initializerTerms rows) := by
  induction rows generalizing slot with
  | nil => simp [initializerTerms, GlobalIR.ContextualGlobalInitializerTypesAgree]
  | cons row tail ih =>
      cases row with
      | function identity signature valid definition =>
          simpa [initializerTerms, ContextualGlobalInitializerRows,
            GlobalIR.ContextualGlobalInitializerTypesAgree] using
            ih (slot := slot) (by simpa [ContextualGlobalInitializerRows] using contextual)
      | value identity type valid initializer =>
          rcases contextual with ⟨slotType, initializerTyped, tailTyped⟩
          simp only [initializerTerms,
            GlobalIR.ContextualGlobalInitializerTypesAgree]
          exact ⟨type, slotType, initializerTyped, ih (slot := slot + 1) tailTyped⟩

theorem ContextualGlobalInitializerRows.toRuntimeRows
    (globals : List Signature) (assignment : Nat → Ty)
    (definitions : Surface.Definitions) (slotTypes : List Ty)
    (functionSources : List (Nat × Nat)) (program : List Definition)
    (slot : Nat) (rows : List Entry)
    (contextual : ContextualGlobalInitializerRows globals assignment slotTypes slot rows) :
    ContextualGlobalRuntimeInitializerRows globals assignment definitions slotTypes
      functionSources program slot rows := by
  induction rows generalizing slot with
  | nil => simp [ContextualGlobalRuntimeInitializerRows]
  | cons row tail ih =>
      cases row with
      | function identity signature valid definition =>
          simpa [ContextualGlobalRuntimeInitializerRows,
            ContextualGlobalInitializerRows] using
            ih (slot := slot) (by
              simpa [ContextualGlobalInitializerRows] using contextual)
      | value identity type valid initializer =>
          rcases contextual with ⟨slotType, initializerTyped, tailTyped⟩
          simp only [ContextualGlobalRuntimeInitializerRows]
          exact ⟨slotType, .arithmetic initializerTyped,
            ih (slot := slot + 1) tailTyped⟩

theorem ContextualGlobalRuntimeInitializerRows.toRuntimeTypesAgree
    (globals : List Signature) (assignment : Nat → Ty)
    (definitions : Surface.Definitions) (slotTypes : List Ty)
    (functionSources : List (Nat × Nat)) (program : List Definition)
    (slot : Nat) (rows : List Entry)
    (contextual : ContextualGlobalRuntimeInitializerRows globals assignment definitions
      slotTypes functionSources program slot rows) :
    GlobalIR.ContextualGlobalRuntimeInitializerTypesAgree globals assignment definitions
      slotTypes functionSources program slot (initializerTerms rows) := by
  induction rows generalizing slot with
  | nil => simp [initializerTerms, GlobalIR.ContextualGlobalRuntimeInitializerTypesAgree]
  | cons row tail ih =>
      cases row with
      | function identity signature valid definition =>
          simpa [initializerTerms, ContextualGlobalRuntimeInitializerRows,
            GlobalIR.ContextualGlobalRuntimeInitializerTypesAgree] using
            ih (slot := slot) (by
              simpa [ContextualGlobalRuntimeInitializerRows] using contextual)
      | value identity type valid initializer =>
          rcases contextual with ⟨slotType, initializerTyped, tailTyped⟩
          simp only [initializerTerms,
            GlobalIR.ContextualGlobalRuntimeInitializerTypesAgree]
          exact ⟨type, slotType, initializerTyped, ih (slot := slot + 1) tailTyped⟩

def toRuntimeProgram (entries : List Entry) (entry : Nat) : GlobalIR.Program :=
  ⟨toDefinitions 0 entries, initializerTerms entries, entry⟩

theorem initializerTerms_length (entries : List Entry) :
    (initializerTerms entries).length = (valueTypes entries).length := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
      cases entry <;> simp [initializerTerms, valueTypes, ih]

/-- A successful initialization of mixed top-level declarations preserves the
whole typed GlobalIR store when each source initializer is typed in the runtime
fragment. This admits generated getters and functions in initializer terms. -/
theorem ContextualGlobalRuntimeInitializerRows.toRuntimeProgram_initialization_preserves_store
    (entries : List Entry) (globals : List Signature) (assignment : Nat → Ty)
    (definitions : Surface.Definitions) (functionSources : List (Nat × Nat))
    (entryIndex fuel : Nat) (result : Store)
    (programTyped : GlobalProgramTyped globals definitions (valueTypes entries)
      functionSources (toRuntimeProgram entries entryIndex).definitions)
    (rows : ContextualGlobalRuntimeInitializerRows globals assignment definitions
      (valueTypes entries) functionSources
      (toRuntimeProgram entries entryIndex).definitions 0 entries)
    (initialization : initializeValues
      (toRuntimeProgram entries entryIndex).definitions fuel
      (List.replicate (toRuntimeProgram entries entryIndex).initializers.length none)
      0 (toRuntimeProgram entries entryIndex).initializers = .ok result) :
    StoreWellTyped globals (valueTypes entries) result := by
  have typesAgree := ContextualGlobalRuntimeInitializerRows.toRuntimeTypesAgree
    globals assignment definitions (valueTypes entries) functionSources
    (toRuntimeProgram entries entryIndex).definitions 0 entries rows
  have initializerTermsEq : (toRuntimeProgram entries entryIndex).initializers =
      initializerTerms entries := rfl
  rw [initializerTermsEq] at initialization
  exact GlobalIR.initializeValues_contextualGlobalRuntime_preserves_typed
    globals assignment definitions (valueTypes entries) functionSources
    (toRuntimeProgram entries entryIndex).definitions programTyped fuel
    (List.replicate (initializerTerms entries).length none) 0 (initializerTerms entries)
    result (by simpa using initializerTerms_length entries)
    (GlobalIR.empty_store_well_typed globals (valueTypes entries)
      (initializerTerms entries).length) typesAgree
    (by
      intro offset below
      simpa using below) initialization

theorem ArithmeticInitializerRows.contextualGlobalTypesAgree
    (globals : List Signature) (assignment : Nat → Ty) (slotTypes : List Ty)
    (slot : Nat) (rows : List Entry)
    (arithmetic : ArithmeticInitializerRows slotTypes slot rows) :
    GlobalIR.ContextualGlobalInitializerTypesAgree globals assignment slotTypes slot
      (initializerTerms rows) := by
  induction rows generalizing slot with
  | nil => simp [initializerTerms, GlobalIR.ContextualGlobalInitializerTypesAgree]
  | cons row tail ih =>
      cases row with
      | function identity signature valid definition =>
          simpa [initializerTerms, ArithmeticInitializerRows,
            GlobalIR.ContextualGlobalInitializerTypesAgree] using
            ih (slot := slot) (by simpa [ArithmeticInitializerRows] using arithmetic)
      | value identity type valid initializer =>
          have parts : slotTypes.get? slot = some type ∧
              ArithmeticSurfaceExpr initializer type ∧
              ArithmeticInitializerRows slotTypes (slot + 1) tail := by
            simpa [ArithmeticInitializerRows] using arithmetic
          simpa [initializerTerms, GlobalIR.ContextualGlobalInitializerTypesAgree] using
            (⟨type, parts.1,
              ContextualGlobalArithmeticTerm.arithmetic
                (ContextualArithmeticTerm.closed parts.2.1.erase),
              ih (slot := slot + 1) parts.2.2⟩)

theorem toRuntimeProgram_layout (entries : List Entry) (entryIndex : Nat) :
    (toRuntimeProgram entries entryIndex).definitions = toDefinitions 0 entries ∧
    (toRuntimeProgram entries entryIndex).initializers.length = (valueTypes entries).length := by
  exact ⟨rfl, initializerTerms_length entries⟩

def compiledGetterTypes : List (Signature × Definition) → List Ty
  | [] => []
  | (_signature, .function _) :: rest => compiledGetterTypes rest
  | (signature, .getter _) :: rest => signature.result :: compiledGetterTypes rest

def compiledDefinitions (layout : List (Signature × Definition)) : List Definition :=
  layout.map Prod.snd

theorem toDefinitions_eq_compiledDefinitions (start : Nat) (entries : List Entry) :
    toDefinitions start entries = compiledDefinitions (compiledLayout start entries) := by
  induction entries generalizing start with
  | nil => rfl
  | cons entry rest ih =>
      cases entry <;> simp [toDefinitions, compiledDefinitions, compiledLayout, ih]

theorem toDefinitions_getter_of_layout (start : Nat) (entries : List Entry)
    (index : Nat) (signature : Signature) (slot : Nat)
    (found : (compiledLayout start entries).get? index =
      some (signature, Definition.getter slot)) :
    (toDefinitions start entries).get? index = some (Definition.getter slot) := by
  rw [toDefinitions_eq_compiledDefinitions]
  simp [compiledDefinitions, found]

theorem toDefinitions_function_of_layout (start : Nat) (entries : List Entry)
    (index : Nat) (signature : Signature) (definition : RuntimeDefinition)
    (found : (compiledLayout start entries).get? index =
      some (signature, Definition.function definition)) :
    (toDefinitions start entries).get? index = some (Definition.function definition) := by
  rw [toDefinitions_eq_compiledDefinitions]
  simp [compiledDefinitions, found]

private theorem entry_getElem?_eq_get? {α : Type} (items : List α) (index : Nat) :
    items[index]? = items.get? index := by
  by_cases bound : index < items.length
  · simp only [getElem?_def, dif_pos bound]
    exact (List.get?_eq_some).2 ⟨bound, rfl⟩ |>.symm
  · have outside : items.length ≤ index := Nat.le_of_not_gt bound
    simp only [getElem?_def, dif_neg bound]
    exact (List.get?_eq_none).2 outside |>.symm

/-- For a uniquely named mixed value declaration, identity lookup selects its
source index, the C `value_slots` ordinal selects its shared cell, and the
compiled GlobalIR getter at the same index observes the same
before-initialization state. -/
theorem mixed_value_identity_cell_and_getter_before_initialization
    (entries : List Entry) (index identity : Nat) (type : Ty)
    (valid : type.wellFormed 0) (initializer : Surface.Expr) (slot : Nat)
    (unique : DistinctIds (identities entries))
    (found : entries.get? index = some (.value identity type valid initializer))
    (ordinal : sourceValueSlotOrdinal entries index = some slot)
    (cells : GlobalIR.Store) (uninitialized : cells[slot]? = some none) :
    globalIndexOf identity entries = some index ∧
      GlobalIR.getterFor (getterMappingsFromEntries 0 entries) index = some index ∧
      cValueSlotCellRead (cValueSlotOrdinals entries) cells index = none ∧
      GlobalIR.evaluate (toDefinitions 0 entries) cells 2 []
        (.app (.global index) []) = .error (.beforeInitialization slot) := by
  have nameLookup := globalIndexOf_get?_unique entries index
    (.value identity type valid initializer) identity unique found rfl
  have getterMapping := getterMappingsFromEntries_value_lookup 0 entries index identity type
    valid initializer found
  have inRange : index < entries.length := (List.get?_eq_some.mp found).1
  have cOrdinal := cValueSlotOrdinals_get entries index inRange
  have cPointer : (cValueSlotOrdinals entries)[index]? = some (some slot) := by
    rw [cOrdinal, ordinal]
  obtain ⟨getterType, getterLayout⟩ := sourceValueSlotOrdinal_layout entries index 0 slot ordinal
  have getterLayout' : (compiledLayout 0 entries).get? index =
      some (⟨0, [], getterType⟩, GlobalIR.Definition.getter slot) := by
    simpa using getterLayout
  have getterGet? := toDefinitions_getter_of_layout 0 entries index
    ⟨0, [], getterType⟩ slot getterLayout'
  have getter : (toDefinitions 0 entries)[index]? =
      some (GlobalIR.Definition.getter slot) := by
    rw [entry_getElem?_eq_get?]
    exact getterGet?
  have cellAndRead := cValueSlotCellRead_and_getter_beforeInitialization
    (cValueSlotOrdinals entries) cells index slot 0 cPointer (toDefinitions 0 entries)
    getter uninitialized
  exact ⟨nameLookup, by simpa using getterMapping, cellAndRead.1, cellAndRead.2⟩

/-- A successful C-style name lookup can be carried through its selected
source index to the corresponding uninitialized value cell and GlobalIR
getter, once the decoded named layout agrees positionally with the source
declarations. -/
theorem named_value_lookup_cell_and_getter_before_initialization
    (named : List CNameResolution.Entry) (entries : List Entry)
    (name : String) (binding : CNameResolution.Entry) (index slot sourceIdentity : Nat)
    (type : Ty) (valid : type.wellFormed 0) (initializer : Surface.Expr)
    (layout : NamedGlobalLayout named entries)
    (unique : DistinctIds (identities entries))
    (nameFound : CNameResolution.findName named name = some binding)
    (nameIndex : CNameResolution.findNameIndex named name = some index)
    (entryAt : entries.get? index = some (.value sourceIdentity type valid initializer))
    (ordinal : sourceValueSlotOrdinal entries index = some slot)
    (cells : GlobalIR.Store) (uninitialized : cells[slot]? = some none) :
    CNameResolution.findNameIndex named name = some index ∧
      globalIndexOf binding.identity entries = some index ∧
      GlobalIR.getterFor (getterMappingsFromEntries 0 entries) index = some index ∧
      cValueSlotCellRead (cValueSlotOrdinals entries) cells index = none ∧
      GlobalIR.evaluate (toDefinitions 0 entries) cells 2 []
        (.app (.global index) []) = .error (.beforeInitialization slot) := by
  obtain ⟨selected, selectedFound, namedAtIndex⟩ :=
    CNameResolution.findNameIndex_sound named name index nameIndex
  have selectedEq : binding = selected := Option.some.inj (by
    rw [nameFound] at selectedFound
    exact selectedFound)
  have namedAtIndex' : named.get? index = some binding := by
    rw [selectedEq]
    exact namedAtIndex
  have identityAgreement := layout.2 index binding
    (.value sourceIdentity type valid initializer) namedAtIndex' entryAt
  change binding.identity = sourceIdentity at identityAgreement
  have base := mixed_value_identity_cell_and_getter_before_initialization entries index
    sourceIdentity type valid initializer slot unique entryAt ordinal cells uninitialized
  have namedIdentityLookup : globalIndexOf binding.identity entries = some index := by
    simpa [identityAgreement] using base.1
  exact ⟨nameIndex, namedIdentityLookup, base.2.1, base.2.2.1, base.2.2.2⟩

/-- After successful initialization, a C-style mixed declaration index reads
back the initialized value through its GlobalIR getter. This composes the
source-index to dense-slot initializer mapping with the compiled getter table
and the store observed at evaluation time. -/
theorem sourceValueSlotOrdinal_successful_getter_reads
    (entries : List Entry) (sourceIndex slot identityValue : Nat) (type : Ty)
    (typeValid : type.wellFormed 0) (initializer : Expr)
    (entryAt : entries.get? sourceIndex =
      some (.value identityValue type typeValid initializer))
    (ordinal : sourceValueSlotOrdinal entries sourceIndex = some slot)
    (fuel : Nat) (result : GlobalIR.Store)
    (initialized : GlobalIR.initializeValues (toDefinitions 0 entries) fuel
      (List.replicate (initializerTerms entries).length
        (none : Option PolyIR.Value)) 0 (initializerTerms entries) = .ok result) :
    ∃ value, GlobalIR.evaluate (toDefinitions 0 entries) result (fuel + 2) []
      (.app (.global sourceIndex) []) = .ok value := by
  obtain ⟨layoutType, layout⟩ :=
    sourceValueSlotOrdinal_layout entries sourceIndex 0 slot ordinal
  have layout' : (compiledLayout 0 entries).get? sourceIndex =
      some (⟨0, [], layoutType⟩, Definition.getter slot) := by
    simpa using layout
  have getter : (toDefinitions 0 entries).get? sourceIndex =
      some (Definition.getter slot) :=
    toDefinitions_getter_of_layout 0 entries sourceIndex ⟨0, [], layoutType⟩ slot layout'
  have getterIndexed : (toDefinitions 0 entries)[sourceIndex]? =
      some (Definition.getter slot) := by
    rw [entry_getElem?_eq_get?]
    exact getter
  obtain ⟨value, stored⟩ := sourceValueSlotOrdinal_successful_initialization_populates
    entries sourceIndex slot identityValue type typeValid initializer entryAt ordinal
    (toDefinitions 0 entries) fuel result initialized
  exact ⟨value, GlobalIR.getter_call_reads_current_store (toDefinitions 0 entries)
    result fuel sourceIndex slot value getterIndexed stored⟩

/-- The value reached through a mixed declaration index is the very value
committed to its dense slot by initialization.  This joins the initializer
slot map and the getter read in one result, rather than proving only that each
side returns some value independently. -/
theorem sourceValueSlotOrdinal_successful_getter_reads_same_value
    (entries : List Entry) (sourceIndex slot identityValue fuel : Nat) (type : Ty)
    (typeValid : type.wellFormed 0) (initializer : Expr)
    (entryAt : entries.get? sourceIndex =
      some (.value identityValue type typeValid initializer))
    (ordinal : sourceValueSlotOrdinal entries sourceIndex = some slot)
    (result : GlobalIR.Store)
    (initialized : GlobalIR.initializeValues (toDefinitions 0 entries) fuel
      (List.replicate (initializerTerms entries).length
        (none : Option PolyIR.Value)) 0 (initializerTerms entries) = .ok result) :
    ∃ value, result[slot]? = some (some value) ∧
      GlobalIR.evaluate (toDefinitions 0 entries) result (fuel + 2) []
        (.app (.global sourceIndex) []) = .ok value := by
  obtain ⟨value, stored⟩ := sourceValueSlotOrdinal_successful_initialization_populates
    entries sourceIndex slot identityValue type typeValid initializer entryAt ordinal
    (toDefinitions 0 entries) fuel result initialized
  obtain ⟨getterType, layout⟩ :=
    sourceValueSlotOrdinal_layout entries sourceIndex 0 slot ordinal
  have layout' : (compiledLayout 0 entries).get? sourceIndex =
      some (⟨0, [], getterType⟩, Definition.getter slot) := by
    simpa [Nat.zero_add] using layout
  have getter : (toDefinitions 0 entries)[sourceIndex]? =
      some (Definition.getter slot) := by
    rw [entry_getElem?_eq_get?]
    exact toDefinitions_getter_of_layout 0 entries sourceIndex
      ⟨0, [], getterType⟩ slot layout'
  exact ⟨value, stored,
    GlobalIR.getter_call_reads_current_store (toDefinitions 0 entries) result fuel
      sourceIndex slot value getter stored⟩

/-- Join the mixed-index C `value_slots` model with successful GlobalIR
initialization and getter evaluation. A C cell pointer at a source declaration
index resolves to the same dense ordinal that initialization commits and the
compiled getter reads. -/
theorem cValueSlotOrdinal_successful_getter_reads_same_value
    (entries : List Entry) (sourceIndex slot identityValue fuel : Nat) (type : Ty)
    (typeValid : type.wellFormed 0) (initializer : Expr)
    (entryAt : entries.get? sourceIndex =
      some (.value identityValue type typeValid initializer))
    (cellPointer : (cValueSlotOrdinals entries)[sourceIndex]? = some (some slot))
    (result : GlobalIR.Store)
    (initialized : GlobalIR.initializeValues (toDefinitions 0 entries) fuel
      (List.replicate (initializerTerms entries).length
        (none : Option PolyIR.Value)) 0 (initializerTerms entries) = .ok result) :
    ∃ value, result[slot]? = some (some value) ∧
      GlobalIR.evaluate (toDefinitions 0 entries) result (fuel + 2) []
        (.app (.global sourceIndex) []) = .ok value := by
  have inRange : sourceIndex < entries.length :=
    (List.get?_eq_some.mp entryAt).1
  have slotMap := cValueSlotOrdinals_get entries sourceIndex inRange
  rw [slotMap] at cellPointer
  have ordinal : sourceValueSlotOrdinal entries sourceIndex = some slot :=
    Option.some.inj cellPointer
  exact sourceValueSlotOrdinal_successful_getter_reads_same_value entries sourceIndex
    slot identityValue fuel type typeValid initializer entryAt ordinal result initialized

/-- A C closure environment that retains the pointer in `value_slots` sees
the initialized value through that same shared cell; reading it agrees with
the GlobalIR getter at the original mixed declaration index. -/
theorem cValueSlotCellRead_matches_initialized_getter
    (entries : List Entry) (sourceIndex slot identityValue fuel : Nat) (type : Ty)
    (typeValid : type.wellFormed 0) (initializer : Expr)
    (entryAt : entries.get? sourceIndex =
      some (.value identityValue type typeValid initializer))
    (cellPointer : (cValueSlotOrdinals entries)[sourceIndex]? = some (some slot))
    (result : GlobalIR.Store)
    (initialized : GlobalIR.initializeValues (toDefinitions 0 entries) fuel
      (List.replicate (initializerTerms entries).length
        (none : Option PolyIR.Value)) 0 (initializerTerms entries) = .ok result) :
    ∃ value, cValueSlotCellRead (cValueSlotOrdinals entries) result sourceIndex =
      some value ∧
      GlobalIR.evaluate (toDefinitions 0 entries) result (fuel + 2) []
        (.app (.global sourceIndex) []) = .ok value := by
  obtain ⟨value, stored, getterEval⟩ := cValueSlotOrdinal_successful_getter_reads_same_value
    entries sourceIndex slot identityValue fuel type typeValid initializer entryAt cellPointer
    result initialized
  refine ⟨value, ?_, getterEval⟩
  simp [cValueSlotCellRead, cellPointer, stored]

/-- End-to-end layout theorem for a mixed top-level value after successful
initialization: C-style name lookup, its selected mixed declaration index,
the shared `value_slots` cell, and the compiled GlobalIR getter all identify
and return the same value. -/
theorem named_value_lookup_matches_initialized_getter
    (named : List CNameResolution.Entry) (entries : List Entry)
    (name : String) (binding : CNameResolution.Entry) (index slot sourceIdentity : Nat)
    (type : Ty) (valid : type.wellFormed 0) (initializer : Expr)
    (layout : NamedGlobalLayout named entries)
    (unique : DistinctIds (identities entries))
    (nameFound : CNameResolution.findName named name = some binding)
    (nameIndex : CNameResolution.findNameIndex named name = some index)
    (entryAt : entries.get? index = some (.value sourceIdentity type valid initializer))
    (ordinal : sourceValueSlotOrdinal entries index = some slot)
    (fuel : Nat) (result : GlobalIR.Store)
    (initialized : GlobalIR.initializeValues (toDefinitions 0 entries) fuel
      (List.replicate (initializerTerms entries).length
        (none : Option PolyIR.Value)) 0 (initializerTerms entries) = .ok result) :
    CNameResolution.findNameIndex named name = some index ∧
      globalIndexOf binding.identity entries = some index ∧
      GlobalIR.getterFor (getterMappingsFromEntries 0 entries) index = some index ∧
      ∃ value, cValueSlotCellRead (cValueSlotOrdinals entries) result index = some value ∧
        GlobalIR.evaluate (toDefinitions 0 entries) result (fuel + 2) []
          (.app (.global index) []) = .ok value := by
  obtain ⟨selected, selectedFound, namedAtIndex⟩ :=
    CNameResolution.findNameIndex_sound named name index nameIndex
  have selectedEq : binding = selected := Option.some.inj (by
    rw [nameFound] at selectedFound
    exact selectedFound)
  have namedAtIndex' : named.get? index = some binding := by
    rw [selectedEq]
    exact namedAtIndex
  have identityMatches := layout.2 index binding
    (.value sourceIdentity type valid initializer) namedAtIndex' entryAt
  change binding.identity = sourceIdentity at identityMatches
  have globalIndexResult := globalIndexOf_get?_unique entries index
    (.value sourceIdentity type valid initializer) binding.identity unique entryAt
    identityMatches.symm
  have getterResult :
      GlobalIR.getterFor (getterMappingsFromEntries 0 entries) index = some index := by
    simpa using getterMappingsFromEntries_value_lookup 0 entries index sourceIdentity type
      valid initializer entryAt
  have inRange : index < entries.length := (List.get?_eq_some.mp entryAt).1
  have cellPointer : (cValueSlotOrdinals entries)[index]? = some (some slot) := by
    rw [cValueSlotOrdinals_get entries index inRange, ordinal]
  have valuesAgree := cValueSlotCellRead_matches_initialized_getter entries index slot
    sourceIdentity fuel type valid initializer entryAt cellPointer result initialized
  exact ⟨nameIndex, globalIndexResult, getterResult, valuesAgree⟩

private theorem sourceValueSlotOrdinal_exists_of_value_lookup (entries : List Entry)
    (sourceIndex identityValue : Nat) (type : Ty) (typeValid : type.wellFormed 0)
    (initializer : Expr)
    (entryAt : entries.get? sourceIndex =
      some (.value identityValue type typeValid initializer)) :
    ∃ slot, sourceValueSlotOrdinal entries sourceIndex = some slot := by
  induction entries generalizing sourceIndex with
  | nil => simp at entryAt
  | cons entry rest ih =>
      cases entry with
      | function functionId signature signatureValid definition =>
          cases sourceIndex with
          | zero => simp at entryAt
          | succ sourceIndex =>
              have tailEntry : rest.get? sourceIndex =
                  some (.value identityValue type typeValid initializer) := by
                simpa using entryAt
              obtain ⟨slot, ordinal⟩ := ih sourceIndex tailEntry
              exact ⟨slot, by simpa [sourceValueSlotOrdinal] using ordinal⟩
      | value valueId valueType valueValid valueInitializer =>
          cases sourceIndex with
          | zero =>
              have entryEq : Entry.value valueId valueType valueValid valueInitializer =
                  Entry.value identityValue type typeValid initializer := Option.some.inj entryAt
              exact ⟨0, by simp [sourceValueSlotOrdinal, congrArg identity entryEq]⟩
          | succ sourceIndex =>
              have tailEntry : rest.get? sourceIndex =
                  some (.value identityValue type typeValid initializer) := by
                simpa using entryAt
              obtain ⟨slot, ordinal⟩ := ih sourceIndex tailEntry
              exact ⟨slot + 1, by simp [sourceValueSlotOrdinal, ordinal]⟩

private theorem replicate_lookup_eq_some_value {α : Type} (count index : Nat)
    (value : α) (bound : index < count) :
    (List.replicate count value)[index]? = some value := by
  induction count generalizing index with
  | zero => omega
  | succ count ih =>
      cases index with
      | zero => simp [List.replicate, getElem?_def]
      | succ index =>
          have tailBound : index < count := by omega
          simpa [List.replicate, getElem?_def, Nat.succ_lt_succ_iff] using
            ih index tailBound

/-- Compose identity-based C lookup, the mixed declaration index, the dense
`value_slots` ordinal, the shared cell read, and the compiled GlobalIR getter
for one initialized top-level value. -/
theorem cIdentityLookup_value_reads_initialized_getter
    (entries : List Entry) (sourceIndex identityValue fuel : Nat) (type : Ty)
    (typeValid : type.wellFormed 0) (initializer : Expr)
    (entryAt : entries.get? sourceIndex =
      some (.value identityValue type typeValid initializer))
    (unique : DistinctIds (identities entries))
    (result : GlobalIR.Store)
    (initialized : GlobalIR.initializeValues (toDefinitions 0 entries) fuel
      (List.replicate (initializerTerms entries).length
        (none : Option PolyIR.Value)) 0 (initializerTerms entries) = .ok result) :
    globalIndexOf identityValue entries = some sourceIndex ∧
    ∃ slot value,
      valueSlotOf identityValue 0 entries = some slot ∧
      cValueSlotCellRead (cValueSlotOrdinals entries) result sourceIndex = some value ∧
      GlobalIR.evaluate (toDefinitions 0 entries) result (fuel + 2) []
        (.app (.global sourceIndex) []) = .ok value := by
  have identityAndGetter := mixed_value_identity_and_getter_index entries sourceIndex
    identityValue type typeValid initializer unique entryAt
  have ordinalMatches := sourceValueSlotOrdinal_matches_identity_lookup entries sourceIndex
    identityValue type typeValid initializer entryAt unique
  cases slotResult : valueSlotOf identityValue 0 entries with
  | none =>
      rw [slotResult] at ordinalMatches
      obtain ⟨slot, ordinal⟩ := sourceValueSlotOrdinal_exists_of_value_lookup
        entries sourceIndex identityValue type typeValid initializer entryAt
      rw [ordinalMatches] at ordinal
      simp at ordinal
  | some slot =>
      have ordinal : sourceValueSlotOrdinal entries sourceIndex = some slot := by
        rw [ordinalMatches, slotResult]
      have cellPointer : (cValueSlotOrdinals entries)[sourceIndex]? = some (some slot) := by
        rw [cValueSlotOrdinals_get entries sourceIndex (List.get?_eq_some.mp entryAt).1,
          ordinal]
      obtain ⟨value, cellRead, getterRead⟩ :=
        cValueSlotCellRead_matches_initialized_getter entries sourceIndex slot identityValue
          fuel type typeValid initializer entryAt cellPointer result initialized
      exact ⟨identityAndGetter.1, ⟨slot, value, rfl, cellRead, getterRead⟩⟩

/-- The same identity-to-slot path preserves the before-initialization state:
the C shared-cell model observes an empty value and the compiled GlobalIR
getter reports the matching slot fault. -/
theorem cIdentityLookup_value_before_initialization
    (entries : List Entry) (sourceIndex identityValue : Nat) (type : Ty)
    (typeValid : type.wellFormed 0) (initializer : Expr)
    (entryAt : entries.get? sourceIndex =
      some (.value identityValue type typeValid initializer))
    (unique : DistinctIds (identities entries))
    (store : GlobalIR.Store)
    (uninitialized : ∀ slot, valueSlotOf identityValue 0 entries = some slot →
      store[slot]? = some none) :
    globalIndexOf identityValue entries = some sourceIndex ∧
    ∃ slot, valueSlotOf identityValue 0 entries = some slot ∧
      store[slot]? = some none ∧
      cValueSlotCellRead (cValueSlotOrdinals entries) store sourceIndex = none ∧
      GlobalIR.evaluate (toDefinitions 0 entries) store 2 []
        (.app (.global sourceIndex) []) = .error (.beforeInitialization slot) := by
  have identityAndGetter := mixed_value_identity_and_getter_index entries sourceIndex
    identityValue type typeValid initializer unique entryAt
  have ordinalMatches := sourceValueSlotOrdinal_matches_identity_lookup entries sourceIndex
    identityValue type typeValid initializer entryAt unique
  have ordinalExists := sourceValueSlotOrdinal_exists_of_value_lookup entries sourceIndex
    identityValue type typeValid initializer entryAt
  cases slotResult : valueSlotOf identityValue 0 entries with
  | none =>
      rw [slotResult] at ordinalMatches
      obtain ⟨someSlot, ordinal⟩ := ordinalExists
      rw [ordinalMatches] at ordinal
      simp at ordinal
  | some foundSlot =>
      have ordinal : sourceValueSlotOrdinal entries sourceIndex = some foundSlot := by
        rw [ordinalMatches, slotResult]
      have emptyCell : store[foundSlot]? = some none :=
        uninitialized foundSlot slotResult
      have cellPointer : (cValueSlotOrdinals entries)[sourceIndex]? =
          some (some foundSlot) := by
        rw [cValueSlotOrdinals_get entries sourceIndex (List.get?_eq_some.mp entryAt).1,
          ordinal]
      obtain ⟨getterType, layout⟩ := sourceValueSlotOrdinal_layout entries sourceIndex
        0 foundSlot ordinal
      have layout' : (compiledLayout 0 entries).get? sourceIndex =
          some (⟨0, [], getterType⟩, Definition.getter foundSlot) := by
        simpa using layout
      have getter : (toDefinitions 0 entries)[sourceIndex]? =
          some (Definition.getter foundSlot) := by
        rw [entry_getElem?_eq_get?]
        exact toDefinitions_getter_of_layout 0 entries sourceIndex
          ⟨0, [], getterType⟩ foundSlot layout'
      have beforeInitialization := cValueSlotCellRead_and_getter_beforeInitialization
        (cValueSlotOrdinals entries) store sourceIndex foundSlot 0 cellPointer
        (toDefinitions 0 entries) getter emptyCell
      exact ⟨identityAndGetter.1, ⟨foundSlot, rfl, emptyCell, beforeInitialization.1,
        by simpa [GlobalIR.evaluate, GlobalIR.evaluateArgs, getter, GlobalIR.readGlobal,
          emptyCell, List.isEmpty] using beforeInitialization.2⟩⟩

/-- Specialize the identity-to-getter fault correspondence to GlobalIR's
actual initial store: every declared value slot begins as `none`, so a
source-order value reference before its initializer commits reports the
matching early-read fault. -/
theorem cIdentityLookup_value_faults_from_initial_store
    (entries : List Entry) (sourceIndex identityValue : Nat) (type : Ty)
    (typeValid : type.wellFormed 0) (initializer : Expr)
    (entryAt : entries.get? sourceIndex =
      some (.value identityValue type typeValid initializer))
    (unique : DistinctIds (identities entries)) :
    globalIndexOf identityValue entries = some sourceIndex ∧
    ∃ slot,
      valueSlotOf identityValue 0 entries = some slot ∧
      cValueSlotCellRead (cValueSlotOrdinals entries)
        (List.replicate (initializerTerms entries).length
          (none : Option PolyIR.Value)) sourceIndex = none ∧
      GlobalIR.evaluate (toDefinitions 0 entries)
        (List.replicate (initializerTerms entries).length
          (none : Option PolyIR.Value)) 2 []
        (.app (.global sourceIndex) []) = .error (.beforeInitialization slot) := by
  have ordinalMatches := sourceValueSlotOrdinal_matches_identity_lookup entries sourceIndex
    identityValue type typeValid initializer entryAt unique
  have ordinalExists := sourceValueSlotOrdinal_exists_of_value_lookup entries sourceIndex
    identityValue type typeValid initializer entryAt
  cases slotResult : valueSlotOf identityValue 0 entries with
  | none =>
      rw [slotResult] at ordinalMatches
      obtain ⟨slot, ordinal⟩ := ordinalExists
      rw [ordinalMatches] at ordinal
      simp at ordinal
  | some slot =>
      have ordinal : sourceValueSlotOrdinal entries sourceIndex = some slot := by
        rw [ordinalMatches, slotResult]
      have initializerFound := sourceValueSlotOrdinal_initializer_lookup entries sourceIndex
        slot identityValue type typeValid initializer entryAt ordinal
      have slotBound : slot < (initializerTerms entries).length :=
        (List.get?_eq_some.mp initializerFound).1
      have emptyAtSlot :
          (List.replicate (initializerTerms entries).length
            (none : Option PolyIR.Value))[slot]? = some none := by
        exact replicate_lookup_eq_some_value (initializerTerms entries).length slot
          none slotBound
      have general := cIdentityLookup_value_before_initialization entries sourceIndex
        identityValue type typeValid initializer entryAt unique
        (List.replicate (initializerTerms entries).length
          (none : Option PolyIR.Value)) (fun other found => by
            have otherOrdinal : sourceValueSlotOrdinal entries sourceIndex = some other :=
              ordinalMatches.trans found
            have otherInitializer := sourceValueSlotOrdinal_initializer_lookup entries
              sourceIndex other identityValue type typeValid initializer entryAt otherOrdinal
            have otherBound : other < (initializerTerms entries).length :=
              (List.get?_eq_some.mp otherInitializer).1
            exact replicate_lookup_eq_some_value (initializerTerms entries).length other
              none otherBound)
      rcases general with ⟨globalIndex, selectedSlot, selected, _emptyCell,
        cellRead, getterRead⟩
      have selectedEq : selectedSlot = slot := Option.some.inj (selected.symm.trans slotResult)
      subst selectedSlot
      exact ⟨globalIndex, slot, rfl, cellRead, getterRead⟩

/-- After an arbitrary successful prefix that ends before a referenced value's
dense slot, the committed store still contains `none` at that slot. Identity
lookup, the prefix frame property, and getter evaluation then agree on the
same before-initialization fault. -/
theorem cIdentityLookup_value_faults_after_prefix
    (entries : List Entry) (sourceIndex identityValue : Nat) (type : Ty)
    (typeValid : type.wellFormed 0) (initializer : Expr)
    (entryAt : entries.get? sourceIndex =
      some (.value identityValue type typeValid initializer))
    (unique : DistinctIds (identities entries)) (prefixFuel : Nat)
    (prefixTerms : List PolyIR.Term) (after : GlobalIR.Store)
    (prefixSuccess : GlobalIR.initializeValues (toDefinitions 0 entries) prefixFuel
      (List.replicate (initializerTerms entries).length
        (none : Option PolyIR.Value)) 0 prefixTerms = .ok after)
    (prefixBeforeValueSlot : ∀ slot,
      valueSlotOf identityValue 0 entries = some slot → prefixTerms.length ≤ slot) :
    globalIndexOf identityValue entries = some sourceIndex ∧
    ∃ slot,
      valueSlotOf identityValue 0 entries = some slot ∧
      cValueSlotCellRead (cValueSlotOrdinals entries) after sourceIndex = none ∧
      GlobalIR.evaluate (toDefinitions 0 entries) after 2 []
        (.app (.global sourceIndex) []) = .error (.beforeInitialization slot) := by
  have ordinalMatches := sourceValueSlotOrdinal_matches_identity_lookup entries sourceIndex
    identityValue type typeValid initializer entryAt unique
  have ordinalExists := sourceValueSlotOrdinal_exists_of_value_lookup entries sourceIndex
    identityValue type typeValid initializer entryAt
  cases slotResult : valueSlotOf identityValue 0 entries with
  | none =>
      rw [slotResult] at ordinalMatches
      obtain ⟨slot, ordinal⟩ := ordinalExists
      rw [ordinalMatches] at ordinal
      simp at ordinal
  | some slot =>
      have ordinal : sourceValueSlotOrdinal entries sourceIndex = some slot := by
        rw [ordinalMatches, slotResult]
      have initializerFound := sourceValueSlotOrdinal_initializer_lookup entries sourceIndex
        slot identityValue type typeValid initializer entryAt ordinal
      have slotBound : slot < (initializerTerms entries).length :=
        (List.get?_eq_some.mp initializerFound).1
      have initialEmpty := replicate_lookup_eq_some_value
        (initializerTerms entries).length slot (none : Option PolyIR.Value) slotBound
      have selectedStillEmpty : after[slot]? = some none := by
        have unchanged := GlobalIR.initializeValues_success_preserves_slots_after
          (toDefinitions 0 entries) prefixFuel
          (List.replicate (initializerTerms entries).length
            (none : Option PolyIR.Value)) 0 prefixTerms after slot prefixSuccess
          (by simpa using prefixBeforeValueSlot slot slotResult)
        exact unchanged.trans initialEmpty
      have everyResolvedSlotEmpty : ∀ other,
          valueSlotOf identityValue 0 entries = some other → after[other]? = some none := by
        intro other found
        have sameSlot : slot = other := Option.some.inj (slotResult.symm.trans found)
        subst other
        exact selectedStillEmpty
      obtain ⟨globalLookup, selectedSlot, selected, _emptyCell, cellRead, getterRead⟩ :=
        cIdentityLookup_value_before_initialization entries sourceIndex identityValue
          type typeValid initializer entryAt unique after everyResolvedSlotEmpty
      have selectedEq : selectedSlot = slot :=
        Option.some.inj (selected.symm.trans slotResult)
      subst selectedSlot
      exact ⟨globalLookup, ⟨slot, rfl, cellRead, getterRead⟩⟩

theorem compiledGetterTypes_compiledLayout (start : Nat) (entries : List Entry) :
    compiledGetterTypes (compiledLayout start entries) = valueTypes entries := by
  induction entries generalizing start with
  | nil => rfl
  | cons entry rest ih =>
      cases entry <;> simp [compiledLayout, compiledGetterTypes, valueTypes, ih]

@[simp] theorem identities_cons (entry : Entry) (entries : List Entry) :
    identities (entry :: entries) = identity entry :: identities entries := rfl

@[simp] theorem valueIdentities_value (id : Nat) (type : Ty)
    (valid : type.wellFormed 0) (initializer : Expr) (entries : List Entry) :
    valueIdentities (.value id type valid initializer :: entries) =
      id :: valueIdentities entries := rfl

theorem identities_length (entries : List Entry) :
    (identities entries).length = entries.length := by
  induction entries with
  | nil => rfl
  | cons _ rest ih => simp [identities, ih]

theorem value_layout_lengths (entries : List Entry) :
    (valueIdentities entries).length = (valueTypes entries).length := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
      cases entry <;> simp [valueIdentities, valueTypes, ih]

theorem valueIdentities_subset_identities (entries : List Entry) :
    ∀ selected, selected ∈ valueIdentities entries → selected ∈ identities entries := by
  induction entries with
  | nil => simp [valueIdentities]
  | cons entry rest ih =>
      cases entry <;> simp_all [valueIdentities, identities, identity]

theorem functionIdentities_subset_identities (entries : List Entry) :
    ∀ selected, selected ∈ functionIdentities entries → selected ∈ identities entries := by
  induction entries with
  | nil => simp [functionIdentities]
  | cons entry rest ih =>
      cases entry <;> simp_all [functionIdentities, identities, identity]

theorem value_function_identity_disjoint (entries : List Entry) (selected : Nat)
    (unique : DistinctIds (identities entries))
    (valueMember : selected ∈ valueIdentities entries) :
    selected ∉ functionIdentities entries := by
  induction entries with
  | nil => simp [valueIdentities] at valueMember
  | cons entry rest ih =>
      cases entry with
      | function id signature valid definition =>
          have uniqueHead : id ∉ identities rest ∧ DistinctIds (identities rest) := by
            change DistinctIds (id :: identities rest) at unique
            exact unique
          have tailValue : selected ∈ valueIdentities rest := by
            simpa [valueIdentities] using valueMember
          intro functionMember
          simp only [functionIdentities, List.mem_cons] at functionMember
          rcases functionMember with same | tailFunction
          · subst selected
            exact uniqueHead.1 (valueIdentities_subset_identities rest id tailValue)
          · exact ih uniqueHead.2 tailValue tailFunction
      | value id type valid initializer =>
          have uniqueHead : id ∉ identities rest ∧ DistinctIds (identities rest) := by
            change DistinctIds (id :: identities rest) at unique
            exact unique
          simp only [valueIdentities, List.mem_cons] at valueMember
          rcases valueMember with same | tailValue
          · subst selected
            intro functionMember
            exact uniqueHead.1
              (functionIdentities_subset_identities rest id functionMember)
          · intro functionMember
            have tailFunction : selected ∈ functionIdentities rest := by
              simpa [functionIdentities] using functionMember
            exact ih uniqueHead.2 tailValue tailFunction

theorem valueIdentities_filter_subset (entries : List Entry) (keep : Entry → Bool) :
    ∀ selected, selected ∈ valueIdentities (entries.filter keep) →
      selected ∈ valueIdentities entries := by
  induction entries with
  | nil => simp [valueIdentities]
  | cons entry rest ih =>
      cases entry with
      | function id signature valid definition =>
          intro selected member
          by_cases kept : keep (.function id signature valid definition) = true
          · have tailMember : selected ∈ valueIdentities (rest.filter keep) := by
              simpa [List.filter_cons, kept, valueIdentities] using member
            exact ih selected tailMember
          · have tailMember : selected ∈ valueIdentities (rest.filter keep) := by
              simpa [List.filter_cons, kept, valueIdentities] using member
            exact ih selected tailMember
      | value id type valid initializer =>
          intro selected member
          by_cases kept : keep (.value id type valid initializer) = true
          · simp only [List.filter_cons, kept, valueIdentities, List.mem_cons] at member
            rcases member with same | tailMember
            · exact List.mem_cons.mpr (Or.inl same)
            · exact List.mem_cons_of_mem _ (ih selected tailMember)
          · have tailMember : selected ∈ valueIdentities (rest.filter keep) := by
              simpa [List.filter_cons, kept, valueIdentities] using member
            exact List.mem_cons_of_mem _ (ih selected tailMember)

theorem functionIdentities_filter_subset (entries : List Entry) (keep : Entry → Bool) :
    ∀ selected, selected ∈ functionIdentities (entries.filter keep) →
      selected ∈ functionIdentities entries := by
  induction entries with
  | nil => simp [functionIdentities]
  | cons entry rest ih =>
      cases entry with
      | function id signature valid definition =>
          intro selected member
          by_cases kept : keep (.function id signature valid definition) = true
          · simp only [List.filter_cons, kept, functionIdentities, List.mem_cons] at member
            rcases member with same | tailMember
            · exact List.mem_cons.mpr (Or.inl same)
            · exact List.mem_cons_of_mem _ (ih selected tailMember)
          · have tailMember : selected ∈ functionIdentities (rest.filter keep) := by
              simpa [List.filter_cons, kept, functionIdentities] using member
            exact List.mem_cons_of_mem _ (ih selected tailMember)
      | value id type valid initializer =>
          intro selected member
          by_cases kept : keep (.value id type valid initializer) = true
          · have tailMember : selected ∈ functionIdentities (rest.filter keep) := by
              simpa [List.filter_cons, kept, functionIdentities] using member
            exact ih selected tailMember
          · have tailMember : selected ∈ functionIdentities (rest.filter keep) := by
              simpa [List.filter_cons, kept, functionIdentities] using member
            exact ih selected tailMember

theorem valueIdentity_getter_at_globalIndex (selected start : Nat) (entries : List Entry)
    (unique : DistinctIds (identities entries))
    (member : selected ∈ valueIdentities entries) :
    ∃ type globalIndex slot,
      globalIndexOf selected entries = some globalIndex ∧
      valueSlotOf selected start entries = some slot ∧
      (compiledLayout start entries).get? globalIndex =
        some (⟨0, [], type⟩, Definition.getter slot) := by
  induction entries generalizing start with
  | nil => simp [valueIdentities] at member
  | cons entry rest ih =>
      cases entry with
      | function id signature valid definition =>
          have uniqueHead : id ∉ identities rest ∧ DistinctIds (identities rest) := by
            change DistinctIds (id :: identities rest) at unique
            exact unique
          have tailMember : selected ∈ valueIdentities rest := by
            simpa [valueIdentities] using member
          have different : id ≠ selected := by
            intro same
            apply uniqueHead.1
            rw [same]
            exact valueIdentities_subset_identities rest selected tailMember
          obtain ⟨type, index, slot, globalFound, slotFound, layoutFound⟩ :=
            ih start uniqueHead.2 tailMember
          refine ⟨type, index + 1, slot, ?_, ?_, ?_⟩
          · simp [identity, globalIndexOf, different, globalFound]
          · simpa [valueSlotOf] using slotFound
          · simp [compiledLayout, layoutFound]
      | value id type valid initializer =>
          have uniqueParts : id ∉ identities rest ∧ DistinctIds (identities rest) := by
            change DistinctIds (id :: identities rest) at unique
            exact unique
          simp only [valueIdentities, List.mem_cons] at member
          rcases member with same | tailMember
          · have selectedEq : selected = id := same
            subst selected
            refine ⟨type, 0, start, ?_, ?_, ?_⟩ <;>
              simp [identity, globalIndexOf, valueSlotOf, compiledLayout]
          · have different : id ≠ selected := by
              intro equal
              apply uniqueParts.1
              rw [equal]
              exact valueIdentities_subset_identities rest selected tailMember
            obtain ⟨resultType, index, slot, globalFound, slotFound, layoutFound⟩ :=
              ih (start + 1) uniqueParts.2 tailMember
            refine ⟨resultType, index + 1, slot, ?_, ?_, ?_⟩
            · simp [identity, globalIndexOf, different, globalFound]
            · simp [identity, valueSlotOf, different, slotFound]
            · simp [compiledLayout, layoutFound]

theorem functionIdentity_function_at_globalIndex (selected start : Nat) (entries : List Entry)
    (unique : DistinctIds (identities entries))
    (member : selected ∈ functionIdentities entries) :
    ∃ signature definition globalIndex,
      globalIndexOf selected entries = some globalIndex ∧
      (compiledLayout start entries).get? globalIndex =
        some (signature, Definition.function definition) := by
  induction entries generalizing start with
  | nil => simp [functionIdentities] at member
  | cons entry rest ih =>
      cases entry with
      | function id signature signatureValid definition =>
          have uniqueHead : id ∉ identities rest ∧ DistinctIds (identities rest) := by
            change DistinctIds (id :: identities rest) at unique
            exact unique
          have memberParts : selected = id ∨ selected ∈ functionIdentities rest := by
            simpa [functionIdentities] using member
          rcases memberParts with same | tailMember
          · subst selected
            exact ⟨signature, definition, 0, by simp [identity, globalIndexOf], by
              simp [compiledLayout]⟩
          · have different : id ≠ selected := by
              intro same
              apply uniqueHead.1
              rw [same]
              exact functionIdentities_subset_identities rest selected tailMember
            obtain ⟨tailSignature, tailDefinition, index, globalFound, layoutFound⟩ :=
              ih start uniqueHead.2 tailMember
            refine ⟨tailSignature, tailDefinition, index + 1, ?_, ?_⟩
            · simp [identity, globalIndexOf, different, globalFound]
            · simpa [compiledLayout] using layoutFound
      | value id type typeValid initializer =>
          have uniqueHead : id ∉ identities rest ∧ DistinctIds (identities rest) := by
            change DistinctIds (id :: identities rest) at unique
            exact unique
          have tailMember : selected ∈ functionIdentities rest := by
            simpa [functionIdentities] using member
          have different : id ≠ selected := by
            intro same
            apply uniqueHead.1
            rw [same]
            exact functionIdentities_subset_identities rest selected tailMember
          obtain ⟨tailSignature, tailDefinition, index, globalFound, layoutFound⟩ :=
            ih (start + 1) uniqueHead.2 tailMember
          refine ⟨tailSignature, tailDefinition, index + 1, ?_, ?_⟩
          · simp [identity, globalIndexOf, different, globalFound]
          · simpa [compiledLayout] using layoutFound


theorem compiledLayout_length (start : Nat) (entries : List Entry) :
    (compiledLayout start entries).length = entries.length := by
  induction entries generalizing start with
  | nil => rfl
  | cons entry rest ih =>
      cases entry <;> simp [compiledLayout, ih]

theorem toDefinitions_length (start : Nat) (entries : List Entry) :
    (toDefinitions start entries).length = entries.length := by
  induction entries generalizing start with
  | nil => rfl
  | cons entry rest ih =>
      cases entry <;> simp [toDefinitions, ih]

def signatures (entries : List Entry) : List Signature :=
  (compiledLayout 0 entries).map Prod.fst

theorem signatures_eq_of_compiledLayout_eq (entries other : List Entry)
    (sameLayout : compiledLayout 0 entries = compiledLayout 0 other) :
    signatures entries = signatures other := by
  simp [signatures, sameLayout]

structure TypedInitializer (entries : List Entry) (expected : Ty) (source : Surface.Expr) where
  expression : Surface.Expr
  typing : Surface.HasType (signatures entries) 0 [] expression expected
  term : PolyIR.Term
  erasure : term = PolyIR.erase expression
  sourceExact : expression = source

def TypedInitializer.transport {entries other : List Entry} {expected : Ty}
    {source : Surface.Expr} (sameSignatures : signatures entries = signatures other)
    (typed : TypedInitializer entries expected source) :
    TypedInitializer other expected source :=
  ⟨typed.expression, by rw [← sameSignatures]; exact typed.typing,
    typed.term, typed.erasure, typed.sourceExact⟩

def checkInitializer (fuel : Nat) (entries : List Entry)
    (expression : Surface.Expr) (expected : Ty) :
    Option (TypedInitializer entries expected expression) :=
  match accepted : Surface.elaborate fuel (signatures entries) 0 [] expression expected with
  | none => none
  | some checked =>
      some ⟨checked.expression, checked.typing, PolyIR.erase checked.expression, rfl,
        Surface.elaborate_expression accepted⟩

theorem checkInitializer_isSome (fuel : Nat) (entries : List Entry)
    (expression : Surface.Expr) (expected : Ty) :
    (checkInitializer fuel entries expression expected).isSome =
      (Surface.elaborate fuel (signatures entries) 0 [] expression expected).isSome := by
  unfold checkInitializer
  split <;> simp_all

theorem checkInitializer_eventually_of_typed (entries : List Entry)
    (expression : Surface.Expr) (expected : Ty)
    (typing : Surface.HasType (signatures entries) 0 [] expression expected) :
    ∃ bound, ∀ fuel, bound ≤ fuel →
      (checkInitializer fuel entries expression expected).isSome = true := by
  obtain ⟨bound, eventually⟩ := Surface.elaborate_eventually typing
  refine ⟨bound, ?_⟩
  intro fuel enough
  rw [checkInitializer_isSome]
  exact eventually fuel enough

theorem checkInitializer_sound (fuel : Nat) (entries : List Entry)
    (expression : Surface.Expr) (expected : Ty)
    (accepted : (checkInitializer fuel entries expression expected).isSome = true) :
    ∃ checked, checkInitializer fuel entries expression expected = some checked ∧
      Surface.HasType (signatures entries) 0 [] checked.expression expected ∧
      checked.expression = expression ∧ checked.term = PolyIR.erase checked.expression := by
  cases result : checkInitializer fuel entries expression expected with
  | none => simp [result] at accepted
  | some checked =>
      exact ⟨checked, rfl, checked.typing, checked.sourceExact, checked.erasure⟩

/- A source-order initializer row carries its own typing derivation and the
slot/type correspondence required by GlobalIR's sequential store invariant. -/
inductive TypedInitializerRows (entries : List Entry) (slotTypes : List Ty) :
    Nat → List Entry → Prop where
  | nil : TypedInitializerRows entries slotTypes slot []
  | function (slot : Nat) (identity : Nat) (signature : Signature)
      (valid : signature.wellFormed) (definition : RuntimeDefinition)
      (tail : List Entry) (rest : TypedInitializerRows entries slotTypes slot tail) :
      TypedInitializerRows entries slotTypes slot
        (.function identity signature valid definition :: tail)
  | value (slot : Nat) (identity : Nat) (type : Ty) (valid : type.wellFormed 0)
      (initializer : Expr)
      (slotType : slotTypes.get? slot = some type)
      (typed : Surface.HasType (signatures entries) 0 [] initializer type)
      (tail : List Entry) (rest : TypedInitializerRows entries slotTypes (slot + 1) tail) :
      TypedInitializerRows entries slotTypes slot
        (.value identity type valid initializer :: tail)

/-- Checker acceptance for each value row, together with the slot layout,
is sufficient evidence to build a typed initializer table. -/
inductive InitializerCheckerRows (fuel : Nat) (entries : List Entry)
    (slotTypes : List Ty) : Nat → List Entry → Prop where
  | nil : InitializerCheckerRows fuel entries slotTypes slot []
  | function (slot identity : Nat) (signature : Signature)
      (valid : signature.wellFormed) (definition : RuntimeDefinition)
      (tail : List Entry)
      (rest : InitializerCheckerRows fuel entries slotTypes slot tail) :
      InitializerCheckerRows fuel entries slotTypes slot
        (.function identity signature valid definition :: tail)
  | value (slot identity : Nat) (type : Ty) (valid : type.wellFormed 0)
      (initializer : Expr) (slotType : slotTypes.get? slot = some type)
      (accepted : (checkInitializer fuel entries initializer type).isSome = true)
      (tail : List Entry)
      (rest : InitializerCheckerRows fuel entries slotTypes (slot + 1) tail) :
      InitializerCheckerRows fuel entries slotTypes slot
        (.value identity type valid initializer :: tail)

/-- Executable scan for checker acceptance and dense value-slot alignment.
Function entries leave the slot counter unchanged; each value row advances it. -/
def checkInitializerRows (fuel : Nat) (entries : List Entry)
    (slotTypes : List Ty) (slot : Nat) : List Entry → Bool
  | [] => true
  | .function _ _ _ _ :: tail => checkInitializerRows fuel entries slotTypes slot tail
  | .value _ type _ initializer :: tail =>
      decide (slotTypes.get? slot = some type) &&
        (checkInitializer fuel entries initializer type).isSome &&
          checkInitializerRows fuel entries slotTypes (slot + 1) tail

/-- Success of the executable row scan yields the proof-carrying invariant
consumed by the GlobalIR initializer and store safety results. -/
theorem checkInitializerRows_sound (fuel : Nat) (entries : List Entry)
    (slotTypes : List Ty) (slot : Nat) (rows : List Entry)
    (accepted : checkInitializerRows fuel entries slotTypes slot rows = true) :
    InitializerCheckerRows fuel entries slotTypes slot rows := by
  induction rows generalizing slot with
  | nil => exact .nil
  | cons row tail ih =>
      cases row with
      | function identity signature valid definition =>
          exact .function slot identity signature valid definition tail
            (ih slot (by simpa [checkInitializerRows] using accepted))
      | value identity type valid initializer =>
          have parts :
              (decide (slotTypes.get? slot = some type) = true ∧
                (checkInitializer fuel entries initializer type).isSome = true) ∧
              checkInitializerRows fuel entries slotTypes (slot + 1) tail = true := by
            simpa [checkInitializerRows, Bool.and_eq_true] using accepted
          exact .value slot identity type valid initializer
            (of_decide_eq_true parts.1.1) parts.1.2 tail (ih (slot + 1) parts.2)

/-- The executable row scan accepts exactly the proof-carrying row layouts;
this gives both soundness and completeness for the local initializer checker. -/
theorem checkInitializerRows_iff (fuel : Nat) (entries : List Entry)
    (slotTypes : List Ty) (slot : Nat) (rows : List Entry) :
    checkInitializerRows fuel entries slotTypes slot rows = true ↔
      InitializerCheckerRows fuel entries slotTypes slot rows := by
  constructor
  · exact checkInitializerRows_sound fuel entries slotTypes slot rows
  · intro checked
    induction checked with
    | nil => rfl
    | function slot identity signature valid definition tail rest ih =>
        simpa [checkInitializerRows] using ih
    | value slot identity type valid initializer slotType accepted tail rest ih =>
        simp [checkInitializerRows, slotType, accepted, ih]

theorem TypedInitializerRows.checkInitializerRows_eventually (entries : List Entry)
    (slotTypes : List Ty) (slot : Nat) (rows : List Entry)
    (typed : TypedInitializerRows entries slotTypes slot rows) :
    ∃ bound, ∀ fuel, bound ≤ fuel →
      checkInitializerRows fuel entries slotTypes slot rows = true := by
  induction typed with
  | nil => exact ⟨0, fun _ _ => rfl⟩
  | function slot identity signature valid definition tail rest ih => exact ih
  | value slot identity type valid initializer slotType initializerTyped tail rest ih =>
      obtain ⟨headBound, headAccepted⟩ :=
        checkInitializer_eventually_of_typed entries initializer type initializerTyped
      obtain ⟨tailBound, tailEventually⟩ := ih
      refine ⟨max headBound tailBound, ?_⟩
      intro fuel enough
      have headOK := headAccepted fuel (Nat.le_trans (Nat.le_max_left _ _) enough)
      have tailOK := tailEventually fuel (Nat.le_trans (Nat.le_max_right _ _) enough)
      simp [checkInitializerRows, slotType, headOK, tailOK]

theorem TypedInitializerRows.toInitializerCheckerRows (entries : List Entry)
    (slotTypes : List Ty) (slot : Nat) (rows : List Entry)
    (typed : TypedInitializerRows entries slotTypes slot rows) :
    ∃ fuel, InitializerCheckerRows fuel entries slotTypes slot rows := by
  obtain ⟨fuel, eventually⟩ :=
    TypedInitializerRows.checkInitializerRows_eventually entries slotTypes slot rows typed
  exact ⟨fuel, checkInitializerRows_sound fuel entries slotTypes slot rows
    (eventually fuel (by omega))⟩

/-- Derive every initializer typing fact from the executable checker rather
than carrying a second, manually supplied `HasType` proof per row. -/
theorem InitializerCheckerRows.toTypedInitializerRows
    (fuel : Nat) (entries : List Entry) (slotTypes : List Ty)
    (slot : Nat) (rows : List Entry)
    (checked : InitializerCheckerRows fuel entries slotTypes slot rows) :
    TypedInitializerRows entries slotTypes slot rows := by
  induction checked with
  | nil => exact .nil
  | function slot identity signature valid definition tail rest ih =>
      exact .function slot identity signature valid definition tail ih
  | value slot identity type valid initializer slotType accepted tail rest ih =>
      obtain ⟨typedInitializer, _, typing, sourceExact, _⟩ :=
        checkInitializer_sound fuel entries initializer type accepted
      have initializerTyped :
          Surface.HasType (signatures entries) 0 [] initializer type := by
        rw [← sourceExact]
        exact typing
      exact .value slot identity type valid initializer slotType initializerTyped tail ih

/-- An arithmetic-fragment row certificate already contains enough type
evidence to construct the general typed initializer layout. This removes the
need to ask callers to provide duplicate per-initializer `HasType` proofs. -/
theorem ArithmeticInitializerRows.toTypedInitializerRows
    (entries : List Entry) (slotTypes : List Ty) (slot : Nat) (rows : List Entry)
    (arithmetic : ArithmeticInitializerRows slotTypes slot rows) :
    TypedInitializerRows entries slotTypes slot rows := by
  induction rows generalizing slot with
  | nil => exact .nil
  | cons row tail ih =>
      cases row with
      | function identity signature valid definition =>
          exact .function slot identity signature valid definition tail
            (ih slot (by simpa [ArithmeticInitializerRows] using arithmetic))
      | value identity type valid initializer =>
          have parts : slotTypes.get? slot = some type ∧
              ArithmeticSurfaceExpr initializer type ∧
              ArithmeticInitializerRows slotTypes (slot + 1) tail := by
            simpa [ArithmeticInitializerRows] using arithmetic
          exact .value slot identity type valid initializer parts.1
            parts.2.1.hasType tail (ih (slot + 1) parts.2.2)

/- Construct a value row directly from the checked initializer certificate
returned by `checkInitializer`. The output keeps the elaborated expression,
and `sourceExact` proves it is still the caller's source initializer. -/
theorem TypedInitializerRows.value_of_checked_initializer
    (entries : List Entry) (slotTypes : List Ty) (slot identity : Nat)
    (type : Ty) (valid : type.wellFormed 0) (source : Surface.Expr)
    (tail : List Entry) (rest : TypedInitializerRows entries slotTypes (slot + 1) tail)
    (slotType : slotTypes.get? slot = some type)
    (checked : TypedInitializer entries type source) :
    TypedInitializerRows entries slotTypes slot
      (.value identity type valid checked.expression :: tail) := by
  exact .value slot identity type valid checked.expression slotType checked.typing tail rest

theorem TypedInitializerRows.value_of_checkInitializer
    (fuel : Nat) (entries : List Entry) (slotTypes : List Ty)
    (slot identity : Nat) (type : Ty) (valid : type.wellFormed 0)
    (source : Surface.Expr) (tail : List Entry)
    (rest : TypedInitializerRows entries slotTypes (slot + 1) tail)
    (slotType : slotTypes.get? slot = some type)
    (accepted : (checkInitializer fuel entries source type).isSome = true) :
    ∃ checked, checkInitializer fuel entries source type = some checked ∧
      checked.expression = source ∧
      TypedInitializerRows entries slotTypes slot
        (.value identity type valid checked.expression :: tail) := by
  obtain ⟨checked, decoded, _, sourceExact, _⟩ :=
    checkInitializer_sound fuel entries source type accepted
  refine ⟨checked, decoded, sourceExact, ?_⟩
  exact TypedInitializerRows.value_of_checked_initializer entries slotTypes slot
    identity type valid source tail rest slotType checked

theorem TypedInitializerRows.checked_initializer_retains_source
    (entries : List Entry) (type : Ty) (source : Surface.Expr)
    (checked : TypedInitializer entries type source) :
    checked.expression = source := checked.sourceExact

theorem TypedInitializerRows.globalIR_types_agree (entries : List Entry)
    (slotTypes : List Ty) (slot : Nat) (rows : List Entry)
    (typed : TypedInitializerRows entries slotTypes slot rows) :
    GlobalIR.InitializerTypesAgree slotTypes slot (initializerTerms rows) := by
  induction typed with
  | nil => simp [initializerTerms, GlobalIR.InitializerTypesAgree]
  | function slot identity signature valid definition tail rest ih =>
      simpa [initializerTerms] using ih
  | value slot identity type valid initializer slotType initializerTyped tail rest ih =>
      simp only [initializerTerms, GlobalIR.InitializerTypesAgree]
      exact ⟨type, slotType, ih⟩

/-- Checker acceptance and slot layout directly establish the initializer
slot agreement required by GlobalIR. -/
theorem InitializerCheckerRows.globalIR_types_agree
    (fuel : Nat) (entries : List Entry) (slotTypes : List Ty)
    (slot : Nat) (rows : List Entry)
    (checked : InitializerCheckerRows fuel entries slotTypes slot rows) :
    GlobalIR.InitializerTypesAgree slotTypes slot (initializerTerms rows) := by
  have typed := checked.toTypedInitializerRows fuel entries slotTypes slot rows
  exact typed.globalIR_types_agree entries slotTypes slot rows

theorem TypedInitializerRows.checker_and_globalIR_types_agree (entries : List Entry)
    (slotTypes : List Ty) (slot : Nat) (rows : List Entry)
    (typed : TypedInitializerRows entries slotTypes slot rows) :
    ∃ fuel, InitializerCheckerRows fuel entries slotTypes slot rows ∧
      GlobalIR.InitializerTypesAgree slotTypes slot (initializerTerms rows) := by
  obtain ⟨fuel, checked⟩ := typed.toInitializerCheckerRows entries slotTypes slot rows
  exact ⟨fuel, checked, checked.globalIR_types_agree fuel entries slotTypes slot rows⟩

theorem InitializerCheckerRows.toRuntimeProgram_types_agree
    (fuel : Nat) (entries : List Entry) (entryIndex : Nat)
    (checked : InitializerCheckerRows fuel entries (valueTypes entries) 0 entries) :
    GlobalIR.InitializerTypesAgree (valueTypes entries) 0
      (toRuntimeProgram entries entryIndex).initializers := by
  simpa [toRuntimeProgram] using checked.globalIR_types_agree fuel entries
    (valueTypes entries) 0 entries

/-- The row invariant is stated over the initializers embedded in the generated
runtime program, so callers can pass it directly to GlobalIR's initializer
preservation theorem. -/
theorem TypedInitializerRows.toRuntimeProgram_types_agree (entries : List Entry)
    (entryIndex : Nat)
    (typed : TypedInitializerRows entries (valueTypes entries) 0 entries) :
    GlobalIR.InitializerTypesAgree (valueTypes entries) 0
      (toRuntimeProgram entries entryIndex).initializers := by
  simpa [toRuntimeProgram] using
    typed.globalIR_types_agree entries (valueTypes entries) 0 entries

theorem TypedInitializerRows.arithmetic_types_agree (entries : List Entry)
    (slotTypes : List Ty) (slot : Nat) (rows : List Entry)
    (typed : TypedInitializerRows entries slotTypes slot rows)
    (arithmetic : ArithmeticInitializerRows slotTypes slot rows) :
    GlobalIR.ArithmeticInitializerTypesAgree slotTypes slot (initializerTerms rows) := by
  induction typed with
  | nil => simp [initializerTerms, GlobalIR.ArithmeticInitializerTypesAgree]
  | function slot identity signature valid definition tail rest ih =>
      simpa [initializerTerms, ArithmeticInitializerRows] using ih arithmetic
  | value slot identity type valid initializer slotType initializerTyped tail rest ih =>
      rcases arithmetic with ⟨rowSlotType, rowArithmetic, rowTail⟩
      simp only [initializerTerms, GlobalIR.ArithmeticInitializerTypesAgree]
      exact ⟨type, rowSlotType, rowArithmetic.erase, ih rowTail⟩

theorem TypedInitializerRows.initialization_preserves_store_arithmetic
    (entries : List Entry) (globals : List Signature) (slotTypes : List Ty)
    (program : List Definition) (fuel : Nat) (rows : List Entry) (result : Store)
    (typedRows : TypedInitializerRows entries slotTypes 0 rows)
    (arithmeticRows : ArithmeticInitializerRows slotTypes 0 rows)
    (success : initializeValues program fuel
      (List.replicate (initializerTerms rows).length none) 0
      (initializerTerms rows) = .ok result) :
    StoreWellTyped globals slotTypes result := by
  apply GlobalIR.initializeValues_arithmetic_preserves_typed globals program slotTypes fuel
    (List.replicate (initializerTerms rows).length none) 0 (initializerTerms rows) result
  · exact GlobalIR.empty_store_well_typed globals slotTypes (initializerTerms rows).length
  · exact typedRows.arithmetic_types_agree entries slotTypes 0 rows arithmeticRows
  · intro offset below
    simpa [List.length_replicate] using below
  · exact success

/- Connect the arithmetic initializer invariant directly to the executable
mixed-entry GlobalIR program. The theorem uses the generated program's own
definition and initializer fields rather than a separately supplied list. -/
theorem TypedInitializerRows.toRuntimeProgram_initialization_preserves_store_arithmetic
    (entries : List Entry) (globals : List Signature) (entryIndex fuel : Nat)
    (result : Store)
    (typedRows : TypedInitializerRows entries (valueTypes entries) 0 entries)
    (arithmeticRows : ArithmeticInitializerRows (valueTypes entries) 0 entries)
    (success : initializeValues (toRuntimeProgram entries entryIndex).definitions fuel
      (List.replicate (toRuntimeProgram entries entryIndex).initializers.length none)
      0 (toRuntimeProgram entries entryIndex).initializers = .ok result) :
    StoreWellTyped globals (valueTypes entries) result := by
  have initialized : initializeValues (toDefinitions 0 entries) fuel
      (List.replicate (initializerTerms entries).length none) 0
      (initializerTerms entries) = .ok result := by
    simpa [toRuntimeProgram] using success
  exact TypedInitializerRows.initialization_preserves_store_arithmetic entries globals
    (valueTypes entries) (toDefinitions 0 entries) fuel entries result typedRows
    arithmeticRows initialized

/-- The executable mixed-entry program uses the same typed initializer rows
as its source-order entry list. This general form leaves evaluator value
preservation explicit, so it applies to every initializer form once the
corresponding GlobalIR safety theorem is available. -/
theorem TypedInitializerRows.toRuntimeProgram_initialization_preserves_store
    (entries : List Entry) (globals : List Signature) (entryIndex fuel : Nat)
    (result : Store)
    (typedRows : TypedInitializerRows entries (valueTypes entries) 0 entries)
    (evaluationTyped : ∀ currentStore remaining expression value type,
      evaluate (toRuntimeProgram entries entryIndex).definitions currentStore remaining []
        expression = .ok value → PolyIR.ValueTyped globals value type)
    (success : initializeValues (toRuntimeProgram entries entryIndex).definitions fuel
      (List.replicate (toRuntimeProgram entries entryIndex).initializers.length none)
      0 (toRuntimeProgram entries entryIndex).initializers = .ok result) :
    StoreWellTyped globals (valueTypes entries) result ∧
      result.length = (valueTypes entries).length := by
  have initialized : initializeValues (toDefinitions 0 entries) fuel
      (List.replicate (initializerTerms entries).length none) 0
      (initializerTerms entries) = .ok result := by
    simpa [toRuntimeProgram] using success
  have initializerCount : (initializerTerms entries).length = (valueTypes entries).length :=
    initializerTerms_length entries
  constructor
  · apply initializeValues_from_empty_preserves_typed globals (toDefinitions 0 entries)
      (valueTypes entries) fuel (initializerTerms entries) result
    · exact typedRows.toRuntimeProgram_types_agree entries entryIndex
    · intro currentStore remaining expression value type evaluated
      exact evaluationTyped currentStore remaining expression value type
        (by simpa [toRuntimeProgram] using evaluated)
    · exact initialized
  · apply initializeValues_preserves_layout_length
      (program := toDefinitions 0 entries)
      (List.replicate (initializerTerms entries).length none) result
      (valueTypes entries) 0 (initializerTerms entries) initialized
    simpa [List.length_replicate] using initializerCount

/-- Contextual GlobalIR initializer typing, which also admits typed global
function/getter calls, is enough to preserve the initialized store type. This
avoids passing a separate evaluator-safety theorem for every initializer. -/
theorem toRuntimeProgram_contextualGlobal_initialization_preserves_store
    (entries : List Entry) (globals : List Signature) (definitions : Surface.Definitions)
    (functionSources : List (Nat × Nat)) (entryIndex fuel : Nat) (result : Store)
    (contextualRows : ContextualGlobalInitializerRows globals
      (fun _ => Ty.unit) (valueTypes entries) 0 entries)
    (programTyped : GlobalIR.GlobalProgramTyped globals definitions
      (valueTypes entries) functionSources
      (toRuntimeProgram entries entryIndex).definitions)
    (success : initializeValues (toRuntimeProgram entries entryIndex).definitions fuel
      (List.replicate (toRuntimeProgram entries entryIndex).initializers.length none)
      0 (toRuntimeProgram entries entryIndex).initializers = .ok result) :
    StoreWellTyped globals (valueTypes entries) result ∧
      result.length = (valueTypes entries).length := by
  have runtimeRows := contextualRows.toRuntimeRows globals (fun _ => Ty.unit)
    definitions (valueTypes entries) functionSources
    (toRuntimeProgram entries entryIndex).definitions 0 entries
  have initializerTypes := runtimeRows.toRuntimeTypesAgree globals (fun _ => Ty.unit)
    definitions (valueTypes entries) functionSources
    (toRuntimeProgram entries entryIndex).definitions 0 entries
  have initialized : initializeValues (toDefinitions 0 entries) fuel
      (List.replicate (initializerTerms entries).length none) 0
      (initializerTerms entries) = .ok result := by
    simpa [toRuntimeProgram] using success
  constructor
  · exact GlobalIR.initializeValues_contextualGlobalRuntime_preserves_typed globals
      (fun _ => Ty.unit) definitions (valueTypes entries) functionSources
      (toRuntimeProgram entries entryIndex).definitions programTyped fuel
      (List.replicate (initializerTerms entries).length none) 0
      (initializerTerms entries) result
      (by simpa using initializerTerms_length entries)
      (GlobalIR.empty_store_well_typed globals (valueTypes entries)
        (initializerTerms entries).length)
      initializerTypes
      (by
        intro offset below
        simpa [List.length_replicate] using below)
      initialized
  · apply GlobalIR.initializeValues_preserves_layout_length
      (program := (toRuntimeProgram entries entryIndex).definitions)
      (List.replicate (initializerTerms entries).length none) result
      (valueTypes entries) 0 (initializerTerms entries) initialized
    simpa [List.length_replicate, initializerTerms_length]

/-- The getter-aware runtime initializer fragment also establishes both the
typed store invariant and slot-layout length for the generated mixed-entry
program. The source rows may read previously initialized value slots. -/
theorem toRuntimeProgram_runtimeContextual_initialization_preserves_store
    (entries : List Entry) (globals : List Signature) (assignment : Nat → Ty)
    (definitions : Surface.Definitions) (functionSources : List (Nat × Nat))
    (entryIndex fuel : Nat) (result : Store)
    (runtimeRows : ContextualGlobalRuntimeInitializerRows globals assignment definitions
      (valueTypes entries) functionSources
      (toRuntimeProgram entries entryIndex).definitions 0 entries)
    (programTyped : GlobalProgramTyped globals definitions (valueTypes entries)
      functionSources (toRuntimeProgram entries entryIndex).definitions)
    (success : initializeValues (toRuntimeProgram entries entryIndex).definitions fuel
      (List.replicate (toRuntimeProgram entries entryIndex).initializers.length none)
      0 (toRuntimeProgram entries entryIndex).initializers = .ok result) :
    StoreWellTyped globals (valueTypes entries) result ∧
      result.length = (valueTypes entries).length := by
  have storeTyped := ContextualGlobalRuntimeInitializerRows.toRuntimeProgram_initialization_preserves_store
    entries globals assignment definitions
    functionSources entryIndex fuel result programTyped runtimeRows success
  have initialized : initializeValues (toRuntimeProgram entries entryIndex).definitions fuel
      (List.replicate (initializerTerms entries).length none) 0
      (initializerTerms entries) = .ok result := by
    simpa [toRuntimeProgram] using success
  refine ⟨storeTyped, ?_⟩
  apply GlobalIR.initializeValues_preserves_layout_length
    (program := (toRuntimeProgram entries entryIndex).definitions)
    (List.replicate (initializerTerms entries).length none) result
    (valueTypes entries) 0 (initializerTerms entries) initialized
  simpa [List.length_replicate, initializerTerms_length]

/-- A checker-accepted mixed declaration table directly establishes the
initialized store's type and slot-count invariants, given evaluator safety. -/
theorem InitializerCheckerRows.toRuntimeProgram_initialization_preserves_store
    (checkerFuel : Nat) (entries : List Entry) (globals : List Signature)
    (entryIndex initializerFuel : Nat) (result : Store)
    (checkedRows : InitializerCheckerRows checkerFuel entries (valueTypes entries) 0 entries)
    (evaluationTyped : ∀ currentStore remaining expression value type,
      evaluate (toRuntimeProgram entries entryIndex).definitions currentStore remaining []
        expression = .ok value → PolyIR.ValueTyped globals value type)
    (success : initializeValues (toRuntimeProgram entries entryIndex).definitions initializerFuel
      (List.replicate (toRuntimeProgram entries entryIndex).initializers.length none)
      0 (toRuntimeProgram entries entryIndex).initializers = .ok result) :
    StoreWellTyped globals (valueTypes entries) result ∧
      result.length = (valueTypes entries).length := by
  exact TypedInitializerRows.toRuntimeProgram_initialization_preserves_store
    entries globals entryIndex initializerFuel result
    (checkedRows.toTypedInitializerRows checkerFuel entries (valueTypes entries) 0 entries)
    evaluationTyped success

/-- General initializer-to-getter path for the generated mixed-entry runtime
program. Initializer evaluation safety and the runtime table typing are
explicit inputs; the arithmetic-only corollary below specializes this path. -/
theorem TypedInitializerRows.toRuntimeProgram_initialization_supports_typed_getter_call
    (entries : List Entry) (globals : List Signature) (definitions : Surface.Definitions)
    (functionSources : List (Nat × Nat)) (entryIndex initializerFuel getterFuel : Nat)
    (initializedStore : Store) (index slot : Nat)
    (typedRows : TypedInitializerRows entries (valueTypes entries) 0 entries)
    (evaluationTyped : ∀ currentStore remaining expression value type,
      evaluate (toRuntimeProgram entries entryIndex).definitions currentStore remaining []
        expression = .ok value → PolyIR.ValueTyped globals value type)
    (initialization : initializeValues
      (toRuntimeProgram entries entryIndex).definitions initializerFuel
      (List.replicate (toRuntimeProgram entries entryIndex).initializers.length none)
      0 (toRuntimeProgram entries entryIndex).initializers = .ok initializedStore)
    (programTyped : GlobalProgramTyped globals definitions (valueTypes entries) functionSources
      (toRuntimeProgram entries entryIndex).definitions)
    (getter : (toRuntimeProgram entries entryIndex).definitions[index]? = some (.getter slot)) :
    ∃ type value, globals[index]? = some ⟨0, [], type⟩ ∧ type.wellFormed 0 ∧
      (valueTypes entries)[slot]? = some type ∧
      evaluate (toRuntimeProgram entries entryIndex).definitions initializedStore
        (getterFuel + 2) [] (.app (.global index) []) = .ok value ∧
      PolyIR.ValueTyped globals value type := by
  have storeResult := TypedInitializerRows.toRuntimeProgram_initialization_preserves_store
    entries globals entryIndex initializerFuel initializedStore typedRows evaluationTyped
    initialization
  have storeTyped := storeResult.1
  have initialized : initializeValues (toRuntimeProgram entries entryIndex).definitions
      initializerFuel
      (List.replicate (toRuntimeProgram entries entryIndex).initializers.length none)
      0 (toRuntimeProgram entries entryIndex).initializers = .ok initializedStore := initialization
  have populated : ∀ currentSlot, currentSlot < (valueTypes entries).length →
      ∃ value, initializedStore[currentSlot]? = some (some value) := by
    intro currentSlot currentSlotBound
    have initializerBound : currentSlot <
        (toRuntimeProgram entries entryIndex).initializers.length := by
      rw [(toRuntimeProgram_layout entries entryIndex).2]
      exact currentSlotBound
    exact GlobalIR.initialized_cells_present initialized (by simp)
      ⟨by omega, by simpa using initializerBound⟩
  exact typed_getter_call_preserves_type_of_populated_store
    (toRuntimeProgram entries entryIndex).definitions globals definitions
    (valueTypes entries) functionSources initializedStore getterFuel index slot
    programTyped getter storeTyped populated

theorem TypedInitializerRows.toRuntimeProgram_checked_initialization_supports_typed_getter_call
    (entries : List Entry) (globals : List Signature) (definitions : Surface.Definitions)
    (functionSources : List (Nat × Nat)) (entryIndex initializerFuel getterFuel : Nat)
    (initializedStore : Store) (index slot : Nat)
    (typedRows : TypedInitializerRows entries (valueTypes entries) 0 entries)
    (evaluationTyped : ∀ currentStore remaining expression value type,
      evaluate (toRuntimeProgram entries entryIndex).definitions currentStore remaining []
        expression = .ok value → PolyIR.ValueTyped globals value type)
    (initialization : initializeValues
      (toRuntimeProgram entries entryIndex).definitions initializerFuel
      (List.replicate (toRuntimeProgram entries entryIndex).initializers.length none)
      0 (toRuntimeProgram entries entryIndex).initializers = .ok initializedStore)
    (programTyped : GlobalProgramTyped globals definitions (valueTypes entries) functionSources
      (toRuntimeProgram entries entryIndex).definitions)
    (getter : (toRuntimeProgram entries entryIndex).definitions[index]? = some (.getter slot)) :
    ∃ checkerFuel, InitializerCheckerRows checkerFuel entries (valueTypes entries) 0 entries ∧
      ∃ type value, globals[index]? = some ⟨0, [], type⟩ ∧ type.wellFormed 0 ∧
        (valueTypes entries)[slot]? = some type ∧
        evaluate (toRuntimeProgram entries entryIndex).definitions initializedStore
          (getterFuel + 2) [] (.app (.global index) []) = .ok value ∧
        PolyIR.ValueTyped globals value type := by
  obtain ⟨checkerFuel, checkedRows, _slotAgreement⟩ :=
    typedRows.checker_and_globalIR_types_agree entries (valueTypes entries) 0 entries
  have getterSafe := TypedInitializerRows.toRuntimeProgram_initialization_supports_typed_getter_call
    entries globals definitions functionSources entryIndex initializerFuel getterFuel
    initializedStore index slot typedRows evaluationTyped initialization programTyped getter
  exact ⟨checkerFuel, checkedRows, getterSafe⟩

/-- Checker-accepted initializer rows can be carried to the runtime getter
once the general initializer evaluation preservation premise is supplied. -/
theorem InitializerCheckerRows.toRuntimeProgram_initialization_supports_typed_getter_call
    (fuel : Nat) (entries : List Entry) (globals : List Signature)
    (definitions : Surface.Definitions) (functionSources : List (Nat × Nat))
    (entryIndex initializerFuel getterFuel : Nat) (initializedStore : Store)
    (index slot : Nat)
    (checkedRows : InitializerCheckerRows fuel entries (valueTypes entries) 0 entries)
    (evaluationTyped : ∀ currentStore remaining expression value type,
      evaluate (toRuntimeProgram entries entryIndex).definitions currentStore remaining []
        expression = .ok value → PolyIR.ValueTyped globals value type)
    (initialization : initializeValues
      (toRuntimeProgram entries entryIndex).definitions initializerFuel
      (List.replicate (toRuntimeProgram entries entryIndex).initializers.length none)
      0 (toRuntimeProgram entries entryIndex).initializers = .ok initializedStore)
    (programTyped : GlobalProgramTyped globals definitions (valueTypes entries) functionSources
      (toRuntimeProgram entries entryIndex).definitions)
    (getter : (toRuntimeProgram entries entryIndex).definitions[index]? = some (.getter slot)) :
    ∃ type value, globals[index]? = some ⟨0, [], type⟩ ∧ type.wellFormed 0 ∧
      (valueTypes entries)[slot]? = some type ∧
      evaluate (toRuntimeProgram entries entryIndex).definitions initializedStore
        (getterFuel + 2) [] (.app (.global index) []) = .ok value ∧
      PolyIR.ValueTyped globals value type := by
  exact TypedInitializerRows.toRuntimeProgram_initialization_supports_typed_getter_call
    entries globals definitions functionSources entryIndex initializerFuel getterFuel
    initializedStore index slot
    (checkedRows.toTypedInitializerRows fuel entries (valueTypes entries) 0 entries)
    evaluationTyped initialization programTyped getter

/-- End-to-end theorem from the executable initializer-row checker to a typed
getter result after successful GlobalIR initialization. -/
theorem checkInitializerRows_initialization_supports_typed_getter_call
    (checkerFuel : Nat) (entries : List Entry) (globals : List Signature)
    (definitions : Surface.Definitions) (functionSources : List (Nat × Nat))
    (entryIndex initializerFuel getterFuel : Nat) (initializedStore : Store)
    (index slot : Nat)
    (accepted : checkInitializerRows checkerFuel entries (valueTypes entries) 0 entries = true)
    (evaluationTyped : ∀ currentStore remaining expression value type,
      evaluate (toRuntimeProgram entries entryIndex).definitions currentStore remaining []
        expression = .ok value → PolyIR.ValueTyped globals value type)
    (initialization : initializeValues
      (toRuntimeProgram entries entryIndex).definitions initializerFuel
      (List.replicate (toRuntimeProgram entries entryIndex).initializers.length none)
      0 (toRuntimeProgram entries entryIndex).initializers = .ok initializedStore)
    (programTyped : GlobalProgramTyped globals definitions (valueTypes entries) functionSources
      (toRuntimeProgram entries entryIndex).definitions)
    (getter : (toRuntimeProgram entries entryIndex).definitions[index]? = some (.getter slot)) :
    ∃ type value, globals[index]? = some ⟨0, [], type⟩ ∧ type.wellFormed 0 ∧
      (valueTypes entries)[slot]? = some type ∧
      evaluate (toRuntimeProgram entries entryIndex).definitions initializedStore
        (getterFuel + 2) [] (.app (.global index) []) = .ok value ∧
      PolyIR.ValueTyped globals value type := by
  exact InitializerCheckerRows.toRuntimeProgram_initialization_supports_typed_getter_call
    checkerFuel entries globals definitions functionSources entryIndex initializerFuel getterFuel
    initializedStore index slot (checkInitializerRows_sound checkerFuel entries
      (valueTypes entries) 0 entries accepted) evaluationTyped initialization programTyped getter

/-- Compose the generated mixed-entry GlobalIR program, its successful
arithmetic initializer run, and a typed getter. This is the arithmetic
fragment of the initializer-to-runtime path used by top-level value programs. -/
theorem TypedInitializerRows.toRuntimeProgram_initialization_supports_typed_getter_call_arithmetic
    (entries : List Entry) (globals : List Signature) (definitions : Surface.Definitions)
    (functionSources : List (Nat × Nat)) (entryIndex initializerFuel getterFuel : Nat)
    (initializedStore : Store) (index slot : Nat)
    (typedRows : TypedInitializerRows entries (valueTypes entries) 0 entries)
    (arithmeticRows : ArithmeticInitializerRows (valueTypes entries) 0 entries)
    (initialization : initializeValues
      (toRuntimeProgram entries entryIndex).definitions initializerFuel
      (List.replicate (toRuntimeProgram entries entryIndex).initializers.length none)
      0 (toRuntimeProgram entries entryIndex).initializers = .ok initializedStore)
    (programTyped : GlobalProgramTyped globals definitions (valueTypes entries) functionSources
      (toRuntimeProgram entries entryIndex).definitions)
    (getter : (toRuntimeProgram entries entryIndex).definitions[index]? = some (.getter slot)) :
    ∃ type value, globals[index]? = some ⟨0, [], type⟩ ∧ type.wellFormed 0 ∧
      (valueTypes entries)[slot]? = some type ∧
      evaluate (toRuntimeProgram entries entryIndex).definitions initializedStore
        (getterFuel + 2) [] (.app (.global index) []) = .ok value ∧
      PolyIR.ValueTyped globals value type := by
  obtain ⟨type, signatureEntry, typeWellFormed, slotType⟩ := getter_layout_typed globals
    definitions (valueTypes entries) functionSources
    (toRuntimeProgram entries entryIndex).definitions programTyped index slot getter
  have initializerCount : (initializerTerms entries).length = (valueTypes entries).length :=
    initializerTerms_length entries
  have slotBound : slot < (initializerTerms entries).length := by
    have sourceBound : slot < (valueTypes entries).length := by
      simp only [getElem?_def] at slotType
      split at slotType
      · assumption
      · contradiction
    omega
  have initialized : initializeValues (toRuntimeProgram entries entryIndex).definitions
      initializerFuel
      (List.replicate (initializerTerms entries).length none) 0 (initializerTerms entries) =
        .ok initializedStore := by
    simpa [toRuntimeProgram] using initialization
  have typedGetter := GlobalIR.initializeValues_contextualGlobal_then_getter_preserves_type
    globals (fun _ => .unit) definitions (valueTypes entries) functionSources
    (toRuntimeProgram entries entryIndex).definitions programTyped initializerFuel getterFuel
    (List.replicate (initializerTerms entries).length none) 0 slot
    (initializerTerms entries) initializedStore type index
    (empty_store_well_typed globals (valueTypes entries) (initializerTerms entries).length)
    (arithmeticRows.contextualGlobalTypesAgree globals (fun _ => .unit)
      (valueTypes entries) 0 entries)
    (by intro offset below; simpa using below)
    (by simp)
    ⟨Nat.zero_le _, by omega⟩ slotType getter initialized
  rcases typedGetter with ⟨value, evaluated, valueTyped⟩
  exact ⟨type, value, signatureEntry, typeWellFormed, slotType, evaluated, valueTyped⟩

/-- Arithmetic initializer certificates alone construct the row typing proof
needed for the executable mixed-entry program and its typed getter. -/
theorem ArithmeticInitializerRows.toRuntimeProgram_initialization_supports_typed_getter_call
    (entries : List Entry) (globals : List Signature) (definitions : Surface.Definitions)
    (functionSources : List (Nat × Nat)) (entryIndex initializerFuel getterFuel : Nat)
    (initializedStore : Store) (index slot : Nat)
    (arithmeticRows : ArithmeticInitializerRows (valueTypes entries) 0 entries)
    (initialization : initializeValues
      (toRuntimeProgram entries entryIndex).definitions initializerFuel
      (List.replicate (toRuntimeProgram entries entryIndex).initializers.length none)
      0 (toRuntimeProgram entries entryIndex).initializers = .ok initializedStore)
    (programTyped : GlobalProgramTyped globals definitions (valueTypes entries) functionSources
      (toRuntimeProgram entries entryIndex).definitions)
    (getter : (toRuntimeProgram entries entryIndex).definitions[index]? = some (.getter slot)) :
    ∃ type value, globals[index]? = some ⟨0, [], type⟩ ∧ type.wellFormed 0 ∧
      (valueTypes entries)[slot]? = some type ∧
      evaluate (toRuntimeProgram entries entryIndex).definitions initializedStore
        (getterFuel + 2) [] (.app (.global index) []) = .ok value ∧
      PolyIR.ValueTyped globals value type := by
  exact TypedInitializerRows.toRuntimeProgram_initialization_supports_typed_getter_call_arithmetic
    entries globals definitions functionSources entryIndex initializerFuel getterFuel
    initializedStore index slot
    (arithmeticRows.toTypedInitializerRows entries (valueTypes entries) 0 entries)
    arithmeticRows initialization programTyped getter

/-- Compose executable initializer checking with arithmetic initializer
typing and the generated runtime getter path. Thus checker acceptance plus a
successful initialization suffices for a typed getter result, without a
separately supplied `TypedInitializerRows` witness. -/
theorem checkInitializerRows_arithmetic_initialization_supports_typed_getter_call
    (checkerFuel : Nat) (entries : List Entry) (globals : List Signature)
    (definitions : Surface.Definitions) (functionSources : List (Nat × Nat))
    (entryIndex initializerFuel getterFuel : Nat) (initializedStore : Store)
    (index slot : Nat)
    (accepted : checkInitializerRows checkerFuel entries (valueTypes entries) 0 entries = true)
    (arithmeticRows : ArithmeticInitializerRows (valueTypes entries) 0 entries)
    (initialization : initializeValues
      (toRuntimeProgram entries entryIndex).definitions initializerFuel
      (List.replicate (toRuntimeProgram entries entryIndex).initializers.length none)
      0 (toRuntimeProgram entries entryIndex).initializers = .ok initializedStore)
    (programTyped : GlobalProgramTyped globals definitions (valueTypes entries) functionSources
      (toRuntimeProgram entries entryIndex).definitions)
    (getter : (toRuntimeProgram entries entryIndex).definitions[index]? = some (.getter slot)) :
    ∃ type value, globals[index]? = some ⟨0, [], type⟩ ∧ type.wellFormed 0 ∧
      (valueTypes entries)[slot]? = some type ∧
      evaluate (toRuntimeProgram entries entryIndex).definitions initializedStore
        (getterFuel + 2) [] (.app (.global index) []) = .ok value ∧
      PolyIR.ValueTyped globals value type := by
  have checkedRows := checkInitializerRows_sound checkerFuel entries
    (valueTypes entries) 0 entries accepted
  have typedRows := checkedRows.toTypedInitializerRows checkerFuel entries
    (valueTypes entries) 0 entries
  exact TypedInitializerRows.toRuntimeProgram_initialization_supports_typed_getter_call_arithmetic
    entries globals definitions functionSources entryIndex initializerFuel getterFuel
    initializedStore index slot typedRows arithmeticRows initialization programTyped getter

/- A typed source-order value table is sufficient to establish the slot/type
agreement consumed by the sequential GlobalIR initializer proof. The only
remaining semantic premise is evaluation preservation for the initializer
terms themselves; keeping it explicit avoids treating the layout lemma as a
proof of evaluator type safety. -/
theorem TypedInitializerRows.initialization_preserves_store (entries : List Entry)
    (globals : List Signature) (slotTypes : List Ty) (program : List Definition)
    (fuel : Nat) (rows : List Entry) (result : Store)
    (typedRows : TypedInitializerRows entries slotTypes 0 rows)
    (evaluationTyped : ∀ currentStore remaining expression value type,
      evaluate program currentStore remaining [] expression = .ok value →
        PolyIR.ValueTyped globals value type)
    (success : initializeValues program fuel
      (List.replicate (initializerTerms rows).length none) 0
      (initializerTerms rows) = .ok result) :
    StoreWellTyped globals slotTypes result := by
  apply initializeValues_from_empty_preserves_typed globals program slotTypes fuel
    (initializerTerms rows) result (typedRows.globalIR_types_agree entries slotTypes 0 rows)
    evaluationTyped success

/-- Combine the typed mixed-declaration rows with the successful GlobalIR
initializer run: the resulting store is well typed and still has exactly the
declared slot-layout length. The semantic typing of each evaluated term is
kept explicit, since general GlobalIR evaluator safety is a separate proof. -/
theorem TypedInitializerRows.initialization_preserves_store_and_layout
    (entries : List Entry) (globals : List Signature) (slotTypes : List Ty)
    (program : List Definition) (fuel : Nat) (rows : List Entry) (result : Store)
    (typedRows : TypedInitializerRows entries slotTypes 0 rows)
    (initializerCount : (initializerTerms rows).length = slotTypes.length)
    (evaluationTyped : ∀ currentStore remaining expression value type,
      evaluate program currentStore remaining [] expression = .ok value →
        PolyIR.ValueTyped globals value type)
    (success : initializeValues program fuel
      (List.replicate (initializerTerms rows).length none) 0
      (initializerTerms rows) = .ok result) :
    StoreWellTyped globals slotTypes result ∧ result.length = slotTypes.length := by
  constructor
  · exact TypedInitializerRows.initialization_preserves_store entries globals slotTypes
      program fuel rows result typedRows evaluationTyped success
  · apply initializeValues_preserves_layout_length (program := program)
      (List.replicate (initializerTerms rows).length none) result slotTypes 0
      (initializerTerms rows) success
    simpa [List.length_replicate] using initializerCount

/-- A successful run that covers the complete value layout leaves no
declared value slot uninitialized. Together with
`initialization_preserves_store_and_layout`, this gives both the typed-store
invariant and a concrete value at every declared slot. -/
theorem TypedInitializerRows.initialization_populates_every_slot
    (entries : List Entry) (slotTypes : List Ty) (program : List Definition)
    (fuel : Nat) (rows : List Entry) (result : Store)
    (initializerCount : (initializerTerms rows).length = slotTypes.length)
    (success : initializeValues program fuel
      (List.replicate (initializerTerms rows).length none) 0
      (initializerTerms rows) = .ok result) :
    ∀ slot, slot < slotTypes.length → ∃ value, result[slot]? = some (some value) := by
  intro slot slotBound
  have slotBound' : slot < (initializerTerms rows).length := by omega
  have present := initialized_cells_present success (by simp)
    ⟨Nat.zero_le _, by simpa using slotBound'⟩
  exact present

/-- Complete initialization of a typed row table produces a store with the
declared layout, preserving its type invariant and containing a correctly
typed value in every slot. The evaluator's value-typing premise remains
explicit so this theorem does not assume unproved GlobalIR evaluator safety. -/
theorem TypedInitializerRows.initialization_type_safe_and_populated
    (entries : List Entry) (globals : List Signature) (slotTypes : List Ty)
    (program : List Definition) (fuel : Nat) (rows : List Entry) (result : Store)
    (typedRows : TypedInitializerRows entries slotTypes 0 rows)
    (initializerCount : (initializerTerms rows).length = slotTypes.length)
    (evaluationTyped : ∀ currentStore remaining expression value type,
      evaluate program currentStore remaining [] expression = .ok value →
        PolyIR.ValueTyped globals value type)
    (success : initializeValues program fuel
      (List.replicate (initializerTerms rows).length none) 0
      (initializerTerms rows) = .ok result) :
    StoreWellTyped globals slotTypes result ∧ result.length = slotTypes.length ∧
      ∀ (slot : Nat) (type : Ty), slotTypes[slot]? = some type →
        ∃ value, result[slot]? = some (some value) ∧
          PolyIR.ValueTyped globals value type := by
  obtain ⟨storeTyped, layout⟩ :=
    TypedInitializerRows.initialization_preserves_store_and_layout entries globals
      slotTypes program fuel rows result typedRows initializerCount evaluationTyped success
  refine ⟨storeTyped, layout, ?_⟩
  intro slot type slotType
  have slotTypeGet : slotTypes.get? slot = some type := by
    have indexedGet : slotTypes[slot]? = slotTypes.get? slot := by
      by_cases bound : slot < slotTypes.length
      · simp only [getElem?_def, dif_pos bound]
        exact (List.get?_eq_some).2 ⟨bound, rfl⟩ |>.symm
      · have outOfBounds : slotTypes.get? slot = none :=
          List.get?_eq_none.mpr (Nat.le_of_not_gt bound)
        simp only [getElem?_def, dif_neg bound]
        exact outOfBounds.symm
    rw [← indexedGet]
    exact slotType
  have slotBound : slot < slotTypes.length := (List.get?_eq_some.mp slotTypeGet).1
  obtain ⟨value, present⟩ := TypedInitializerRows.initialization_populates_every_slot
    entries slotTypes program fuel rows result initializerCount success slot slotBound
  have presentGet : result.get? slot = some (some value) := by
    have indexedGet : result[slot]? = result.get? slot := by
      by_cases bound : slot < result.length
      · simp only [getElem?_def, dif_pos bound]
        exact (List.get?_eq_some).2 ⟨bound, rfl⟩ |>.symm
      · have outOfBounds : result.get? slot = none :=
          List.get?_eq_none.mpr (Nat.le_of_not_gt bound)
        simp only [getElem?_def, dif_neg bound]
        exact outOfBounds.symm
    rw [← indexedGet]
    exact present
  exact ⟨value, present, storeTyped slot value type presentGet slotTypeGet⟩

/-- End-to-end initializer/getter composition: after a typed initializer row
table initializes every declared slot successfully, any typed GlobalIR getter
reads a value of its declared type from that store. The initializer evaluator
typing premise is explicit; deriving it for arbitrary GlobalIR programs is a
separate safety theorem. -/
theorem TypedInitializerRows.initialization_supports_typed_getter_call
    (entries : List Entry) (globals : List Signature) (definitions : Surface.Definitions)
    (slotTypes : List Ty) (functionSources : List (Nat × Nat))
    (program : List Definition) (initializerFuel getterFuel : Nat)
    (rows : List Entry) (initializedStore : Store) (index slot : Nat)
    (typedRows : TypedInitializerRows entries slotTypes 0 rows)
    (initializerCount : (initializerTerms rows).length = slotTypes.length)
    (evaluationTyped : ∀ currentStore remaining expression value type,
      evaluate program currentStore remaining [] expression = .ok value →
        PolyIR.ValueTyped globals value type)
    (initialization : initializeValues program initializerFuel
      (List.replicate (initializerTerms rows).length none) 0
      (initializerTerms rows) = .ok initializedStore)
    (programTyped : GlobalProgramTyped globals definitions slotTypes functionSources program)
    (getter : program[index]? = some (.getter slot)) :
    ∃ type value, globals[index]? = some ⟨0, [], type⟩ ∧ type.wellFormed 0 ∧
      slotTypes[slot]? = some type ∧
      evaluate program initializedStore (getterFuel + 2) [] (.app (.global index) []) = .ok value ∧
      PolyIR.ValueTyped globals value type := by
  obtain ⟨storeTyped, _layout, _slotValues⟩ :=
    TypedInitializerRows.initialization_type_safe_and_populated entries globals slotTypes
      program initializerFuel rows initializedStore typedRows initializerCount
      evaluationTyped initialization
  have populated := TypedInitializerRows.initialization_populates_every_slot entries
    slotTypes program initializerFuel rows initializedStore initializerCount initialization
  exact typed_getter_call_preserves_type_of_populated_store program globals definitions
    slotTypes functionSources initializedStore getterFuel index slot programTyped getter
    storeTyped populated

/-- End-to-end initializer/getter type safety for mixed programs whose value
initializers are integer arithmetic Surface expressions. Their type safety is
derived from `ArithmeticSurfaceExpr`, so this theorem needs no separate
per-evaluation value-typing premise. -/
theorem TypedInitializerRows.initialization_supports_typed_getter_call_arithmetic
    (entries : List Entry) (globals : List Signature) (definitions : Surface.Definitions)
    (slotTypes : List Ty) (functionSources : List (Nat × Nat))
    (program : List Definition) (initializerFuel getterFuel : Nat)
    (rows : List Entry) (initializedStore : Store) (index slot : Nat)
    (typedRows : TypedInitializerRows entries slotTypes 0 rows)
    (arithmeticRows : ArithmeticInitializerRows slotTypes 0 rows)
    (initializerCount : (initializerTerms rows).length = slotTypes.length)
    (initialization : initializeValues program initializerFuel
      (List.replicate (initializerTerms rows).length none) 0
      (initializerTerms rows) = .ok initializedStore)
    (programTyped : GlobalProgramTyped globals definitions slotTypes functionSources program)
    (getter : program[index]? = some (.getter slot)) :
    ∃ type value, globals[index]? = some ⟨0, [], type⟩ ∧ type.wellFormed 0 ∧
      slotTypes[slot]? = some type ∧
      evaluate program initializedStore (getterFuel + 2) [] (.app (.global index) []) = .ok value ∧
      PolyIR.ValueTyped globals value type := by
  have storeTyped := TypedInitializerRows.initialization_preserves_store_arithmetic
    entries globals slotTypes program initializerFuel rows initializedStore typedRows
    arithmeticRows initialization
  have populated := TypedInitializerRows.initialization_populates_every_slot entries
    slotTypes program initializerFuel rows initializedStore initializerCount initialization
  exact typed_getter_call_preserves_type_of_populated_store program globals definitions
    slotTypes functionSources initializedStore getterFuel index slot programTyped getter
    storeTyped populated


end NLisp.GlobalProgramEntry
