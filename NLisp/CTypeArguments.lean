import NLisp.TypeArguments

namespace NLisp.Surface

/- A structural model of the C `Type` nodes used by the type-argument
collector. Variables carry pointer identities and `pointers` is the
quantifier's ordered identity array. -/
inductive CTypeNode where
  | boolean
  | integer
  | floating
  | string
  | character
  | unit
  | variable (identity : Nat)
  | list (element : CTypeNode)
  | option (element : CTypeNode)
  | function (parameters : List CTypeNode) (result : CTypeNode)
  | forallType (variables : List Nat) (body : CTypeNode)
  deriving Repr

def cPointerIndex (identity : Nat) : List Nat → Option Nat
  | [] => none
  | head :: tail =>
      if head = identity then some 0 else (cPointerIndex identity tail).map Nat.succ

/- The quantified-variable branch of C `substitute_type`: a pointer found in
the ordered scheme array selects the inferred substitution at the same slot. -/
def cSubstituteVariable (scheme : List Nat) (substitutions : List CTypeNode) (identity : Nat) :
    Option CTypeNode :=
  match cPointerIndex identity scheme with
  | none => some (.variable identity)
  | some index => substitutions[index]?

mutual
def cSubstituteType (scheme : List Nat) (substitutions : List CTypeNode) :
    CTypeNode → Option CTypeNode
  | .variable identity => cSubstituteVariable scheme substitutions identity
  | .list element => (cSubstituteType scheme substitutions element).map CTypeNode.list
  | .option element => (cSubstituteType scheme substitutions element).map CTypeNode.option
  | .function parameters result => do
      let parameters ← cSubstituteTypes scheme substitutions parameters
      let result ← cSubstituteType scheme substitutions result
      pure (.function parameters result)
  | node => some node

def cSubstituteTypes (scheme : List Nat) (substitutions : List CTypeNode) :
    List CTypeNode → Option (List CTypeNode)
  | [] => some []
  | head :: tail => do
      let head ← cSubstituteType scheme substitutions head
      let tail ← cSubstituteTypes scheme substitutions tail
      pure (head :: tail)
end

def CNoDuplicatePointers : List Nat → Prop
  | [] => True
  | head :: tail => head ∉ tail ∧ CNoDuplicatePointers tail

private theorem pointerIndexedEqGet? {α : Type} (pointers : List α) (index : Nat) :
    pointers[index]? = pointers.get? index := by
  induction pointers generalizing index with
  | nil => cases index <;> simp [getElem?_def]
  | cons head tail ih =>
      cases index with
      | zero => simp [getElem?_def]
      | succ index => simpa [getElem?_def, Nat.succ_lt_succ_iff] using ih index

private theorem pointerLookupMem (pointers : List Nat) (index identity : Nat)
    (found : pointers.get? index = some identity) : identity ∈ pointers := by
  induction pointers generalizing index with
  | nil => simp at found
  | cons head tail ih =>
      cases index with
      | zero => simp at found; subst identity; simp
      | succ index => exact List.mem_cons_of_mem head (ih index (by simpa using found))

theorem cPointerIndex_matches_unique_slot (pointers : List Nat) (identity index : Nat)
    (distinct : CNoDuplicatePointers pointers)
    (found : pointers[index]? = some identity) :
    cPointerIndex identity pointers = some index := by
  induction pointers generalizing index with
  | nil =>
      have impossible : ([] : List Nat).get? index = some identity := by
        rw [← pointerIndexedEqGet?]
        exact found
      simp at impossible
  | cons head tail ih =>
      cases index with
      | zero =>
          have same : head = identity := by simpa [getElem?_def] using found
          simp [cPointerIndex, same]
      | succ index =>
          have tailFound : tail[index]? = some identity := by
            simpa [getElem?_def, Nat.succ_lt_succ_iff] using found
          have headDifferent : head ≠ identity := by
            intro same
            subst identity
            have inTail : head ∈ tail := by
              apply pointerLookupMem tail index head
              rw [← pointerIndexedEqGet?]
              exact tailFound
            exact distinct.1 inTail
          simp [cPointerIndex, headDifferent, ih index distinct.2 tailFound]

theorem cPointerIndex_missing (identity : Nat) (pointers : List Nat)
    (missing : identity ∉ pointers) : cPointerIndex identity pointers = none := by
  induction pointers with
  | nil => rfl
  | cons head tail ih =>
      simp only [List.mem_cons, not_or] at missing
      have notHead : head ≠ identity := Ne.symm missing.1
      simp [cPointerIndex, notHead, ih missing.2]

theorem cPointerIndex_result_is_identity (identity : Nat) (pointers : List Nat)
    (index : Nat) (found : cPointerIndex identity pointers = some index) :
    pointers.get? index = some identity := by
  induction pointers generalizing index with
  | nil => simp [cPointerIndex] at found
  | cons head tail ih =>
      by_cases headMatches : head = identity
      · simp [cPointerIndex, headMatches] at found
        cases index with
        | zero => simp [headMatches]
        | succ index => simp at found
      · simp [cPointerIndex, headMatches] at found
        cases index with
        | zero => simp at found
        | succ index =>
            have tailFound : cPointerIndex identity tail = some index := by
              simpa using found
            simpa using ih index tailFound

/-- Every index returned by the C-style pointer search is a valid de Bruijn
slot in the pointer array. This is the range half of the C-to-Lean type
argument correspondence; `cPointerIndex_result_is_identity` supplies the
matching identity half. -/
theorem cPointerIndex_result_lt_length (identity : Nat) (pointers : List Nat)
    (index : Nat) (found : cPointerIndex identity pointers = some index) :
    index < pointers.length := by
  induction pointers generalizing index with
  | nil => simp [cPointerIndex] at found
  | cons head tail ih =>
      by_cases headMatches : head = identity
      · simp [cPointerIndex, headMatches] at found
        subst index
        simp
      · simp [cPointerIndex, headMatches] at found
        cases index with
        | zero => simp at found
        | succ index =>
            have tailFound : cPointerIndex identity tail = some index := by
              simpa using found
            have tailBound := ih index tailFound
            simp
            omega

theorem decodeCType_variable_wellFormed (pointers : List Nat) (identity : Nat)
    (index : Nat) (found : cPointerIndex identity pointers = some index) :
    (Ty.var index).wellFormed pointers.length := by
  simpa [Ty.wellFormed] using cPointerIndex_result_lt_length identity pointers index found

theorem cPointerIndex_has_slot_iff_mem (identity : Nat) (pointers : List Nat) :
    (∃ index, cPointerIndex identity pointers = some index) ↔ identity ∈ pointers := by
  induction pointers with
  | nil => simp [cPointerIndex]
  | cons head tail ih =>
      by_cases same : head = identity
      · simp [cPointerIndex, same]
      · simp only [cPointerIndex, if_neg same, List.mem_cons]
        constructor
        · rintro ⟨index, found⟩
          cases index with
          | zero => simp at found
          | succ index =>
              right
              apply ih.mp
              exact ⟨index, by simpa using found⟩
        · intro member
          rcases member with same' | tailMember
          · exact False.elim (same (same'.symm))
          · obtain ⟨index, found⟩ := ih.mpr tailMember
            exact ⟨index + 1, by simp [found]⟩

/- The pointer decoder implements the same identity-based slot search as C.
The executable behavior remains explicit even when a pointer is absent. -/
mutual
def decodeCType (pointers : List Nat) : CTypeNode → Option Ty
  | .boolean => some .boolean
  | .integer => some .integer
  | .floating => some .float
  | .string => some .string
  | .character => some .character
  | .unit => some .unit
  | .variable identity => (cPointerIndex identity pointers).map Ty.var
  | .list element => (decodeCType pointers element).map Ty.list
  | .option element => (decodeCType pointers element).map Ty.option
  | .function parameters result => do
      let parameters ← decodeCTypes pointers parameters
      let result ← decodeCType pointers result
      pure (.fn parameters result)
  | .forallType _ _ => none

def decodeCTypes (pointers : List Nat) : List CTypeNode → Option (List Ty)
  | [] => some []
  | head :: tail => do
      let head ← decodeCType pointers head
      let tail ← decodeCTypes pointers tail
      pure (head :: tail)
end

/-- When decoding a C type array succeeds, mapping the per-node decoder with
an arbitrary failure default yields exactly the decoded array. This makes
the successful decoding premise explicit at list-level simulation sites. -/
theorem decodeCTypes_map_getD (pointers : List Nat) (nodes : List CTypeNode)
    (types : List Ty) (decoded : decodeCTypes pointers nodes = some types) :
    nodes.map (fun node => (decodeCType pointers node).getD .unit) = types := by
  induction nodes generalizing types with
  | nil =>
      simp [decodeCTypes] at decoded
      subst types
      rfl
  | cons head tail ih =>
      cases headDecoded : decodeCType pointers head with
      | none => simp [decodeCTypes, headDecoded] at decoded
      | some headType =>
          cases tailDecoded : decodeCTypes pointers tail with
          | none => simp [decodeCTypes, headDecoded, tailDecoded] at decoded
          | some tailTypes =>
              have decodedEqRaw : headType :: tailTypes = types := by
                simpa [decodeCTypes, headDecoded, tailDecoded] using decoded
              have decodedEq : types = headType :: tailTypes := decodedEqRaw.symm
              subst types
              simp [headDecoded, ih tailTypes tailDecoded]

/-- Pointwise evidence that C's substitution array and Lean's inferred type
arguments contain the same decoded caller type at every quantified slot. -/
def CSubstitutionRowsAgree (callerPointers scheme : List Nat)
    (substitutions : List CTypeNode) (arguments : List Ty) : Prop :=
  ∀ index, index < scheme.length →
    ∃ ctype type, substitutions[index]? = some ctype ∧
      arguments[index]? = some type ∧ decodeCType callerPointers ctype = some type

/-- Partial assignment-state correspondence during left-to-right call
constraint collection. Each quantified slot is empty on both sides or stores
C and Lean types related by `decodeCType`. -/
def CSubstitutionStateAgree (callerPointers scheme : List Nat)
    (substitutions : List (Option CTypeNode)) (arguments : List (Option Ty)) : Prop :=
  substitutions.length = scheme.length ∧ arguments.length = scheme.length ∧
    ∀ index, index < scheme.length →
      ((substitutions[index]? = some none ∧ arguments[index]? = some none) ∨
        ∃ ctype type, substitutions[index]? = some (some ctype) ∧
          arguments[index]? = some (some type) ∧
          decodeCType callerPointers ctype = some type)

private theorem replicate_getElem_eq {α : Type} (count index : Nat) (value : α)
    (bound : index < count) : (List.replicate count value)[index]'(by simp; omega) = value := by
  induction count generalizing index with
  | zero => omega
  | succ count ih =>
      cases index with
      | zero => simp [List.replicate]
      | succ index =>
          simpa [List.replicate] using ih index (by omega)

private theorem replicate_lookup_eq_some {α : Type} (count index : Nat) (value : α)
    (bound : index < count) : (List.replicate count value)[index]? = some value := by
  simp only [getElem?_def, List.length_replicate, dif_pos bound]
  exact congrArg some (replicate_getElem_eq count index value bound)

/-- C `check_call` allocates its substitution array with `calloc`, so every
quantified slot starts empty. This is the corresponding Lean/C abstract-state
invariant for both inferred assignment arrays. -/
theorem cSubstitutionStateAgree_initial_empty (callerPointers scheme : List Nat) :
    CSubstitutionStateAgree callerPointers scheme
      (List.replicate scheme.length none) (List.replicate scheme.length none) := by
  constructor
  · simp
  constructor
  · simp
  · intro index bound
    exact Or.inl
      ⟨replicate_lookup_eq_some scheme.length index none bound,
        replicate_lookup_eq_some scheme.length index none bound⟩

/-- Once C `check_call` has rejected every unassigned quantified slot, its
pointwise assignment-state relation becomes the total substitution relation
used by `substitute_type`. -/
theorem CSubstitutionStateAgree.toRowsAgree
    (callerPointers scheme : List Nat)
    (cAssignments : List (Option CTypeNode)) (arguments : List Ty)
    (stateAgree : CSubstitutionStateAgree callerPointers scheme cAssignments
      (arguments.map some))
    (allAssigned : ∀ index, index < scheme.length →
      ∃ ctype, cAssignments[index]? = some (some ctype)) :
    CSubstitutionRowsAgree callerPointers scheme
      (cAssignments.map (Option.getD · .unit)) arguments := by
  rcases stateAgree with ⟨cLength, leanLength, pointwise⟩
  intro index bound
  obtain ⟨ctype, cAssigned⟩ := allAssigned index bound
  rcases pointwise index bound with empty | assigned
  · have contradiction : (none : Option CTypeNode) = some ctype :=
      Option.some.inj (empty.1.symm.trans cAssigned)
    cases contradiction
  · obtain ⟨relatedCType, type, cFound, leanFound, decoded⟩ := assigned
    have sameCType : relatedCType = ctype := by
      have both := cFound.symm.trans cAssigned
      exact Option.some.inj (Option.some.inj both)
    have mappedLean :
        (arguments.get? index).map some = some (some type) := by
      have found : (arguments.map some).get? index = some (some type) := by
        rw [← pointerIndexedEqGet?]
        exact leanFound
      rw [List.get?_map] at found
      exact found
    have expected : arguments.get? index = some type := by
      cases found : arguments.get? index with
      | none => simp [found] at mappedLean
      | some value =>
          have valueEq : value = type := by simpa [found] using mappedLean
          simp [found, valueEq]
    subst relatedCType
    refine ⟨ctype, type, ?_, ?_, decoded⟩
    · have found : (cAssignments.map (Option.getD · .unit)).get? index = some ctype := by
        rw [List.get?_map]
        have cFound' : cAssignments.get? index = some (some ctype) := by
          rw [← pointerIndexedEqGet?]
          exact cAssigned
        simp [List.get?_map, cFound']
      exact (pointerIndexedEqGet? (cAssignments.map (Option.getD · .unit)) index).trans found
    · exact (pointerIndexedEqGet? arguments index).trans expected

private theorem cListSetLookupOther {α : Type} (items : List α) (index queried : Nat)
    (replacement value : α) (different : index ≠ queried)
    (old : items[queried]? = some value) :
    (items.set index replacement)[queried]? = some value := by
  have old' : items.get? queried = some value := by
    rw [← pointerIndexedEqGet?]
    exact old
  obtain ⟨bound, entry⟩ := List.get?_eq_some.mp old'
  have newBound : queried < (items.set index replacement).length := by
    simpa [List.length_set] using bound
  have unchanged := List.get_set_ne items different replacement newBound
  have new' : (items.set index replacement).get? queried = some value :=
    List.get?_eq_some.mpr ⟨newBound, unchanged.trans entry⟩
  rw [pointerIndexedEqGet?]
  exact new'

/-- Filling the same currently empty quantified slot with a decoded actual
type preserves the C/Lean assignment-state correspondence at every slot. -/
theorem cSubstitutionStateAgree_first_capture
    (callerPointers scheme : List Nat) (cAssignments : List (Option CTypeNode))
    (leanAssignments : List (Option Ty)) (index : Nat) (actual : CTypeNode)
    (actualType : Ty)
    (stateAgree : CSubstitutionStateAgree callerPointers scheme cAssignments
      leanAssignments)
    (indexBound : index < scheme.length)
    (cEmpty : cAssignments[index]? = some none)
    (leanEmpty : leanAssignments[index]? = some none)
    (actualDecoded : decodeCType callerPointers actual = some actualType) :
    CSubstitutionStateAgree callerPointers scheme
      (cAssignments.set index (some actual))
      (leanAssignments.set index (some actualType)) := by
  rcases stateAgree with ⟨cLength, leanLength, pointwise⟩
  refine ⟨by simpa [List.length_set] using cLength,
    by simpa [List.length_set] using leanLength, ?_⟩
  intro queried queriedBound
  by_cases same : queried = index
  · subst queried
    right
    exact ⟨actual, actualType, by
      rw [pointerIndexedEqGet?]
      exact List.get?_eq_some.mpr ⟨by simpa [List.length_set] using
        (List.get?_eq_some.mp (by rw [← pointerIndexedEqGet?]; exact cEmpty)).1,
        List.get_set_eq cAssignments index (some actual)
          (by simpa using (List.get?_eq_some.mp (by rw [← pointerIndexedEqGet?]; exact cEmpty)).1)⟩,
      by
        rw [pointerIndexedEqGet?]
        exact List.get?_eq_some.mpr ⟨by simpa [List.length_set] using
          (List.get?_eq_some.mp (by rw [← pointerIndexedEqGet?]; exact leanEmpty)).1,
          List.get_set_eq leanAssignments index (some actualType)
            (by simpa using (List.get?_eq_some.mp (by rw [← pointerIndexedEqGet?]; exact leanEmpty)).1)⟩,
      actualDecoded⟩
  · have different : index ≠ queried := fun equality => same equality.symm
    rcases pointwise queried queriedBound with empty | assigned
    · left
      exact ⟨cListSetLookupOther cAssignments index queried (some actual) none
          different empty.1,
        cListSetLookupOther leanAssignments index queried (some actualType) none
          different empty.2⟩
    · right
      obtain ⟨ctype, type, cFound, leanFound, decoded⟩ := assigned
      exact ⟨ctype, type,
        cListSetLookupOther cAssignments index queried (some actual) (some ctype)
          different cFound,
        cListSetLookupOther leanAssignments index queried (some actualType) (some type)
          different leanFound,
        decoded⟩

theorem decodeCTypes_length (pointers : List Nat) (nodes : List CTypeNode)
    (types : List Ty) (decoded : decodeCTypes pointers nodes = some types) :
    nodes.length = types.length := by
  induction nodes generalizing types with
  | nil => cases types <;> simp [decodeCTypes] at decoded ⊢
  | cons node rest ih =>
      cases headDecoded : decodeCType pointers node with
      | none => simp [decodeCTypes, headDecoded] at decoded
      | some headType =>
          cases tailDecoded : decodeCTypes pointers rest with
          | none => simp [decodeCTypes, headDecoded, tailDecoded] at decoded
          | some tailTypes =>
              have typesEq : headType :: tailTypes = types := by
                simpa [decodeCTypes, headDecoded, tailDecoded] using decoded
              cases typesEq
              simp only [List.length_cons]
              have tailLength := ih tailTypes tailDecoded
              omega

/-- At one quantified-variable substitution, the C pointer-array lookup and
Lean's de Bruijn instantiation select the same inferred caller type. -/
theorem cSubstituteVariable_matches_Lean_inferred_argument
    (scheme callerPointers : List Nat) (substitutions : List CTypeNode)
    (arguments : List Ty) (identity index : Nat) (actual : CTypeNode)
    (actualType : Ty)
    (pointerSlot : cPointerIndex identity scheme = some index)
    (cSubstitution : substitutions[index]? = some actual)
    (actualDecoded : decodeCType callerPointers actual = some actualType)
    (leanArgument : arguments[index]? = some actualType) :
    cSubstituteVariable scheme substitutions identity = some actual ∧
      (Ty.var index).instantiate arguments = actualType := by
  refine ⟨?_, ?_⟩
  · simp [cSubstituteVariable, pointerSlot, cSubstitution]
  · simp [Ty.instantiate, leanArgument]

/-- Caller-owned variables are rigid during C substitution. The C pointer is
left intact, while Lean removes the quantified prefix from the corresponding
de Bruijn index and preserves the caller's slot. -/
theorem cSubstituteVariable_preserves_rigid_caller_variable
    (scheme callerPointers : List Nat) (substitutions : List CTypeNode)
    (arguments : List Ty) (identity callerIndex : Nat)
    (notQuantified : cPointerIndex identity scheme = none)
    (callerSlot : cPointerIndex identity callerPointers = some callerIndex) :
    cSubstituteVariable scheme substitutions identity = some (.variable identity) ∧
      decodeCType callerPointers (.variable identity) = some (.var callerIndex) ∧
      (Ty.var (arguments.length + callerIndex)).instantiate arguments =
        .var callerIndex := by
  refine ⟨?_, ?_, ?_⟩
  · simp [cSubstituteVariable, notQuantified]
  · simp [decodeCType, callerSlot]
  · have outside : ¬ arguments.length + callerIndex < arguments.length := by omega
    simp [Ty.instantiate, getElem?_def, outside, Nat.add_sub_cancel_left]

/-- Every successful C type decode is scoped by its ordered scheme-pointer
array, including variables nested through function parameter lists. -/
theorem decodeCType_wellFormed (pointers : List Nat) (node : CTypeNode) (type : Ty)
    (decoded : decodeCType pointers node = some type) : type.wellFormed pointers.length := by
  refine CTypeNode.rec
    (motive_1 := fun node => ∀ type, decodeCType pointers node = some type →
      type.wellFormed pointers.length)
    (motive_2 := fun nodes => ∀ types, decodeCTypes pointers nodes = some types →
      ∀ type ∈ types, type.wellFormed pointers.length)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ node type decoded
  · intro type decoded
    simp [decodeCType] at decoded
    cases decoded
    simp [Ty.wellFormed]

  · intro type decoded
    simp [decodeCType] at decoded
    cases decoded
    simp [Ty.wellFormed]
  · intro type decoded
    simp [decodeCType] at decoded
    cases decoded
    simp [Ty.wellFormed]
  · intro type decoded
    simp [decodeCType] at decoded
    cases decoded
    simp [Ty.wellFormed]
  · intro type decoded
    simp [decodeCType] at decoded
    cases decoded
    simp [Ty.wellFormed]
  · intro type decoded
    simp [decodeCType] at decoded
    cases decoded
    simp [Ty.wellFormed]
  · intro identity type decoded
    cases found : cPointerIndex identity pointers with
    | none => simp [decodeCType, found] at decoded
    | some index =>
        simp [decodeCType, found] at decoded
        cases decoded
        exact decodeCType_variable_wellFormed pointers identity index found
  · intro element elementIH type decoded
    cases elementDecoded : decodeCType pointers element with
    | none => simp [decodeCType, elementDecoded] at decoded
    | some elementType =>
        have elementWF := elementIH elementType elementDecoded
        simp [decodeCType, elementDecoded] at decoded
        cases decoded
        simpa [Ty.wellFormed] using elementWF
  · intro element elementIH type decoded
    cases elementDecoded : decodeCType pointers element with
    | none => simp [decodeCType, elementDecoded] at decoded
    | some elementType =>
        have elementWF := elementIH elementType elementDecoded
        simp [decodeCType, elementDecoded] at decoded
        cases decoded
        simpa [Ty.wellFormed] using elementWF
  · intro parameters result parametersIH resultIH type decoded
    cases parametersDecoded : decodeCTypes pointers parameters with
    | none => simp [decodeCType, parametersDecoded] at decoded
    | some parameterTypes =>
      cases resultDecoded : decodeCType pointers result with
      | none => simp [decodeCType, parametersDecoded, resultDecoded] at decoded
      | some resultType =>
        have parametersWF := parametersIH parameterTypes parametersDecoded
        have resultWF := resultIH resultType resultDecoded
        simp [decodeCType, parametersDecoded, resultDecoded] at decoded
        have typeEq : type = .fn parameterTypes resultType := decoded.symm
        subst type
        simpa [Ty.wellFormed] using And.intro parametersWF resultWF
  · intro variables body bodyIH type decoded
    simp [decodeCType] at decoded
  · intro types decoded
    simp [decodeCTypes] at decoded
    cases decoded
    simp
  · intro head tail headIH tailIH types decoded
    cases headDecoded : decodeCType pointers head with
    | none => simp [decodeCTypes, headDecoded] at decoded
    | some headType =>
      cases tailDecoded : decodeCTypes pointers tail with
      | none => simp [decodeCTypes, headDecoded, tailDecoded] at decoded
      | some tailTypes =>
        have headWF := headIH headType headDecoded
        have tailWF := tailIH tailTypes tailDecoded
        simp [decodeCTypes, headDecoded, tailDecoded] at decoded
        cases decoded
        intro item member
        simp only [List.mem_cons] at member
        rcases member with same | member
        · cases same
          exact headWF
        · exact tailWF item member

theorem decodeCTypes_wellFormed (pointers : List Nat) (nodes : List CTypeNode)
    (types : List Ty) (decoded : decodeCTypes pointers nodes = some types) :
    ∀ type ∈ types, type.wellFormed pointers.length := by
  induction nodes generalizing types with
  | nil =>
      simp [decodeCTypes] at decoded
      subst types
      intro type member
      simp at member
  | cons node rest ih =>
      cases headDecoded : decodeCType pointers node with
      | none => simp [decodeCTypes, headDecoded] at decoded
      | some headType =>
          cases restDecoded : decodeCTypes pointers rest with
          | none => simp [decodeCTypes, headDecoded, restDecoded] at decoded
          | some restTypes =>
              have typesEq : headType :: restTypes = types := by
                simpa [decodeCTypes, headDecoded, restDecoded] using decoded
              cases typesEq
              intro type member
              simp only [List.mem_cons] at member
              rcases member with same | member
              · cases same
                exact decodeCType_wellFormed pointers node headType headDecoded
              · exact ih restTypes restDecoded type member

/-- Structural substitution correspondence for C `substitute_type` and
Lean's quantified-prefix `Ty.instantiate`. The state assumption says both
inferred substitution arrays decode to the same type at every quantified slot. -/
theorem cSubstituteType_decodes_to_instantiate
    (scheme callerPointers : List Nat) (substitutions : List CTypeNode)
    (arguments : List Ty) (rowsAgree : CSubstitutionRowsAgree callerPointers
      scheme substitutions arguments) (node : CTypeNode) (type : Ty)
    (decoded : decodeCType scheme node = some type) :
    ∃ output, cSubstituteType scheme substitutions node = some output ∧
      decodeCType callerPointers output = some (type.instantiate arguments) := by
  refine CTypeNode.rec
    (motive_1 := fun current => ∀ type, decodeCType scheme current = some type →
      ∃ output, cSubstituteType scheme substitutions current = some output ∧
        decodeCType callerPointers output = some (type.instantiate arguments))
    (motive_2 := fun currents => ∀ types, decodeCTypes scheme currents = some types →
      ∃ outputs, cSubstituteTypes scheme substitutions currents = some outputs ∧
        decodeCTypes callerPointers outputs = some (instantiateTypes arguments types))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ node type decoded
  · intro type decoded
    have typeEq : type = .boolean := by simpa [decodeCType] using decoded.symm
    subst type
    exact ⟨.boolean, by simp [cSubstituteType], by simp [decodeCType, Ty.instantiate]⟩
  · intro type decoded
    have typeEq : type = .integer := by simpa [decodeCType] using decoded.symm
    subst type
    exact ⟨.integer, by simp [cSubstituteType], by simp [decodeCType, Ty.instantiate]⟩
  · intro type decoded
    have typeEq : type = .float := by simpa [decodeCType] using decoded.symm
    subst type
    exact ⟨.floating, by simp [cSubstituteType], by simp [decodeCType, Ty.instantiate]⟩
  · intro type decoded
    have typeEq : type = .string := by simpa [decodeCType] using decoded.symm
    subst type
    exact ⟨.string, by simp [cSubstituteType], by simp [decodeCType, Ty.instantiate]⟩
  · intro type decoded
    have typeEq : type = .character := by simpa [decodeCType] using decoded.symm
    subst type
    exact ⟨.character, by simp [cSubstituteType], by simp [decodeCType, Ty.instantiate]⟩
  · intro type decoded
    have typeEq : type = .unit := by simpa [decodeCType] using decoded.symm
    subst type
    exact ⟨.unit, by simp [cSubstituteType], by simp [decodeCType, Ty.instantiate]⟩
  · intro identity type decoded
    cases pointerSlot : cPointerIndex identity scheme with
    | none => simp [decodeCType, pointerSlot] at decoded
    | some index =>
        have typeEq : type = .var index := by
          simpa [decodeCType, pointerSlot] using decoded.symm
        subst type
        have indexBound := cPointerIndex_result_lt_length identity scheme index pointerSlot
        obtain ⟨cActual, actualType, cAssignment, leanAssignment, actualDecoded⟩ :=
          rowsAgree index indexBound
        refine ⟨cActual, ?_, ?_⟩
        · simp [cSubstituteType, cSubstituteVariable, pointerSlot, cAssignment]
        · simp [decodeCType, actualDecoded, Ty.instantiate, leanAssignment]
  · intro element elementIH type decoded
    cases elementDecoded : decodeCType scheme element with
    | none => simp [decodeCType, elementDecoded] at decoded
    | some elementType =>
        obtain ⟨output, substituted, outputDecoded⟩ := elementIH elementType elementDecoded
        have typeEq : type = .list elementType := by
          simpa [decodeCType, elementDecoded] using decoded.symm
        subst type
        refine ⟨.list output, ?_, ?_⟩
        · simp [cSubstituteType, substituted]
        · simpa [decodeCType, outputDecoded, Ty.instantiate]
  · intro element elementIH type decoded
    cases elementDecoded : decodeCType scheme element with
    | none => simp [decodeCType, elementDecoded] at decoded
    | some elementType =>
        obtain ⟨output, substituted, outputDecoded⟩ := elementIH elementType elementDecoded
        have typeEq : type = .option elementType := by
          simpa [decodeCType, elementDecoded] using decoded.symm
        subst type
        refine ⟨.option output, ?_, ?_⟩
        · simp [cSubstituteType, substituted]
        · simpa [decodeCType, outputDecoded, Ty.instantiate]
  · intro parameters result parametersIH resultIH type decoded
    cases parametersDecoded : decodeCTypes scheme parameters with
    | none => simp [decodeCType, parametersDecoded] at decoded
    | some parameterTypes =>
        cases resultDecoded : decodeCType scheme result with
        | none => simp [decodeCType, parametersDecoded, resultDecoded] at decoded
        | some resultType =>
            obtain ⟨outputParameters, parametersSubstituted, parametersOutputDecoded⟩ :=
              parametersIH parameterTypes parametersDecoded
            obtain ⟨outputResult, resultSubstituted, resultOutputDecoded⟩ :=
              resultIH resultType resultDecoded
            have typeEq : type = .fn parameterTypes resultType := by
              simpa [decodeCType, parametersDecoded, resultDecoded] using decoded.symm
            subst type
            refine ⟨.function outputParameters outputResult, ?_, ?_⟩
            · simp [cSubstituteType, parametersSubstituted, resultSubstituted]
            · simpa [decodeCType, parametersOutputDecoded, resultOutputDecoded,
                Ty.instantiate]
  · intro variables body bodyIH type decoded
    simp [decodeCType] at decoded
  · intro types decoded
    have typesEq : types = [] := by simpa [decodeCTypes] using decoded.symm
    subst types
    exact ⟨[], by simp [cSubstituteTypes], by simp [decodeCTypes, instantiateTypes]⟩
  · intro head tail headIH tailIH types decoded
    cases headDecoded : decodeCType scheme head with
    | none => simp [decodeCTypes, headDecoded] at decoded
    | some headType =>
        cases tailDecoded : decodeCTypes scheme tail with
        | none => simp [decodeCTypes, headDecoded, tailDecoded] at decoded
        | some tailTypes =>
            obtain ⟨headOutput, headSubstituted, headOutputDecoded⟩ :=
              headIH headType headDecoded
            obtain ⟨tailOutputs, tailSubstituted, tailOutputsDecoded⟩ :=
              tailIH tailTypes tailDecoded
            have typesEq : types = headType :: tailTypes := by
              simpa [decodeCTypes, headDecoded, tailDecoded] using decoded.symm
            subst types
            refine ⟨headOutput :: tailOutputs, ?_, ?_⟩
            · simp [cSubstituteTypes, headSubstituted, tailSubstituted]
            · simpa [decodeCTypes, headOutputDecoded, tailOutputsDecoded,
                instantiateTypes]

/-- C result substitution also preserves caller-scope well-formedness when
the inferred arguments are monotypes in that scope and the scheme result is
well formed under its quantified prefix. -/
theorem cSubstituteType_decodes_to_instantiate_wellFormed
    (scheme callerPointers : List Nat) (substitutions : List CTypeNode)
    (arguments : List Ty)
    (rowsAgree : CSubstitutionRowsAgree callerPointers scheme substitutions arguments)
    (node : CTypeNode) (type : Ty)
    (decoded : decodeCType scheme node = some type)
    (argumentsWellFormed : ∀ argument ∈ arguments,
      argument.wellFormed callerPointers.length)
    (typeWellFormed : type.wellFormed (arguments.length + callerPointers.length)) :
    ∃ output,
      cSubstituteType scheme substitutions node = some output ∧
      decodeCType callerPointers output = some (type.instantiate arguments) ∧
      (type.instantiate arguments).wellFormed callerPointers.length := by
  obtain ⟨output, substituted, outputDecoded⟩ :=
    cSubstituteType_decodes_to_instantiate scheme callerPointers substitutions arguments
      rowsAgree node type decoded
  exact ⟨output, substituted, outputDecoded,
    Ty.instantiate_wellFormed arguments type callerPointers.length
      argumentsWellFormed typeWellFormed⟩

theorem decodeCType_pointer_missing (pointers : List Nat) (identity : Nat)
    (missing : identity ∉ pointers) :
    decodeCType pointers (.variable identity) = none := by
  simp [decodeCType, cPointerIndex_missing identity pointers missing]

theorem decodeCType_variable_at_unique_pointer (pointers : List Nat) (identity index : Nat)
    (distinct : CNoDuplicatePointers pointers)
    (found : pointers[index]? = some identity) :
    decodeCType pointers (.variable identity) = some (.var index) := by
  simp [decodeCType, cPointerIndex_matches_unique_slot pointers identity index distinct found]

/-- With distinct scheme pointers, C variable-node decoding selects exactly
the corresponding Lean scheme index, in both directions. -/
theorem decodeCType_variable_iff_pointer_slot (pointers : List Nat)
    (identity index : Nat) (distinct : CNoDuplicatePointers pointers) :
    decodeCType pointers (.variable identity) = some (.var index) ↔
      pointers[index]? = some identity := by
  constructor
  · intro decoded
    simp [decodeCType] at decoded
    rw [pointerIndexedEqGet?]
    exact cPointerIndex_result_is_identity identity pointers index decoded
  · intro found
    exact decodeCType_variable_at_unique_pointer pointers identity index distinct found

/-- Two C identities that decode to the same de Bruijn slot must be equal.
The first-match lookup itself forces both identities to equal the value at
that slot, so this fact does not require a duplicate-free pointer array. -/
theorem cPointerIndex_same_slot_identity (pointers : List Nat)
    (left right index : Nat)
    (leftFound : cPointerIndex left pointers = some index)
    (rightFound : cPointerIndex right pointers = some index) :
    left = right := by
  have leftAtSlot := cPointerIndex_result_is_identity left pointers index leftFound
  have rightAtSlot := cPointerIndex_result_is_identity right pointers index rightFound
  rw [leftAtSlot] at rightAtSlot
  exact Option.some.inj rightAtSlot

/-- Injectivity of decoding for the variable-node case. -/
theorem decodeCType_variable_injective (pointers : List Nat)
    (left right index : Nat)
    (leftDecoded : decodeCType pointers (.variable left) = some (.var index))
    (rightDecoded : decodeCType pointers (.variable right) = some (.var index)) :
    left = right := by
  have leftFound : cPointerIndex left pointers = some index := by
    simpa [decodeCType] using leftDecoded
  have rightFound : cPointerIndex right pointers = some index := by
    simpa [decodeCType] using rightDecoded
  exact cPointerIndex_same_slot_identity pointers left right index leftFound rightFound

/-- A decoded variable preserves the identity stored at its slot. Together
with `decodeCType_variable_injective`, this gives both directions of the
identity/index correspondence even when the pointer array is malformed with
duplicates: duplicate slots can affect the selected index, but cannot make
two different identities decode to one index. -/
theorem decodeCType_variable_slot_identity (pointers : List Nat)
    (identity index : Nat)
    (decoded : decodeCType pointers (.variable identity) = some (.var index)) :
    pointers.get? index = some identity := by
  have found : cPointerIndex identity pointers = some index := by
    simpa [decodeCType] using decoded
  exact cPointerIndex_result_is_identity identity pointers index found

mutual
def cMonotype : CTypeNode → Bool
  | .boolean | .integer | .floating | .string | .character | .unit | .variable _ => true
  | .list element => cMonotype element
  | .option element => cMonotype element
  | .function parameters result => cMonotypes parameters && cMonotype result
  | .forallType _ _ => false

def cMonotypes : List CTypeNode → Bool
  | [] => true
  | head :: tail => cMonotype head && cMonotypes tail
end

theorem cMonotype_rejects_forall (variables : List Nat) (body : CTypeNode) :
    cMonotype (.forallType variables body) = false := by
  simp [cMonotype]

theorem cMonotype_rejects_nested_forall (variables : List Nat) (body : CTypeNode)
    (pointers : List Nat) :
    cMonotype (.function [.option (.forallType variables body)] (.list .integer)) = false := by
  simp [cMonotype, cMonotypes]

mutual
def cTypeEq : Nat → CTypeNode → CTypeNode → Bool
  | 0, _, _ => false
  | fuel + 1, left, right =>
      match left, right with
      | .boolean, .boolean | .integer, .integer | .floating, .floating
      | .string, .string | .character, .character | .unit, .unit => true
      | .variable a, .variable b => a == b
      | .list a, .list b | .option a, .option b => cTypeEq fuel a b
      | .function leftArgs leftResult, .function rightArgs rightResult =>
          leftArgs.length == rightArgs.length &&
            cTypesEq fuel leftArgs rightArgs && cTypeEq fuel leftResult rightResult
      | _, _ => false

def cTypesEq : Nat → List CTypeNode → List CTypeNode → Bool
  | 0, _, _ => false
  | fuel + 1, [], [] => true
  | fuel + 1, left :: leftTail, right :: rightTail =>
      cTypeEq fuel left right && cTypesEq fuel leftTail rightTail
  | fuel + 1, _, _ => false
end

/-- The reverse comparison fact for caller-side variable leaves: if two C
variable nodes decode to the same rigid Lean `Ty.var`, C's structural
equality accepts them at every positive fuel. This is a local completeness
lemma for the repeated-variable path in the inverse constraint simulation. -/
theorem cTypeEq_variable_of_decode_eq (fuel : Nat) (pointers : List Nat)
    (left right index : Nat)
    (leftDecoded : decodeCType pointers (.variable left) = some (.var index))
    (rightDecoded : decodeCType pointers (.variable right) = some (.var index)) :
    cTypeEq (fuel + 1) (.variable left) (.variable right) = true := by
  have sameIdentity := decodeCType_variable_injective pointers left right index
    leftDecoded rightDecoded
  subst right
  simp [cTypeEq]

mutual
def cTypeCost : CTypeNode → Nat
  | .boolean | .integer | .floating | .string | .character | .unit | .variable _ | .forallType _ _ => 1
  | .list element | .option element => cTypeCost element + 1
  | .function parameters result => cTypesCost parameters + cTypeCost result + 1

def cTypesCost : List CTypeNode → Nat
  | [] => 1
  | head :: tail => cTypeCost head + cTypesCost tail + 1
end


/-- The C structural equality model accepts a monotype compared with itself
once fuel exceeds its structural cost. This is the completeness direction on
identical C type trees. -/
theorem cTypeEq_reflexive_of_cost (fuel : Nat) :
    (∀ node, cMonotype node = true → cTypeCost node < fuel →
      cTypeEq fuel node node = true) ∧
    (∀ nodes, cMonotypes nodes = true → cTypesCost nodes < fuel →
      cTypesEq fuel nodes nodes = true) := by
  induction fuel with
  | zero =>
      constructor
      · intro node _ bound
        cases node <;> simp [cTypeCost] at bound <;> omega
      · intro nodes _ bound
        cases nodes with
        | nil => simp [cTypesCost] at bound <;> omega
        | cons head tail => simp [cTypesCost] at bound <;> omega
  | succ fuel ih =>
      constructor
      · intro node monotype costBound
        cases node with
        | boolean | integer | floating | string | character | unit | «variable» _ => simp [cTypeEq]
        | list element =>
            have elementMono : cMonotype element = true := by simpa [cMonotype] using monotype
            have elementCost : cTypeCost element < fuel := by
              simp [cTypeCost] at costBound
              omega
            simpa only [cTypeEq] using ih.1 element elementMono elementCost
        | option element =>
            have elementMono : cMonotype element = true := by simpa [cMonotype] using monotype
            have elementCost : cTypeCost element < fuel := by
              simp [cTypeCost] at costBound
              omega
            simpa only [cTypeEq] using ih.1 element elementMono elementCost
        | function parameters result =>
            have parts : cMonotypes parameters = true ∧ cMonotype result = true := by
              simpa [cMonotype, cMonotypes] using monotype
            have parametersCost : cTypesCost parameters < fuel := by
              simp [cTypeCost] at costBound
              omega
            have resultCost : cTypeCost result < fuel := by
              simp [cTypeCost] at costBound
              omega
            simp [cTypeEq, ih.2 parameters parts.1 parametersCost,
              ih.1 result parts.2 resultCost]
        | forallType _ _ => simp [cMonotype] at monotype
      · intro nodes monotypes costBound
        cases nodes with
        | nil => simp [cTypesEq]
        | cons head tail =>
            have parts : cMonotype head = true ∧ cMonotypes tail = true := by
              simpa [cMonotypes, Bool.and_eq_true] using monotypes
            have headCost : cTypeCost head < fuel := by
              simp [cTypesCost] at costBound
              omega
            have tailCost : cTypesCost tail < fuel := by
              simp [cTypesCost] at costBound
              omega
            simp [cTypesEq, ih.1 head parts.1 headCost,
              ih.2 tail parts.2 tailCost]

/-- A successful structural type comparison always produces the same decoded
Lean type on both sides. This is the soundness direction needed for repeated
variable constraints. -/
theorem cTypeEq_decode_agreement (fuel : Nat) (pointers : List Nat) :
    (∀ left right, cTypeEq fuel left right = true →
      decodeCType pointers left = decodeCType pointers right) ∧
    (∀ left right, cTypesEq fuel left right = true →
      decodeCTypes pointers left = decodeCTypes pointers right) := by
  induction fuel with
  | zero =>
      constructor
      · intro left right equal
        simp [cTypeEq] at equal
      · intro left right equal
        simp [cTypesEq] at equal
  | succ fuel ih =>
      constructor
      · intro left right equal
        cases left with
        | boolean => cases right <;> simp_all [cTypeEq, decodeCType]
        | integer => cases right <;> simp_all [cTypeEq, decodeCType]
        | floating => cases right <;> simp_all [cTypeEq, decodeCType]
        | string => cases right <;> simp_all [cTypeEq, decodeCType]
        | character => cases right <;> simp_all [cTypeEq, decodeCType]
        | unit => cases right <;> simp_all [cTypeEq, decodeCType]
        | «variable» leftIdentity =>
            cases right with
            | «variable» rightIdentity => simp_all [cTypeEq, decodeCType]
            | _ => simp [cTypeEq] at equal
        | list leftElement =>
            cases right with
            | list rightElement =>
                simp only [cTypeEq] at equal
                have childDecoded := ih.1 leftElement rightElement equal
                simpa [decodeCType] using congrArg (Option.map Ty.list) childDecoded
            | _ => simp [cTypeEq] at equal
        | option leftElement =>
            cases right with
            | option rightElement =>
                simp only [cTypeEq] at equal
                have childDecoded := ih.1 leftElement rightElement equal
                simpa [decodeCType] using congrArg (Option.map Ty.option) childDecoded
            | _ => simp [cTypeEq] at equal
        | function leftParameters leftResult =>
            cases right with
            | function rightParameters rightResult =>
                simp only [cTypeEq, Bool.and_eq_true] at equal
                rcases equal with ⟨⟨lengthsEqual, parametersEqual⟩, resultEqual⟩
                have _lengthsEqual : leftParameters.length = rightParameters.length :=
                  Nat.eq_of_beq_eq_true lengthsEqual
                have parametersDecoded := ih.2 leftParameters rightParameters parametersEqual
                have resultDecoded := ih.1 leftResult rightResult resultEqual
                simp [decodeCType, parametersDecoded, resultDecoded]
            | _ => simp [cTypeEq] at equal
        | forallType _ _ => simp [cTypeEq] at equal
      · intro left right equal
        cases left with
        | nil =>
            cases right with
            | nil => rfl
            | cons head tail => simp [cTypesEq] at equal
        | cons head tail =>
            cases right with
            | nil => simp [cTypesEq] at equal
            | cons rightHead rightTail =>
                simp only [cTypesEq, Bool.and_eq_true] at equal
                rcases equal with ⟨headEqual, tailEqual⟩
                have headDecoded := ih.1 head rightHead headEqual
                have tailDecoded := ih.2 tail rightTail tailEqual
                simp [decodeCTypes, headDecoded, tailDecoded]

/- Structural model of C `match_type`. The scheme is the ordered pointer
array whose entries alone are flexible. Assignments store actual C type
nodes, so repeated constraints compare the same structural representation. -/
mutual
def cMatchType : Nat → List Nat → CTypeNode → CTypeNode →
    List (Option CTypeNode) → Option (List (Option CTypeNode))
  | 0, _, _, _, _ => none
  | fuel + 1, scheme, pattern, actual, assignments =>
      if cMonotype actual then
        match pattern with
        | .variable identity =>
            match cPointerIndex identity scheme with
            | none => if cTypeEq (fuel + 1) actual (.variable identity) then some assignments else none
            | some index =>
                match assignments[index]? with
                | none => none
                | some none => some (assignments.set index (some actual))
                | some (some previous) =>
                    if cTypeEq (fuel + 1) previous actual then some assignments else none
        | .boolean => if cTypeEq (fuel + 1) actual .boolean then some assignments else none
        | .integer => if cTypeEq (fuel + 1) actual .integer then some assignments else none
        | .floating => if cTypeEq (fuel + 1) actual .floating then some assignments else none
        | .string => if cTypeEq (fuel + 1) actual .string then some assignments else none
        | .character => if cTypeEq (fuel + 1) actual .character then some assignments else none
        | .unit => if cTypeEq (fuel + 1) actual .unit then some assignments else none
        | .list element =>
            match actual with
            | .list input => cMatchType fuel scheme element input assignments
            | _ => none
        | .option element =>
            match actual with
            | .option input => cMatchType fuel scheme element input assignments
            | _ => none
        | .function parameters result =>
            match actual with
            | .function inputs output =>
                if parameters.length = inputs.length then do
                  let next ← cMatchTypes fuel scheme parameters inputs assignments
                  cMatchType fuel scheme result output next
                else none
            | _ => none
        | .forallType _ _ => none
      else none

def cMatchTypes : Nat → List Nat → List CTypeNode → List CTypeNode →
    List (Option CTypeNode) → Option (List (Option CTypeNode))
  | 0, _, _, _, _ => none
  | fuel + 1, scheme, patterns, actuals, assignments =>
      match patterns, actuals with
      | [], [] => some assignments
      | pattern :: patternTail, actual :: actualTail => do
          let next ← cMatchType fuel scheme pattern actual assignments
          cMatchTypes fuel scheme patternTail actualTail next
      | _, _ => none
end

inductive CPrimitiveType : CTypeNode → Prop where
  | boolean : CPrimitiveType .boolean
  | integer : CPrimitiveType .integer
  | floating : CPrimitiveType .floating
  | string : CPrimitiveType .string
  | character : CPrimitiveType .character
  | unit : CPrimitiveType .unit

private theorem cMatchPrimitive_extract (fuel : Nat) (actual base : CTypeNode)
    (assignments : List (Option CTypeNode)) (next : List (Option CTypeNode))
    (matched : (if cMonotype actual then
      if cTypeEq (fuel + 1) actual base then some assignments else none else none) =
        some next) :
    cTypeEq (fuel + 1) actual base = true ∧ next = assignments := by
  cases mono : cMonotype actual with
  | false => simp [mono] at matched
  | true =>
      cases equal : cTypeEq (fuel + 1) actual base with
      | false => simp [mono, equal] at matched
      | true =>
          simp [mono, equal] at matched
          exact ⟨rfl, matched.symm⟩

/-- Primitive C type constraints leave both assignment arrays unchanged. A
successful C comparison decodes to the same Lean primitive type, so the Lean
collector makes the identical no-op transition. -/
theorem cMatchType_primitive_simulation (fuel : Nat)
    (scheme callerPointers : List Nat) (pattern actual : CTypeNode)
    (patternType actualType : Ty) (cAssignments : List (Option CTypeNode))
    (leanAssignments : List (Option Ty)) (cNext : List (Option CTypeNode))
    (primitive : CPrimitiveType pattern)
    (patternDecoded : decodeCType scheme pattern = some patternType)
    (actualDecoded : decodeCType callerPointers actual = some actualType)
    (matched : cMatchType (fuel + 1) scheme pattern actual cAssignments = some cNext) :
    cNext = cAssignments ∧
      collectArgument (fuel + 1) patternType actualType leanAssignments =
        some leanAssignments := by
  cases primitive with
  | boolean =>
      have extracted := cMatchPrimitive_extract fuel actual .boolean cAssignments cNext
        (by simpa [cMatchType] using matched)
      have equal := extracted.1
      have decodedEqual := (cTypeEq_decode_agreement (fuel + 1) callerPointers).1
        actual .boolean equal
      simp [decodeCType] at decodedEqual
      have actualEq : actualType = .boolean := by
        simpa [actualDecoded] using decodedEqual
      have patternEq : patternType = .boolean := by
        simpa [decodeCType] using patternDecoded.symm
      subst actualType patternType
      exact ⟨extracted.2, by simp [collectArgument]⟩
  | integer =>
      have extracted := cMatchPrimitive_extract fuel actual .integer cAssignments cNext
        (by simpa [cMatchType] using matched)
      have equal := extracted.1
      have decodedEqual := (cTypeEq_decode_agreement (fuel + 1) callerPointers).1
        actual .integer equal
      simp [decodeCType] at decodedEqual
      have actualEq : actualType = .integer := by simpa [actualDecoded] using decodedEqual
      have patternEq : patternType = .integer := by simpa [decodeCType] using patternDecoded.symm
      subst actualType patternType
      exact ⟨extracted.2, by simp [collectArgument]⟩
  | floating =>
      have extracted := cMatchPrimitive_extract fuel actual .floating cAssignments cNext
        (by simpa [cMatchType] using matched)
      have equal := extracted.1
      have decodedEqual := (cTypeEq_decode_agreement (fuel + 1) callerPointers).1
        actual .floating equal
      simp [decodeCType] at decodedEqual
      have actualEq : actualType = .float := by simpa [actualDecoded] using decodedEqual
      have patternEq : patternType = .float := by simpa [decodeCType] using patternDecoded.symm
      subst actualType patternType
      exact ⟨extracted.2, by simp [collectArgument]⟩
  | string =>
      have extracted := cMatchPrimitive_extract fuel actual .string cAssignments cNext
        (by simpa [cMatchType] using matched)
      have equal := extracted.1
      have decodedEqual := (cTypeEq_decode_agreement (fuel + 1) callerPointers).1
        actual .string equal
      simp [decodeCType] at decodedEqual
      have actualEq : actualType = .string := by simpa [actualDecoded] using decodedEqual
      have patternEq : patternType = .string := by simpa [decodeCType] using patternDecoded.symm
      subst actualType patternType
      exact ⟨extracted.2, by simp [collectArgument]⟩
  | character =>
      have extracted := cMatchPrimitive_extract fuel actual .character cAssignments cNext
        (by simpa [cMatchType] using matched)
      have equal := extracted.1
      have decodedEqual := (cTypeEq_decode_agreement (fuel + 1) callerPointers).1
        actual .character equal
      simp [decodeCType] at decodedEqual
      have actualEq : actualType = .character := by simpa [actualDecoded] using decodedEqual
      have patternEq : patternType = .character := by simpa [decodeCType] using patternDecoded.symm
      subst actualType patternType
      exact ⟨extracted.2, by simp [collectArgument]⟩
  | unit =>
      have extracted := cMatchPrimitive_extract fuel actual .unit cAssignments cNext
        (by simpa [cMatchType] using matched)
      have equal := extracted.1
      have decodedEqual := (cTypeEq_decode_agreement (fuel + 1) callerPointers).1
        actual .unit equal
      simp [decodeCType] at decodedEqual
      have actualEq : actualType = .unit := by simpa [actualDecoded] using decodedEqual
      have patternEq : patternType = .unit := by simpa [decodeCType] using patternDecoded.symm
      subst actualType patternType
      exact ⟨extracted.2, by simp [collectArgument]⟩

/-- The first flexible-variable constraint takes the same slot-update step in
the C-pointer model and the Lean collector, once the C actual has been decoded
to its corresponding Lean type. -/
theorem cMatchType_matches_Lean_variable_capture (fuel : Nat)
    (schemePointers : List Nat) (identity index : Nat) (actual : CTypeNode)
    (callerPointers : List Nat)
    (actualType : Ty) (cAssignments : List (Option CTypeNode))
    (leanAssignments : List (Option Ty))
    (monotype : cMonotype actual = true)
    (pointerSlot : cPointerIndex identity schemePointers = some index)
    (cEmpty : cAssignments[index]? = some none)
    (leanEmpty : leanAssignments[index]? = some none)
    (actualDecodes : decodeCType callerPointers actual = some actualType) :
    cMatchType (fuel + 1) schemePointers (.variable identity) actual cAssignments =
        some (cAssignments.set index (some actual)) ∧
      collectArgument (fuel + 1) (.var index) actualType leanAssignments =
        some (leanAssignments.set index (some actualType)) ∧
      actualType.wellFormed callerPointers.length := by
  refine ⟨?_, ?_, ?_⟩
  · simp [cMatchType, monotype, pointerSlot, cEmpty]
  · exact collectArgument_first_variable_capture fuel index actualType leanAssignments leanEmpty
  · exact decodeCType_wellFormed callerPointers actual actualType actualDecodes

/-- First capture under an already related partial substitution state updates
the same quantified slot on both sides and preserves pointwise agreement for
all other quantified variables. -/
theorem cMatchType_variable_capture_preserves_substitution_state (fuel : Nat)
    (schemePointers callerPointers : List Nat) (identity index : Nat)
    (actual : CTypeNode) (actualType : Ty)
    (cAssignments : List (Option CTypeNode)) (leanAssignments : List (Option Ty))
    (stateAgree : CSubstitutionStateAgree callerPointers schemePointers
      cAssignments leanAssignments)
    (monotype : cMonotype actual = true)
    (pointerSlot : cPointerIndex identity schemePointers = some index)
    (cEmpty : cAssignments[index]? = some none)
    (leanEmpty : leanAssignments[index]? = some none)
    (actualDecoded : decodeCType callerPointers actual = some actualType) :
    cMatchType (fuel + 1) schemePointers (.variable identity) actual cAssignments =
        some (cAssignments.set index (some actual)) ∧
      collectArgument (fuel + 1) (.var index) actualType leanAssignments =
        some (leanAssignments.set index (some actualType)) ∧
      CSubstitutionStateAgree callerPointers schemePointers
        (cAssignments.set index (some actual))
        (leanAssignments.set index (some actualType)) := by
  have capture := cMatchType_matches_Lean_variable_capture fuel schemePointers identity index
    actual callerPointers actualType cAssignments leanAssignments monotype pointerSlot cEmpty
    leanEmpty actualDecoded
  have preserved := cSubstitutionStateAgree_first_capture callerPointers schemePointers
    cAssignments leanAssignments index actual actualType stateAgree
    (cPointerIndex_result_lt_length identity schemePointers index pointerSlot)
    cEmpty leanEmpty actualDecoded
  exact ⟨capture.1, capture.2.1, preserved⟩

/-- When C's actual argument is a caller-side type variable, resolving its
pointer identity through the caller's ordered pointer array gives the same
rigid Lean variable that the first quantified constraint stores. This joins
the C pointer lookup and assignment update to Lean's indexed caller scope. -/
theorem cMatchType_captures_rigid_caller_variable (fuel : Nat)
    (schemePointers callerPointers : List Nat)
    (quantifiedIdentity quantifiedIndex callerIdentity callerIndex : Nat)
    (cAssignments : List (Option CTypeNode))
    (leanAssignments : List (Option Ty))
    (schemeDistinct : CNoDuplicatePointers schemePointers)
    (callerDistinct : CNoDuplicatePointers callerPointers)
    (quantifiedFound : schemePointers[quantifiedIndex]? = some quantifiedIdentity)
    (callerFound : callerPointers[callerIndex]? = some callerIdentity)
    (cEmpty : cAssignments[quantifiedIndex]? = some none)
    (leanEmpty : leanAssignments[quantifiedIndex]? = some none) :
    cMatchType (fuel + 1) schemePointers (.variable quantifiedIdentity)
        (.variable callerIdentity) cAssignments =
      some (cAssignments.set quantifiedIndex (some (.variable callerIdentity))) ∧
    collectArgument (fuel + 1) (.var quantifiedIndex) (.var callerIndex)
        leanAssignments =
      some (leanAssignments.set quantifiedIndex (some (.var callerIndex))) ∧
    (Ty.var callerIndex).wellFormed callerPointers.length := by
  have quantifiedSlot :
      cPointerIndex quantifiedIdentity schemePointers = some quantifiedIndex :=
    cPointerIndex_matches_unique_slot schemePointers quantifiedIdentity quantifiedIndex
      schemeDistinct quantifiedFound
  have actualDecodes :
      decodeCType callerPointers (.variable callerIdentity) = some (.var callerIndex) :=
    decodeCType_variable_at_unique_pointer callerPointers callerIdentity callerIndex
      callerDistinct callerFound
  obtain ⟨cResult, leanResult, callerWellFormed⟩ :=
    cMatchType_matches_Lean_variable_capture fuel schemePointers quantifiedIdentity
      quantifiedIndex (.variable callerIdentity) callerPointers (.var callerIndex)
      cAssignments leanAssignments (by simp [cMonotype]) quantifiedSlot cEmpty leanEmpty
      actualDecodes
  exact ⟨cResult, leanResult, callerWellFormed⟩

/-- Rigid caller-variable capture also preserves the whole partial
substitution relation, not only the newly written slot. This joins the
identity-to-index lookups to the generic first-capture state invariant. -/
theorem cMatchType_captures_rigid_caller_variable_preserves_state (fuel : Nat)
    (schemePointers callerPointers : List Nat)
    (quantifiedIdentity quantifiedIndex callerIdentity callerIndex : Nat)
    (cAssignments : List (Option CTypeNode)) (leanAssignments : List (Option Ty))
    (schemeDistinct : CNoDuplicatePointers schemePointers)
    (callerDistinct : CNoDuplicatePointers callerPointers)
    (quantifiedFound : schemePointers[quantifiedIndex]? = some quantifiedIdentity)
    (callerFound : callerPointers[callerIndex]? = some callerIdentity)
    (stateAgree : CSubstitutionStateAgree callerPointers schemePointers
      cAssignments leanAssignments)
    (cEmpty : cAssignments[quantifiedIndex]? = some none)
    (leanEmpty : leanAssignments[quantifiedIndex]? = some none) :
    cMatchType (fuel + 1) schemePointers (.variable quantifiedIdentity)
        (.variable callerIdentity) cAssignments =
      some (cAssignments.set quantifiedIndex (some (.variable callerIdentity))) ∧
    collectArgument (fuel + 1) (.var quantifiedIndex) (.var callerIndex) leanAssignments =
      some (leanAssignments.set quantifiedIndex (some (.var callerIndex))) ∧
    CSubstitutionStateAgree callerPointers schemePointers
      (cAssignments.set quantifiedIndex (some (.variable callerIdentity)))
      (leanAssignments.set quantifiedIndex (some (.var callerIndex))) := by
  have quantifiedSlot := cPointerIndex_matches_unique_slot schemePointers quantifiedIdentity
    quantifiedIndex schemeDistinct quantifiedFound
  have actualDecoded := decodeCType_variable_at_unique_pointer callerPointers callerIdentity
    callerIndex callerDistinct callerFound
  exact cMatchType_variable_capture_preserves_substitution_state fuel schemePointers
    callerPointers quantifiedIdentity quantifiedIndex (.variable callerIdentity)
    (.var callerIndex) cAssignments leanAssignments stateAgree (by simp [cMonotype])
    quantifiedSlot cEmpty leanEmpty actualDecoded

/-- The C and Lean collectors make the same one-step structural descent for a
List constraint. After decoding the child nodes, both recurse at one less
fuel with their respective assignment states unchanged. This is the List case
needed to lift the variable-slot correspondence through nested types. -/
theorem cMatchType_list_constraint_step (fuel : Nat)
    (schemePointers callerPointers : List Nat)
    (pattern actual : CTypeNode) (patternType actualType : Ty)
    (cAssignments : List (Option CTypeNode)) (leanAssignments : List (Option Ty))
    (actualMonotype : cMonotype actual = true)
    (patternDecoded : decodeCType schemePointers pattern = some patternType)
    (actualDecoded : decodeCType callerPointers actual = some actualType) :
    cMatchType (fuel + 1) schemePointers (.list pattern) (.list actual) cAssignments =
      cMatchType fuel schemePointers pattern actual cAssignments ∧
    collectArgument (fuel + 1) (.list patternType) (.list actualType) leanAssignments =
      collectArgument fuel patternType actualType leanAssignments ∧
    decodeCType schemePointers (.list pattern) = some (.list patternType) ∧
    decodeCType callerPointers (.list actual) = some (.list actualType) := by
  constructor
  · simp [cMatchType, cMonotype, actualMonotype, patternDecoded, actualDecoded]
  constructor
  · simp [collectArgument]
  constructor
  · simp [decodeCType, patternDecoded]
  · simp [decodeCType, actualDecoded]

/-- Option constraints follow the same one-step descent as List constraints:
after successful child decoding, C's matcher and Lean's collector recurse on
the element type at the decremented fuel. -/
theorem cMatchType_option_constraint_step (fuel : Nat)
    (schemePointers callerPointers : List Nat)
    (pattern actual : CTypeNode) (patternType actualType : Ty)
    (cAssignments : List (Option CTypeNode)) (leanAssignments : List (Option Ty))
    (actualMonotype : cMonotype actual = true)
    (patternDecoded : decodeCType schemePointers pattern = some patternType)
    (actualDecoded : decodeCType callerPointers actual = some actualType) :
    cMatchType (fuel + 1) schemePointers (.option pattern) (.option actual) cAssignments =
      cMatchType fuel schemePointers pattern actual cAssignments ∧
    collectArgument (fuel + 1) (.option patternType) (.option actualType) leanAssignments =
      collectArgument fuel patternType actualType leanAssignments ∧
    decodeCType schemePointers (.option pattern) = some (.option patternType) ∧
    decodeCType callerPointers (.option actual) = some (.option actualType) := by
  constructor
  · simp [cMatchType, cMonotype, actualMonotype, patternDecoded, actualDecoded]
  constructor
  · simp [collectArgument]
  constructor
  · simp [decodeCType, patternDecoded]
  · simp [decodeCType, actualDecoded]

/-- For a Function constraint, both implementations first traverse parameter
types left to right and then constrain the result type. The C branch checks
arity before entering that traversal; the Lean branch has the same list shape
in its recursive collector. -/
theorem cMatchType_function_constraint_step (fuel : Nat)
    (schemePointers callerPointers : List Nat)
    (patternParameters actualParameters : List CTypeNode)
    (patternResult actualResult : CTypeNode)
    (patternParameterTypes actualParameterTypes : List Ty)
    (patternResultType actualResultType : Ty)
    (cAssignments : List (Option CTypeNode)) (leanAssignments : List (Option Ty))
    (actualParametersMonotype : cMonotypes actualParameters = true)
    (actualResultMonotype : cMonotype actualResult = true)
    (arity : patternParameters.length = actualParameters.length)
    (patternParametersDecoded : decodeCTypes schemePointers patternParameters =
      some patternParameterTypes)
    (actualParametersDecoded : decodeCTypes callerPointers actualParameters =
      some actualParameterTypes)
    (patternResultDecoded : decodeCType schemePointers patternResult =
      some patternResultType)
    (actualResultDecoded : decodeCType callerPointers actualResult =
      some actualResultType) :
    cMatchType (fuel + 1) schemePointers
        (.function patternParameters patternResult)
        (.function actualParameters actualResult) cAssignments = (do
        let intermediate ← cMatchTypes fuel schemePointers patternParameters
          actualParameters cAssignments
        cMatchType fuel schemePointers patternResult actualResult intermediate) ∧
    collectArgument (fuel + 1)
        (.fn patternParameterTypes patternResultType)
        (.fn actualParameterTypes actualResultType) leanAssignments = (do
        let intermediate ← collectArguments fuel patternParameterTypes
          actualParameterTypes leanAssignments
        collectArgument fuel patternResultType actualResultType intermediate) ∧
    decodeCType schemePointers (.function patternParameters patternResult) =
      some (.fn patternParameterTypes patternResultType) ∧
    decodeCType callerPointers (.function actualParameters actualResult) =
      some (.fn actualParameterTypes actualResultType) := by
  constructor
  · simp [cMatchType, cMonotype, actualParametersMonotype,
      actualResultMonotype, arity]
  constructor
  · rfl
  constructor
  · simp [decodeCType, patternParametersDecoded, patternResultDecoded]
  · simp [decodeCType, actualParametersDecoded, actualResultDecoded]

/-- C's function-arity guard and Lean's synchronous argument collector reject
the same decoded function constraint when their parameter counts differ. The
successful decodes transfer the C array-length mismatch to Lean's type lists. -/
theorem cMatchType_rejects_function_arity_mismatch (fuel : Nat)
    (schemePointers callerPointers : List Nat)
    (patternParameters actualParameters : List CTypeNode)
    (patternResult actualResult : CTypeNode)
    (patternParameterTypes actualParameterTypes : List Ty)
    (patternResultType actualResultType : Ty)
    (cAssignments : List (Option CTypeNode)) (leanAssignments : List (Option Ty))
    (actualMonotype : cMonotype (.function actualParameters actualResult) = true)
    (differentArity : patternParameters.length ≠ actualParameters.length)
    (patternParametersDecoded : decodeCTypes schemePointers patternParameters =
      some patternParameterTypes)
    (actualParametersDecoded : decodeCTypes callerPointers actualParameters =
      some actualParameterTypes)
    (patternResultDecoded : decodeCType schemePointers patternResult =
      some patternResultType)
    (actualResultDecoded : decodeCType callerPointers actualResult =
      some actualResultType) :
    cMatchType (fuel + 1) schemePointers
        (.function patternParameters patternResult)
        (.function actualParameters actualResult) cAssignments = none ∧
      collectArgument (fuel + 1) (.fn patternParameterTypes patternResultType)
        (.fn actualParameterTypes actualResultType) leanAssignments = none ∧
      decodeCType schemePointers (.function patternParameters patternResult) =
        some (.fn patternParameterTypes patternResultType) ∧
      decodeCType callerPointers (.function actualParameters actualResult) =
        some (.fn actualParameterTypes actualResultType) := by
  have patternLength := decodeCTypes_length schemePointers patternParameters
    patternParameterTypes patternParametersDecoded
  have actualLength := decodeCTypes_length callerPointers actualParameters
    actualParameterTypes actualParametersDecoded
  have decodedArityMismatch : patternParameterTypes.length ≠ actualParameterTypes.length := by
    intro same
    apply differentArity
    omega
  exact ⟨by simp [cMatchType, actualMonotype, differentArity],
    collectArgument_function_arity_mismatch fuel patternParameterTypes actualParameterTypes
      patternResultType actualResultType leanAssignments decodedArityMismatch,
    by simp [decodeCType, patternParametersDecoded, patternResultDecoded],
    by simp [decodeCType, actualParametersDecoded, actualResultDecoded]⟩

/-- For a repeated quantified variable, when C's structural equality accepts
the saved and new C nodes and both decode to the same Lean type, both matchers
keep their assignment states unchanged. -/
theorem cMatchType_matches_Lean_variable_repeat (fuel : Nat)
    (schemePointers : List Nat) (identity index : Nat)
    (previous actual : CTypeNode) (callerPointers : List Nat)
    (previousType actualType : Ty) (cAssignments : List (Option CTypeNode))
    (leanAssignments : List (Option Ty))
    (monotype : cMonotype actual = true)
    (pointerSlot : cPointerIndex identity schemePointers = some index)
    (cAssigned : cAssignments[index]? = some (some previous))
    (leanAssigned : leanAssignments[index]? = some (some previousType))
    (cEqual : cTypeEq (fuel + 1) previous actual = true)
    (previousDecodes : decodeCType callerPointers previous = some previousType)
    (actualDecodes : decodeCType callerPointers actual = some actualType) :
    cMatchType (fuel + 1) schemePointers (.variable identity) actual cAssignments =
        some cAssignments ∧
      collectArgument (fuel + 1) (.var index) actualType leanAssignments =
        some leanAssignments ∧ previousType.wellFormed callerPointers.length ∧
      actualType.wellFormed callerPointers.length := by
  have decodedTypesEqual := (cTypeEq_decode_agreement (fuel + 1) callerPointers).1
    previous actual cEqual
  rw [previousDecodes, actualDecodes] at decodedTypesEqual
  have sameDecodedType : previousType = actualType := Option.some.inj decodedTypesEqual
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [cMatchType, monotype, pointerSlot, cAssigned, cEqual]
  · exact collectArgument_repeated_variable_same fuel index previousType actualType
      leanAssignments leanAssigned sameDecodedType
  · exact decodeCType_wellFormed callerPointers previous previousType previousDecodes
  · exact decodeCType_wellFormed callerPointers actual actualType actualDecodes

/-- A repeated quantified constraint preserves the complete partial C/Lean
substitution-state invariant, since both collectors return their input arrays. -/
theorem cMatchType_repeated_preserves_substitution_state
    (fuel : Nat) (schemePointers : List Nat) (identity index : Nat)
    (previous actual : CTypeNode) (callerPointers : List Nat)
    (previousType actualType : Ty) (cAssignments : List (Option CTypeNode))
    (leanAssignments : List (Option Ty))
    (stateAgree : CSubstitutionStateAgree callerPointers schemePointers
      cAssignments leanAssignments)
    (monotype : cMonotype actual = true)
    (pointerSlot : cPointerIndex identity schemePointers = some index)
    (cAssigned : cAssignments[index]? = some (some previous))
    (leanAssigned : leanAssignments[index]? = some (some previousType))
    (cEqual : cTypeEq (fuel + 1) previous actual = true)
    (previousDecodes : decodeCType callerPointers previous = some previousType)
    (actualDecodes : decodeCType callerPointers actual = some actualType) :
    cMatchType (fuel + 1) schemePointers (.variable identity) actual cAssignments =
        some cAssignments ∧
      collectArgument (fuel + 1) (.var index) actualType leanAssignments =
        some leanAssignments ∧
      CSubstitutionStateAgree callerPointers schemePointers
        cAssignments leanAssignments := by
  have matched := cMatchType_matches_Lean_variable_repeat fuel schemePointers identity index
    previous actual callerPointers previousType actualType cAssignments leanAssignments
    monotype pointerSlot cAssigned leanAssigned cEqual previousDecodes actualDecodes
  exact ⟨matched.1, matched.2.1, stateAgree⟩

/-- A decoded quantified-variable constraint simulates both first capture and
repeated capture under the full partial-state invariant. -/
theorem cMatchType_variable_state_simulation (fuel : Nat)
    (scheme callerPointers : List Nat) (identity : Nat) (actual : CTypeNode)
    (actualType patternType : Ty) (cAssignments : List (Option CTypeNode))
    (leanAssignments : List (Option Ty)) (cNext : List (Option CTypeNode))
    (stateAgree : CSubstitutionStateAgree callerPointers scheme cAssignments leanAssignments)
    (actualMonotype : cMonotype actual = true)
    (patternDecoded : decodeCType scheme (.variable identity) = some patternType)
    (actualDecoded : decodeCType callerPointers actual = some actualType)
    (matched : cMatchType (fuel + 1) scheme (.variable identity) actual cAssignments =
      some cNext) :
    ∃ leanNext, collectArgument (fuel + 1) patternType actualType leanAssignments =
        some leanNext ∧ CSubstitutionStateAgree callerPointers scheme cNext leanNext := by
  cases pointerSlot : cPointerIndex identity scheme with
  | none => simp [decodeCType, pointerSlot] at patternDecoded
  | some index =>
      have patternEq : patternType = .var index := by
        simpa [decodeCType, pointerSlot] using patternDecoded.symm
      subst patternType
      have indexBound := cPointerIndex_result_lt_length identity scheme index pointerSlot
      rcases stateAgree with ⟨cLength, leanLength, pointwise⟩
      cases cAt : cAssignments[index]? with
      | none => simp [cMatchType, actualMonotype, pointerSlot, cAt] at matched
      | some cEntry =>
          cases cEntry with
          | none =>
              have leanEmpty : leanAssignments[index]? = some none := by
                rcases pointwise index indexBound with empty | assigned
                · exact empty.2
                · obtain ⟨_, _, cFound, _, _⟩ := assigned
                  rw [cAt] at cFound
                  cases cFound
              have capture := cMatchType_variable_capture_preserves_substitution_state
                fuel scheme callerPointers identity index actual actualType cAssignments
                leanAssignments ⟨cLength, leanLength, pointwise⟩ actualMonotype pointerSlot
                cAt leanEmpty actualDecoded
              rw [capture.1] at matched
              cases Option.some.inj matched
              exact ⟨_, capture.2.1, capture.2.2⟩
          | some previous =>
              have cAssigned : cAssignments[index]? = some (some previous) := cAt
              rcases pointwise index indexBound with empty | assigned
              · rw [cAt] at empty
                cases empty.1
              · obtain ⟨cPrevious, previousType, cFound, leanAssigned, previousDecoded⟩ := assigned
                have same : cPrevious = previous := by
                  have both := cFound.symm.trans cAt
                  exact Option.some.inj (Option.some.inj both)
                subst cPrevious
                have cEqual : cTypeEq (fuel + 1) previous actual = true := by
                  simp [cMatchType, actualMonotype, pointerSlot, cAt] at matched
                  exact matched.1
                have repeated := cMatchType_repeated_preserves_substitution_state fuel
                  scheme identity index previous actual callerPointers previousType actualType
                  cAssignments leanAssignments ⟨cLength, leanLength, pointwise⟩ actualMonotype
                  pointerSlot cAssigned leanAssigned cEqual previousDecoded actualDecoded
                rw [repeated.1] at matched
                cases Option.some.inj matched
                exact ⟨leanAssignments, repeated.2.1, repeated.2.2⟩

/-- Reverse the quantified-variable case of the C/Lean constraint-step
simulation. A successful Lean capture either performs the same first update
on both assignment arrays or proves the saved and current decoded C nodes
equal, which makes C's repeated-variable comparison succeed. -/
theorem cMatchType_variable_state_simulation_reverse (fuel : Nat)
    (scheme callerPointers : List Nat) (identity : Nat) (actual : CTypeNode)
    (actualType patternType : Ty) (cAssignments : List (Option CTypeNode))
    (leanAssignments leanNext : List (Option Ty))
    (stateAgree : CSubstitutionStateAgree callerPointers scheme cAssignments leanAssignments)
    (actualMonotype : cMonotype actual = true)
    (patternDecoded : decodeCType scheme (.variable identity) = some patternType)
    (actualDecoded : decodeCType callerPointers actual = some actualType)
    (comparisonComplete : ∀ (index : Nat) (previous : CTypeNode) (previousType : Ty),
      cAssignments[index]? = some (some previous) →
      decodeCType callerPointers previous = some previousType →
      previousType = actualType →
      cTypeEq (fuel + 1) previous actual = true)
    (collected : collectArgument (fuel + 1) patternType actualType leanAssignments =
      some leanNext) :
    ∃ cNext, cMatchType (fuel + 1) scheme (.variable identity) actual cAssignments =
      some cNext ∧ CSubstitutionStateAgree callerPointers scheme cNext leanNext := by
  cases pointerSlot : cPointerIndex identity scheme with
  | none => simp [decodeCType, pointerSlot] at patternDecoded
  | some index =>
      have patternEq : patternType = .var index := by
        simpa [decodeCType, pointerSlot] using patternDecoded.symm
      subst patternType
      have indexBound := cPointerIndex_result_lt_length identity scheme index pointerSlot
      rcases stateAgree with ⟨cLength, leanLength, pointwise⟩
      have stateAgree : CSubstitutionStateAgree callerPointers scheme
          cAssignments leanAssignments := ⟨cLength, leanLength, pointwise⟩
      cases cAt : cAssignments[index]? with
      | none =>
          rcases pointwise index indexBound with empty | assigned
          · rw [cAt] at empty
            simp at empty
          · obtain ⟨_, _, cFound, _, _⟩ := assigned
            rw [cAt] at cFound
            simp at cFound
      | some entry =>
          cases entry with
          | none =>
              have leanEmpty : leanAssignments[index]? = some none := by
                rcases pointwise index indexBound with empty | assigned
                · exact empty.2
                · obtain ⟨_, _, cFound, _, _⟩ := assigned
                  rw [cAt] at cFound
                  cases cFound
              have capture := cMatchType_variable_capture_preserves_substitution_state
                fuel scheme callerPointers identity index actual actualType cAssignments
                leanAssignments stateAgree actualMonotype pointerSlot cAt leanEmpty actualDecoded
              rw [capture.2.1] at collected
              have nextEq : leanNext = leanAssignments.set index (some actualType) :=
                Option.some.inj collected.symm
              subst leanNext
              exact ⟨cAssignments.set index (some actual), capture.1, capture.2.2⟩
          | some previous =>
              rcases pointwise index indexBound with empty | assigned
              · rw [cAt] at empty
                cases empty.1
              · obtain ⟨previousNode, previousType, cFound, leanFound, previousDecoded⟩ := assigned
                have previousNodeEq : previousNode = previous := by
                  have both := cFound.symm.trans cAt
                  exact Option.some.inj (Option.some.inj both)
                subst previousNode
                have collectedEq :
                    (if previousType = actualType then some leanAssignments else none) =
                      some leanNext := by
                  simpa [collectArgument, leanFound] using collected
                have sameType : previousType = actualType := by
                  by_cases same : previousType = actualType
                  · exact same
                  · simp [same] at collectedEq
                have nextEq : leanNext = leanAssignments := by
                  simp [sameType] at collectedEq
                  exact collectedEq.symm
                subst leanNext
                have cEqual := comparisonComplete index previous previousType cAt
                  previousDecoded sameType
                refine ⟨cAssignments, ?_, stateAgree⟩
                simp [cMatchType, actualMonotype, pointerSlot, cAt, cEqual]

inductive CAtomicConstraintPattern : CTypeNode → Prop where
  | primitive {pattern} : CPrimitiveType pattern → CAtomicConstraintPattern pattern
  | quantified (identity : Nat) : CAtomicConstraintPattern (.variable identity)

/-- One List wrapper around a primitive or quantified-variable constraint
preserves the C/Lean state simulation, consuming the same matcher fuel. -/
theorem cMatchType_list_atomic_state_simulation (fuel : Nat)
    (scheme callerPointers : List Nat) (pattern actual : CTypeNode)
    (patternType actualType : Ty) (cAssignments : List (Option CTypeNode))
    (leanAssignments : List (Option Ty)) (cNext : List (Option CTypeNode))
    (atomic : CAtomicConstraintPattern pattern)
    (actualMonotype : cMonotype actual = true)
    (patternDecoded : decodeCType scheme pattern = some patternType)
    (actualDecoded : decodeCType callerPointers actual = some actualType)
    (matched : cMatchType (fuel + 2) scheme (.list pattern) (.list actual) cAssignments =
      some cNext)
    (stateAgree : CSubstitutionStateAgree callerPointers scheme cAssignments leanAssignments) :
    ∃ leanNext, collectArgument (fuel + 2) (.list patternType) (.list actualType)
        leanAssignments = some leanNext ∧
      CSubstitutionStateAgree callerPointers scheme cNext leanNext := by
  have childMatched : cMatchType (fuel + 1) scheme pattern actual cAssignments = some cNext := by
    simpa [cMatchType, cMonotype, actualMonotype] using matched
  have childSimulation :
      ∃ leanNext, collectArgument (fuel + 1) patternType actualType leanAssignments =
        some leanNext ∧ CSubstitutionStateAgree callerPointers scheme cNext leanNext := by
    cases atomic with
    | primitive primitive =>
        have sim := cMatchType_primitive_simulation fuel scheme callerPointers
          pattern actual patternType actualType cAssignments leanAssignments cNext
          primitive patternDecoded actualDecoded childMatched
        exact ⟨leanAssignments, sim.2, by simpa [sim.1] using stateAgree⟩
    | quantified identity =>
        exact cMatchType_variable_state_simulation fuel scheme callerPointers identity
          actual actualType patternType cAssignments leanAssignments cNext stateAgree
          actualMonotype patternDecoded actualDecoded childMatched
  obtain ⟨leanNext, collected, finalState⟩ := childSimulation
  refine ⟨leanNext, ?_, finalState⟩
  simpa [collectArgument] using collected

/-- The corresponding one-level Option wrapper also preserves assignment
state and maps to Lean's option constraint descent. -/
theorem cMatchType_option_atomic_state_simulation (fuel : Nat)
    (scheme callerPointers : List Nat) (pattern actual : CTypeNode)
    (patternType actualType : Ty) (cAssignments : List (Option CTypeNode))
    (leanAssignments : List (Option Ty)) (cNext : List (Option CTypeNode))
    (atomic : CAtomicConstraintPattern pattern)
    (actualMonotype : cMonotype actual = true)
    (patternDecoded : decodeCType scheme pattern = some patternType)
    (actualDecoded : decodeCType callerPointers actual = some actualType)
    (matched : cMatchType (fuel + 2) scheme (.option pattern) (.option actual) cAssignments =
      some cNext)
    (stateAgree : CSubstitutionStateAgree callerPointers scheme cAssignments leanAssignments) :
    ∃ leanNext, collectArgument (fuel + 2) (.option patternType) (.option actualType)
        leanAssignments = some leanNext ∧
      CSubstitutionStateAgree callerPointers scheme cNext leanNext := by
  have childMatched : cMatchType (fuel + 1) scheme pattern actual cAssignments = some cNext := by
    simpa [cMatchType, cMonotype, actualMonotype] using matched
  have childSimulation :
      ∃ leanNext, collectArgument (fuel + 1) patternType actualType leanAssignments =
        some leanNext ∧ CSubstitutionStateAgree callerPointers scheme cNext leanNext := by
    cases atomic with
    | primitive primitive =>
        have sim := cMatchType_primitive_simulation fuel scheme callerPointers
          pattern actual patternType actualType cAssignments leanAssignments cNext
          primitive patternDecoded actualDecoded childMatched
        exact ⟨leanAssignments, sim.2, by simpa [sim.1] using stateAgree⟩
    | quantified identity =>
        exact cMatchType_variable_state_simulation fuel scheme callerPointers identity
          actual actualType patternType cAssignments leanAssignments cNext stateAgree
          actualMonotype patternDecoded actualDecoded childMatched
  obtain ⟨leanNext, collected, finalState⟩ := childSimulation
  refine ⟨leanNext, ?_, finalState⟩
  simpa [collectArgument] using collected

/-- Mutual fuel induction for C's single-type and type-list constraint
walkers. This composes nested List/Option/Function constraints while carrying
the partial substitution-state correspondence throughout. -/
theorem cMatchType_and_types_state_simulation :
    ∀ fuel,
      (∀ (scheme callerPointers : List Nat) (pattern actual : CTypeNode)
        (patternType actualType : Ty) (cAssignments : List (Option CTypeNode))
        (leanAssignments : List (Option Ty)) (cNext : List (Option CTypeNode)),
        cMonotype actual = true →
        decodeCType scheme pattern = some patternType →
        decodeCType callerPointers actual = some actualType →
        CSubstitutionStateAgree callerPointers scheme cAssignments leanAssignments →
        cMatchType fuel scheme pattern actual cAssignments = some cNext →
        ∃ leanNext, collectArgument fuel patternType actualType leanAssignments =
          some leanNext ∧ CSubstitutionStateAgree callerPointers scheme cNext leanNext) ∧
      (∀ (scheme callerPointers : List Nat) (patterns actuals : List CTypeNode)
        (patternTypes actualTypes : List Ty) (cAssignments : List (Option CTypeNode))
        (leanAssignments : List (Option Ty)) (cNext : List (Option CTypeNode)),
        cMonotypes actuals = true →
        decodeCTypes scheme patterns = some patternTypes →
        decodeCTypes callerPointers actuals = some actualTypes →
        CSubstitutionStateAgree callerPointers scheme cAssignments leanAssignments →
        cMatchTypes fuel scheme patterns actuals cAssignments = some cNext →
        ∃ leanNext, collectArguments fuel patternTypes actualTypes leanAssignments =
          some leanNext ∧ CSubstitutionStateAgree callerPointers scheme cNext leanNext) := by
  intro fuel
  induction fuel with
  | zero =>
      constructor
      · intro scheme caller pattern actual patternType actualType cAssignments leanAssignments
          cNext _ _ _ _ matched
        simp [cMatchType] at matched
      · intro scheme caller patterns actuals patternTypes actualTypes cAssignments
          leanAssignments cNext _ _ _ _ matched
        simp [cMatchTypes] at matched
  | succ fuel ih =>
      constructor
      · intro scheme caller pattern actual patternType actualType cAssignments leanAssignments
          cNext actualMono patternDecoded actualDecoded stateAgree matched
        cases pattern with
        | boolean =>
            have sim := cMatchType_primitive_simulation fuel scheme caller .boolean actual
              patternType actualType cAssignments leanAssignments cNext .boolean
              patternDecoded actualDecoded matched
            exact ⟨leanAssignments, sim.2, by simpa [sim.1] using stateAgree⟩
        | integer =>
            have sim := cMatchType_primitive_simulation fuel scheme caller .integer actual
              patternType actualType cAssignments leanAssignments cNext .integer
              patternDecoded actualDecoded matched
            exact ⟨leanAssignments, sim.2, by simpa [sim.1] using stateAgree⟩
        | floating =>
            have sim := cMatchType_primitive_simulation fuel scheme caller .floating actual
              patternType actualType cAssignments leanAssignments cNext .floating
              patternDecoded actualDecoded matched
            exact ⟨leanAssignments, sim.2, by simpa [sim.1] using stateAgree⟩
        | string =>
            have sim := cMatchType_primitive_simulation fuel scheme caller .string actual
              patternType actualType cAssignments leanAssignments cNext .string
              patternDecoded actualDecoded matched
            exact ⟨leanAssignments, sim.2, by simpa [sim.1] using stateAgree⟩
        | character =>
            have sim := cMatchType_primitive_simulation fuel scheme caller .character actual
              patternType actualType cAssignments leanAssignments cNext .character
              patternDecoded actualDecoded matched
            exact ⟨leanAssignments, sim.2, by simpa [sim.1] using stateAgree⟩
        | unit =>
            have sim := cMatchType_primitive_simulation fuel scheme caller .unit actual
              patternType actualType cAssignments leanAssignments cNext .unit
              patternDecoded actualDecoded matched
            exact ⟨leanAssignments, sim.2, by simpa [sim.1] using stateAgree⟩
        | «variable» identity =>
            exact cMatchType_variable_state_simulation fuel scheme caller identity actual
              actualType patternType cAssignments leanAssignments cNext stateAgree actualMono
              patternDecoded actualDecoded matched
        | list element =>
            cases actual with
            | list input =>
                cases elementDecoded : decodeCType scheme element with
                | none => simp [decodeCType, elementDecoded] at patternDecoded
                | some elementType =>
                  cases inputDecoded : decodeCType caller input with
                  | none => simp [decodeCType, inputDecoded] at actualDecoded
                  | some inputType =>
                    have pEq : patternType = .list elementType := by
                      simpa [decodeCType, elementDecoded] using patternDecoded.symm
                    have aEq : actualType = .list inputType := by
                      simpa [decodeCType, inputDecoded] using actualDecoded.symm
                    have elementMono : cMonotype input = true := by
                      simpa [cMonotype] using actualMono
                    have childMatch : cMatchType fuel scheme element input cAssignments =
                        some cNext := by
                      simpa [cMatchType, cMonotype, elementMono] using matched
                    obtain ⟨leanNext, collected, finalState⟩ := ih.1 scheme caller element input
                      elementType inputType cAssignments leanAssignments cNext elementMono
                      elementDecoded inputDecoded stateAgree childMatch
                    subst patternType actualType
                    exact ⟨leanNext, by simpa [collectArgument] using collected, finalState⟩
            | _ => simp [cMatchType] at matched
        | option element =>
            cases actual with
            | option input =>
                cases elementDecoded : decodeCType scheme element with
                | none => simp [decodeCType, elementDecoded] at patternDecoded
                | some elementType =>
                  cases inputDecoded : decodeCType caller input with
                  | none => simp [decodeCType, inputDecoded] at actualDecoded
                  | some inputType =>
                    have pEq : patternType = .option elementType := by
                      simpa [decodeCType, elementDecoded] using patternDecoded.symm
                    have aEq : actualType = .option inputType := by
                      simpa [decodeCType, inputDecoded] using actualDecoded.symm
                    have elementMono : cMonotype input = true := by
                      simpa [cMonotype] using actualMono
                    have childMatch : cMatchType fuel scheme element input cAssignments =
                        some cNext := by
                      simpa [cMatchType, cMonotype, elementMono] using matched
                    obtain ⟨leanNext, collected, finalState⟩ := ih.1 scheme caller element input
                      elementType inputType cAssignments leanAssignments cNext elementMono
                      elementDecoded inputDecoded stateAgree childMatch
                    subst patternType actualType
                    exact ⟨leanNext, by simpa [collectArgument] using collected, finalState⟩
            | _ => simp [cMatchType] at matched
        | function parameters result =>
            cases actual with
            | function inputs output =>
                cases patternParametersDecoded : decodeCTypes scheme parameters with
                | none => simp [decodeCType, patternParametersDecoded] at patternDecoded
                | some parameterTypes =>
                  cases patternResultDecoded : decodeCType scheme result with
                  | none => simp [decodeCType, patternParametersDecoded, patternResultDecoded]
                      at patternDecoded
                  | some resultType =>
                    cases actualParametersDecoded : decodeCTypes caller inputs with
                    | none => simp [decodeCType, actualParametersDecoded] at actualDecoded
                    | some inputTypes =>
                      cases actualResultDecoded : decodeCType caller output with
                      | none => simp [decodeCType, actualParametersDecoded, actualResultDecoded]
                          at actualDecoded
                      | some outputType =>
                        have pEq : patternType = .fn parameterTypes resultType := by
                          simpa [decodeCType, patternParametersDecoded, patternResultDecoded]
                            using patternDecoded.symm
                        have aEq : actualType = .fn inputTypes outputType := by
                          simpa [decodeCType, actualParametersDecoded, actualResultDecoded]
                            using actualDecoded.symm
                        have monoParts : cMonotypes inputs = true ∧ cMonotype output = true := by
                          simpa [cMonotype, Bool.and_eq_true] using actualMono
                        by_cases arity : parameters.length = inputs.length
                        · have componentsMatch : (do
                              let intermediate ← cMatchTypes fuel scheme parameters inputs cAssignments
                              cMatchType fuel scheme result output intermediate) = some cNext := by
                            simpa [cMatchType, cMonotype, monoParts.1, monoParts.2, arity]
                              using matched
                          obtain ⟨intermediate, paramsMatched, resultMatched⟩ :=
                            Option.bind_eq_some.mp componentsMatch
                          obtain ⟨leanIntermediate, paramsCollected, paramsState⟩ := ih.2
                            scheme caller parameters inputs parameterTypes inputTypes cAssignments
                            leanAssignments intermediate monoParts.1 patternParametersDecoded
                            actualParametersDecoded stateAgree paramsMatched
                          obtain ⟨leanNext, resultCollected, finalState⟩ := ih.1 scheme caller
                            result output resultType outputType intermediate leanIntermediate cNext
                            monoParts.2 patternResultDecoded actualResultDecoded paramsState
                            resultMatched
                          subst patternType actualType
                          refine ⟨leanNext, ?_, finalState⟩
                          simpa [collectArgument, paramsCollected] using resultCollected
                        · simp [cMatchType, cMonotype, monoParts.1, monoParts.2, arity] at matched
            | _ => simp [cMatchType] at matched
        | forallType variables body => simp [decodeCType] at patternDecoded
      · intro scheme caller patterns actuals patternTypes actualTypes cAssignments
          leanAssignments cNext actualsMono patternsDecoded actualsDecoded stateAgree matched
        cases fuel with
        | zero =>
            cases patterns with
            | nil => cases actuals with
              | nil =>
                  have pNil : patternTypes = [] := by
                    simpa [decodeCTypes] using patternsDecoded.symm
                  have aNil : actualTypes = [] := by
                    simpa [decodeCTypes] using actualsDecoded.symm
                  subst patternTypes actualTypes
                  simp [cMatchTypes] at matched
                  subst cNext
                  exact ⟨leanAssignments, by simp [collectArguments], stateAgree⟩
              | cons actual rest => simp [cMatchTypes] at matched
            | cons pattern rest => cases actuals <;> simp [cMatchTypes, cMatchType] at matched
        | succ fuel =>
            cases patterns with
            | nil =>
                cases actuals with
                | nil =>
                    have pNil : patternTypes = [] := by
                      simpa [decodeCTypes] using patternsDecoded.symm
                    have aNil : actualTypes = [] := by
                      simpa [decodeCTypes] using actualsDecoded.symm
                    subst patternTypes actualTypes
                    simp [cMatchTypes] at matched
                    subst cNext
                    exact ⟨leanAssignments, by simp [collectArguments], stateAgree⟩
                | cons actual rest => simp [cMatchTypes] at matched
            | cons pattern patternTail =>
                cases actuals with
                | nil => simp [cMatchTypes] at matched
                | cons actual actualTail =>
                    have monoParts : cMonotype actual = true ∧ cMonotypes actualTail = true := by
                      simpa [cMonotypes, Bool.and_eq_true] using actualsMono
                    cases patternHeadDecoded : decodeCType scheme pattern with
                    | none => simp [decodeCTypes, patternHeadDecoded] at patternsDecoded
                    | some patternType =>
                      cases patternTailDecoded : decodeCTypes scheme patternTail with
                      | none => simp [decodeCTypes, patternHeadDecoded, patternTailDecoded]
                          at patternsDecoded
                      | some patternTypesTail =>
                        cases actualHeadDecoded : decodeCType caller actual with
                        | none => simp [decodeCTypes, actualHeadDecoded] at actualsDecoded
                        | some actualType =>
                          cases actualTailDecoded : decodeCTypes caller actualTail with
                          | none => simp [decodeCTypes, actualHeadDecoded, actualTailDecoded]
                              at actualsDecoded
                          | some actualTypesTail =>
                            have pEq : patternTypes = patternType :: patternTypesTail := by
                              simpa [decodeCTypes, patternHeadDecoded, patternTailDecoded]
                                using patternsDecoded.symm
                            have aEq : actualTypes = actualType :: actualTypesTail := by
                              simpa [decodeCTypes, actualHeadDecoded, actualTailDecoded]
                                using actualsDecoded.symm
                            have componentsMatch : (do
                                let next ← cMatchType (fuel + 1) scheme pattern actual cAssignments
                                cMatchTypes (fuel + 1) scheme patternTail actualTail next) =
                                  some cNext := by
                              simpa [cMatchTypes] using matched
                            obtain ⟨intermediate, headMatched, tailMatched⟩ :=
                              Option.bind_eq_some.mp componentsMatch
                            obtain ⟨leanIntermediate, headCollected, headState⟩ := ih.1 scheme
                              caller pattern actual patternType actualType cAssignments
                              leanAssignments intermediate monoParts.1 patternHeadDecoded
                              actualHeadDecoded stateAgree headMatched
                            obtain ⟨leanNext, tailCollected, finalState⟩ := ih.2 scheme caller
                              patternTail actualTail patternTypesTail actualTypesTail intermediate
                              leanIntermediate cNext monoParts.2 patternTailDecoded actualTailDecoded
                              headState tailMatched
                            subst patternTypes actualTypes
                            refine ⟨leanNext, ?_, finalState⟩
                            simp [collectArguments, headCollected, tailCollected]

/-- C's left-to-right argument walk agrees with Lean's collector for any
parameter list whose constraints are primitive leaves or quantified
variables. Unlike the lower-level step theorem, this result constructs each
step from the concrete matcher and propagates the shared assignment invariant. -/
theorem cMatchTypes_atomic_state_simulation :
    ∀ (fuel : Nat) (callerPointers scheme : List Nat)
      (patterns actuals : List CTypeNode) (patternTypes actualTypes : List Ty)
      (cAssignments : List (Option CTypeNode)) (leanAssignments : List (Option Ty))
      (cFinal : List (Option CTypeNode)),
      cMonotypes actuals = true →
      decodeCTypes scheme patterns = some patternTypes →
      decodeCTypes callerPointers actuals = some actualTypes →
      (∀ pattern ∈ patterns, CAtomicConstraintPattern pattern) →
      CSubstitutionStateAgree callerPointers scheme cAssignments leanAssignments →
      cMatchTypes fuel scheme patterns actuals cAssignments = some cFinal →
      ∃ leanFinal, collectArguments fuel patternTypes actualTypes leanAssignments =
          some leanFinal ∧ CSubstitutionStateAgree callerPointers scheme cFinal leanFinal := by
  intro fuel
  induction fuel with
  | zero =>
      intro callerPointers scheme patterns actuals patternTypes actualTypes
        cAssignments leanAssignments cFinal _ _ _ _ _ matched
      simp [cMatchTypes] at matched
  | succ fuel ih =>
    cases fuel with
    | zero =>
      intro callerPointers scheme patterns actuals patternTypes actualTypes
        cAssignments leanAssignments cFinal actualsMono patternsDecoded actualsDecoded
        atomic stateAgree matched
      cases patterns with
      | nil => cases actuals with
        | nil =>
            have patternTypesNil : patternTypes = [] := by
              simpa [decodeCTypes] using patternsDecoded.symm
            have actualTypesNil : actualTypes = [] := by
              simpa [decodeCTypes] using actualsDecoded.symm
            subst patternTypes actualTypes
            simp [cMatchTypes] at matched
            subst cFinal
            exact ⟨leanAssignments, by simp [collectArguments], stateAgree⟩
        | cons actual rest => simp [cMatchTypes] at matched
      | cons pattern rest => cases actuals <;> simp [cMatchTypes, cMatchType] at matched
    | succ fuel =>
      intro callerPointers scheme patterns actuals patternTypes actualTypes
        cAssignments leanAssignments cFinal actualsMono patternsDecoded actualsDecoded
        atomic stateAgree matched
      cases patterns with
      | nil =>
          cases actuals with
          | nil =>
              simp [cMatchTypes] at matched
              subst cFinal
              have patternTypesNil : patternTypes = [] := by
                simpa [decodeCTypes] using patternsDecoded.symm
              have actualTypesNil : actualTypes = [] := by
                simpa [decodeCTypes] using actualsDecoded.symm
              subst patternTypes actualTypes
              exact ⟨leanAssignments, by simp [collectArguments], stateAgree⟩
          | cons actual rest => simp [cMatchTypes] at matched
      | cons pattern patternTail =>
          cases actuals with
          | nil => simp [cMatchTypes] at matched
          | cons actual actualTail =>
              have headMono : cMonotype actual = true := by
                have both : cMonotype actual = true ∧ cMonotypes actualTail = true := by
                  simpa [cMonotypes, Bool.and_eq_true] using actualsMono
                exact both.1
              cases headDecoded : decodeCType scheme pattern with
              | none => simp [decodeCTypes, headDecoded] at patternsDecoded
              | some patternType =>
                cases tailDecoded : decodeCTypes scheme patternTail with
                | none => simp [decodeCTypes, headDecoded, tailDecoded] at patternsDecoded
                | some patternTypeTail =>
                  have patternTypesEq : patternTypes = patternType :: patternTypeTail := by
                    simpa [decodeCTypes, headDecoded, tailDecoded] using patternsDecoded.symm
                  cases actualHeadDecoded : decodeCType callerPointers actual with
                  | none => simp [decodeCTypes, actualHeadDecoded] at actualsDecoded
                  | some actualType =>
                    cases actualTailDecoded : decodeCTypes callerPointers actualTail with
                    | none => simp [decodeCTypes, actualHeadDecoded, actualTailDecoded] at actualsDecoded
                    | some actualTypeTail =>
                      have actualTypesEq : actualTypes = actualType :: actualTypeTail := by
                        simpa [decodeCTypes, actualHeadDecoded, actualTailDecoded] using actualsDecoded.symm
                      have headAtomic : CAtomicConstraintPattern pattern := by
                        exact atomic pattern (by simp)
                      simp only [cMatchTypes] at matched
                      obtain ⟨cAfterHead, headMatched, tailMatched⟩ := Option.bind_eq_some.mp matched
                      have headSimulation :
                          ∃ leanAfterHead,
                            collectArgument (fuel + 1) patternType actualType leanAssignments =
                              some leanAfterHead ∧
                            CSubstitutionStateAgree callerPointers scheme cAfterHead leanAfterHead := by
                        cases headAtomic with
                        | primitive primitive =>
                            have sim := cMatchType_primitive_simulation fuel scheme callerPointers
                              pattern actual patternType actualType cAssignments leanAssignments
                              cAfterHead primitive headDecoded actualHeadDecoded headMatched
                            refine ⟨leanAssignments, sim.2, ?_⟩
                            simpa [sim.1] using stateAgree
                        | quantified identity =>
                            exact cMatchType_variable_state_simulation fuel scheme callerPointers
                              identity actual actualType patternType cAssignments leanAssignments
                              cAfterHead stateAgree headMono headDecoded actualHeadDecoded headMatched
                      obtain ⟨leanAfterHead, headCollected, stateAfterHead⟩ := headSimulation
                      have tailMono : cMonotypes actualTail = true := by
                        have both : cMonotype actual = true ∧ cMonotypes actualTail = true := by
                          simpa [cMonotypes, Bool.and_eq_true] using actualsMono
                        exact both.2
                      obtain ⟨leanFinal, tailCollected, finalState⟩ :=
                        ih callerPointers scheme patternTail actualTail patternTypeTail
                          actualTypeTail cAfterHead leanAfterHead cFinal tailMono tailDecoded
                          actualTailDecoded (by
                            intro item member
                            exact atomic item (by simp [member])) stateAfterHead tailMatched
                      rw [patternTypesEq, actualTypesEq]
                      refine ⟨leanFinal, ?_, finalState⟩
                      simp [collectArguments, headCollected, tailCollected]

/-- Repeated caller-side type-variable constraints need no extra C equality
assumption: if both pointer nodes decode to the same Lean slot, their C
identities coincide, so `match_type` accepts and the Lean collector preserves
the already captured rigid variable. -/
theorem cMatchType_matches_Lean_rigid_variable_repeat (fuel : Nat)
    (schemePointers callerPointers : List Nat)
    (quantifiedIdentity quantifiedIndex previousIdentity actualIdentity callerIndex : Nat)
    (cAssignments : List (Option CTypeNode)) (leanAssignments : List (Option Ty))
    (monotype : cMonotype (.variable actualIdentity) = true)
    (pointerSlot : cPointerIndex quantifiedIdentity schemePointers = some quantifiedIndex)
    (cAssigned : cAssignments[quantifiedIndex]? =
      some (some (.variable previousIdentity)))
    (leanAssigned : leanAssignments[quantifiedIndex]? = some (some (.var callerIndex)))
    (previousDecodes : decodeCType callerPointers (.variable previousIdentity) =
      some (.var callerIndex))
    (actualDecodes : decodeCType callerPointers (.variable actualIdentity) =
      some (.var callerIndex)) :
    cMatchType (fuel + 1) schemePointers (.variable quantifiedIdentity)
        (.variable actualIdentity) cAssignments = some cAssignments ∧
    collectArgument (fuel + 1) (.var quantifiedIndex) (.var callerIndex) leanAssignments =
      some leanAssignments ∧
    (Ty.var callerIndex).wellFormed callerPointers.length := by
  have sameIdentity := decodeCType_variable_injective callerPointers
    previousIdentity actualIdentity callerIndex previousDecodes actualDecodes
  have cEqual : cTypeEq (fuel + 1) (.variable previousIdentity)
      (.variable actualIdentity) = true := by
    simp [cTypeEq, sameIdentity]
  have repeated := cMatchType_matches_Lean_variable_repeat fuel schemePointers quantifiedIdentity
    quantifiedIndex (.variable previousIdentity) (.variable actualIdentity) callerPointers
    (.var callerIndex) (.var callerIndex) cAssignments leanAssignments monotype pointerSlot
    cAssigned leanAssigned cEqual previousDecodes actualDecodes
  exact ⟨repeated.1, repeated.2.1, repeated.2.2.1⟩

/-- A repeated rigid caller-variable constraint keeps an already related
partial substitution state unchanged on both implementations. -/
theorem cMatchType_rigid_repeat_preserves_substitution_state (fuel : Nat)
    (schemePointers callerPointers : List Nat)
    (quantifiedIdentity quantifiedIndex previousIdentity actualIdentity callerIndex : Nat)
    (cAssignments : List (Option CTypeNode)) (leanAssignments : List (Option Ty))
    (stateAgree : CSubstitutionStateAgree callerPointers schemePointers
      cAssignments leanAssignments)
    (monotype : cMonotype (.variable actualIdentity) = true)
    (pointerSlot : cPointerIndex quantifiedIdentity schemePointers = some quantifiedIndex)
    (cAssigned : cAssignments[quantifiedIndex]? =
      some (some (.variable previousIdentity)))
    (leanAssigned : leanAssignments[quantifiedIndex]? = some (some (.var callerIndex)))
    (previousDecodes : decodeCType callerPointers (.variable previousIdentity) =
      some (.var callerIndex))
    (actualDecodes : decodeCType callerPointers (.variable actualIdentity) =
      some (.var callerIndex)) :
    cMatchType (fuel + 1) schemePointers (.variable quantifiedIdentity)
        (.variable actualIdentity) cAssignments = some cAssignments ∧
      collectArgument (fuel + 1) (.var quantifiedIndex) (.var callerIndex) leanAssignments =
        some leanAssignments ∧
      CSubstitutionStateAgree callerPointers schemePointers cAssignments leanAssignments := by
  have repeated := cMatchType_matches_Lean_rigid_variable_repeat fuel schemePointers
    callerPointers quantifiedIdentity quantifiedIndex previousIdentity actualIdentity callerIndex
    cAssignments leanAssignments monotype pointerSlot cAssigned leanAssigned previousDecodes
    actualDecodes
  exact ⟨repeated.1, repeated.2.1, stateAgree⟩

/-- The corresponding conflict case: C equality rejects, and the decoded
Lean types differ, so both constraint collectors reject the repeated slot. -/
theorem cMatchType_rejects_Lean_variable_conflict (fuel : Nat)
    (schemePointers : List Nat) (identity index : Nat)
    (previous actual : CTypeNode) (callerPointers : List Nat)
    (previousType actualType : Ty) (cAssignments : List (Option CTypeNode))
    (leanAssignments : List (Option Ty))
    (monotype : cMonotype actual = true)
    (pointerSlot : cPointerIndex identity schemePointers = some index)
    (cAssigned : cAssignments[index]? = some (some previous))
    (leanAssigned : leanAssignments[index]? = some (some previousType))
    (cDifferent : cTypeEq (fuel + 1) previous actual = false)
    (previousDecodes : decodeCType callerPointers previous = some previousType)
    (actualDecodes : decodeCType callerPointers actual = some actualType)
    (differentDecodedTypes : previousType ≠ actualType) :
    cMatchType (fuel + 1) schemePointers (.variable identity) actual cAssignments = none ∧
      collectArgument (fuel + 1) (.var index) actualType leanAssignments = none ∧
      previousType.wellFormed callerPointers.length ∧
      actualType.wellFormed callerPointers.length := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [cMatchType, monotype, pointerSlot, cAssigned, cDifferent]
  · exact collectArgument_repeated_variable_conflict fuel index previousType actualType
      leanAssignments leanAssigned differentDecodedTypes
  · exact decodeCType_wellFormed callerPointers previous previousType previousDecodes
  · exact decodeCType_wellFormed callerPointers actual actualType actualDecodes

/-- Distinct successfully decoded types force C's repeated-variable structural
comparison to reject. This derives the C-side rejection from the existing
comparison soundness theorem, then transfers it to Lean's collector. -/
theorem cMatchType_rejects_decoded_variable_conflict (fuel : Nat)
    (schemePointers callerPointers : List Nat) (identity index : Nat)
    (previous actual : CTypeNode) (previousType actualType : Ty)
    (cAssignments : List (Option CTypeNode)) (leanAssignments : List (Option Ty))
    (monotype : cMonotype actual = true)
    (pointerSlot : cPointerIndex identity schemePointers = some index)
    (cAssigned : cAssignments[index]? = some (some previous))
    (leanAssigned : leanAssignments[index]? = some (some previousType))
    (previousDecodes : decodeCType callerPointers previous = some previousType)
    (actualDecodes : decodeCType callerPointers actual = some actualType)
    (different : previousType ≠ actualType) :
    cMatchType (fuel + 1) schemePointers (.variable identity) actual cAssignments = none ∧
    collectArgument (fuel + 1) (.var index) actualType leanAssignments = none ∧
    previousType.wellFormed callerPointers.length ∧
    actualType.wellFormed callerPointers.length := by
  have cDifferent : cTypeEq (fuel + 1) previous actual = false := by
    cases compared : cTypeEq (fuel + 1) previous actual with
    | false => rfl
    | true =>
        have decodedEqual := (cTypeEq_decode_agreement (fuel + 1) callerPointers).1
          previous actual compared
        rw [previousDecodes, actualDecodes] at decodedEqual
        have same : previousType = actualType := Option.some.inj decodedEqual
        exact (different same).elim
  exact cMatchType_rejects_Lean_variable_conflict fuel schemePointers identity index
    previous actual callerPointers previousType actualType cAssignments leanAssignments
    monotype pointerSlot cAssigned leanAssigned cDifferent previousDecodes actualDecodes different

theorem cMatchTypes_arity_mismatch (fuel : Nat) (scheme : List Nat)
    (patterns actuals : List CTypeNode) (assignments : List (Option CTypeNode))
    (different : patterns.length ≠ actuals.length) :
    cMatchTypes fuel scheme patterns actuals assignments = none := by
  induction patterns generalizing fuel actuals assignments with
  | nil =>
      cases actuals with
      | nil => simp at different
      | cons head tail => cases fuel <;> rfl
  | cons pattern tail ih =>
      cases actuals with
      | nil => cases fuel <;> rfl
      | cons actual actualTail =>
          cases fuel with
          | zero => rfl
          | succ fuel =>
              simp only [cMatchTypes]
              cases first : cMatchType fuel scheme pattern actual assignments with
              | none => rfl
              | some next =>
                  have tailDifferent : tail.length ≠ actualTail.length := by
                    intro same
                    apply different
                    simpa [same]
                  simpa using ih fuel actualTail next tailDifferent

/-- Compose one-constraint C/Lean simulations across the left-to-right
argument walk used by `check_call`. The step premise captures the structural
type comparison proof for a single parameter; this theorem propagates its
assignment-state invariant through every remaining argument. -/
theorem cMatchTypes_state_simulation_of_steps
    (callerPointers scheme : List Nat)
    (step : ∀ (fuel : Nat) (pattern actual : CTypeNode)
      (cAssignments cNext : List (Option CTypeNode))
      (leanAssignments : List (Option Ty)),
      CSubstitutionStateAgree callerPointers scheme cAssignments leanAssignments →
      cMatchType fuel scheme pattern actual cAssignments = some cNext →
      ∃ leanNext, collectArgument fuel (decodeCType scheme pattern |>.getD .unit)
        (decodeCType callerPointers actual |>.getD .unit) leanAssignments = some leanNext ∧
        CSubstitutionStateAgree callerPointers scheme cNext leanNext)
    (fuel : Nat) (patterns actuals : List CTypeNode)
    (cAssignments : List (Option CTypeNode)) (leanAssignments : List (Option Ty))
    (stateAgree : CSubstitutionStateAgree callerPointers scheme cAssignments leanAssignments)
    (matched : cMatchTypes fuel scheme patterns actuals cAssignments = some cFinal) :
    ∃ leanFinal, collectArguments fuel
        (patterns.map (fun pattern => (decodeCType scheme pattern).getD .unit))
        (actuals.map (fun actual => (decodeCType callerPointers actual).getD .unit))
        leanAssignments = some leanFinal ∧
      CSubstitutionStateAgree callerPointers scheme cFinal leanFinal := by
  induction fuel generalizing patterns actuals cAssignments leanAssignments cFinal with
  | zero => simp [cMatchTypes] at matched
  | succ fuel ih =>
      cases patterns with
      | nil =>
          cases actuals with
          | nil =>
              simp [cMatchTypes] at matched
              subst cFinal
              exact ⟨leanAssignments, by simp [collectArguments], stateAgree⟩
          | cons actual rest => simp [cMatchTypes] at matched
      | cons pattern patternTail =>
          cases actuals with
          | nil => simp [cMatchTypes] at matched
          | cons actual actualTail =>
              simp only [cMatchTypes] at matched
              obtain ⟨cNext, headMatched, tailMatched⟩ := Option.bind_eq_some.mp matched
              obtain ⟨leanNext, headSimulated, nextAgree⟩ :=
                step fuel pattern actual cAssignments cNext leanAssignments stateAgree headMatched
              obtain ⟨leanFinal, tailSimulated, finalAgree⟩ :=
                ih (patterns := patternTail) (actuals := actualTail)
                  (cAssignments := cNext) (leanAssignments := leanNext)
                  (cFinal := cFinal) nextAgree tailMatched
              refine ⟨leanFinal, ?_, finalAgree⟩
              simpa [collectArguments, headSimulated] using tailSimulated

/-- Decoder-backed form of the argument-list simulation. On successful C
parameter and argument array decoding, the collector runs over those exact
Lean type arrays; the fallback values in the underlying structural map are
therefore unreachable. -/
theorem cMatchTypes_state_simulation_of_steps_decoded
    (callerPointers scheme : List Nat)
    (step : ∀ (fuel : Nat) (pattern actual : CTypeNode)
      (cAssignments cNext : List (Option CTypeNode))
      (leanAssignments : List (Option Ty)),
      CSubstitutionStateAgree callerPointers scheme cAssignments leanAssignments →
      cMatchType fuel scheme pattern actual cAssignments = some cNext →
      ∃ leanNext, collectArgument fuel (decodeCType scheme pattern |>.getD .unit)
        (decodeCType callerPointers actual |>.getD .unit) leanAssignments = some leanNext ∧
        CSubstitutionStateAgree callerPointers scheme cNext leanNext)
    (fuel : Nat) (patterns actuals : List CTypeNode)
    (patternTypes actualTypes : List Ty)
    (patternsDecoded : decodeCTypes scheme patterns = some patternTypes)
    (actualsDecoded : decodeCTypes callerPointers actuals = some actualTypes)
    (cAssignments : List (Option CTypeNode)) (leanAssignments : List (Option Ty))
    (stateAgree : CSubstitutionStateAgree callerPointers scheme cAssignments leanAssignments)
    (matched : cMatchTypes fuel scheme patterns actuals cAssignments = some cFinal) :
    ∃ leanFinal, collectArguments fuel patternTypes actualTypes leanAssignments =
        some leanFinal ∧
      CSubstitutionStateAgree callerPointers scheme cFinal leanFinal := by
  obtain ⟨leanFinal, collected, finalAgree⟩ := cMatchTypes_state_simulation_of_steps
    callerPointers scheme step fuel patterns actuals cAssignments leanAssignments stateAgree matched
  rw [decodeCTypes_map_getD scheme patterns patternTypes patternsDecoded,
    decodeCTypes_map_getD callerPointers actuals actualTypes actualsDecoded] at collected
  exact ⟨leanFinal, collected, finalAgree⟩

/-- Decoder-backed C argument matching, followed by C's unassigned-slot
rejection and result substitution, agrees with Lean instantiation. The
single-type/type-list mutual simulation supplies every local constraint step;
the remaining hypotheses record C's `check_call` decode and completeness
conditions around its left-to-right loop. -/
theorem cMatchTypes_success_substitutes_result_like_Lean
    (callerPointers scheme : List Nat)
    (fuel : Nat) (patterns actuals : List CTypeNode)
    (patternTypes actualTypes : List Ty)
    (patternsDecoded : decodeCTypes scheme patterns = some patternTypes)
    (actualsDecoded : decodeCTypes callerPointers actuals = some actualTypes)
    (actualsMonotype : cMonotypes actuals = true)
    (cAssignments : List (Option CTypeNode)) (leanAssignments : List (Option Ty))
    (initialState : CSubstitutionStateAgree callerPointers scheme cAssignments leanAssignments)
    (matched : cMatchTypes fuel scheme patterns actuals cAssignments = some cFinal)
    (arguments : List Ty)
    (argumentsLength : arguments.length = scheme.length)
    (collectedState : cFinal.length = scheme.length ∧
      ∀ index, index < scheme.length →
        ∃ ctype type, cFinal[index]? = some (some ctype) ∧
          (arguments.map some)[index]? = some (some type) ∧
          decodeCType callerPointers ctype = some type)
    (result : CTypeNode) (resultType : Ty)
    (resultDecoded : decodeCType scheme result = some resultType) :
    ∃ output,
      cSubstituteType scheme (cFinal.map (Option.getD · .unit)) result = some output ∧
      decodeCType callerPointers output = some (resultType.instantiate arguments) := by
  obtain ⟨leanFinal, leanCollected, finalState⟩ :=
    (cMatchType_and_types_state_simulation fuel).2 scheme callerPointers patterns actuals
      patternTypes actualTypes cAssignments leanAssignments cFinal actualsMonotype
      patternsDecoded actualsDecoded initialState matched
  have finalMatchesArguments : leanFinal = arguments.map some := by
    apply List.ext_get (by
      rcases finalState with ⟨_, leanLength, _⟩
      exact leanLength.trans (by simp [argumentsLength]))
    intro index leftBound rightBound
    have bound : index < scheme.length := by
      rcases finalState with ⟨_, leanLength, _⟩
      omega
    have pointwiseEq : leanFinal[index]? = (arguments.map some)[index]? := by
      rcases finalState with ⟨_, _, relation⟩
      rcases relation index bound with empty | assigned
      · obtain ⟨ctype, type, cAssigned, argumentAssigned, decoded⟩ :=
          collectedState.2 index bound
        have contradiction : (some none : Option (Option CTypeNode)) =
            some (some ctype) := empty.1.symm.trans cAssigned
        cases contradiction
      · obtain ⟨ctype, type, cAssigned, leanAssigned, decoded⟩ := assigned
        obtain ⟨otherCType, otherType, _cAssigned, argumentAssigned, _decoded⟩ :=
          collectedState.2 index bound
        have typeEq : type = otherType := by
          have sameCType : ctype = otherCType := by
            have both := cAssigned.symm.trans _cAssigned
            exact Option.some.inj (Option.some.inj both)
          subst otherCType
          exact Option.some.inj (decoded.symm.trans _decoded)
        subst otherType
        exact leanAssigned.trans argumentAssigned.symm
    have argumentsBound : index < arguments.length := by simpa using rightBound
    have elementEq : some (leanFinal[index]'leftBound) =
        some ((arguments.map some)[index]'rightBound) := by
      simpa [getElem?_def, leftBound, argumentsBound] using pointwiseEq
    exact Option.some.inj elementEq
  have totalState : CSubstitutionStateAgree callerPointers scheme cFinal
      (arguments.map some) := by
    rw [← finalMatchesArguments]
    exact finalState
  have allAssigned : ∀ index, index < scheme.length →
      ∃ ctype, cFinal[index]? = some (some ctype) := by
    intro index bound
    obtain ⟨ctype, _type, found, _argumentFound, _decoded⟩ := collectedState.2 index bound
    exact ⟨ctype, found⟩
  have rows := CSubstitutionStateAgree.toRowsAgree callerPointers scheme cFinal
    arguments totalState allAssigned
  exact cSubstituteType_decodes_to_instantiate scheme callerPointers
    (cFinal.map (Option.getD · .unit)) arguments rows result resultType resultDecoded

/-- The `check_call` result theorem specialized to C's initially zeroed
substitution arrays. This composes the `calloc`-shaped empty state with the
constraint simulation, assigned-slot check, and result-type substitution. -/
theorem cMatchTypes_success_substitutes_result_like_Lean_from_empty
    (callerPointers scheme : List Nat) (fuel : Nat) (patterns actuals : List CTypeNode)
    (patternTypes actualTypes : List Ty)
    (patternsDecoded : decodeCTypes scheme patterns = some patternTypes)
    (actualsDecoded : decodeCTypes callerPointers actuals = some actualTypes)
    (actualsMonotype : cMonotypes actuals = true)
    (cFinal : List (Option CTypeNode))
    (matched : cMatchTypes fuel scheme patterns actuals
      (List.replicate scheme.length (none : Option CTypeNode)) = some cFinal)
    (arguments : List Ty) (argumentsLength : arguments.length = scheme.length)
    (collectedState : cFinal.length = scheme.length ∧
      ∀ index, index < scheme.length →
        ∃ ctype type, cFinal[index]? = some (some ctype) ∧
          (arguments.map some)[index]? = some (some type) ∧
          decodeCType callerPointers ctype = some type)
    (result : CTypeNode) (resultType : Ty)
    (resultDecoded : decodeCType scheme result = some resultType) :
    ∃ output,
      cSubstituteType scheme (cFinal.map (Option.getD · .unit)) result = some output ∧
      decodeCType callerPointers output = some (resultType.instantiate arguments) := by
  exact cMatchTypes_success_substitutes_result_like_Lean callerPointers scheme fuel patterns actuals
    patternTypes actualTypes patternsDecoded actualsDecoded actualsMonotype
    (List.replicate scheme.length (none : Option CTypeNode))
    (List.replicate scheme.length (none : Option Ty))
    (cSubstitutionStateAgree_initial_empty callerPointers scheme) matched arguments
    argumentsLength collectedState result resultType resultDecoded

private theorem map_getD_some_eq_of_all_assigned {α : Type} (default : α)
    (assignments : List (Option α))
    (allAssigned : ∀ index, index < assignments.length →
      ∃ value, assignments[index]? = some (some value)) :
    (assignments.map (Option.getD · default)).map some = assignments := by
  induction assignments with
  | nil => rfl
  | cons head tail ih =>
      obtain ⟨value, found⟩ := allAssigned 0 (by simp)
      have headEq : head = some value := by
        simpa [getElem?_def] using found
      have tailAssigned : ∀ index, index < tail.length →
          ∃ value, tail[index]? = some (some value) := by
        intro index bound
        obtain ⟨value, found⟩ := allAssigned (index + 1) (by simp; omega)
        exact ⟨value, by simpa [getElem?_def, Nat.succ_lt_succ_iff] using found⟩
      rw [headEq]
      simp [ih tailAssigned]

private theorem mappedAssignments_wellFormed
    (callerPointers scheme : List Nat) (cAssignments : List (Option CTypeNode))
    (leanAssignments : List (Option Ty))
    (stateAgree : CSubstitutionStateAgree callerPointers scheme cAssignments leanAssignments)
    (allAssigned : ∀ index, index < scheme.length →
      ∃ ctype, cAssignments[index]? = some (some ctype)) :
    ∀ type ∈ leanAssignments.map (Option.getD · .unit),
      type.wellFormed callerPointers.length := by
  induction scheme generalizing cAssignments leanAssignments with
  | nil =>
      have leanEmpty : leanAssignments = [] := by
        cases leanAssignments with
        | nil => rfl
        | cons head tail =>
            have lengthEq := stateAgree.2.1
            simp at lengthEq
      simp [leanEmpty]
  | cons schemeHead schemeTail ih =>
      cases cAssignments with
      | nil =>
          have cLength := stateAgree.1
          simp at cLength
      | cons cHead cTail =>
          cases leanAssignments with
          | nil =>
              have leanLength := stateAgree.2.1
              simp at leanLength
          | cons leanHead leanTail =>
              obtain ⟨cHeadType, cHeadFound⟩ := allAssigned 0 (by simp)
              have cHeadEq : cHead = some cHeadType := by
                simpa [getElem?_def] using cHeadFound
              have slotRelation := stateAgree.2.2 0 (by simp)
              have decodedHead : ∃ type, leanHead = some type ∧
                  decodeCType callerPointers cHeadType = some type := by
                rw [cHeadEq] at slotRelation
                rcases slotRelation with empty | assigned
                · simp [getElem?_def] at empty
                · rcases assigned with ⟨ctype, type, cFound, leanFound, decoded⟩
                  have ctypeEq : cHeadType = ctype := by
                    simpa [getElem?_def, cHeadEq] using cFound
                  have leanTypeEq : leanHead = some type := by
                    simpa [getElem?_def] using leanFound
                  exact ⟨type, leanTypeEq, by simpa [ctypeEq] using decoded⟩
              obtain ⟨headType, leanHeadEq, headDecoded⟩ := decodedHead
              have headWellFormed := decodeCType_wellFormed callerPointers
                cHeadType headType headDecoded
              have cTailAssigned : ∀ index, index < schemeTail.length →
                  ∃ ctype, cTail[index]? = some (some ctype) := by
                intro index bound
                obtain ⟨ctype, found⟩ := allAssigned (index + 1) (by simp; omega)
                exact ⟨ctype, by simpa [getElem?_def, Nat.succ_lt_succ_iff] using found⟩
              have tailState : CSubstitutionStateAgree callerPointers schemeTail cTail leanTail := by
                refine ⟨?_, ?_, ?_⟩
                · have h := stateAgree.1
                  simp at h ⊢
                  omega
                · have h := stateAgree.2.1
                  simp at h ⊢
                  omega
                · intro index bound
                  have oldRelation := stateAgree.2.2 (index + 1) (by simp; omega)
                  simpa [getElem?_def, Nat.succ_lt_succ_iff] using oldRelation
              have tailWellFormed := ih cTail leanTail tailState cTailAssigned
              intro type member
              simp only [List.map_cons, List.mem_cons] at member
              rcases member with head | tail
              · cases head
                simpa [leanHeadEq] using headWellFormed
              · exact tailWellFormed type tail

/-- If C's successful call check has assigned every quantified slot, the
state simulation itself determines the Lean type-argument vector.  Result
substitution then agrees with instantiating the decoded scheme result by
that vector; no separately supplied assignment correspondence is needed. -/
theorem cMatchTypes_success_infers_arguments_and_substitutes_result
    (callerPointers scheme : List Nat) (fuel : Nat) (patterns actuals : List CTypeNode)
    (patternTypes actualTypes : List Ty)
    (patternsDecoded : decodeCTypes scheme patterns = some patternTypes)
    (actualsDecoded : decodeCTypes callerPointers actuals = some actualTypes)
    (actualsMonotype : cMonotypes actuals = true)
    (cFinal : List (Option CTypeNode))
    (matched : cMatchTypes fuel scheme patterns actuals
      (List.replicate scheme.length (none : Option CTypeNode)) = some cFinal)
    (allAssigned : cFinal.length = scheme.length ∧
      ∀ index, index < scheme.length →
        ∃ ctype, cFinal[index]? = some (some ctype))
    (result : CTypeNode) (resultType : Ty)
    (resultDecoded : decodeCType scheme result = some resultType) :
    ∃ arguments output,
      arguments.length = scheme.length ∧
      (∀ type ∈ arguments, type.wellFormed callerPointers.length) ∧
      instantiateTypes arguments patternTypes = actualTypes ∧
      cSubstituteType scheme (cFinal.map (Option.getD · .unit)) result = some output ∧
      decodeCType callerPointers output = some (resultType.instantiate arguments) := by
  obtain ⟨leanFinal, _leanCollected, finalState⟩ :=
    (cMatchType_and_types_state_simulation fuel).2 scheme callerPointers patterns actuals
      patternTypes actualTypes (List.replicate scheme.length none)
      (List.replicate scheme.length none) cFinal actualsMonotype patternsDecoded
      actualsDecoded (cSubstitutionStateAgree_initial_empty callerPointers scheme) matched
  have leanSlotAssigned : ∀ index, index < scheme.length →
      ∃ type, leanFinal[index]? = some (some type) := by
    intro index bound
    obtain ⟨ctype, cAssigned⟩ := allAssigned.2 index bound
    rcases finalState.2.2 index bound with empty | assigned
    · have contradiction : (none : Option CTypeNode) = some ctype :=
        Option.some.inj (empty.1.symm.trans cAssigned)
      cases contradiction
    · rcases assigned with ⟨_ctype, type, _cFound, leanFound, _decoded⟩
      exact ⟨type, leanFound⟩
  let arguments := leanFinal.map (Option.getD · .unit)
  have argumentsLength : arguments.length = scheme.length := by
    simp [arguments, finalState.2.1]
  have argumentsMap : arguments.map some = leanFinal := by
    apply map_getD_some_eq_of_all_assigned .unit leanFinal
    intro index bound
    apply leanSlotAssigned index
    rw [finalState.2.1] at bound
    exact bound
  have totalState : CSubstitutionStateAgree callerPointers scheme cFinal
      (arguments.map some) := by
    rw [argumentsMap]
    exact finalState
  have finalAgree : AssignmentsAgree arguments leanFinal := by
    intro index type assigned
    rw [← argumentsMap] at assigned
    have inner : arguments[index]? = some type := by
      by_cases bound : index < arguments.length
      · have mapElement : (arguments.map some)[index]'(by simpa using bound) =
            some (arguments[index]'bound) := by
          change (arguments.map some).get ⟨index, by simp [bound]⟩ =
            some (arguments.get ⟨index, bound⟩)
          exact List.get_map some
        have element : arguments[index]'bound = some type := by
          have found : some (arguments[index]'bound) = some (some type) := by
            simpa [getElem?_def, bound, mapElement] using assigned
          exact Option.some.inj found
        simp [getElem?_def, bound, element]
      · simp [getElem?_def, bound] at assigned
    exact inner
  have patternsWellFormed : ∀ type ∈ patternTypes, type.wellFormed scheme.length :=
    decodeCTypes_wellFormed scheme patterns patternTypes patternsDecoded
  have argumentsInstantiate : instantiateTypes arguments patternTypes = actualTypes :=
    -- The candidate length is the scheme length, as required by the decoded
    -- parameter types' well-formedness measure.
    collectArguments_sound fuel patternTypes actualTypes arguments
      (List.replicate scheme.length none) leanFinal (by
        intro type mem
        rw [argumentsLength]
        exact patternsWellFormed type mem) _leanCollected finalAgree
  have argumentsValid : ∀ type ∈ arguments, type.wellFormed callerPointers.length :=
    mappedAssignments_wellFormed callerPointers scheme cFinal leanFinal finalState
      allAssigned.2
  have rows := CSubstitutionStateAgree.toRowsAgree callerPointers scheme cFinal
    arguments totalState allAssigned.2
  obtain ⟨output, substituted, decoded⟩ := cSubstituteType_decodes_to_instantiate
    scheme callerPointers (cFinal.map (Option.getD · .unit)) arguments rows result resultType
    resultDecoded
  exact ⟨arguments, output, argumentsLength, argumentsValid, argumentsInstantiate,
    substituted, decoded⟩

theorem decodeCType_rejects_forall (pointers variables : List Nat) (body : CTypeNode) :
    decodeCType pointers (.forallType variables body) = none := by
  simp [decodeCType]

end NLisp.Surface
