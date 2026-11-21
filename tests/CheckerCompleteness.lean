import NLisp.CheckerCompleteness

open NLisp.Surface

example (typing : HasType globals count context expression type) :
    ∃ fuel, (infer fuel globals count context expression).isSome = true := by
  obtain ⟨bound, result⟩ := inference_eventually typing
  exact ⟨bound, by simp [result bound (Nat.le_refl bound)]⟩

example (first : HasType globals count context expression a)
    (second : HasType globals count context expression b) : a = b := type_unique first second

example (type : Ty) (count : Nat) (valid : type.wellFormed count) :
    (checkWF (checkerTypeFuel type) count type).isSome = true := by
  obtain ⟨checked, accepted⟩ :=
    checkWF_sufficient type count (checkerTypeFuel type) valid (Nat.le_refl _)
  simp [accepted]

example (types : List Ty) (count : Nat) (valid : ∀ t ∈ types, t.wellFormed count) :
    (checkTypesWF (checkerTypesFuel types) count types).isSome = true := by
  obtain ⟨checked, accepted⟩ :=
    checkTypesWF_sufficient types count (checkerTypesFuel types) valid (Nat.le_refl _)
  simp [accepted]

example (signature : Signature) (valid : signature.wellFormed) :
    ∃ parametersChecked resultChecked,
      checkTypesWF (checkerSignatureFuel signature) signature.typeArity signature.parameters =
        some parametersChecked ∧
      checkWF (checkerSignatureFuel signature) signature.typeArity signature.result =
        some resultChecked :=
  checkSignatureWF_sufficient signature valid

#print axioms checkWF_complete
#print axioms checkWF_sufficient
#print axioms checkTypesWF_sufficient
#print axioms checkSignatureWF_sufficient
#print axioms inference_eventually
#print axioms type_unique
