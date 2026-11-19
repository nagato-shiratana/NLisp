import NLisp.CheckerCompleteness

open NLisp.Surface

example (typing : HasType globals count context expression type) :
    ∃ fuel, (infer fuel globals count context expression).isSome = true := by
  obtain ⟨bound, result⟩ := inference_eventually typing
  exact ⟨bound, by simp [result bound (Nat.le_refl bound)]⟩

example (first : HasType globals count context expression a)
    (second : HasType globals count context expression b) : a = b := type_unique first second

#print axioms checkWF_complete
#print axioms inference_eventually
#print axioms type_unique
