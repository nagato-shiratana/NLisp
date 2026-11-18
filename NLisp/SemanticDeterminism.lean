import NLisp.ErasureExecution

namespace NLisp.PolyIR

theorem evaluation_deterministic
    (left : Evaluates program env term first)
    (right : Evaluates program env term second) : first = second := by
  obtain ⟨a, ha⟩ := evaluation_eventually left
  obtain ⟨b, hb⟩ := evaluation_eventually right
  have same := (ha (a + b) (by omega)).symm.trans (hb (a + b) (by omega))
  exact Except.ok.inj same

end NLisp.PolyIR

