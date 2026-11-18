import NLisp.EvaluatorCompleteness
import NLisp.SurfaceEvaluatorCorrectness

namespace NLisp.Surface

theorem evaluation_eventually (h : Evaluates program env term value) :
    ∃ bound, ∀ fuel, bound ≤ fuel → evaluate program fuel env term = .ok value := by
  apply Evaluates.rec
    (motive_1 := fun env term value _ =>
      ∃ bound, ∀ fuel, bound ≤ fuel → evaluate program fuel env term = .ok value)
    (motive_2 := fun env terms values _ =>
      ∃ bound, ∀ fuel, bound ≤ fuel → evaluateArgs program fuel env terms = .ok values)
    (motive_3 := fun env terms previous value _ =>
      ∃ bound, ∀ fuel, bound ≤ fuel → evaluateSequence program fuel env previous terms = .ok value)
    (t := h)
  all_goals intros
  all_goals convergence_bound
  all_goals intro fuel bound
  all_goals cases fuel with
  | zero => omega
  | succ fuel =>
    use_bounds_at fuel
    simp_all [evaluate, evaluateArgs, evaluateSequence, bind, Except.bind, pure, Except.pure]

theorem evaluate_complete (h : Evaluates program env term value) :
    ∃ fuel, evaluate program fuel env term = .ok value := by
  obtain ⟨bound, proof⟩ := evaluation_eventually h
  exact ⟨bound, proof bound (Nat.le_refl bound)⟩

theorem evaluates_iff_success : Evaluates program env term value ↔
    ∃ fuel, evaluate program fuel env term = .ok value :=
  ⟨evaluate_complete, fun ⟨_, proof⟩ => evaluate_sound proof⟩

theorem evaluation_deterministic
    (left : Evaluates program env term first)
    (right : Evaluates program env term second) : first = second := by
  obtain ⟨a, ha⟩ := evaluation_eventually left
  obtain ⟨b, hb⟩ := evaluation_eventually right
  have same := (ha (a + b) (by omega)).symm.trans (hb (a + b) (by omega))
  exact Except.ok.inj same

end NLisp.Surface
