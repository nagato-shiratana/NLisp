import NLisp.SurfaceEvaluator

namespace NLisp.Surface

/- The executable interpreter cannot report success without a corresponding
independent big-step derivation. The three interpreter functions are proved
together by induction on fuel, including their argument/sequence traversals. -/
theorem evaluator_sound (program : Definitions) (fuel : Nat) :
    (∀ env term value, evaluate program fuel env term = .ok value → Evaluates program env term value) ∧
    (∀ env terms values, evaluateArgs program fuel env terms = .ok values →
      ArgumentsEvaluate program env terms values) ∧
    (∀ env previous terms value, evaluateSequence program fuel env previous terms = .ok value →
      SequenceEvaluates program env terms previous value) := by
  induction fuel with
  | zero => simp [evaluate, evaluateArgs, evaluateSequence]
  | succ fuel ih =>
    obtain ⟨exprSound, argsSound, sequenceSound⟩ := ih
    refine ⟨?_, ?_, ?_⟩
    · intro env term value h
      cases term <;> simp only [evaluate, bind, Except.bind, pure, Except.pure] at h
      all_goals repeat' (first | split at h | (simp only [Except.bind, Except.pure] at h; split at h))
      all_goals try simp_all
      all_goals subst_vars
      all_goals first
        | solve | apply Evaluates.var <;> first | assumption | rfl | (apply exprSound; assumption) | (apply argsSound; assumption) | (apply sequenceSound; assumption)
        | solve | apply Evaluates.global <;> first | assumption | rfl | (apply exprSound; assumption) | (apply argsSound; assumption) | (apply sequenceSound; assumption)
        | solve | apply Evaluates.bool <;> first | assumption | rfl | (apply exprSound; assumption) | (apply argsSound; assumption) | (apply sequenceSound; assumption)
        | solve | apply Evaluates.int <;> first | assumption | rfl | (apply exprSound; assumption) | (apply argsSound; assumption) | (apply sequenceSound; assumption)
        | solve | apply Evaluates.float <;> first | assumption | rfl | (apply exprSound; assumption) | (apply argsSound; assumption) | (apply sequenceSound; assumption)
        | solve | apply Evaluates.string <;> first | assumption | rfl | (apply exprSound; assumption) | (apply argsSound; assumption) | (apply sequenceSound; assumption)
        | solve | apply Evaluates.character <;> first | assumption | rfl | (apply exprSound; assumption) | (apply argsSound; assumption) | (apply sequenceSound; assumption)
        | solve | apply Evaluates.floatBin <;> first | assumption | rfl | (apply exprSound; assumption) | (apply argsSound; assumption) | (apply sequenceSound; assumption)
        | solve | apply Evaluates.unit <;> first | assumption | rfl | (apply exprSound; assumption) | (apply argsSound; assumption) | (apply sequenceSound; assumption)
        | solve | apply Evaluates.lam <;> first | assumption | rfl | (apply exprSound; assumption) | (apply argsSound; assumption) | (apply sequenceSound; assumption)
        | solve | apply Evaluates.appClosure <;> first | assumption | rfl | (apply exprSound; assumption) | (apply argsSound; assumption) | (apply sequenceSound; assumption)
        | solve | apply Evaluates.appGlobal <;> first | assumption | rfl | (apply exprSound; assumption) | (apply argsSound; assumption) | (apply sequenceSound; assumption)
        | solve | apply Evaluates.ifTrue <;> first | assumption | rfl | (apply exprSound; assumption) | (apply argsSound; assumption) | (apply sequenceSound; assumption)
        | solve | apply Evaluates.ifFalse <;> first | assumption | rfl | (apply exprSound; assumption) | (apply argsSound; assumption) | (apply sequenceSound; assumption)
        | solve | apply Evaluates.add <;> first | assumption | rfl | (apply exprSound; assumption) | (apply argsSound; assumption) | (apply sequenceSound; assumption)
        | solve | apply Evaluates.sub <;> first | assumption | rfl | (apply exprSound; assumption) | (apply argsSound; assumption) | (apply sequenceSound; assumption)
        | solve | apply Evaluates.mul <;> first | assumption | rfl | (apply exprSound; assumption) | (apply argsSound; assumption) | (apply sequenceSound; assumption)
        | solve | apply Evaluates.le <;> first | assumption | rfl | (apply exprSound; assumption) | (apply argsSound; assumption) | (apply sequenceSound; assumption)
        | solve | apply Evaluates.intEq <;> first | assumption | rfl | (apply exprSound; assumption) | (apply argsSound; assumption) | (apply sequenceSound; assumption)
        | solve | apply Evaluates.letMany <;> first | assumption | rfl | (apply exprSound; assumption) | (apply argsSound; assumption) | (apply sequenceSound; assumption)
        | solve | apply Evaluates.begin <;> first | assumption | rfl | (apply exprSound; assumption) | (apply argsSound; assumption) | (apply sequenceSound; assumption)
        | solve | apply Evaluates.nil <;> first | assumption | rfl | (apply exprSound; assumption) | (apply argsSound; assumption) | (apply sequenceSound; assumption)
        | solve | apply Evaluates.cons <;> first | assumption | rfl | (apply exprSound; assumption) | (apply argsSound; assumption) | (apply sequenceSound; assumption)
        | solve | apply Evaluates.none <;> first | assumption | rfl | (apply exprSound; assumption) | (apply argsSound; assumption) | (apply sequenceSound; assumption)
        | solve | apply Evaluates.some <;> first | assumption | rfl | (apply exprSound; assumption) | (apply argsSound; assumption) | (apply sequenceSound; assumption)
        | solve | apply Evaluates.matchNil <;> first | assumption | rfl | (apply exprSound; assumption) | (apply argsSound; assumption) | (apply sequenceSound; assumption)
        | solve | apply Evaluates.matchCons <;> first | assumption | rfl | (apply exprSound; assumption) | (apply argsSound; assumption) | (apply sequenceSound; assumption)
        | solve | apply Evaluates.matchNone <;> first | assumption | rfl | (apply exprSound; assumption) | (apply argsSound; assumption) | (apply sequenceSound; assumption)
        | solve | apply Evaluates.matchSome <;> first | assumption | rfl | (apply exprSound; assumption) | (apply argsSound; assumption) | (apply sequenceSound; assumption)
    · intro env terms values h
      cases terms <;> simp only [evaluateArgs, bind, Except.bind, pure, Except.pure] at h
      all_goals repeat' (first | split at h | (simp only [Except.bind, Except.pure] at h; split at h))
      all_goals try simp_all
      all_goals subst_vars
      all_goals solve_by_elim [exprSound, argsSound, ArgumentsEvaluate.nil, ArgumentsEvaluate.cons]
    · intro env previous terms value h
      cases terms <;> simp only [evaluateSequence, bind, Except.bind, pure, Except.pure] at h
      all_goals repeat' (first | split at h | (simp only [Except.bind, Except.pure] at h; split at h))
      all_goals try simp_all
      all_goals subst_vars
      all_goals solve_by_elim [exprSound, sequenceSound, SequenceEvaluates.nil, SequenceEvaluates.cons]

theorem evaluate_sound (h : evaluate program fuel env term = .ok value) :
    Evaluates program env term value := (evaluator_sound program fuel).1 env term value h


end NLisp.Surface

