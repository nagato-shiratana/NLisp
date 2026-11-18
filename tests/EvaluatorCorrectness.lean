import NLisp.EvaluatorCorrectness

open NLisp.PolyIR

-- Success of the executable evaluator yields a semantic derivation.
example : Evaluates [] [] (.app (.lam 0 (.int 42)) []) (.int 42) := by
  apply evaluate_sound (fuel := 20)
  rfl

example : Evaluates [] [.int 10]
    (.letMany [.int 1, .var 0] (.var 1)) (.int 10) := by
  apply evaluate_sound (fuel := 30)
  rfl

private def recursiveProgram : List RuntimeDefinition :=
  [⟨1, .ite (.le (.var 0) (.int 0)) (.int 0)
    (.add (.var 0) (.app (.global 0) [.sub (.var 0) (.int 1)]))⟩]

example : Evaluates recursiveProgram [] (.app (.global 0) [.int 3]) (.int 6) := by
  apply evaluate_sound (fuel := 40)
  rfl

-- Finite fuel is not interpreted as a successful result.
example : (evaluate recursiveProgram 0 [] (.app (.global 0) [.int 3])).isOk = false := by decide

#print axioms evaluator_sound
#print axioms evaluate_sound
