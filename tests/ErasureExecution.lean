import NLisp.ErasureExecution
import NLisp.SemanticDeterminism
import NLisp.SurfaceEvaluatorCompleteness

open NLisp

private def identityProgram : Surface.Definitions :=
  [(⟨1, [.var 0], .var 0⟩, .var 0)]

example : PolyIR.Evaluates (PolyIR.eraseDefinitions identityProgram) []
    (PolyIR.erase (.app (.global 0 [.integer]) [.int 42])) (.int 42) := by
  apply PolyIR.evaluate_sound (fuel := 20)
  rfl

example : ∃ value, Surface.Evaluates identityProgram []
    (.app (.global 0 [.integer]) [.int 42]) value ∧ PolyIR.eraseValue value = .int 42 := by
  apply PolyIR.finite_evaluation_iff.mp
  apply PolyIR.evaluate_sound (fuel := 20)
  rfl

-- Errors, including discarded begin expressions, are reflected at equal fuel.
example : Surface.evaluate [] 20 [] (.begin (.var 99) [.int 42]) = .error .unbound := by
  apply PolyIR.execution_error_iff.mp
  rfl

example (h : PolyIR.Evaluates [] [] (.int 42) value) : value = .int 42 :=
  PolyIR.evaluation_deterministic h .int

#print axioms PolyIR.evaluation_eventually
#print axioms PolyIR.execution_commutes
#print axioms PolyIR.finite_evaluation_iff
#print axioms PolyIR.execution_error_iff
#print axioms PolyIR.fuel_divergence_iff
#print axioms PolyIR.evaluation_deterministic
#print axioms Surface.evaluation_eventually
#print axioms Surface.evaluation_deterministic
