import NLisp.PolymorphicSafety

open NLisp

private def identitySignature : Surface.Signature := ⟨1, [.var 0], .var 0⟩
private def signatures : List Surface.Signature := [identitySignature]
private def bodies : List Surface.Expr := [.var 0]
private def definitions : Surface.Definitions := signatures.zip bodies
private def expression : Surface.Expr := .app (.global 0 [.integer]) [.int 42]
private def assignment : Nat → Surface.Ty := fun _ => .unit

private theorem programTyped : PolyIR.ProgramTyped signatures definitions :=
  Surface.elaborateProgram_programTyped (fuel := 50) (by decide)

private theorem expressionTyped : Surface.HasType signatures 0 [] expression .integer :=
  Surface.elaborate_typed (fuel := 50) (by decide)

example {fuel : Nat} {fault : PolyIR.Fault}
    (h : PolyIR.evaluate (PolyIR.eraseDefinitions definitions) fuel [] (PolyIR.erase expression) = .error fault) :
    fault = .outOfFuel :=
  PolyIR.evaluation_no_type_error programTyped expressionTyped
    (assignment := assignment) (by simpa only [Surface.interpretTypes] using PolyIR.ValuesTyped.nil) h

example : PolyIR.ValueTyped signatures (.int 42) (Surface.interpret assignment .integer) := by
  apply PolyIR.evaluation_preserves_type programTyped expressionTyped
    (assignment := assignment) (env := [])
  · simpa only [Surface.interpretTypes] using PolyIR.ValuesTyped.nil
  · exact (rfl : PolyIR.evaluate (PolyIR.eraseDefinitions definitions) 20 []
      (PolyIR.erase expression) = .ok (.int 42))

-- The theorem covers divergent polymorphic recursion without claiming termination.
private def growSignature : Surface.Signature := ⟨1, [.var 0], .integer⟩
private def growBody : Surface.Expr :=
  .app (.global 0 [.list (.var 0)]) [.cons (.var 0) (.var 0) (.nil (.var 0))]
private def growDefinitions : Surface.Definitions := [(growSignature, growBody)]
private theorem growProgramTyped : PolyIR.ProgramTyped [growSignature] growDefinitions :=
  Surface.elaborateProgram_programTyped (fuel := 60) (bodies := [growBody]) (by decide)
private theorem growExpressionTyped : Surface.HasType [growSignature] 0 []
    (.app (.global 0 [.integer]) [.int 0]) .integer :=
  Surface.elaborate_typed (fuel := 60) (by decide)

example {fuel : Nat} {fault : PolyIR.Fault}
    (h : PolyIR.evaluate (PolyIR.eraseDefinitions growDefinitions) fuel []
      (PolyIR.erase (.app (.global 0 [.integer]) [.int 0])) = .error fault) : fault = .outOfFuel := by
  apply PolyIR.evaluation_no_type_error growProgramTyped
    growExpressionTyped
    (assignment := assignment) (env := [])
  · simpa only [Surface.interpretTypes] using PolyIR.ValuesTyped.nil
  · exact h

#print axioms PolyIR.evaluator_type_safe
#print axioms PolyIR.evaluation_preserves_type
#print axioms PolyIR.evaluation_no_type_error
#print axioms Surface.elaborateProgram_programTyped
