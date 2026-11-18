import NLisp.PolyIR
import NLisp.SurfaceSemantics

open NLisp

private def intResult : Except PolyIR.Fault PolyIR.Value → Option Int
  | .ok (.int n) => some n
  | _ => none

-- Parallel initializers use the outer environment (10), not the new binding (1).
example : intResult (PolyIR.evaluate [] 30 [.int 10]
    (.letMany [.int 1, .var 0] (.var 1))) = some 10 := by decide

-- Unselected branches are not evaluated.
example : intResult (PolyIR.evaluate [] 30 []
    (.ite (.bool true) (.int 42) (.var 99))) = some 42 := by decide

-- begin does evaluate discarded expressions.
example : (PolyIR.evaluate [] 30 [] (.begin (.var 99) [.int 42])).isOk = false := by decide

-- A zero-argument lambda remains a zero-argument function.
example : intResult (PolyIR.evaluate [] 30 [] (.app (.lam 0 (.int 42)) [])) = some 42 := by decide

-- Generic identity shares one runtime body for Integer and Boolean calls.
private def identityRuntime : List PolyIR.RuntimeDefinition := [⟨1, .var 0⟩]
example : intResult (PolyIR.evaluate identityRuntime 30 []
    (PolyIR.erase (.app (.global 0 [.integer]) [.int 42]))) = some 42 := by decide

-- Independently construct a source-level derivation for the same parallel let.
example : Surface.Evaluates [] [.int 10]
    (.letMany [.integer, .integer] [.int 1, .var 0] (.var 1)) (.int 10) := by
  apply Surface.Evaluates.letMany
  · exact .cons .int (.cons (.var rfl) .nil)
  · exact .var rfl

private def identitySignature : Surface.Signature := ⟨1, [.var 0], .var 0⟩
private def identityDefinition : PolyIR.Definition [identitySignature] identitySignature where
  signature_valid := by simp [Surface.Signature.wellFormed, Surface.Ty.wellFormed, identitySignature]
  body := ⟨.var 0, .var rfl⟩

#eval intResult (PolyIR.evaluate identityRuntime 30 []
  (PolyIR.erase (.app (.global 0 [.integer]) [.int 42])))

#print axioms PolyIR.erase_type_arguments
#print axioms PolyIR.checked_expression_has_type
