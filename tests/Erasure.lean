import NLisp.Erasure

open NLisp

-- The source derivation, not the erased interpreter, is the premise.
private theorem parallelLet : Surface.Evaluates [] [.int 10]
    (.letMany [.integer, .integer] [.int 1, .var 0] (.var 1)) (.int 10) := by
  apply Surface.Evaluates.letMany
  · exact .cons .int (.cons (.var rfl) .nil)
  · exact .var rfl

example : PolyIR.Evaluates [] [.int 10]
    (.letMany [.int 1, .var 0] (.var 1)) (.int 10) := by
  simpa [PolyIR.eraseDefinitions, PolyIR.erase, PolyIR.eraseList,
    PolyIR.eraseValues, PolyIR.eraseValue] using PolyIR.evaluation_preserved parallelLet

private def identitySignature : Surface.Signature := ⟨1, [.var 0], .var 0⟩
private def definitions : Surface.Definitions := [(identitySignature, .var 0)]

private theorem identityCall : Surface.Evaluates definitions []
    (.app (.global 0 [.integer]) [.int 42]) (.int 42) := by
  apply Surface.Evaluates.appGlobal (signature := identitySignature) (body := .var 0)
  · exact .global rfl
  · exact .cons .int .nil
  · rfl
  · rfl
  · exact .var rfl

example : PolyIR.Evaluates (PolyIR.eraseDefinitions definitions) []
    (.app (.global 0) [.int 42]) (.int 42) := by
  simpa [PolyIR.erase, PolyIR.eraseList] using PolyIR.closed_integer_result identityCall

#print axioms PolyIR.evaluation_preserved
#print axioms PolyIR.closed_integer_result
