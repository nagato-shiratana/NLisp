import NLisp.SurfaceChecker

open NLisp.Surface

-- A single generic body is checked once, without enumerating instantiations.
private def identitySignature : Signature := ⟨1, [.var 0], .var 0⟩
example : (elaborateProgram 40 [identitySignature] [.var 0]).isSome = true := by decide

example : (infer 40 [identitySignature] 0 []
    (.app (.global 0 [.integer]) [.int 42])).isSome = true := by decide
example : (infer 40 [identitySignature] 0 []
    (.app (.global 0 [.boolean]) [.bool true])).isSome = true := by decide

-- Out-of-scope type variables, arity mismatches and wrong argument types fail.
example : (infer 40 [identitySignature] 0 [] (.global 0 [.var 0])).isSome = false := by decide
example : (infer 40 [identitySignature] 0 [] (.global 0 [])).isSome = false := by decide
example : (infer 40 [identitySignature] 0 []
    (.app (.global 0 [.integer]) [.bool true])).isSome = false := by decide

-- An annotated generic definition is rejected when its body violates its contract.
example : (elaborateProgram 40 [identitySignature] [.int 42]).isSome = false := by decide
example : (elaborateProgram 40 [identitySignature] []).isSome = false := by decide

-- Polymorphic recursion changes type arguments but never creates another body.
private def recursiveSignature : Signature := ⟨1, [.var 0], .integer⟩
private def recursiveBody : Expr :=
  .app (.global 0 [.list (.var 0)]) [.cons (.var 0) (.var 0) (.nil (.var 0))]
example : (elaborateProgram 60 [recursiveSignature] [recursiveBody]).isSome = true := by decide

-- Parallel let initializers and match-bound variables use the specified order.
example : (infer 40 [] 0 [.integer]
    (.letMany [.integer, .integer] [.int 1, .var 0] (.var 1))).isSome = true := by decide
example : (infer 40 [] 0 []
    (.matchList (.cons .integer (.int 42) (.nil .integer)) (.int 0) (.var 0))).isSome = true := by decide
example : (infer 40 [] 0 []
    (.matchOption (.some .integer (.int 42)) (.int 0) (.var 0))).isSome = true := by decide

#print axioms infer_sound
#print axioms elaborateProgram
