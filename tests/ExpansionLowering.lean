import NLisp.ExpansionLowering

open NLisp NLisp.ExpansionLowering

private def a (n : String) (token : Nat := 4) (selected : Nat := 0) : CBindingWalk.Node :=
  .atom ⟨n, none, token⟩ selected

private def signature : Surface.Signature := ⟨0, [.integer, .integer], .integer⟩
private def form : CBindingWalk.Node := .list [a "defun", a "choose" 10,
  .list [.list [a "x" 13, a "Integer"], .list [a "x" 16, a "Integer"]],
  a "Integer", a "x" 19 16]

-- Even same-named, same-typed binders remain distinct by identity.
example : checkProgram 60 [form] [signature] [.var 1] = true := by decide
example : checkProgram 60 [form] [signature] [.var 0] = false := by decide
example : checkProgram 60 [form] [signature] [.int 42] = false := by decide

-- Annotation and evaluation-order changes cannot be hidden by equal types.
private def addition : CBindingWalk.Node :=
  .list [a "+" 22 3, a "1", a "2"]
private def addPrimitive : Surface.Expr :=
  .lam [.integer, .integer] .integer (.add (.var 0) (.var 1))
example : checkExpr 50 [] [] [] false addition
    (.app addPrimitive [.int 1, .int 2]) = true := by decide
example : checkExpr 50 [] [] [] false addition
    (.app addPrimitive [.int 2, .int 1]) = false := by decide
example : checkExpr 50 [] [] [] false addition
    (.app (.lam [.integer, .integer] .integer (.sub (.var 0) (.var 1)))
      [.int 1, .int 2]) = false := by decide

-- Parallel RHSs retain the original environment.
private def parallelLet : CBindingWalk.Node := .list [a "let",
  .list [.list [.list [a "y" 25, a "Integer"], a "x" 28 13]], a "y" 31 25]
example : checkExpr 50 [] [] [13] false parallelLet
    (.letMany [.integer] [.var 0] (.var 0)) = true := by decide

#print axioms local_reference_preserved
#print axioms signatures_preserved
