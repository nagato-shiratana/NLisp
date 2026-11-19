import NLisp.NamedDecoder
import NLisp.EvaluatorCompleteness

open NLisp

private theorem closureSource : Named.Evaluates [] []
    (.app (.lam [13, 16] (.var 16)) [.int 1, .int 42]) (.int 42) :=
  .appClosure .lam (.cons .int (.cons .int .nil)) rfl (.var rfl)

example : PolyIR.Evaluates [] []
    (Named.lower [] (.app (.lam [13, 16] (.var 16)) [.int 1, .int 42])) (.int 42) :=
  Named.evaluation_preserved closureSource

private theorem parallelSource : Named.Evaluates [] [(13, .int 10)]
    (.letMany [16, 19] [.int 1, .var 13] (.var 19)) (.int 10) :=
  .letMany (.cons .int (.cons (.var rfl) .nil)) rfl (.var rfl)

example : PolyIR.Evaluates [] [.int 10]
    (Named.lower [13] (.letMany [16, 19] [.int 1, .var 13] (.var 19))) (.int 10) :=
  Named.evaluation_preserved parallelSource

example : Named.Evaluates [] []
    (.matchList (.cons (.int 42) .nil) (.int 0) 13 16 (.var 13)) (.int 42) :=
  .matchCons (.cons .int .nil) (.var rfl)

-- A source semantic derivation also yields eventual success of the real IR evaluator.
example : ∃ fuel, PolyIR.evaluate [] fuel []
    (Named.lower [] (.app (.lam [13, 16] (.var 16)) [.int 1, .int 42])) = .ok (.int 42) :=
  PolyIR.evaluate_complete (Named.evaluation_preserved closureSource)

private def a (n : String) (token : Nat := 4) (selected : Nat := 0) : CBindingWalk.Node :=
  .atom ⟨n, none, token⟩ selected

private def sourceForm : CBindingWalk.Node := .list [a "defun", a "main" 10,
  .list [], a "Integer", .list [a "+" 22 3, a "40", a "2"]]

example : (Named.decodeProgram 40 [sourceForm]).isSome = true := by decide
example : ExpansionLowering.checkMain 40 [sourceForm] 0 = true := by decide
example : ExpansionLowering.checkMain 40 [sourceForm] 1 = false := by decide

-- Decoding preserves identities; conversion to positional locals is a separate function.
example : Named.decodeExpr 40 [] (a "x" 28 13) = some (.var 13) := by rfl
example : Named.lower [16, 13] (.var 13) = .var 1 := by rfl

#print axioms Named.evaluation_preserved
#print axioms Named.lookup_lowered
#print axioms Named.definitions_lookup
