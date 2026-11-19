import NLisp.PolyIR

open NLisp

-- Decimal bit width, rather than the numeric value, is the relevant input size.
private def large : Int :=
  10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001

example : PolyIR.sourceNodes (.int large) = 1 := by rfl
example : PolyIR.sourceNodes (.var 10000000000000000000000000000000000000000) = 1 := by rfl
example : PolyIR.erase (.int large) = .int large := by rfl

private def intResult : Except PolyIR.Fault PolyIR.Value → Option Int
  | .ok (.int n) => some n
  | _ => none

-- Native execution of erasure still works: the node measure is proof-only.
#eval (intResult (PolyIR.evaluate [] 10 [] (PolyIR.erase (.int large)))) == some large

example : intResult (PolyIR.evaluate [] 10 [] (PolyIR.erase (.int large))) = some large := by decide
