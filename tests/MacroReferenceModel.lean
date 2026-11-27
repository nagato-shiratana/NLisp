import NLisp.MacroReferenceModel

open NLisp.CMacroCopy NLisp.CExpansion NLisp.MacroTermination NLisp.MacroReferenceModel

private def atom (name : String) (token : Nat) : Tree :=
  .atom ⟨name, none, token⟩

private def rule : Tree :=
  .list [.list [atom "m" 4, atom "x" 7], atom "Syntax" 10,
    .list [atom "lambda" 13, .list [.list [atom "y" 16, atom "Int" 19]],
      atom "Int" 22, .list [atom "x" 7, atom "y" 16]],
    .list [atom "x" 7, atom "x" 7]]

private def rules : List (Nat × Tree) := [(0, rule)]
private def input : Tree := .list [atom "m" 4, atom "value" 25]

example : (matchRule rule input).isSome = true := by
  simp [matchRule, rule, input, atom, holeEntries]

example : rankStatus [] [] = .proven := by rfl

example : rankTraceStatus [(1, 0)] [1, 0] [0, 1] = .proven := by
  apply rankTraceStatus_proven
  exact ⟨by simp [Calls], by decide, trivial⟩

