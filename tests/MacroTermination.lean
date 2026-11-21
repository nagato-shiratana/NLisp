import NLisp.MacroTermination

open NLisp.CMacroCopy NLisp.CExpansion NLisp.MacroTermination

private def atom (name : String) (token : Nat) : Tree :=
  .atom ⟨name, none, token⟩

private def rule : Tree :=
  .list [.list [atom "m" 4, atom "x" 7], atom "Syntax" 10, atom "Syntax" 11, atom "x" 7]

private def argument : Tree := atom "value" 13
private def input : Tree := .list [atom "m" 4, argument]
private def template : Tree := atom "x" 7
private def holes : Holes := [("x", argument)]
private def rules : List (Nat × Tree) := [(0, rule)]

example : matchRule rule input = some (holes, template) := by rfl

example : ∃ target, StaticCall rules [] input target :=
  macro_step_input_is_static_candidate rules 0 rule input template holes
    (by simp [rules]) (by rfl)

#print axioms holeEntries_success_lengths
#print axioms successful_match_has_signature
#print axioms macro_step_input_is_static_candidate
