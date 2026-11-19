import NLisp.TypeArguments

open NLisp.Surface NLisp.ExpansionLowering

private def header (count : Nat) (parameters : List Ty) : Header :=
  ⟨10, (List.range count).map (fun i => "T" ++ toString i),
    parameters.enum.map (fun (index, t) => (13 + 3 * index, t)), .integer, .list []⟩

example : ((inferTypeArguments 60 0 (header 1 [.var 0]) [.integer]).map
    TypeArgumentSolution.arguments) = some [.integer] := by decide

example : ((inferTypeArguments 60 0
    (header 2 [.fn [.var 0] (.var 1), .list (.var 0)])
    [.fn [.integer] .boolean, .list .integer]).map TypeArgumentSolution.arguments) =
      some [.integer, .boolean] := by decide

-- Conflicting constraints and undetermined variables do not get defaults.
example : (inferTypeArguments 60 0 (header 1 [.var 0, .var 0])
    [.integer, .boolean]).isSome = false := by decide
example : (inferTypeArguments 60 0 (header 2 [.var 0]) [.integer]).isSome = false := by decide
example : (inferTypeArguments 60 0 (header 1 []) []).isSome = false := by decide

-- Caller variables stay rigid, even when their indices match callee variables.
-- This is the growing instantiation needed for polymorphic recursion.
example : ((inferTypeArguments 60 1 (header 1 [.var 0]) [.list (.var 0)]).map
    TypeArgumentSolution.arguments) = some [.list (.var 0)] := by decide

-- A candidate mentioning a variable outside the caller's scope is rejected.
example : (inferTypeArguments 60 0 (header 1 [.var 0]) [.list (.var 0)]).isSome = false := by decide

#print axioms inferred_arguments_unique
#print axioms type_argument_solution_unique
#print axioms inferTypeArguments
