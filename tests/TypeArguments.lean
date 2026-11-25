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

-- Successful nested C-style collection is sound for substitution through
-- function parameters and option results, including a rigid caller variable.
example :
    instantiateTypes [.var 2]
      [.fn [.var 0] (.option (.var 0))] =
      [.fn [.var 2] (.option (.var 2))] := by
  have collected : collectArguments 8
      [.fn [.var 0] (.option (.var 0))]
      [.fn [.var 2] (.option (.var 2))]
      [none] = some [some (.var 2)] := by decide
  have patternWellFormed : ∀ (type : Ty),
      type ∈ ([.fn [.var 0] (.option (.var 0))] : List Ty) → type.wellFormed 1 := by
    intro type member
    have same : type = .fn [.var 0] (.option (.var 0)) := by simpa using member
    subst type
    simp [Ty.wellFormed]
  have assignmentsAgree : AssignmentsAgree [.var 2] [some (.var 2)] := by
    intro index value assigned
    cases index with
    | zero =>
        simpa [getElem?_def] using assigned
    | succ index =>
        have impossible : ¬ index + 1 < 1 := by omega
        simp [getElem?_def, impossible] at assigned ⊢
  simpa [instantiateTypes] using collectArguments_sound 8
    [.fn [.var 0] (.option (.var 0))]
    [.fn [.var 2] (.option (.var 2))]
    [.var 2] [none] [some (.var 2)]
    patternWellFormed collected assignmentsAgree

-- A candidate mentioning a variable outside the caller's scope is rejected.
example : (inferTypeArguments 60 0 (header 1 [.var 0]) [.list (.var 0)]).isSome = false := by decide

#print axioms inferred_arguments_unique
#print axioms type_argument_solution_unique
#print axioms inferTypeArguments
