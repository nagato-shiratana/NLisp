import NLisp.ExpansionLowering

namespace NLisp.Surface
open ExpansionLowering

private theorem range_loop_member (n index : Nat) (acc : List Nat)
    (h : index < n ∨ index ∈ acc) : index ∈ List.range.loop n acc := by
  induction n generalizing acc with
  | zero => simpa [List.range.loop, Nat.not_lt_zero] using h
  | succ n ih =>
    apply ih
    rcases h with bound | member
    · by_cases same : index = n
      · exact Or.inr (by simp [same])
      · exact Or.inl (by omega)
    · exact Or.inr (List.mem_cons_of_mem n member)

private theorem below_member_range {index count : Nat} (bound : index < count) :
    index ∈ List.range count := range_loop_member count index [] (Or.inl bound)

/- Every occurrence of a quantified variable determines the corresponding
argument. Candidates are compared as syntax, with caller variables rigid. -/
theorem occurrence_determines (fuel : Nat) (typeIndex : Nat) (left right : List Ty)
    (bound : typeIndex < left.length) (sameLength : left.length = right.length) :
    (∀ type, occurs fuel typeIndex type = true →
      Ty.instantiate left type = Ty.instantiate right type → left[typeIndex]? = right[typeIndex]?) ∧
    (∀ types, occursMany fuel typeIndex types = true →
      instantiateTypes left types = instantiateTypes right types → left[typeIndex]? = right[typeIndex]?) := by
  induction fuel with
  | zero => simp [occurs, occursMany]
  | succ fuel ih =>
    refine ⟨?_, ?_⟩
    · intro type occurrence same
      cases type with
      | boolean | integer | unit => simp [occurs] at occurrence
      | var i =>
        have eq : i = typeIndex := by simpa [occurs] using occurrence
        subst i
        have otherBound : typeIndex < right.length := by omega
        simpa [Ty.instantiate, getElem?_def, bound, otherBound] using same
      | fn parameters result =>
        simp only [occurs, Bool.or_eq_true] at occurrence
        simp only [Ty.instantiate] at same
        have parts := Ty.fn.inj same
        rcases occurrence with fromParameters | fromResult
        · exact ih.2 parameters fromParameters parts.1
        · exact ih.1 result fromResult parts.2
      | list element =>
        simp only [occurs] at occurrence
        simp only [Ty.instantiate] at same
        exact ih.1 element occurrence (Ty.list.inj same)
      | option element =>
        simp only [occurs] at occurrence
        simp only [Ty.instantiate] at same
        exact ih.1 element occurrence (Ty.option.inj same)
    · intro types occurrence same
      cases types with
      | nil => simp [occursMany] at occurrence
      | cons head tail =>
        simp only [occursMany, Bool.or_eq_true] at occurrence
        simp only [instantiateTypes] at same
        have parts := List.cons.inj same
        rcases occurrence with fromHead | fromTail
        · exact ih.1 head fromHead parts.1
        · exact ih.2 tail fromTail parts.2

theorem inferred_arguments_unique (fuel : Nat) (header : Header)
    (accepted : inferrable fuel header = true) (left right : List Ty)
    (leftArity : left.length = header.variables.length)
    (rightArity : right.length = header.variables.length)
    (same : instantiateTypes left (header.parameters.map Prod.snd) =
      instantiateTypes right (header.parameters.map Prod.snd)) : left = right := by
  apply List.ext_get (by omega)
  intro index leftBound rightBound
  have bound : index < header.variables.length := by omega
  have occurrence : occursMany fuel index (header.parameters.map Prod.snd) = true :=
    List.all_eq_true.mp accepted index (below_member_range bound)
  have sameLookup := (occurrence_determines fuel index left right leftBound (by omega)).2 _ occurrence same
  simpa [getElem?_def, leftBound, rightBound] using sameLookup

mutual
def collectArgument : Nat → Ty → Ty → List (Option Ty) → Option (List (Option Ty))
  | 0, _, _, _ => none
  | fuel + 1, pattern, actual, assignments =>
    match pattern with
    | .var index =>
      match assignments[index]? with
      | none => none
      | some none => some (assignments.set index (some actual))
      | some (some previous) => if previous = actual then some assignments else none
    | .boolean => if actual = .boolean then some assignments else none
    | .integer => if actual = .integer then some assignments else none
    | .unit => if actual = .unit then some assignments else none
    | .fn parameters result =>
      match actual with
      | .fn inputs output => do
        let next ← collectArguments fuel parameters inputs assignments
        collectArgument fuel result output next
      | _ => none
    | .list element =>
      match actual with
      | .list input => collectArgument fuel element input assignments
      | _ => none
    | .option element =>
      match actual with
      | .option input => collectArgument fuel element input assignments
      | _ => none

def collectArguments : Nat → List Ty → List Ty → List (Option Ty) → Option (List (Option Ty))
  | 0, _, _, _ => none
  | fuel + 1, patterns, actuals, assignments =>
    match patterns, actuals with
    | [], [] => some assignments
    | pattern :: patterns, actual :: actuals => do
      let next ← collectArgument fuel pattern actual assignments
      collectArguments fuel patterns actuals next
    | _, _ => none
end

structure TypeArgumentSolution (callerCount : Nat) (header : Header) (actuals : List Ty) where
  arguments : List Ty
  arity : arguments.length = header.variables.length
  valid : ∀ t ∈ arguments, t.wellFormed callerCount
  instantiates : instantiateTypes arguments (header.parameters.map Prod.snd) = actuals
  unique : ∀ other, other.length = header.variables.length →
    instantiateTypes other (header.parameters.map Prod.snd) = actuals → other = arguments

/- No expected return type is an input. Caller type variables appearing in
actuals are rigid syntax; they are never recursively solved or unified. -/
def inferTypeArguments (fuel callerCount : Nat) (header : Header) (actuals : List Ty) :
    Option (TypeArgumentSolution callerCount header actuals) := do
  if covered : inferrable fuel header = true then
    let assignments ← collectArguments fuel (header.parameters.map Prod.snd) actuals
      (List.replicate header.variables.length none)
    let arguments ← assignments.mapM (fun value => value)
    let valid ← checkTypesWF fuel callerCount arguments
    if arity : arguments.length = header.variables.length then
      if matched : instantiateTypes arguments (header.parameters.map Prod.snd) = actuals then
        pure ⟨arguments, arity, valid.down, matched, fun other otherArity otherMatches =>
          inferred_arguments_unique fuel header covered other arguments otherArity arity
            (otherMatches.trans matched.symm)⟩
      else none
    else none
  else none

theorem type_argument_solution_unique (first second : TypeArgumentSolution callerCount header actuals) :
    first.arguments = second.arguments := first.unique second.arguments second.arity second.instantiates |>.symm

end NLisp.Surface
