import NLisp.Surface

namespace NLisp.Surface

mutual
def typeDecEq (a b : Ty) : Decidable (a = b) := by
  cases a <;> cases b
  all_goals first
    | solve | apply isTrue; rfl
    | solve | apply isFalse; intro h; cases h
  case var.var a b =>
    exact decidable_of_iff (a = b) (by simp)
  case fn.fn args result args' result' =>
    letI := typesDecEq args args'
    letI := typeDecEq result result'
    exact decidable_of_iff (args = args' ∧ result = result') (by simp)
  case list.list a b =>
    letI := typeDecEq a b
    exact decidable_of_iff (a = b) (by simp)
  case option.option a b =>
    letI := typeDecEq a b
    exact decidable_of_iff (a = b) (by simp)
termination_by sizeOf a + sizeOf b
decreasing_by all_goals simp_wf; omega

def typesDecEq (a b : List Ty) : Decidable (a = b) :=
  match a, b with
  | [], [] => isTrue rfl
  | [], _ :: _ => isFalse (by intro h; cases h)
  | _ :: _, [] => isFalse (by intro h; cases h)
  | x :: xs, y :: ys =>
    letI := typeDecEq x y
    letI := typesDecEq xs ys
    decidable_of_iff (x = y ∧ xs = ys) (by simp)
termination_by sizeOf a + sizeOf b
decreasing_by all_goals simp_wf; omega
end

instance : DecidableEq Ty := typeDecEq

end NLisp.Surface
