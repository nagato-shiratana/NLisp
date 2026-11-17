import NLisp.CExpansion

namespace NLisp.MacroTermination
open CMacroCopy CExpansion

abbrev Edge := Nat × Nat -- child, parent

def signature : Tree → Option (String × Nat)
  | .list [.list (.atom head :: parameters), _, _, _] => some (head.name, parameters.length)
  | _ => none

def findRule (name : String) (arity : Nat) : Nat → List (Nat × Tree) → Option Nat
  | _, [] => none
  | index, (_, rule) :: tail =>
      if signature rule = some (name, arity) then some index else findRule name arity (index + 1) tail

def parameters : Tree → Option (List String × Tree)
  | .list [.list (_ :: names), _, _, template] => do
      let holes ← names.mapM (fun tree => match tree with
        | .atom a => some a.name
        | _ => none)
      pure (holes, template)
  | _ => none

/- Conservative call extraction. A hole in head position can manufacture a
new call; no static termination certificate is issued for such templates.
Scanning annotations too only adds edges and may reduce completeness. -/
structure CallOperations where
  calls : List (Nat × Tree) → List String → Tree → Option (List Nat)
  callsMany : List (Nat × Tree) → List String → List Tree → Option (List Nat)

def callOperations : Nat → CallOperations
  | 0 => ⟨fun _ _ _ => none, fun _ _ _ => none⟩
  | fuel + 1 =>
      let previous := callOperations fuel
      { calls := fun rules holes tree =>
          match tree with
          | .atom _ => some []
          | .list items => do
              let nested ← previous.callsMany rules holes items
              match items with
              | .atom head :: arguments =>
                  if head.name ∈ holes then none else
                  match findRule head.name arguments.length 0 rules with
                  | some target => pure (target :: nested)
                  | none => pure nested
              | _ => pure nested
        callsMany := fun rules holes trees =>
          match trees with
          | [] => some []
          | head :: tail => do
              return (← previous.calls rules holes head) ++ (← previous.callsMany rules holes tail) }

def calls (fuel : Nat) := (callOperations fuel).calls
def callsMany (fuel : Nat) := (callOperations fuel).callsMany

def graphRows (fuel : Nat) (rules : List (Nat × Tree)) : Nat → List (Nat × Tree) → Option (List Edge)
  | _, [] => some []
  | index, (_, rule) :: tail => do
      let (holes, template) ← parameters rule
      let dependencies ← calls fuel rules holes template
      let remaining ← graphRows fuel rules (index + 1) tail
      pure (dependencies.map (fun child => (child, index)) ++ remaining)

def graph (fuel : Nat) (rules : List (Nat × Tree)) : Option (List Edge) := graphRows fuel rules 0 rules

def rank (ranks : List Nat) (node : Nat) : Nat := (ranks[node]?).getD 0

def checkRanks (edges : List Edge) (ranks : List Nat) : Bool :=
  edges.all (fun edge => decide (rank ranks edge.1 < rank ranks edge.2))

def Calls (edges : List Edge) (child parent : Nat) : Prop := (child, parent) ∈ edges

theorem checkRanks_decreases (accepted : checkRanks edges ranks = true)
    (edge : Calls edges child parent) : rank ranks child < rank ranks parent := by
  have all := List.all_eq_true.mp accepted
  exact of_decide_eq_true (all (child, parent) edge)

/- This is Lean's ordinary well-founded recursion mechanism, with the
certificate's rule rank as termination_by measure. It constructs accessibility
for every node rather than merely testing a recursion-depth threshold. -/
def accessible (edges : List Edge) (ranks : List Nat)
    (accepted : checkRanks edges ranks = true) (node : Nat) : Acc (Calls edges) node :=
  Acc.intro node (fun child _edge => accessible edges ranks accepted child)
termination_by rank ranks node
decreasing_by exact checkRanks_decreases accepted _edge

theorem ranked_graph_wellFounded (accepted : checkRanks edges ranks = true) :
    WellFounded (Calls edges) := ⟨accessible edges ranks accepted⟩

/- A path is a finite prefix of nested recursive invocations. -/
inductive Path (edges : List Edge) : Nat → Nat → Nat → Prop where
  | zero (node : Nat) : Path edges node node 0
  | step : Calls edges next first → Path edges next last count →
      Path edges first last (count + 1)

theorem path_length_bounded (accepted : checkRanks edges ranks = true)
    (path : Path edges first last count) : count + rank ranks last ≤ rank ranks first := by
  induction path with
  | zero _ => omega
  | step edge _ ih =>
      have decrease := checkRanks_decreases accepted edge
      omega

end NLisp.MacroTermination
