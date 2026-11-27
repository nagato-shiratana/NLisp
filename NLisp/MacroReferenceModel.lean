import NLisp.CExpansion
import NLisp.MacroTermination

/-!
  A small executable reference model for the part of C macro expansion used in
  the paper experiment.  It deliberately starts after decoding and typing.
  `CMacroCopy` is used for the hygienic copy operation; this file supplies the
  missing outer machine which repeatedly selects and expands a macro call.
-/
namespace NLisp.MacroReferenceModel

open CMacroCopy CExpansion MacroTermination

inductive RunResult where
  | completed (tree : Tree) (fresh : Nat)
  | fuelExhausted (tree : Tree) (fresh : Nat)
  | failed (tree : Tree) (fresh : Nat)
  deriving Repr

inductive StepResult where
  | progressed (tree : Tree) (fresh : Nat)
  | noRedex
  | failed
  deriving Inhabited

def ruleOrigin (rule : Nat × Tree) : Nat := rule.1

def tryRoot (rules : List (Nat × Tree)) (fuel fresh : Nat) (input : Tree) :
    StepResult :=
  match rules with
  | [] => .noRedex
  | (origin, rule) :: tail =>
      match matchRule rule input with
      | some (holes, template) =>
          match copyWithMacros (macroNames rules) fuel origin holes [] fresh template with
          | some (output, final) => .progressed output final
          | none => .failed
      | none => tryRoot tail fuel fresh input

partial def hasRootRedex (rules : List (Nat × Tree)) (input : Tree) : Bool :=
  match rules with
  | [] => false
  | (_, rule) :: tail =>
      if (matchRule rule input).isSome then true else hasRootRedex tail input

partial def hasRedex (rules : List (Nat × Tree)) : Tree → Bool
  | input =>
      if hasRootRedex rules input then true else
        match input with
        | .atom _ => false
        | .list items => items.any (hasRedex rules)

mutual
  partial def stepAt (rules : List (Nat × Tree)) (fuel fresh : Nat) : Tree → StepResult
    | input =>
        match tryRoot rules fuel fresh input with
        | .progressed output final => .progressed output final
        | .failed => .failed
        | .noRedex =>
            match input with
            | .atom _ => .noRedex
            | .list items => stepItems rules fuel fresh items

  partial def stepItems (rules : List (Nat × Tree)) (fuel fresh : Nat) : List Tree → StepResult
    | [] => .noRedex
    | head :: tail =>
        match stepAt rules fuel fresh head with
        | .progressed head' final => .progressed (.list (head' :: tail)) final
        | .failed => .failed
        | .noRedex =>
            match stepItems rules fuel fresh tail with
            | .progressed (.list tail') final => .progressed (.list (head :: tail')) final
            | .progressed tail' final => .progressed (.list (head :: [tail'])) final
            | .failed => .failed
            | .noRedex => .noRedex
end

def run (rules : List (Nat × Tree)) : Nat → Nat → Tree → RunResult
  | 0, fresh, tree =>
      if hasRedex rules tree then .fuelExhausted tree fresh else .completed tree fresh
  | fuel + 1, fresh, tree =>
      match stepAt rules (fuel + 1) fresh tree with
      | .noRedex => .completed tree fresh
      | .failed => .failed tree fresh
      | .progressed tree' fresh' => run rules fuel fresh' tree'

partial def normalize : Tree → Tree
  | .atom a => .atom { a with origin := none, token := 0 }
  | .list items => .list (items.map normalize)

def completedTree : RunResult → Option Tree
  | .completed tree _ => some (normalize tree)
  | .fuelExhausted _ _ => none
  | .failed _ _ => none

def status : RunResult → String
  | .completed _ _ => "completed"
  | .fuelExhausted _ _ => "fuel-exhausted"
  | .failed _ _ => "failed"

/- A metadata-free, deterministic serialization used by the external C bridge.
   It intentionally serializes only syntax names and list shape. -/
partial def syntaxKey : Tree → String
  | .atom a => "A" ++ a.name ++ ";"
  | .list items => "L" ++ items.foldl (fun acc item => acc ++ syntaxKey item) "" ++ "E"

def resultKey : RunResult → String
  | .completed tree _ => "completed|" ++ syntaxKey (normalize tree)
  | .fuelExhausted _ _ => "fuel-exhausted"
  | .failed _ _ => "failed"

inductive RankStatus where
  | proven
  | unproved
  deriving DecidableEq, Repr

def rankStatus (edges : List Edge) (ranks : List Nat) : RankStatus :=
  if checkRanks edges ranks then .proven else .unproved

def rankStatusName : RankStatus → String
  | .proven => "proven"
  | .unproved => "unproved"

/- The C export contains an ordered macro trace.  For the fixed experiment,
   the caller/callee rule indices supplied by the trace are checked against
   the accepted static graph in order.  A missing edge is reported as
   `unproved`; it is never interpreted as divergence. -/
def rankTraceStatus (edges : List Edge) (ranks : List Nat) : List Nat → RankStatus
  | [] | [_] => .proven
  | parent :: child :: tail =>
      if decide ((child, parent) ∈ edges) &&
          decide (rank ranks child < rank ranks parent) then
        rankTraceStatus edges ranks (child :: tail)
      else .unproved

def GoodRankTrace (edges : List Edge) (ranks : List Nat) : List Nat → Prop
  | [] | [_] => True
  | parent :: child :: tail =>
      Calls edges child parent ∧ rank ranks child < rank ranks parent ∧
        GoodRankTrace edges ranks (child :: tail)

theorem rankTraceStatus_proven
    (edges : List Edge) (ranks : List Nat) (trace : List Nat)
    (good : GoodRankTrace edges ranks trace) :
    rankTraceStatus edges ranks trace = .proven := by
  induction trace with
  | nil => rfl
  | cons parent tail ih =>
      cases tail with
      | nil => rfl
      | cons child rest =>
          have edge := good.1
          have smaller := good.2.2
          have edgeBool : decide ((child, parent) ∈ edges) = true :=
            decide_eq_true_eq.mpr edge
          simp [rankTraceStatus, edgeBool, good.2.1, ih smaller]

theorem goodRankTrace_noInfiniteChain (edges : List Edge) (ranks : List Nat)
    (accepted : checkRanks edges ranks = true) (chain : Nat → Nat)
    (step : ∀ index, Calls edges (chain (index + 1)) (chain index)) : False :=
  no_infinite_call_chain accepted chain step

structure Comparison where
  cResult : RunResult
  leanResult : RunResult
  normalizedC : Option Tree
  normalizedLean : Option Tree
  equal : Bool
  deriving Repr

noncomputable def compare (cResult leanResult : RunResult) : Comparison :=
  let c := completedTree cResult
  let l := completedTree leanResult
  { cResult := cResult
    leanResult := leanResult
    normalizedC := c
    normalizedLean := l
    equal := match c, l with
      | some cTree, some leanTree => decide (cTree = leanTree)
      | _, _ => false }

theorem rankStatus_proven_iff (edges : List Edge) (ranks : List Nat) :
    rankStatus edges ranks = .proven ↔ checkRanks edges ranks = true := by
  simp [rankStatus]

end NLisp.MacroReferenceModel
