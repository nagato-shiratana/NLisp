import NLisp.GlobalIR

open NLisp

-- Functions 0/1 are make/main; getters 2/3 read early/offset respectively.
private def escaped : GlobalIR.Program where
  definitions := [
    .function ⟨0, .lam 0 (.app (.global 3) [])⟩,
    .function ⟨0, .app (.app (.global 2) []) []⟩,
    .getter 0, .getter 1]
  initializers := [.app (.global 0) [], .int 42]
  entry := 1

private def resultInteger : Except GlobalIR.Fault PolyIR.Value → Option Int
  | .ok (.int value) => some value
  | _ => none

example : resultInteger (GlobalIR.run escaped 40) = some 42 := by decide

-- Getter reads are delayed until the closure is called in the completed store.
example : (GlobalIR.evaluate escaped.definitions [none, none] 20 [] (.global 3)).isOk = true := by decide
example : GlobalIR.evaluate escaped.definitions [none, none] 20 [] (.app (.global 3) []) =
    .error (.beforeInitialization 1) := by rfl

-- The getter is independent of similarly positioned local variables.
example : resultInteger (GlobalIR.evaluate escaped.definitions [none, some (.int 42)] 20 [.int 10]
    (.app (.global 3) [])) = some 42 := by decide

private def divergingDefinitions : List GlobalIR.Definition :=
  [.function ⟨0, .app (.global 0) []⟩]

example : GlobalIR.Diverges divergingDefinitions [] [] (.app (.global 0) []) :=
  GlobalIR.recursive_getter_call_diverges

example : GlobalIR.initializeValues divergingDefinitions 20 [] 0
    [.app (.global 0) [], .int 42] = .error (.core .outOfFuel) := by
  exact GlobalIR.initializeValues_stops_on_divergence divergingDefinitions [] 0 19
    (.app (.global 0) []) [.int 42] GlobalIR.recursive_getter_call_diverges

-- The lowering map contains global-value definition indices only. Local
-- variables and ordinary function callees stay as they were.
example : GlobalIR.lowerGlobalReads [(4, 8)] (.var 4) = .var 4 :=
  GlobalIR.lowerGlobalReads_local [(4, 8)] 4
example : GlobalIR.lowerGlobalReads [(4, 8)] (.global 4) = .app (.global 8) [] :=
  GlobalIR.lowerGlobalReads_global_getter [(4, 8)] 4 8 rfl
example : GlobalIR.lowerGlobalReads [(4, 8)] (.global 2) = .global 2 :=
  GlobalIR.lowerGlobalReads_global_function [(4, 8)] 2 rfl
example : GlobalIR.lowerGlobalReads [(4, 8)] (.app (.global 2) [.global 4]) =
    .app (.global 2) [.app (.global 8) []] := by rfl
example : GlobalIR.lowerGlobalReads [(4, 8)] (.app (.global 4) [.int 7]) =
    .app (.app (.global 8) []) [.int 7] := by rfl

#print axioms GlobalIR.initialization_length
#print axioms GlobalIR.initialized_prefix_unchanged
#print axioms GlobalIR.initialized_cells_present
#print axioms GlobalIR.evaluate_lambda_store_independent
#print axioms GlobalIR.getter_call_reads_current_store
#print axioms GlobalIR.getter_call_reports_early_read
#print axioms GlobalIR.initializeValues_stops_on_error
#print axioms GlobalIR.initializeValues_commits_head
#print axioms GlobalIR.recursive_getter_call_diverges
#print axioms GlobalIR.initializeValues_stops_on_divergence
