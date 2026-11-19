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

#print axioms GlobalIR.initialization_length
#print axioms GlobalIR.initialized_prefix_unchanged
#print axioms GlobalIR.initialized_cells_present
