import NLisp.ProcessCertificate
import NLisp.NamedArithmeticReflection

namespace NLisp.CertifiedArithmeticReflection

open NLisp

/- A single artifact packages a checked source/expansion/scope certificate
and a mixed top-level decode result identifying one closed arithmetic
initializer. The syntax fragment is explicit because general evaluation
reflection is still outstanding. -/
structure CheckedArithmeticInitializer where
  expansion : ProcessCertificate.CheckedExpansion
  decodeFuel : Nat
  definitions : Named.Definitions
  slotTypes : List Surface.Ty
  initializers : List Named.Expr
  decoded : Named.decodeTopLevelProgram decodeFuel expansion.annotated =
    some (definitions, slotTypes, initializers)
  expression : Named.Expr
  member : expression ∈ initializers
  fragment : Named.ArithmeticFragment expression

/- Generic certificate payload for any initializer whose semantic reflection
proofs have been established. The source and expansion evidence is shared by
all syntax fragments; only the three semantic obligations vary. -/
structure CheckedSourceInitializer where
  expansion : ProcessCertificate.CheckedExpansion
  decodeFuel : Nat
  definitions : Named.Definitions
  slotTypes : List Surface.Ty
  initializers : List Named.Expr
  decoded : Named.decodeTopLevelProgram decodeFuel expansion.annotated =
    some (definitions, slotTypes, initializers)
  expression : Named.Expr
  member : expression ∈ initializers
  reflection : ∀ (value : PolyIR.Value),
    PolyIR.Evaluates (Named.lowerDefinitions definitions) []
      (Named.lower [] expression) value →
    ∃ sourceValue, Named.Evaluates definitions [] expression sourceValue ∧
      Named.lowerValue sourceValue = value
  termination : Named.SourceTerminates definitions [] expression ↔
    Named.LoweredTerminates definitions [] expression
  divergence : Named.SourceDiverges definitions [] expression ↔
    Named.LoweredDiverges definitions [] expression

/-- A certificate for any initializer in the currently compositional
reflection fragment, including arbitrary-arity calls and finite begin/let
sequences. -/
structure CheckedCompositionalInitializer where
  expansion : ProcessCertificate.CheckedExpansion
  decodeFuel : Nat
  definitions : Named.Definitions
  slotTypes : List Surface.Ty
  initializers : List Named.Expr
  decoded : Named.decodeTopLevelProgram decodeFuel expansion.annotated =
    some (definitions, slotTypes, initializers)
  expression : Named.Expr
  member : expression ∈ initializers
  fragment : Named.CompositionalReflectionFragment definitions expression

def CheckedCompositionalInitializer.toCheckedSourceInitializer
    (certificate : CheckedCompositionalInitializer) : CheckedSourceInitializer where
  expansion := certificate.expansion
  decodeFuel := certificate.decodeFuel
  definitions := certificate.definitions
  slotTypes := certificate.slotTypes
  initializers := certificate.initializers
  decoded := certificate.decoded
  expression := certificate.expression
  member := certificate.member
  reflection := by
    intro value evaluated
    obtain ⟨programScoped, initializersAligned⟩ := Named.decodeTopLevelProgram_wellScoped
      certificate.decodeFuel certificate.expansion.annotated certificate.definitions
      certificate.slotTypes certificate.initializers certificate.decoded
    obtain ⟨sourceValue, sourceEvaluation, lowers, _valueScoped⟩ :=
      Named.compositionalReflection_evaluation_reflected_scoped
        certificate.definitions programScoped certificate.expression certificate.fragment
        [] Named.EnvironmentWellScoped.nil
        (initializersAligned certificate.expression certificate.member) value evaluated
    exact ⟨sourceValue, sourceEvaluation, lowers⟩
  termination := Named.compositionalReflection_termination_iff
    certificate.definitions certificate.expression certificate.fragment []
  divergence := Named.compositionalReflection_divergence_iff
    certificate.definitions certificate.expression certificate.fragment []


/-- General proof-certificate main theorem: source reading, normalization,
finite expansion, freshness, binding correspondence, termination and
divergence all follow from a single certificate, for any initializer syntax
with supplied semantic reflection evidence. -/
theorem checked_source_initializer_main (certificate : CheckedSourceInitializer) :
    certificate.expansion.text.toUTF8.data.data = certificate.expansion.bytes ∧
    SourceReader.readWithFuel certificate.expansion.lexFuel
      certificate.expansion.parseFuel certificate.expansion.text =
        some certificate.expansion.parsed ∧
    SourceReader.normalize certificate.expansion.parsed =
      some certificate.expansion.normalized ∧
    CExpansion.Expands
      (CExpansion.sourceRules 0 certificate.expansion.normalized)
      (.list (CExpansion.programForms certificate.expansion.normalized))
      (.list certificate.expansion.expanded) ∧
    CExpansion.disjointIntervals
      (ExpansionCertificate.freshIntervals certificate.expansion.localCertificate) = true ∧
    certificate.expansion.annotated.map CBindingWalk.Node.erase =
      certificate.expansion.expanded ∧
    (∃ sites, CBindingWalk.references certificate.expansion.scopeFuel
        certificate.expansion.annotated CBindingWalk.builtinEnvironment = some sites ∧
        ∀ site ∈ sites, CBindingWalk.Corresponds site) ∧
    Named.programWellScoped certificate.definitions ∧
    (∀ initializer ∈ certificate.initializers,
      Named.letLayoutsAligned initializer = true) ∧
    (Named.SourceTerminates certificate.definitions [] certificate.expression ↔
      Named.LoweredTerminates certificate.definitions [] certificate.expression) ∧
    (Named.SourceDiverges certificate.definitions [] certificate.expression ↔
      Named.LoweredDiverges certificate.definitions [] certificate.expression) := by
  obtain ⟨bytesMatch, parsed, normalized, expands, fresh, sameSyntax, scopes⟩ :=
    ProcessCertificate.source_expands_with_scopes_and_freshness certificate.expansion
  obtain ⟨programScoped, initializersAligned⟩ := Named.decodeTopLevelProgram_wellScoped
    certificate.decodeFuel certificate.expansion.annotated certificate.definitions
    certificate.slotTypes certificate.initializers certificate.decoded
  exact ⟨bytesMatch, parsed, normalized, expands, fresh, sameSyntax, scopes,
    programScoped, initializersAligned,
    certificate.termination, certificate.divergence⟩

theorem checked_source_initializer_value (certificate : CheckedSourceInitializer)
    (value : PolyIR.Value)
    (evaluated : PolyIR.Evaluates (Named.lowerDefinitions certificate.definitions) []
      (Named.lower [] certificate.expression) value) :
    ∃ sourceValue,
      Named.Evaluates certificate.definitions [] certificate.expression sourceValue ∧
      Named.lowerValue sourceValue = value ∧ Named.valueWellScoped sourceValue := by
  obtain ⟨sourceValue, sourceEvaluation, lowers⟩ := certificate.reflection value evaluated
  have sourceScoped := Named.decodeTopLevel_initializer_evaluation_preserves_valueWellScoped
    certificate.decodeFuel certificate.expansion.annotated certificate.definitions
    certificate.slotTypes certificate.initializers certificate.decoded []
    certificate.expression sourceValue certificate.member
    Named.EnvironmentWellScoped.nil sourceEvaluation
  exact ⟨sourceValue, sourceEvaluation, lowers, sourceScoped⟩

theorem checked_source_initializer_main_with_value
    (certificate : CheckedSourceInitializer) (value : PolyIR.Value)
    (evaluated : PolyIR.Evaluates (Named.lowerDefinitions certificate.definitions) []
      (Named.lower [] certificate.expression) value) :
    (certificate.expansion.text.toUTF8.data.data = certificate.expansion.bytes ∧
      SourceReader.readWithFuel certificate.expansion.lexFuel
        certificate.expansion.parseFuel certificate.expansion.text =
          some certificate.expansion.parsed ∧
      SourceReader.normalize certificate.expansion.parsed =
        some certificate.expansion.normalized ∧
      CExpansion.Expands
        (CExpansion.sourceRules 0 certificate.expansion.normalized)
        (.list (CExpansion.programForms certificate.expansion.normalized))
        (.list certificate.expansion.expanded) ∧
      CExpansion.disjointIntervals
        (ExpansionCertificate.freshIntervals certificate.expansion.localCertificate) = true ∧
      certificate.expansion.annotated.map CBindingWalk.Node.erase =
        certificate.expansion.expanded ∧
      (∃ sites, CBindingWalk.references certificate.expansion.scopeFuel
          certificate.expansion.annotated CBindingWalk.builtinEnvironment = some sites ∧
        ∀ site ∈ sites, CBindingWalk.Corresponds site) ∧
      Named.programWellScoped certificate.definitions ∧
      (∀ initializer ∈ certificate.initializers,
        Named.letLayoutsAligned initializer = true) ∧
      (Named.SourceTerminates certificate.definitions [] certificate.expression ↔
        Named.LoweredTerminates certificate.definitions [] certificate.expression) ∧
      (Named.SourceDiverges certificate.definitions [] certificate.expression ↔
        Named.LoweredDiverges certificate.definitions [] certificate.expression)) ∧
    (∃ sourceValue,
      Named.Evaluates certificate.definitions [] certificate.expression sourceValue ∧
      Named.lowerValue sourceValue = value ∧ Named.valueWellScoped sourceValue) := by
  exact ⟨checked_source_initializer_main certificate,
    checked_source_initializer_value certificate value evaluated⟩

/-- The unified source/expansion/scope/semantics theorem accepts every
initializer in `CompositionalReflectionFragment`. -/
def checked_compositional_initializer_main
    (certificate : CheckedCompositionalInitializer) :=
  checked_source_initializer_main certificate.toCheckedSourceInitializer

/-- The unified certificate also returns a reflected source value with
closure-scope safety for any terminating lowered initializer in this
fragment. -/
def checked_compositional_initializer_main_with_value
    (certificate : CheckedCompositionalInitializer) (value : PolyIR.Value)
    (evaluated : PolyIR.Evaluates (Named.lowerDefinitions certificate.definitions) []
      (Named.lower [] certificate.expression) value) :=
  checked_source_initializer_main_with_value certificate.toCheckedSourceInitializer
    value evaluated

def CheckedArithmeticInitializer.toCheckedSourceInitializer
    (certificate : CheckedArithmeticInitializer) : CheckedSourceInitializer where
  expansion := certificate.expansion
  decodeFuel := certificate.decodeFuel
  definitions := certificate.definitions
  slotTypes := certificate.slotTypes
  initializers := certificate.initializers
  decoded := certificate.decoded
  expression := certificate.expression
  member := certificate.member
  reflection := by
    intro value evaluated
    obtain ⟨sourceValue, sourceEvaluation, lowers, _sourceScoped⟩ :=
      Named.decodedInitializer_arithmetic_evaluation_reflected
        certificate.decodeFuel certificate.expansion.annotated certificate.definitions
        certificate.slotTypes certificate.initializers certificate.decoded
        certificate.expression certificate.member certificate.fragment [] value
        Named.EnvironmentWellScoped.nil evaluated
    exact ⟨sourceValue, sourceEvaluation, lowers⟩
  termination := Named.arithmeticFragment_termination_preserved_and_reflected
    certificate.definitions [] certificate.expression certificate.fragment
  divergence := Named.arithmeticFragment_divergence_preserved_and_reflected
    certificate.definitions [] certificate.expression certificate.fragment

/- Reading, finite expansion, binding correspondence, freshness, and the
finite-termination/divergence correspondence are reported by one theorem
from the packaged certificate. -/
theorem checked_initializer_main (certificate : CheckedArithmeticInitializer) :
    certificate.expansion.text.toUTF8.data.data = certificate.expansion.bytes ∧
    SourceReader.readWithFuel certificate.expansion.lexFuel
      certificate.expansion.parseFuel certificate.expansion.text =
        some certificate.expansion.parsed ∧
    SourceReader.normalize certificate.expansion.parsed =
      some certificate.expansion.normalized ∧
    CExpansion.Expands
      (CExpansion.sourceRules 0 certificate.expansion.normalized)
      (.list (CExpansion.programForms certificate.expansion.normalized))
      (.list certificate.expansion.expanded) ∧
    CExpansion.disjointIntervals
      (ExpansionCertificate.freshIntervals certificate.expansion.localCertificate) = true ∧
    certificate.expansion.annotated.map CBindingWalk.Node.erase =
      certificate.expansion.expanded ∧
    (∃ sites, CBindingWalk.references certificate.expansion.scopeFuel
        certificate.expansion.annotated CBindingWalk.builtinEnvironment = some sites ∧
      ∀ site ∈ sites, CBindingWalk.Corresponds site) ∧
    (Named.SourceTerminates certificate.definitions [] certificate.expression ↔
      Named.LoweredTerminates certificate.definitions [] certificate.expression) ∧
    (Named.SourceDiverges certificate.definitions [] certificate.expression ↔
      Named.LoweredDiverges certificate.definitions [] certificate.expression) := by
  have process := ProcessCertificate.source_expands_with_scopes_and_freshness
    certificate.expansion
  rcases process with ⟨bytesMatch, parsed, normalized, expands, fresh,
    sameSyntax, scopes⟩
  have termination := Named.arithmeticFragment_termination_preserved_and_reflected
    certificate.definitions [] certificate.expression certificate.fragment
  have divergence := Named.arithmeticFragment_divergence_preserved_and_reflected
    certificate.definitions [] certificate.expression certificate.fragment
  exact ⟨bytesMatch, parsed, normalized, expands, fresh, sameSyntax, scopes,
    termination, divergence⟩

/- If the certified initializer terminates in the lowered semantics, its
result reflects to the Named semantics and preserves the closure-scope
invariant supplied by successful top-level decoding. -/
theorem checked_initializer_value (certificate : CheckedArithmeticInitializer)
    (value : PolyIR.Value)
    (evaluated : PolyIR.Evaluates (Named.lowerDefinitions certificate.definitions) []
      (Named.lower [] certificate.expression) value) :
    ∃ sourceValue,
      Named.Evaluates certificate.definitions [] certificate.expression sourceValue ∧
      Named.lowerValue sourceValue = value ∧ Named.valueWellScoped sourceValue := by
  simpa using Named.decodedInitializer_arithmetic_evaluation_reflected
    certificate.decodeFuel certificate.expansion.annotated certificate.definitions
    certificate.slotTypes certificate.initializers certificate.decoded
    certificate.expression certificate.member certificate.fragment [] value
    Named.EnvironmentWellScoped.nil evaluated

/-- Main certificate theorem for a finite initializer run: source reading,
finite expansion, binding/freshness evidence, termination and divergence
correspondence, and the reflected runtime value with closure-scope safety are
available together from one certificate. -/
theorem checked_initializer_main_with_value
    (certificate : CheckedArithmeticInitializer) (value : PolyIR.Value)
    (evaluated : PolyIR.Evaluates (Named.lowerDefinitions certificate.definitions) []
      (Named.lower [] certificate.expression) value) :
    (certificate.expansion.text.toUTF8.data.data = certificate.expansion.bytes ∧
      SourceReader.readWithFuel certificate.expansion.lexFuel
        certificate.expansion.parseFuel certificate.expansion.text =
          some certificate.expansion.parsed ∧
      SourceReader.normalize certificate.expansion.parsed =
        some certificate.expansion.normalized ∧
      CExpansion.Expands
        (CExpansion.sourceRules 0 certificate.expansion.normalized)
        (.list (CExpansion.programForms certificate.expansion.normalized))
        (.list certificate.expansion.expanded) ∧
      CExpansion.disjointIntervals
        (ExpansionCertificate.freshIntervals certificate.expansion.localCertificate) = true ∧
      certificate.expansion.annotated.map CBindingWalk.Node.erase =
        certificate.expansion.expanded ∧
      (∃ sites, CBindingWalk.references certificate.expansion.scopeFuel
          certificate.expansion.annotated CBindingWalk.builtinEnvironment = some sites ∧
        ∀ site ∈ sites, CBindingWalk.Corresponds site) ∧
      (Named.SourceTerminates certificate.definitions [] certificate.expression ↔
        Named.LoweredTerminates certificate.definitions [] certificate.expression) ∧
      (Named.SourceDiverges certificate.definitions [] certificate.expression ↔
        Named.LoweredDiverges certificate.definitions [] certificate.expression)) ∧
    (∃ sourceValue,
      Named.Evaluates certificate.definitions [] certificate.expression sourceValue ∧
      Named.lowerValue sourceValue = value ∧ Named.valueWellScoped sourceValue) := by
  exact ⟨checked_initializer_main certificate,
    checked_initializer_value certificate value evaluated⟩

/- The same certificate shape can carry an arbitrary-length `begin` initializer.
Its evaluation proof is supplied by the compositional BeginFragment theorem. -/
structure CheckedBeginInitializer where
  expansion : ProcessCertificate.CheckedExpansion
  decodeFuel : Nat
  definitions : Named.Definitions
  slotTypes : List Surface.Ty
  initializers : List Named.Expr
  decoded : Named.decodeTopLevelProgram decodeFuel expansion.annotated =
    some (definitions, slotTypes, initializers)
  expression : Named.Expr
  member : expression ∈ initializers
  fragment : Named.BeginFragment expression

theorem checked_begin_initializer_main (certificate : CheckedBeginInitializer) :
    certificate.expansion.text.toUTF8.data.data = certificate.expansion.bytes ∧
    SourceReader.readWithFuel certificate.expansion.lexFuel
      certificate.expansion.parseFuel certificate.expansion.text =
        some certificate.expansion.parsed ∧
    SourceReader.normalize certificate.expansion.parsed =
      some certificate.expansion.normalized ∧
    CExpansion.Expands
      (CExpansion.sourceRules 0 certificate.expansion.normalized)
      (.list (CExpansion.programForms certificate.expansion.normalized))
      (.list certificate.expansion.expanded) ∧
    CExpansion.disjointIntervals
      (ExpansionCertificate.freshIntervals certificate.expansion.localCertificate) = true ∧
    certificate.expansion.annotated.map CBindingWalk.Node.erase =
      certificate.expansion.expanded ∧
    (∃ sites, CBindingWalk.references certificate.expansion.scopeFuel
        certificate.expansion.annotated CBindingWalk.builtinEnvironment = some sites ∧
      ∀ site ∈ sites, CBindingWalk.Corresponds site) ∧
    (Named.SourceTerminates certificate.definitions [] certificate.expression ↔
      Named.LoweredTerminates certificate.definitions [] certificate.expression) ∧
    (Named.SourceDiverges certificate.definitions [] certificate.expression ↔
      Named.LoweredDiverges certificate.definitions [] certificate.expression) := by
  have process := ProcessCertificate.source_expands_with_scopes_and_freshness
    certificate.expansion
  rcases process with ⟨bytesMatch, parsed, normalized, expands, fresh,
    sameSyntax, scopes⟩
  have termination := Named.beginFragment_termination_preserved_and_reflected
    certificate.definitions [] certificate.expression certificate.fragment
  have divergence := Named.beginFragment_divergence_preserved_and_reflected
    certificate.definitions [] certificate.expression certificate.fragment
  exact ⟨bytesMatch, parsed, normalized, expands, fresh, sameSyntax, scopes,
    termination, divergence⟩

theorem checked_begin_initializer_value (certificate : CheckedBeginInitializer)
    (value : PolyIR.Value)
    (evaluated : PolyIR.Evaluates (Named.lowerDefinitions certificate.definitions) []
      (Named.lower [] certificate.expression) value) :
    ∃ sourceValue,
      Named.Evaluates certificate.definitions [] certificate.expression sourceValue ∧
      Named.lowerValue sourceValue = value ∧ Named.valueWellScoped sourceValue := by
  obtain ⟨sourceValue, sourceEvaluation, lowers⟩ :=
    Named.beginFragment_evaluation_reflected certificate.definitions certificate.expression
      certificate.fragment [] value evaluated
  have sourceScoped := Named.decodeTopLevel_initializer_evaluation_preserves_valueWellScoped
    certificate.decodeFuel certificate.expansion.annotated certificate.definitions
    certificate.slotTypes certificate.initializers certificate.decoded []
    certificate.expression sourceValue certificate.member
    Named.EnvironmentWellScoped.nil sourceEvaluation
  exact ⟨sourceValue, sourceEvaluation, lowers, sourceScoped⟩

theorem checked_begin_initializer_main_with_value
    (certificate : CheckedBeginInitializer) (value : PolyIR.Value)
    (evaluated : PolyIR.Evaluates (Named.lowerDefinitions certificate.definitions) []
      (Named.lower [] certificate.expression) value) :
    (certificate.expansion.text.toUTF8.data.data = certificate.expansion.bytes ∧
      SourceReader.readWithFuel certificate.expansion.lexFuel
        certificate.expansion.parseFuel certificate.expansion.text =
          some certificate.expansion.parsed ∧
      SourceReader.normalize certificate.expansion.parsed =
        some certificate.expansion.normalized ∧
      CExpansion.Expands
        (CExpansion.sourceRules 0 certificate.expansion.normalized)
        (.list (CExpansion.programForms certificate.expansion.normalized))
        (.list certificate.expansion.expanded) ∧
      CExpansion.disjointIntervals
        (ExpansionCertificate.freshIntervals certificate.expansion.localCertificate) = true ∧
      certificate.expansion.annotated.map CBindingWalk.Node.erase =
        certificate.expansion.expanded ∧
      (∃ sites, CBindingWalk.references certificate.expansion.scopeFuel
          certificate.expansion.annotated CBindingWalk.builtinEnvironment = some sites ∧
        ∀ site ∈ sites, CBindingWalk.Corresponds site) ∧
      (Named.SourceTerminates certificate.definitions [] certificate.expression ↔
        Named.LoweredTerminates certificate.definitions [] certificate.expression) ∧
      (Named.SourceDiverges certificate.definitions [] certificate.expression ↔
        Named.LoweredDiverges certificate.definitions [] certificate.expression)) ∧
    (∃ sourceValue,
      Named.Evaluates certificate.definitions [] certificate.expression sourceValue ∧
      Named.lowerValue sourceValue = value ∧ Named.valueWellScoped sourceValue) := by
  exact ⟨checked_begin_initializer_main certificate,
    checked_begin_initializer_value certificate value evaluated⟩

def CheckedBeginInitializer.toCheckedSourceInitializer
    (certificate : CheckedBeginInitializer) : CheckedSourceInitializer where
  expansion := certificate.expansion
  decodeFuel := certificate.decodeFuel
  definitions := certificate.definitions
  slotTypes := certificate.slotTypes
  initializers := certificate.initializers
  decoded := certificate.decoded
  expression := certificate.expression
  member := certificate.member
  reflection := by
    intro value evaluated
    obtain ⟨sourceValue, sourceEvaluation, lowers, _⟩ :=
      checked_begin_initializer_value certificate value evaluated
    exact ⟨sourceValue, sourceEvaluation, lowers⟩
  termination := Named.beginFragment_termination_preserved_and_reflected
    certificate.definitions [] certificate.expression certificate.fragment
  divergence := Named.beginFragment_divergence_preserved_and_reflected
    certificate.definitions [] certificate.expression certificate.fragment

/- Parallel `let` initializers use the same complete source certificate. The
fragment carries the decoder-relevant binder/initializer length invariant. -/
structure CheckedLetManyInitializer where
  expansion : ProcessCertificate.CheckedExpansion
  decodeFuel : Nat
  definitions : Named.Definitions
  slotTypes : List Surface.Ty
  initializers : List Named.Expr
  decoded : Named.decodeTopLevelProgram decodeFuel expansion.annotated =
    some (definitions, slotTypes, initializers)
  expression : Named.Expr
  member : expression ∈ initializers
  fragment : Named.LetManyFragment expression

theorem checked_letMany_initializer_main (certificate : CheckedLetManyInitializer) :
    certificate.expansion.text.toUTF8.data.data = certificate.expansion.bytes ∧
    SourceReader.readWithFuel certificate.expansion.lexFuel
      certificate.expansion.parseFuel certificate.expansion.text =
        some certificate.expansion.parsed ∧
    SourceReader.normalize certificate.expansion.parsed =
      some certificate.expansion.normalized ∧
    CExpansion.Expands
      (CExpansion.sourceRules 0 certificate.expansion.normalized)
      (.list (CExpansion.programForms certificate.expansion.normalized))
      (.list certificate.expansion.expanded) ∧
    CExpansion.disjointIntervals
      (ExpansionCertificate.freshIntervals certificate.expansion.localCertificate) = true ∧
    certificate.expansion.annotated.map CBindingWalk.Node.erase =
      certificate.expansion.expanded ∧
    (∃ sites, CBindingWalk.references certificate.expansion.scopeFuel
        certificate.expansion.annotated CBindingWalk.builtinEnvironment = some sites ∧
      ∀ site ∈ sites, CBindingWalk.Corresponds site) ∧
    (Named.SourceTerminates certificate.definitions [] certificate.expression ↔
      Named.LoweredTerminates certificate.definitions [] certificate.expression) ∧
    (Named.SourceDiverges certificate.definitions [] certificate.expression ↔
      Named.LoweredDiverges certificate.definitions [] certificate.expression) := by
  have process := ProcessCertificate.source_expands_with_scopes_and_freshness
    certificate.expansion
  rcases process with ⟨bytesMatch, parsed, normalized, expands, fresh,
    sameSyntax, scopes⟩
  have termination := Named.letManyFragment_termination_preserved_and_reflected
    certificate.definitions [] certificate.expression certificate.fragment
  have divergence := Named.letManyFragment_divergence_preserved_and_reflected
    certificate.definitions [] certificate.expression certificate.fragment
  exact ⟨bytesMatch, parsed, normalized, expands, fresh, sameSyntax, scopes,
    termination, divergence⟩

theorem checked_letMany_initializer_value (certificate : CheckedLetManyInitializer)
    (value : PolyIR.Value)
    (evaluated : PolyIR.Evaluates (Named.lowerDefinitions certificate.definitions) []
      (Named.lower [] certificate.expression) value) :
    ∃ sourceValue,
      Named.Evaluates certificate.definitions [] certificate.expression sourceValue ∧
      Named.lowerValue sourceValue = value ∧ Named.valueWellScoped sourceValue := by
  obtain ⟨sourceValue, sourceEvaluation, lowers⟩ :=
    Named.letManyFragment_evaluation_reflected certificate.definitions certificate.expression
      certificate.fragment [] value evaluated
  have sourceScoped := Named.decodeTopLevel_initializer_evaluation_preserves_valueWellScoped
    certificate.decodeFuel certificate.expansion.annotated certificate.definitions
    certificate.slotTypes certificate.initializers certificate.decoded []
    certificate.expression sourceValue certificate.member
    Named.EnvironmentWellScoped.nil sourceEvaluation
  exact ⟨sourceValue, sourceEvaluation, lowers, sourceScoped⟩

theorem checked_letMany_initializer_main_with_value
    (certificate : CheckedLetManyInitializer) (value : PolyIR.Value)
    (evaluated : PolyIR.Evaluates (Named.lowerDefinitions certificate.definitions) []
      (Named.lower [] certificate.expression) value) :
    (certificate.expansion.text.toUTF8.data.data = certificate.expansion.bytes ∧
      SourceReader.readWithFuel certificate.expansion.lexFuel
        certificate.expansion.parseFuel certificate.expansion.text =
          some certificate.expansion.parsed ∧
      SourceReader.normalize certificate.expansion.parsed =
        some certificate.expansion.normalized ∧
      CExpansion.Expands
        (CExpansion.sourceRules 0 certificate.expansion.normalized)
        (.list (CExpansion.programForms certificate.expansion.normalized))
        (.list certificate.expansion.expanded) ∧
      CExpansion.disjointIntervals
        (ExpansionCertificate.freshIntervals certificate.expansion.localCertificate) = true ∧
      certificate.expansion.annotated.map CBindingWalk.Node.erase =
        certificate.expansion.expanded ∧
      (∃ sites, CBindingWalk.references certificate.expansion.scopeFuel
          certificate.expansion.annotated CBindingWalk.builtinEnvironment = some sites ∧
        ∀ site ∈ sites, CBindingWalk.Corresponds site) ∧
      (Named.SourceTerminates certificate.definitions [] certificate.expression ↔
        Named.LoweredTerminates certificate.definitions [] certificate.expression) ∧
      (Named.SourceDiverges certificate.definitions [] certificate.expression ↔
        Named.LoweredDiverges certificate.definitions [] certificate.expression)) ∧
    (∃ sourceValue,
      Named.Evaluates certificate.definitions [] certificate.expression sourceValue ∧
      Named.lowerValue sourceValue = value ∧ Named.valueWellScoped sourceValue) := by
  exact ⟨checked_letMany_initializer_main certificate,
    checked_letMany_initializer_value certificate value evaluated⟩

def CheckedLetManyInitializer.toCheckedSourceInitializer
    (certificate : CheckedLetManyInitializer) : CheckedSourceInitializer where
  expansion := certificate.expansion
  decodeFuel := certificate.decodeFuel
  definitions := certificate.definitions
  slotTypes := certificate.slotTypes
  initializers := certificate.initializers
  decoded := certificate.decoded
  expression := certificate.expression
  member := certificate.member
  reflection := by
    intro value evaluated
    obtain ⟨sourceValue, sourceEvaluation, lowers, _⟩ :=
      checked_letMany_initializer_value certificate value evaluated
    exact ⟨sourceValue, sourceEvaluation, lowers⟩
  termination := Named.letManyFragment_termination_preserved_and_reflected
    certificate.definitions [] certificate.expression certificate.fragment
  divergence := Named.letManyFragment_divergence_preserved_and_reflected
    certificate.definitions [] certificate.expression certificate.fragment

/- Explicit lambda initializers admit any arity. The body and every argument
must still carry their fragment reflection evidence. -/
structure CheckedLambdaApplicationInitializer where
  expansion : ProcessCertificate.CheckedExpansion
  decodeFuel : Nat
  definitions : Named.Definitions
  slotTypes : List Surface.Ty
  initializers : List Named.Expr
  decoded : Named.decodeTopLevelProgram decodeFuel expansion.annotated =
    some (definitions, slotTypes, initializers)
  expression : Named.Expr
  member : expression ∈ initializers
  fragment : Named.LambdaApplicationFragment expression

theorem checked_lambda_application_initializer_main
    (certificate : CheckedLambdaApplicationInitializer) :
    certificate.expansion.text.toUTF8.data.data = certificate.expansion.bytes ∧
    SourceReader.readWithFuel certificate.expansion.lexFuel
      certificate.expansion.parseFuel certificate.expansion.text =
        some certificate.expansion.parsed ∧
    SourceReader.normalize certificate.expansion.parsed =
      some certificate.expansion.normalized ∧
    CExpansion.Expands
      (CExpansion.sourceRules 0 certificate.expansion.normalized)
      (.list (CExpansion.programForms certificate.expansion.normalized))
      (.list certificate.expansion.expanded) ∧
    CExpansion.disjointIntervals
      (ExpansionCertificate.freshIntervals certificate.expansion.localCertificate) = true ∧
    certificate.expansion.annotated.map CBindingWalk.Node.erase =
      certificate.expansion.expanded ∧
    (∃ sites, CBindingWalk.references certificate.expansion.scopeFuel
        certificate.expansion.annotated CBindingWalk.builtinEnvironment = some sites ∧
      ∀ site ∈ sites, CBindingWalk.Corresponds site) ∧
    (Named.SourceTerminates certificate.definitions [] certificate.expression ↔
      Named.LoweredTerminates certificate.definitions [] certificate.expression) ∧
    (Named.SourceDiverges certificate.definitions [] certificate.expression ↔
      Named.LoweredDiverges certificate.definitions [] certificate.expression) := by
  have process := ProcessCertificate.source_expands_with_scopes_and_freshness
    certificate.expansion
  rcases process with ⟨bytesMatch, parsed, normalized, expands, fresh,
    sameSyntax, scopes⟩
  have termination := Named.lambdaApplicationFragment_termination_preserved_and_reflected
    certificate.definitions [] certificate.expression certificate.fragment
  have divergence := Named.lambdaApplicationFragment_divergence_preserved_and_reflected
    certificate.definitions [] certificate.expression certificate.fragment
  exact ⟨bytesMatch, parsed, normalized, expands, fresh, sameSyntax, scopes,
    termination, divergence⟩

theorem checked_lambda_application_initializer_value
    (certificate : CheckedLambdaApplicationInitializer) (value : PolyIR.Value)
    (evaluated : PolyIR.Evaluates (Named.lowerDefinitions certificate.definitions) []
      (Named.lower [] certificate.expression) value) :
    ∃ sourceValue,
      Named.Evaluates certificate.definitions [] certificate.expression sourceValue ∧
      Named.lowerValue sourceValue = value ∧ Named.valueWellScoped sourceValue := by
  obtain ⟨sourceValue, sourceEvaluation, lowers⟩ :=
    Named.lambdaApplicationFragment_evaluation_reflected certificate.definitions
      certificate.expression certificate.fragment [] value evaluated
  have sourceScoped := Named.decodeTopLevel_initializer_evaluation_preserves_valueWellScoped
    certificate.decodeFuel certificate.expansion.annotated certificate.definitions
    certificate.slotTypes certificate.initializers certificate.decoded []
    certificate.expression sourceValue certificate.member
    Named.EnvironmentWellScoped.nil sourceEvaluation
  exact ⟨sourceValue, sourceEvaluation, lowers, sourceScoped⟩

theorem checked_lambda_application_initializer_main_with_value
    (certificate : CheckedLambdaApplicationInitializer) (value : PolyIR.Value)
    (evaluated : PolyIR.Evaluates (Named.lowerDefinitions certificate.definitions) []
      (Named.lower [] certificate.expression) value) :
    (certificate.expansion.text.toUTF8.data.data = certificate.expansion.bytes ∧
      SourceReader.readWithFuel certificate.expansion.lexFuel
        certificate.expansion.parseFuel certificate.expansion.text =
          some certificate.expansion.parsed ∧
      SourceReader.normalize certificate.expansion.parsed =
        some certificate.expansion.normalized ∧
      CExpansion.Expands
        (CExpansion.sourceRules 0 certificate.expansion.normalized)
        (.list (CExpansion.programForms certificate.expansion.normalized))
        (.list certificate.expansion.expanded) ∧
      CExpansion.disjointIntervals
        (ExpansionCertificate.freshIntervals certificate.expansion.localCertificate) = true ∧
      certificate.expansion.annotated.map CBindingWalk.Node.erase =
        certificate.expansion.expanded ∧
      (∃ sites, CBindingWalk.references certificate.expansion.scopeFuel
          certificate.expansion.annotated CBindingWalk.builtinEnvironment = some sites ∧
        ∀ site ∈ sites, CBindingWalk.Corresponds site) ∧
      (Named.SourceTerminates certificate.definitions [] certificate.expression ↔
        Named.LoweredTerminates certificate.definitions [] certificate.expression) ∧
      (Named.SourceDiverges certificate.definitions [] certificate.expression ↔
        Named.LoweredDiverges certificate.definitions [] certificate.expression)) ∧
    (∃ sourceValue,
      Named.Evaluates certificate.definitions [] certificate.expression sourceValue ∧
      Named.lowerValue sourceValue = value ∧ Named.valueWellScoped sourceValue) := by
  exact ⟨checked_lambda_application_initializer_main certificate,
    checked_lambda_application_initializer_value certificate value evaluated⟩

def CheckedLambdaApplicationInitializer.toCheckedSourceInitializer
    (certificate : CheckedLambdaApplicationInitializer) : CheckedSourceInitializer where
  expansion := certificate.expansion
  decodeFuel := certificate.decodeFuel
  definitions := certificate.definitions
  slotTypes := certificate.slotTypes
  initializers := certificate.initializers
  decoded := certificate.decoded
  expression := certificate.expression
  member := certificate.member
  reflection := by
    intro value evaluated
    obtain ⟨sourceValue, sourceEvaluation, lowers, _⟩ :=
      checked_lambda_application_initializer_value certificate value evaluated
    exact ⟨sourceValue, sourceEvaluation, lowers⟩
  termination := Named.lambdaApplicationFragment_termination_preserved_and_reflected
    certificate.definitions [] certificate.expression certificate.fragment
  divergence := Named.lambdaApplicationFragment_divergence_preserved_and_reflected
    certificate.definitions [] certificate.expression certificate.fragment

/- Unified explicit-lambda/global application certificate. The application
fragment makes function resolution and arbitrary-arity argument evidence part
of one input object. -/
structure CheckedApplicationInitializer where
  expansion : ProcessCertificate.CheckedExpansion
  decodeFuel : Nat
  definitions : Named.Definitions
  slotTypes : List Surface.Ty
  initializers : List Named.Expr
  decoded : Named.decodeTopLevelProgram decodeFuel expansion.annotated =
    some (definitions, slotTypes, initializers)
  expression : Named.Expr
  member : expression ∈ initializers
  fragment : Named.ApplicationFragment definitions expression

def CheckedApplicationInitializer.toCheckedSourceInitializer
    (certificate : CheckedApplicationInitializer) : CheckedSourceInitializer where
  expansion := certificate.expansion
  decodeFuel := certificate.decodeFuel
  definitions := certificate.definitions
  slotTypes := certificate.slotTypes
  initializers := certificate.initializers
  decoded := certificate.decoded
  expression := certificate.expression
  member := certificate.member
  reflection := by
    intro value evaluated
    obtain ⟨sourceValue, sourceEvaluation, lowers⟩ :=
      Named.applicationFragment_evaluation_reflected certificate.definitions
        certificate.expression certificate.fragment [] value evaluated
    exact ⟨sourceValue, sourceEvaluation, lowers⟩
  termination := Named.applicationFragment_termination_preserved_and_reflected
    certificate.definitions [] certificate.expression certificate.fragment
  divergence := Named.applicationFragment_divergence_preserved_and_reflected
    certificate.definitions [] certificate.expression certificate.fragment

def checked_application_initializer_main
    (certificate : CheckedApplicationInitializer) :=
  checked_source_initializer_main certificate.toCheckedSourceInitializer

def checked_application_initializer_main_with_value
    (certificate : CheckedApplicationInitializer) (value : PolyIR.Value)
    (evaluated : PolyIR.Evaluates (Named.lowerDefinitions certificate.definitions) []
      (Named.lower [] certificate.expression) value) :=
  checked_source_initializer_main_with_value certificate.toCheckedSourceInitializer
    value evaluated

/- Extend the combined proof artifact to a global call whose body and finite
argument expressions are in the reflected arithmetic fragment. This covers
nonzero and arbitrary call arities without claiming arbitrary expression
reflection. -/
structure CheckedGlobalCallInitializer where
  expansion : ProcessCertificate.CheckedExpansion
  decodeFuel : Nat
  definitions : Named.Definitions
  slotTypes : List Surface.Ty
  initializers : List Named.Expr
  decoded : Named.decodeTopLevelProgram decodeFuel expansion.annotated =
    some (definitions, slotTypes, initializers)
  index : Nat
  parameters : List Nat
  body : Named.Expr
  arguments : List Named.Expr
  initializerMember : Named.Expr.app (.global index) arguments ∈ initializers
  definitionFound : definitions[index]? = some (parameters, body)
  bodyFragment : Named.ArithmeticFragment body
  argumentsFragments : Named.ArithmeticFragmentList arguments

/-- The source read, finite expansion, binding correspondence, freshness, and
termination/divergence correspondence are combined for a decoded initializer
that calls a global function. -/
theorem checked_global_call_initializer_main (certificate : CheckedGlobalCallInitializer) :
    certificate.expansion.text.toUTF8.data.data = certificate.expansion.bytes ∧
    SourceReader.readWithFuel certificate.expansion.lexFuel
      certificate.expansion.parseFuel certificate.expansion.text =
        some certificate.expansion.parsed ∧
    SourceReader.normalize certificate.expansion.parsed =
      some certificate.expansion.normalized ∧
    CExpansion.Expands
      (CExpansion.sourceRules 0 certificate.expansion.normalized)
      (.list (CExpansion.programForms certificate.expansion.normalized))
      (.list certificate.expansion.expanded) ∧
    CExpansion.disjointIntervals
      (ExpansionCertificate.freshIntervals certificate.expansion.localCertificate) = true ∧
    certificate.expansion.annotated.map CBindingWalk.Node.erase =
      certificate.expansion.expanded ∧
    (∃ sites, CBindingWalk.references certificate.expansion.scopeFuel
        certificate.expansion.annotated CBindingWalk.builtinEnvironment = some sites ∧
      ∀ site ∈ sites, CBindingWalk.Corresponds site) ∧
    (Named.SourceTerminates certificate.definitions []
      (.app (.global certificate.index) certificate.arguments) ↔
      Named.LoweredTerminates certificate.definitions []
        (.app (.global certificate.index) certificate.arguments)) ∧
    (Named.SourceDiverges certificate.definitions []
      (.app (.global certificate.index) certificate.arguments) ↔
      Named.LoweredDiverges certificate.definitions []
        (.app (.global certificate.index) certificate.arguments)) := by
  have process := ProcessCertificate.source_expands_with_scopes_and_freshness
    certificate.expansion
  rcases process with ⟨bytesMatch, parsed, normalized, expands, fresh,
    sameSyntax, scopes⟩
  have termination := Named.global_application_termination_preserved_and_reflected
    certificate.definitions [] certificate.index certificate.parameters certificate.body
    certificate.arguments certificate.definitionFound certificate.bodyFragment
    certificate.argumentsFragments
  have divergence := Named.global_application_divergence_preserved_and_reflected
    certificate.definitions [] certificate.index certificate.parameters certificate.body
    certificate.arguments certificate.definitionFound certificate.bodyFragment
    certificate.argumentsFragments
  exact ⟨bytesMatch, parsed, normalized, expands, fresh, sameSyntax, scopes,
    termination, divergence⟩

/-- The same combined artifact reflects any finite lowered result of the
global-call initializer and proves the returned closure/binder invariant. -/
theorem checked_global_call_initializer_value
    (certificate : CheckedGlobalCallInitializer) (value : PolyIR.Value)
    (evaluated : PolyIR.Evaluates (Named.lowerDefinitions certificate.definitions) []
      (Named.lower [] (.app (.global certificate.index) certificate.arguments)) value) :
    ∃ sourceValue,
      Named.Evaluates certificate.definitions []
        (.app (.global certificate.index) certificate.arguments) sourceValue ∧
      Named.lowerValue sourceValue = value ∧ Named.valueWellScoped sourceValue := by
  obtain ⟨sourceValue, sourceEval, lowers⟩ :=
    Named.global_application_evaluation_reflected_of_fragments
      certificate.definitions [] certificate.index certificate.parameters certificate.body
      certificate.arguments certificate.definitionFound certificate.bodyFragment
      certificate.argumentsFragments value (by simpa [Named.lower_eq] using evaluated)
  have sourceScoped := Named.decodeTopLevel_initializer_evaluation_preserves_valueWellScoped
    certificate.decodeFuel certificate.expansion.annotated certificate.definitions
    certificate.slotTypes certificate.initializers certificate.decoded
    [] (Named.Expr.app (.global certificate.index) certificate.arguments) sourceValue
    certificate.initializerMember Named.EnvironmentWellScoped.nil sourceEval
  exact ⟨sourceValue, sourceEval, lowers, sourceScoped⟩

def CheckedGlobalCallInitializer.toCheckedSourceInitializer
    (certificate : CheckedGlobalCallInitializer) : CheckedSourceInitializer where
  expansion := certificate.expansion
  decodeFuel := certificate.decodeFuel
  definitions := certificate.definitions
  slotTypes := certificate.slotTypes
  initializers := certificate.initializers
  decoded := certificate.decoded
  expression := .app (.global certificate.index) certificate.arguments
  member := certificate.initializerMember
  reflection := by
    intro value evaluated
    obtain ⟨sourceValue, sourceEvaluation, lowers, _scope⟩ :=
      checked_global_call_initializer_value certificate value evaluated
    exact ⟨sourceValue, sourceEvaluation, lowers⟩
  termination := Named.global_application_termination_preserved_and_reflected
    certificate.definitions [] certificate.index certificate.parameters certificate.body
    certificate.arguments certificate.definitionFound certificate.bodyFragment
    certificate.argumentsFragments
  divergence := Named.global_application_divergence_preserved_and_reflected
    certificate.definitions [] certificate.index certificate.parameters certificate.body
    certificate.arguments certificate.definitionFound certificate.bodyFragment
    certificate.argumentsFragments

/-- Combined global-call certificate theorem for finite initializer runs. It
packages all source/expansion/binding evidence, termination and divergence
equivalence, and the returned value's source derivation and scope invariant. -/
theorem checked_global_call_initializer_main_with_value
    (certificate : CheckedGlobalCallInitializer) (value : PolyIR.Value)
    (evaluated : PolyIR.Evaluates (Named.lowerDefinitions certificate.definitions) []
      (Named.lower [] (.app (.global certificate.index) certificate.arguments)) value) :
    (certificate.expansion.text.toUTF8.data.data = certificate.expansion.bytes ∧
      SourceReader.readWithFuel certificate.expansion.lexFuel
        certificate.expansion.parseFuel certificate.expansion.text =
          some certificate.expansion.parsed ∧
      SourceReader.normalize certificate.expansion.parsed =
        some certificate.expansion.normalized ∧
      CExpansion.Expands
        (CExpansion.sourceRules 0 certificate.expansion.normalized)
        (.list (CExpansion.programForms certificate.expansion.normalized))
        (.list certificate.expansion.expanded) ∧
      CExpansion.disjointIntervals
        (ExpansionCertificate.freshIntervals certificate.expansion.localCertificate) = true ∧
      certificate.expansion.annotated.map CBindingWalk.Node.erase =
        certificate.expansion.expanded ∧
      (∃ sites, CBindingWalk.references certificate.expansion.scopeFuel
          certificate.expansion.annotated CBindingWalk.builtinEnvironment = some sites ∧
        ∀ site ∈ sites, CBindingWalk.Corresponds site) ∧
      (Named.SourceTerminates certificate.definitions []
          (.app (.global certificate.index) certificate.arguments) ↔
        Named.LoweredTerminates certificate.definitions []
          (.app (.global certificate.index) certificate.arguments)) ∧
      (Named.SourceDiverges certificate.definitions []
          (.app (.global certificate.index) certificate.arguments) ↔
        Named.LoweredDiverges certificate.definitions []
          (.app (.global certificate.index) certificate.arguments))) ∧
    (∃ sourceValue,
      Named.Evaluates certificate.definitions []
        (.app (.global certificate.index) certificate.arguments) sourceValue ∧
      Named.lowerValue sourceValue = value ∧ Named.valueWellScoped sourceValue) := by
  exact ⟨checked_global_call_initializer_main certificate,
    checked_global_call_initializer_value certificate value evaluated⟩

end NLisp.CertifiedArithmeticReflection
