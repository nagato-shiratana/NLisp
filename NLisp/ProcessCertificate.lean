import NLisp.SourceReader
import NLisp.CBindingWalk
import NLisp.MacroTermination
import NLisp.ExpansionCertificate

namespace NLisp.ProcessCertificate

structure CheckedSource where
  bytes : List UInt8
  text : String
  lexFuel : Nat
  parseFuel : Nat
  parsed : List CMacroCopy.Tree
  normalized : List CMacroCopy.Tree
  /- Use the byte array's logical list directly; Array.toList performs an
  indexed fold that is unnecessarily expensive during kernel reduction. -/
  bytes_match : text.toUTF8.data.data = bytes
  parses : SourceReader.readWithFuel lexFuel parseFuel text = some parsed
  normalizes : SourceReader.normalize parsed = some normalized

structure CheckedExpansion extends CheckedSource where
  expanded : List CMacroCopy.Tree
  annotated : List CBindingWalk.Node
  scopeFuel : Nat
  localCertificate : ExpansionCertificate.Certificate
  localCertificate_source : ExpansionCertificate.source localCertificate =
    .list (CExpansion.programForms normalized)
  localCertificate_target : ExpansionCertificate.target localCertificate = .list expanded
  localCertificate_fresh : ExpansionCertificate.checkFresh
    (CExpansion.sourceRules 0 normalized) localCertificate = true
  same_syntax : annotated.map CBindingWalk.Node.erase = expanded
  scope_checks : ∃ sites, CBindingWalk.references scopeFuel annotated CBindingWalk.builtinEnvironment = some sites ∧
    ∀ site ∈ sites, CBindingWalk.Corresponds site

structure CheckedStaticTermination extends CheckedSource where
  graphFuel : Nat
  edges : List MacroTermination.Edge
  ranks : List Nat
  graph_matches : MacroTermination.graph graphFuel (CExpansion.sourceRules 0 normalized) = some edges
  decreases : MacroTermination.checkRanks edges ranks = true

theorem source_expands_with_scopes (certificate : CheckedExpansion) :
    certificate.text.toUTF8.data.data = certificate.bytes ∧
    SourceReader.readWithFuel certificate.lexFuel certificate.parseFuel certificate.text = some certificate.parsed ∧
    SourceReader.normalize certificate.parsed = some certificate.normalized ∧
    CExpansion.Expands (CExpansion.sourceRules 0 certificate.normalized)
      (.list (CExpansion.programForms certificate.normalized)) (.list certificate.expanded) ∧
    certificate.annotated.map CBindingWalk.Node.erase = certificate.expanded ∧
    ∃ sites, CBindingWalk.references certificate.scopeFuel certificate.annotated
        CBindingWalk.builtinEnvironment = some sites ∧
      ∀ site ∈ sites, CBindingWalk.Corresponds site := by
  have joint := ExpansionCertificate.checkFresh_sound_with_intervals
    (rules := CExpansion.sourceRules 0 certificate.normalized) certificate.localCertificate
    certificate.localCertificate_fresh
  rw [certificate.localCertificate_source, certificate.localCertificate_target] at joint
  exact ⟨certificate.bytes_match, certificate.parses, certificate.normalizes,
    joint.1, certificate.same_syntax, certificate.scope_checks⟩

/-- One process record can carry source parsing, normalization, a finite local
expansion certificate, scope correspondences, and freshness interval checks.
The local checker proves expansion and interval disjointness together; this
still does not claim that interval disjointness alone establishes binder
non-capture or type preservation. -/
theorem source_expands_with_scopes_and_freshness (certificate : CheckedExpansion) :
    certificate.text.toUTF8.data.data = certificate.bytes ∧
    SourceReader.readWithFuel certificate.lexFuel certificate.parseFuel certificate.text =
      some certificate.parsed ∧
    SourceReader.normalize certificate.parsed = some certificate.normalized ∧
    CExpansion.Expands (CExpansion.sourceRules 0 certificate.normalized)
      (.list (CExpansion.programForms certificate.normalized)) (.list certificate.expanded) ∧
    CExpansion.disjointIntervals
      (ExpansionCertificate.freshIntervals certificate.localCertificate) = true ∧
    certificate.annotated.map CBindingWalk.Node.erase = certificate.expanded ∧
    ∃ sites, CBindingWalk.references certificate.scopeFuel certificate.annotated
        CBindingWalk.builtinEnvironment = some sites ∧
      ∀ site ∈ sites, CBindingWalk.Corresponds site := by
  have joint := ExpansionCertificate.checkFresh_sound_with_intervals
    (rules := CExpansion.sourceRules 0 certificate.normalized) certificate.localCertificate
    certificate.localCertificate_fresh
  rw [certificate.localCertificate_source, certificate.localCertificate_target] at joint
  exact ⟨certificate.bytes_match, certificate.parses, certificate.normalizes,
    joint.1, joint.2, certificate.same_syntax, certificate.scope_checks⟩

theorem source_rules_wellFounded (certificate : CheckedStaticTermination) :
    MacroTermination.graph certificate.graphFuel (CExpansion.sourceRules 0 certificate.normalized) =
      some certificate.edges ∧ WellFounded (MacroTermination.Calls certificate.edges) :=
  ⟨certificate.graph_matches, MacroTermination.ranked_graph_wellFounded certificate.decreases⟩

theorem source_static_calls_decrease (certificate : CheckedStaticTermination)
    (edge : MacroTermination.Edge)
    (call : MacroTermination.GraphCall (CExpansion.sourceRules 0 certificate.normalized)
      0 (CExpansion.sourceRules 0 certificate.normalized) edge) :
    MacroTermination.rank certificate.ranks edge.1 < MacroTermination.rank certificate.ranks edge.2 := by
  apply MacroTermination.checkRanks_decreases certificate.decreases
  exact MacroTermination.graphRows_contains_static_calls certificate.graphFuel
    (CExpansion.sourceRules 0 certificate.normalized) 0
    (CExpansion.sourceRules 0 certificate.normalized) certificate.edges
    certificate.graph_matches call

/-- A static call extracted from a checked source process decreases the macro
component of the two-phase expansion measure, regardless of how much syntax
the child expansion will produce. -/
theorem source_static_call_expansion_progress (certificate : CheckedStaticTermination)
    (edge : MacroTermination.Edge)
    (call : MacroTermination.GraphCall (CExpansion.sourceRules 0 certificate.normalized)
      0 (CExpansion.sourceRules 0 certificate.normalized) edge)
    (parentNodes childNodes : Nat) :
    MacroTermination.ExpansionProgress
      (MacroTermination.rank certificate.ranks edge.1, childNodes)
      (MacroTermination.rank certificate.ranks edge.2, parentNodes) :=
  MacroTermination.macroExpansionProgress_decreases
    (source_static_calls_decrease certificate edge call)

/-- A checked process-level rank certificate excludes every infinite path in
its conservative static call graph. Relating all runtime macro expansions to
such paths remains a separate simulation obligation. -/
theorem source_static_call_chain_terminates (certificate : CheckedStaticTermination)
    (chain : Nat → Nat)
    (step : ∀ index, MacroTermination.Calls certificate.edges
      (chain (index + 1)) (chain index)) : False :=
  MacroTermination.no_infinite_call_chain certificate.decreases chain step

theorem source_static_call_chain_length_bounded (certificate : CheckedStaticTermination)
    (chain : Nat → Nat)
    (step : ∀ index, MacroTermination.Calls certificate.edges
      (chain (index + 1)) (chain index)) (count : Nat) :
    count + MacroTermination.rank certificate.ranks (chain count) ≤
      MacroTermination.rank certificate.ranks (chain 0) :=
  MacroTermination.call_chain_length_bounded certificate.decreases chain step count

end NLisp.ProcessCertificate
