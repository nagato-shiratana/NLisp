import NLisp.SourceReader
import NLisp.CBindingWalk
import NLisp.MacroTermination

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
  expands : CExpansion.Expands (CExpansion.sourceRules 0 normalized)
    (.list (CExpansion.programForms normalized)) (.list expanded)
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
      ∀ site ∈ sites, CBindingWalk.Corresponds site :=
  ⟨certificate.bytes_match, certificate.parses, certificate.normalizes, certificate.expands,
    certificate.same_syntax, certificate.scope_checks⟩

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

end NLisp.ProcessCertificate
