import NLisp.SourceReader
import NLisp.CBindingWalk
import NLisp.MacroTermination
import NLisp.ExpansionCertificate
import NLisp.BinderCertificateComposition

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

/-- An alternative source certificate may provide any well-founded measure
for the extracted conservative call graph.  Unlike `CheckedStaticTermination`,
it is not restricted to a finite list of natural-number ranks. -/
structure CheckedUserDecrease extends CheckedSource where
  graphFuel : Nat
  edges : List MacroTermination.Edge
  graph_matches : MacroTermination.graph graphFuel
      (CExpansion.sourceRules 0 normalized) = some edges
  measure : MacroTermination.WellFoundedDecreaseCertificate edges

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

/-- Compose an accepted source/expansion certificate with any finite family
of phase-composed binder-copy results. Pairwise interval separation gives
cross-copy freshness, while each chunk avoids every source identifier in the
reserved source-token class. -/
theorem checked_process_finite_binder_freshness
    (certificate : CheckedExpansion)
    (chunks : List (CMacroCopy.CertifiedBinderTokenChunk certificate.localCertificate))
    (intervalsDistinct : ∀ first, first ∈ chunks → ∀ second, second ∈ chunks →
      first.interval ≠ second.interval) :
    (certificate.text.toUTF8.data.data = certificate.bytes ∧
      SourceReader.readWithFuel certificate.lexFuel certificate.parseFuel certificate.text =
        some certificate.parsed ∧
      SourceReader.normalize certificate.parsed = some certificate.normalized ∧
      CExpansion.Expands (CExpansion.sourceRules 0 certificate.normalized)
        (.list (CExpansion.programForms certificate.normalized))
        (.list certificate.expanded) ∧
      CExpansion.disjointIntervals
        (ExpansionCertificate.freshIntervals certificate.localCertificate) = true ∧
      certificate.annotated.map CBindingWalk.Node.erase = certificate.expanded ∧
      (∃ sites, CBindingWalk.references certificate.scopeFuel certificate.annotated
        CBindingWalk.builtinEnvironment = some sites ∧
        ∀ site ∈ sites, CBindingWalk.Corresponds site)) ∧
    CMacroCopy.PairwiseTokenDisjoint chunks ∧
    CMacroCopy.Unique (CMacroCopy.binderTokenSequence chunks) ∧
    (∀ token, token % 3 = 1 → token ∉ CMacroCopy.binderTokenSequence chunks) ∧
    (∀ token, token ∈ CMacroCopy.binderTokenSequence chunks →
      ∃ chunk, chunk ∈ chunks ∧
        chunk.interval ∈ ExpansionCertificate.freshIntervals certificate.localCertificate ∧
        ∃ counter, chunk.interval.1 < counter ∧ counter ≤ chunk.interval.2 ∧
          token = 3 * counter + 2) ∧
    (∃ lexerTokens,
      SourceReader.lex certificate.lexFuel certificate.text.toList 0 = some lexerTokens ∧
      (SourceReader.parseOperations certificate.parseFuel).forms lexerTokens =
        some certificate.parsed ∧
      ∀ token, token ∈ SourceReader.sourceTokenIdentities lexerTokens →
        token ∉ CMacroCopy.binderTokenSequence chunks) := by
  have pairwise := CMacroCopy.certifiedBinderTokenChunks_pairwise_disjoint
    (CExpansion.sourceRules 0 certificate.normalized) certificate.localCertificate
    certificate.localCertificate_fresh chunks intervalsDistinct
  have source := source_expands_with_scopes certificate
  have intervals := ExpansionCertificate.checkFresh_sound_with_intervals
    (rules := CExpansion.sourceRules 0 certificate.normalized) certificate.localCertificate
    certificate.localCertificate_fresh
  rw [certificate.localCertificate_source, certificate.localCertificate_target] at intervals
  rcases source with ⟨bytes, parsed, normalized, expanded, syntaxCorr, scopes⟩
  obtain ⟨_noNul, lexerTokens, lexerSuccess, parseSuccess⟩ :=
    (SourceReader.readWithFuel_success_iff certificate.lexFuel certificate.parseFuel
      certificate.text certificate.parsed).mp certificate.parses
  have aggregateFresh := CMacroCopy.certifiedBinderTokenChunks_freshness
    (CExpansion.sourceRules 0 certificate.normalized) certificate.localCertificate
    certificate.localCertificate_fresh chunks intervalsDistinct
    (SourceReader.sourceTokenIdentities lexerTokens)
    (SourceReader.sourceTokenIdentities_have_source_class lexerTokens)
  refine ⟨⟨bytes, parsed, normalized, expanded, intervals.2, syntaxCorr, scopes⟩,
    pairwise, CMacroCopy.pairwiseTokenDisjoint_flatMap_unique chunks pairwise,
    ?_, ?_, ⟨lexerTokens, lexerSuccess, parseSuccess, ?_⟩⟩
  · intro token sourceClass
    exact CMacroCopy.binderTokenSequence_avoids_source_class chunks token sourceClass
  · intro token member
    exact aggregateFresh.2.2 token member
  · intro token member
    exact aggregateFresh.2.1 token member

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

/-- Compose one accepted process certificate with two binder-phase copy
certificates. This packages source decoding, certified expansion, annotated
syntax correspondence, scope correspondence, disjoint expansion intervals,
and within/across-copy freshness into one result. Type preservation of the
expanded program is intentionally not asserted: the current typed expansion
certificate language has not yet been connected to these syntax certificates. -/
theorem checked_process_binder_freshness
    (certificate : CheckedExpansion)
    {fuelA originA : Nat} {holesA : CMacroCopy.Holes} {macrosA : List String}
    {outsideA : CMacroCopy.Renames} {freshA : Nat}
    {parametersA bindingsA patternA casesA : List CMacroCopy.Tree}
    (firstCopy : CMacroCopy.BinderPhaseCopy fuelA originA holesA macrosA outsideA freshA
      parametersA bindingsA patternA casesA)
    (firstInterval : Nat × Nat)
    (firstIntervalEq : firstInterval = (freshA, firstCopy.afterCases))
    (firstIntervalMember : firstInterval ∈
      ExpansionCertificate.freshIntervals certificate.localCertificate)
    {fuelB originB : Nat} {holesB : CMacroCopy.Holes} {macrosB : List String}
    {outsideB : CMacroCopy.Renames} {freshB : Nat}
    {parametersB bindingsB patternB casesB : List CMacroCopy.Tree}
    (secondCopy : CMacroCopy.BinderPhaseCopy fuelB originB holesB macrosB outsideB freshB
      parametersB bindingsB patternB casesB)
    (secondInterval : Nat × Nat)
    (secondIntervalEq : secondInterval = (freshB, secondCopy.afterCases))
    (secondIntervalMember : secondInterval ∈
      ExpansionCertificate.freshIntervals certificate.localCertificate)
    (intervalsDiffer : firstInterval ≠ secondInterval)
    (sourceTokens : List Nat)
    (sourceClass : ∀ token, token ∈ sourceTokens → token % 3 = 1) :
    certificate.text.toUTF8.data.data = certificate.bytes ∧
    SourceReader.readWithFuel certificate.lexFuel certificate.parseFuel certificate.text =
      some certificate.parsed ∧
    SourceReader.normalize certificate.parsed = some certificate.normalized ∧
    CExpansion.Expands (CExpansion.sourceRules 0 certificate.normalized)
      (.list (CExpansion.programForms certificate.normalized)) (.list certificate.expanded) ∧
    certificate.annotated.map CBindingWalk.Node.erase = certificate.expanded ∧
    (∃ sites, CBindingWalk.references certificate.scopeFuel certificate.annotated
      CBindingWalk.builtinEnvironment = some sites ∧
      ∀ site ∈ sites, CBindingWalk.Corresponds site) ∧
    CExpansion.disjointIntervals (ExpansionCertificate.freshIntervals certificate.localCertificate) =
      true ∧
    CMacroCopy.Unique firstCopy.tokens ∧ CMacroCopy.Unique secondCopy.tokens ∧
    (∀ tokenA, tokenA ∈ firstCopy.tokens → ∀ tokenB, tokenB ∈ secondCopy.tokens →
      tokenA ≠ tokenB) ∧
    (∀ token, token ∈ sourceTokens → token ∉ firstCopy.tokens) ∧
    (∀ token, token ∈ sourceTokens → token ∉ secondCopy.tokens) := by
  have processFacts := source_expands_with_scopes_and_freshness certificate
  have copiesFresh := CMacroCopy.certifiedBinderPhaseCopies_freshness
    (CExpansion.sourceRules 0 certificate.normalized) certificate.localCertificate
    certificate.localCertificate_fresh firstInterval secondInterval firstIntervalMember
    secondIntervalMember intervalsDiffer firstCopy firstIntervalEq secondCopy secondIntervalEq
    sourceTokens sourceClass
  exact ⟨processFacts.1, processFacts.2.1, processFacts.2.2.1, processFacts.2.2.2.1,
    processFacts.2.2.2.2.2.1, processFacts.2.2.2.2.2.2,
    processFacts.2.2.2.2.1,
    copiesFresh.1, copiesFresh.2.1, copiesFresh.2.2.1, copiesFresh.2.2.2.1,
    copiesFresh.2.2.2.2⟩

theorem source_rules_wellFounded (certificate : CheckedStaticTermination) :
    MacroTermination.graph certificate.graphFuel (CExpansion.sourceRules 0 certificate.normalized) =
      some certificate.edges ∧ WellFounded (MacroTermination.Calls certificate.edges) :=
  ⟨certificate.graph_matches, MacroTermination.ranked_graph_wellFounded certificate.decreases⟩

/-- A user-supplied well-founded measure also certifies the extracted source
rule graph.  This supports structural or lexicographic orders when the finite
`Nat` rank-vector checker is too restrictive. -/
theorem source_rules_wellFounded_of_user_decrease
    (certificate : CheckedUserDecrease) :
    MacroTermination.graph certificate.graphFuel
        (CExpansion.sourceRules 0 certificate.normalized) = some certificate.edges ∧
      WellFounded (MacroTermination.Calls certificate.edges) :=
  ⟨certificate.graph_matches,
    MacroTermination.wellFoundedDecreaseCertificate_calls_wellFounded certificate.measure⟩

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

/-- Every extracted static source call decreases the caller-provided measure
under the declared well-founded relation. -/
theorem source_static_calls_user_decrease (certificate : CheckedUserDecrease)
    (edge : MacroTermination.Edge)
    (call : MacroTermination.GraphCall (CExpansion.sourceRules 0 certificate.normalized)
      0 (CExpansion.sourceRules 0 certificate.normalized) edge) :
    certificate.measure.decrease (certificate.measure.measure edge.1)
      (certificate.measure.measure edge.2) := by
  apply certificate.measure.calls_decrease
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
