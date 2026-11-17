import NLisp

#print axioms NLisp.progress
#print axioms NLisp.preservation
#print axioms NLisp.notStuck
#print axioms NLisp.TypedMacro.expand_preserves_type
#print axioms NLisp.liftSub_keeps_bound
#print axioms NLisp.liftSub_shifts_hole
#print axioms NLisp.subst_under_lambda
#print axioms NLisp.expandLambdaHole_hygienic
#print axioms NLisp.expandLambdaHole_open
#print axioms NLisp.expandLambdaHole_closed
#print axioms NLisp.expandTwice_eq
#print axioms NLisp.TypedExpansion.Expr.hasType
#print axioms NLisp.ScopedSyntax.transport_var
#print axioms NLisp.ScopedSyntax.transport_string
#print axioms NLisp.ScopedSyntax.transport_float_bits
#print axioms NLisp.ScopedSyntax.transport_builtin
#print axioms NLisp.ScopedSyntax.distinct_origins_remain_distinct
#print axioms NLisp.ScopedSyntax.appendSub_hole
#print axioms NLisp.ScopedSyntax.appendSub_definition
#print axioms NLisp.ScopedSyntax.expand_hole
#print axioms NLisp.ScopedSyntax.expand_capture
#print axioms NLisp.ScopedSyntax.Examples.shadowing_preserves_both_origins
#print axioms NLisp.ScopedSyntax.Examples.wrong_same_typed_binding_rejected
#print axioms NLisp.ScopedSyntax.Examples.introduced_lambda_captures_neither_origin
#print axioms NLisp.ScopedSyntax.Examples.fresh_scope_shifts_both_origins
#print axioms NLisp.ScopedSyntax.Examples.duplicate_binding_identity_invalid

#print axioms NLisp.CNameResolution.findName_sound
#print axioms NLisp.CNameResolution.checked_lookup_corresponds
#print axioms NLisp.CNameResolution.shadowed_binding_not_selected
#print axioms NLisp.CNameResolution.scope_ids_invariant
#print axioms NLisp.CMacroCopy.checkCopy_sound
#print axioms NLisp.CMacroCopy.capture_uses_definition_origin
#print axioms NLisp.CMacroCopy.hole_keeps_argument
#print axioms NLisp.CBindingWalk.accepts_sound
#print axioms NLisp.CBindingWalk.check_sound
#print axioms NLisp.CExpansion.expansion_keeps_argument

#print axioms NLisp.MacroTermination.checkRanks_decreases
#print axioms NLisp.MacroTermination.ranked_graph_wellFounded
#print axioms NLisp.MacroTermination.path_length_bounded
#print axioms NLisp.CExpansion.separated_fresh_values_differ

#print axioms NLisp.CNameResolution.member_to_scoped_variable
#print axioms NLisp.CNameResolution.observations_correspond

#print axioms NLisp.CExpansion.source_and_generated_ids_differ

#print axioms NLisp.ProcessCertificate.source_expands_with_scopes
#print axioms NLisp.ProcessCertificate.source_rules_wellFounded
