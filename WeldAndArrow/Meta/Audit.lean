import WeldAndArrow.Meta.Invariance
import WeldAndArrow.Meta.InvarianceNegative
import WeldAndArrow.Meta.ReflexivityWitness
import WeldAndArrow.Meta.VerdictLedger
import WeldAndArrow.Doctrines.SraddhaNegative
import WeldAndArrow.Doctrines.FaithNegative
import WeldAndArrow.Doctrines.Deliberation
import WeldAndArrow.Doctrines.Ledger
import WeldAndArrow.Doctrines.CorrelationsNegative
import WeldAndArrow.Doctrines.FettersNegative
import WeldAndArrow.Doctrines.FactorsNegative

namespace WAA

/--
info: 'WAA.no_agent_recovery_of_field_collision' does not depend on any axioms
-/
#guard_msgs in
#print axioms no_agent_recovery_of_field_collision

/--
info: 'WAA.strict_asymm' does not depend on any axioms
-/
#guard_msgs in
#print axioms strict_asymm

/--
info: 'WAA.strict_trans' does not depend on any axioms
-/
#guard_msgs in
#print axioms strict_trans

/--
info: 'WAA.Grid.transpose_transpose' does not depend on any axioms
-/
#guard_msgs in
#print axioms Grid.transpose_transpose

/--
info: 'WAA.DirectionNegative.no_direction_recovery_from_conditionsEither' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms DirectionNegative.no_direction_recovery_from_conditionsEither

/--
info: 'WAA.CoverageNegative.directionVoid_needs_coverage' does not depend on any axioms
-/
#guard_msgs in
#print axioms CoverageNegative.directionVoid_needs_coverage

/--
info: 'WAA.CoverageNegative.waaFullyEnlightened_needs_coverage' does not depend on any axioms
-/
#guard_msgs in
#print axioms CoverageNegative.waaFullyEnlightened_needs_coverage

/--
info: 'WAA.Grid.stateToolFits_iff_atBot' does not depend on any axioms
-/
#guard_msgs in
#print axioms Grid.stateToolFits_iff_atBot

/--
info: 'WAA.Grid.map_actual_iff' does not depend on any axioms
-/
#guard_msgs in
#print axioms Grid.map_actual_iff

/--
info: 'WAA.Grid.map_isShareDrop_iff' does not depend on any axioms
-/
#guard_msgs in
#print axioms Grid.map_isShareDrop_iff

/--
info: 'WAA.Grid.map_transpose' does not depend on any axioms
-/
#guard_msgs in
#print axioms Grid.map_transpose

/--
info: 'WAA.Grid.staticized_transpose' does not depend on any axioms
-/
#guard_msgs in
#print axioms Grid.staticized_transpose

/--
info: 'WAA.Grid.map_staticized' does not depend on any axioms
-/
#guard_msgs in
#print axioms Grid.map_staticized

/--
info: 'WAA.Grid.DirectedConvention.DirectionCoarsening.mapDir_resolutionBounded_iff' does not depend on any axioms
-/
#guard_msgs in
#print axioms Grid.DirectedConvention.DirectionCoarsening.mapDir_resolutionBounded_iff

/--
info: 'WAA.DirectionCoarseningWitness.registerClock_unitTick_not_resolutionBounded' does not depend on any axioms
-/
#guard_msgs in
#print axioms DirectionCoarseningWitness.registerClock_unitTick_not_resolutionBounded

/--
info: 'WAA.DirectionCoarseningWitness.unit_directionVoid_via_mergeToUnit' does not depend on any axioms
-/
#guard_msgs in
#print axioms DirectionCoarseningWitness.unit_directionVoid_via_mergeToUnit

/--
info: 'WAA.DirectionCoarseningWitness.fullyCoarseRegisterClock_no_timeDirection' does not depend on any axioms
-/
#guard_msgs in
#print axioms DirectionCoarseningWitness.fullyCoarseRegisterClock_no_timeDirection

/--
info: 'WAA.DirectionCoarseningWitness.registerClock_directionCoarsening_independence' does not depend on any axioms
-/
#guard_msgs in
#print axioms DirectionCoarseningWitness.registerClock_directionCoarsening_independence

/--
info: 'WAA.Grid.DirectedConvention.map_landsWithShareDrop_iff' does not depend on any axioms
-/
#guard_msgs in
#print axioms Grid.DirectedConvention.map_landsWithShareDrop_iff

/--
info: 'WAA.Grid.DirectedConvention.BeingConvention.BeingCoarsening.map_selfConditioningTag_iff' does not depend on any axioms
-/
#guard_msgs in
#print axioms Grid.DirectedConvention.BeingConvention.BeingCoarsening.map_selfConditioningTag_iff

/--
info: 'WAA.Grid.DirectedConvention.BeingConvention.BeingCoarsening.map_fiberAtPoleOn_iff' does not depend on any axioms
-/
#guard_msgs in
#print axioms Grid.DirectedConvention.BeingConvention.BeingCoarsening.map_fiberAtPoleOn_iff

/--
info: 'WAA.Grid.DirectedConvention.BeingConvention.BeingCoarsening.total_sameFiber' does not depend on any axioms
-/
#guard_msgs in
#print axioms Grid.DirectedConvention.BeingConvention.BeingCoarsening.total_sameFiber

/--
info: 'WAA.Grid.DirectedConvention.BeingConvention.BeingCoarsening.id_not_sameFiber_of_ne' does not depend on any axioms
-/
#guard_msgs in
#print axioms Grid.DirectedConvention.BeingConvention.BeingCoarsening.id_not_sameFiber_of_ne

/--
info: 'WAA.Grid.map_waaBullSeven_iff' does not depend on any axioms
-/
#guard_msgs in
#print axioms Grid.map_waaBullSeven_iff

/--
info: 'WAA.Grid.map_waaBullTen_iff' does not depend on any axioms
-/
#guard_msgs in
#print axioms Grid.map_waaBullTen_iff

/--
info: 'WAA.Grid.bullSeven_not_bullEight' does not depend on any axioms
-/
#guard_msgs in
#print axioms Grid.bullSeven_not_bullEight

/--
info: 'WAA.Grid.bullTen_to_bullNine' does not depend on any axioms
-/
#guard_msgs in
#print axioms Grid.bullTen_to_bullNine

/--
info: 'WAA.CorrelationsNegative.pratyekabuddha_countermodel' does not depend on any axioms
-/
#guard_msgs in
#print axioms CorrelationsNegative.pratyekabuddha_countermodel

/--
info: 'WAA.CorrelationsNegative.no_stage_boundary_recovery' does not depend on any axioms
-/
#guard_msgs in
#print axioms CorrelationsNegative.no_stage_boundary_recovery

/--
info: 'WAA.Grid.classQuiet_no_clench_in_class' does not depend on any axioms
-/
#guard_msgs in
#print axioms Grid.classQuiet_no_clench_in_class

/--
info: 'WAA.Fetter.kind_lower_iff_cut_by_nonReturn' does not depend on any axioms
-/
#guard_msgs in
#print axioms Fetter.kind_lower_iff_cut_by_nonReturn

/--
info: 'WAA.Grid.arhatPathQuiet_iff_fiberAtPole' does not depend on any axioms
-/
#guard_msgs in
#print axioms Grid.arhatPathQuiet_iff_fiberAtPole

/--
info: 'WAA.Grid.all_fetters_cut_at_arhatFiber' does not depend on any axioms
-/
#guard_msgs in
#print axioms Grid.all_fetters_cut_at_arhatFiber

/--
info: 'WAA.Grid.identityView_excluded_at_arhatFiber' does not depend on any axioms
-/
#guard_msgs in
#print axioms Grid.identityView_excluded_at_arhatFiber

/--
info: 'WAA.Grid.conceit_excluded_at_arhatFiber' does not depend on any axioms
-/
#guard_msgs in
#print axioms Grid.conceit_excluded_at_arhatFiber

/--
info: 'WAA.Grid.waaIrreversibleRegime_conditional' does not depend on any axioms
-/
#guard_msgs in
#print axioms Grid.waaIrreversibleRegime_conditional

/--
info: 'WAA.Grid.lower_fetters_covered_by_rites_view_resolve' does not depend on any axioms
-/
#guard_msgs in
#print axioms Grid.lower_fetters_covered_by_rites_view_resolve

/--
info: 'WAA.Grid.waaStreamWinner_iff_streamEntry_cutClasses' does not depend on any axioms
-/
#guard_msgs in
#print axioms Grid.waaStreamWinner_iff_streamEntry_cutClasses

/--
info: 'WAA.Grid.waaNonReturner_iff_nonReturn_cut' does not depend on any axioms
-/
#guard_msgs in
#print axioms Grid.waaNonReturner_iff_nonReturn_cut

/--
info: 'WAA.Grid.waaSerialFactorRegime_conditional' does not depend on any axioms
-/
#guard_msgs in
#print axioms Grid.waaSerialFactorRegime_conditional

/--
info: 'WAA.Grid.waaOnceReturner_attenuation_witness' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Grid.waaOnceReturner_attenuation_witness

/--
info: 'WAA.FactorsNegative.no_hold_conceit_boundary_recovery' does not depend on any axioms
-/
#guard_msgs in
#print axioms FactorsNegative.no_hold_conceit_boundary_recovery

/--
info: 'WAA.FactorsNegative.seen_run_underdetermines_factorOrder' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms FactorsNegative.seen_run_underdetermines_factorOrder

/--
info: 'WAA.FactorsNegative.lineage_underdetermined_by_seen_run' does not depend on any axioms
-/
#guard_msgs in
#print axioms FactorsNegative.lineage_underdetermined_by_seen_run

/--
info: 'WAA.FettersNegative.seen_run_underdetermines_fetterCut' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms FettersNegative.seen_run_underdetermines_fetterCut

/--
info: 'WAA.Grid.DirectedConvention.waaPathOught_conditional' does not depend on any axioms
-/
#guard_msgs in
#print axioms Grid.DirectedConvention.waaPathOught_conditional

/--
info: 'WAA.Grid.DirectedConvention.waaFaithOught_conditional' does not depend on any axioms
-/
#guard_msgs in
#print axioms Grid.DirectedConvention.waaFaithOught_conditional

/--
info: 'WAA.Grid.DirectedConvention.map_waaFaithPrinciple_reflect' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Grid.DirectedConvention.map_waaFaithPrinciple_reflect

/--
info: 'WAA.FaithNegative.waaFaithPrinciple_id_fails' does not depend on any axioms
-/
#guard_msgs in
#print axioms FaithNegative.waaFaithPrinciple_id_fails

/--
info: 'WAA.Grid.DirectedConvention.no_waa_path_at_pole' does not depend on any axioms
-/
#guard_msgs in
#print axioms Grid.DirectedConvention.no_waa_path_at_pole

/--
info: 'WAA.Grid.DirectedConvention.BeingConvention.GridConvention.rowOf_obeys' does not depend on any axioms
-/
#guard_msgs in
#print axioms Grid.DirectedConvention.BeingConvention.GridConvention.rowOf_obeys

/--
info: 'WAA.Grid.DirectedConvention.BeingConvention.GridConvention.pole_validates_all_claims' does not depend on any axioms
-/
#guard_msgs in
#print axioms Grid.DirectedConvention.BeingConvention.GridConvention.pole_validates_all_claims

/--
info: 'WAA.Grid.DirectedConvention.BeingConvention.GridConvention.denied_misfits_live_offer' does not depend on any axioms
-/
#guard_msgs in
#print axioms Grid.DirectedConvention.BeingConvention.GridConvention.denied_misfits_live_offer

/--
info: 'WAA.Grid.DirectedConvention.BeingConvention.GridConvention.rowOf_obeys_iff_errorFree' does not depend on any axioms
-/
#guard_msgs in
#print axioms Grid.DirectedConvention.BeingConvention.GridConvention.rowOf_obeys_iff_errorFree

/--
info: 'WAA.Grid.DirectedConvention.BeingConvention.GridConvention.reEmptied_obeys_of_errorFree' does not depend on any axioms
-/
#guard_msgs in
#print axioms Grid.DirectedConvention.BeingConvention.GridConvention.reEmptied_obeys_of_errorFree

/--
info: 'WAA.rung_not_pole_witness' does not depend on any axioms
-/
#guard_msgs in
#print axioms rung_not_pole_witness

/--
info: 'WAA.standing_does_not_determine_dated' does not depend on any axioms
-/
#guard_msgs in
#print axioms standing_does_not_determine_dated

/--
info: 'WAA.Grid.DirectedConvention.map_waaAversionContext_iff' does not depend on any axioms
-/
#guard_msgs in
#print axioms Grid.DirectedConvention.map_waaAversionContext_iff

/--
info: 'WAA.OrthogonalityNegative.waaFullyEnlightened_stronger_than_terminus' does not depend on any axioms
-/
#guard_msgs in
#print axioms OrthogonalityNegative.waaFullyEnlightened_stronger_than_terminus

/--
info: 'WAA.MisFeedNegative.fence_and_gate' does not depend on any axioms
-/
#guard_msgs in
#print axioms MisFeedNegative.fence_and_gate

/--
info: 'WAA.misFeed_entries_carry_decomposition' does not depend on any axioms
-/
#guard_msgs in
#print axioms misFeed_entries_carry_decomposition

/--
info: 'WAA.Grid.grade_independent_of_conditions' does not depend on any axioms
-/
#guard_msgs in
#print axioms Grid.grade_independent_of_conditions

/--
info: 'WAA.Grid.rePitch_forgets' does not depend on any axioms
-/
#guard_msgs in
#print axioms Grid.rePitch_forgets

/--
info: 'WAA.Grid.stone_of_no_call' does not depend on any axioms
-/
#guard_msgs in
#print axioms Grid.stone_of_no_call

/--
info: 'WAA.Grid.respondsToEveryCall_of_no_call' does not depend on any axioms
-/
#guard_msgs in
#print axioms Grid.respondsToEveryCall_of_no_call

/--
info: 'WAA.Grid.allStone_of_no_being' does not depend on any axioms
-/
#guard_msgs in
#print axioms Grid.allStone_of_no_being

/--
info: 'WAA.ContentNegative.emptyCallGrid_false_stone_and_respondsToEveryCall' does not depend on any axioms
-/
#guard_msgs in
#print axioms ContentNegative.emptyCallGrid_false_stone_and_respondsToEveryCall

/--
info: 'WAA.ContentNegative.emptyBeingGrid_no_liveTier' does not depend on any axioms
-/
#guard_msgs in
#print axioms ContentNegative.emptyBeingGrid_no_liveTier

/--
info: 'WAA.ContentNegative.contentBeingsRow_obeys_emptyBeing' does not depend on any axioms
-/
#guard_msgs in
#print axioms ContentNegative.contentBeingsRow_obeys_emptyBeing

/--
info: 'WAA.Grid.DirectedConvention.PrudentialPrivilegeNegative.prudentialPrivilege_failure_modes' does not depend on any axioms
-/
#guard_msgs in
#print axioms Grid.DirectedConvention.PrudentialPrivilegeNegative.prudentialPrivilege_failure_modes

/--
info: 'WAA.Grid.ConsequentialistConvention.dropCountInFiber_le_dropCount' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Grid.ConsequentialistConvention.dropCountInFiber_le_dropCount

/--
info: 'WAA.Grid.ConsequentialistConvention.dropCount_eq_sum_dropCountInFiber' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Grid.ConsequentialistConvention.dropCount_eq_sum_dropCountInFiber

/--
info: 'WAA.Grid.ConsequentialistConvention.map_dropCountInFiberSum' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Grid.ConsequentialistConvention.map_dropCountInFiberSum

/--
info: 'WAA.ObjectiveNegative.split_dropCount_sum_eq_mergedDropCount' does not depend on any axioms
-/
#guard_msgs in
#print axioms ObjectiveNegative.split_dropCount_sum_eq_mergedDropCount

/--
info: 'WAA.ObjectiveNegative.no_grid_data_objective_for_my_drops' does not depend on any axioms
-/
#guard_msgs in
#print axioms ObjectiveNegative.no_grid_data_objective_for_my_drops

/--
info: 'WAA.TransferNegative.adaptive_track_record_underdetermines_new_effect' does not depend on any axioms
-/
#guard_msgs in
#print axioms TransferNegative.adaptive_track_record_underdetermines_new_effect

/--
info: 'WAA.DeliveryArrogationNegative.command_utterance_not_fits' does not depend on any axioms
-/
#guard_msgs in
#print axioms DeliveryArrogationNegative.command_utterance_not_fits

/--
info: 'WAA.Grid.DirectedConvention.landing_call_in_modality' does not depend on any axioms
-/
#guard_msgs in
#print axioms Grid.DirectedConvention.landing_call_in_modality

/--
info: 'WAA.LedgerCase.decree_engineers_calls_not_receptions' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms LedgerCase.decree_engineers_calls_not_receptions

/--
info: 'WAA.LedgerCase.purge_loop_runs_on' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms LedgerCase.purge_loop_runs_on

/--
info: 'WAA.InteriorDirectionNegative.transposeCR_involutive' does not depend on any axioms
-/
#guard_msgs in
#print axioms InteriorDirectionNegative.transposeCR_involutive

/--
info: 'WAA.InteriorDirectionNegative.unorderedCRContent_transpose_invariant' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms InteriorDirectionNegative.unorderedCRContent_transpose_invariant

/--
info: 'WAA.InteriorDirectionNegative.transpose_swaps_readings' does not depend on any axioms
-/
#guard_msgs in
#print axioms InteriorDirectionNegative.transpose_swaps_readings

/--
info: 'WAA.DoerDeedNegative.priority_readings_disagree' does not depend on any axioms
-/
#guard_msgs in
#print axioms DoerDeedNegative.priority_readings_disagree

/--
info: 'WAA.DoerDeedNegative.no_priority_recovery' does not depend on any axioms
-/
#guard_msgs in
#print axioms DoerDeedNegative.no_priority_recovery

/--
info: 'WAA.ContentNegative.constantResponseGrid_no_variation' does not depend on any axioms
-/
#guard_msgs in
#print axioms ContentNegative.constantResponseGrid_no_variation

/--
info: 'WAA.ContentNegative.constantResponseWeld_no_live_share' does not depend on any axioms
-/
#guard_msgs in
#print axioms ContentNegative.constantResponseWeld_no_live_share

/--
info: 'WAA.ContentNegative.contentIntraWeldArrowRow_not_fused_constantResponse' does not depend on any axioms
-/
#guard_msgs in
#print axioms ContentNegative.contentIntraWeldArrowRow_not_fused_constantResponse

/--
info: 'WAA.ContentNegative.contentIntraWeldArrowRow_not_obeys_constantResponse' does not depend on any axioms
-/
#guard_msgs in
#print axioms ContentNegative.contentIntraWeldArrowRow_not_obeys_constantResponse

/--
info: 'WAA.Grid.DirectedConvention.BeingConvention.GridConvention.intraWeldArrowRow_obeys' does not depend on any axioms
-/
#guard_msgs in
#print axioms Grid.DirectedConvention.BeingConvention.GridConvention.intraWeldArrowRow_obeys

/--
info: 'WAA.Grid.DirectedConvention.BeingConvention.GridConvention.intraWeldArrowRow_not_freeze' does not depend on any axioms
-/
#guard_msgs in
#print axioms Grid.DirectedConvention.BeingConvention.GridConvention.intraWeldArrowRow_not_freeze

/--
info: 'WAA.Grid.DirectedConvention.BeingConvention.GridConvention.no_order_collapse_self_refuting' does not depend on any axioms
-/
#guard_msgs in
#print axioms Grid.DirectedConvention.BeingConvention.GridConvention.no_order_collapse_self_refuting

/--
info: 'WAA.Grid.DirectedConvention.BeingConvention.GridConvention.doerDeedRow_obeys' does not depend on any axioms
-/
#guard_msgs in
#print axioms Grid.DirectedConvention.BeingConvention.GridConvention.doerDeedRow_obeys

/--
info: 'WAA.Grid.DirectedConvention.BeingConvention.GridConvention.doerDeedRow_not_freeze' does not depend on any axioms
-/
#guard_msgs in
#print axioms Grid.DirectedConvention.BeingConvention.GridConvention.doerDeedRow_not_freeze

/--
info: 'WAA.Grid.DirectedConvention.BeingConvention.GridConvention.no_prior_doer_collapse_self_refuting' does not depend on any axioms
-/
#guard_msgs in
#print axioms Grid.DirectedConvention.BeingConvention.GridConvention.no_prior_doer_collapse_self_refuting

/--
info: 'WAA.Grid.DirectedConvention.BeingConvention.GridConvention.contentLayerRow_obeys_of_variation' does not depend on any axioms
-/
#guard_msgs in
#print axioms Grid.DirectedConvention.BeingConvention.GridConvention.contentLayerRow_obeys_of_variation

/--
info: 'WAA.Grid.DirectedConvention.BeingConvention.GridConvention.contentIntraWeldArrowRow_obeys_of_variation' does not depend on any axioms
-/
#guard_msgs in
#print axioms Grid.DirectedConvention.BeingConvention.GridConvention.contentIntraWeldArrowRow_obeys_of_variation

/--
info: 'WAA.Grid.DirectedConvention.BeingConvention.GridConvention.interior_order_denial_unfit_for_live_utterer' does not depend on any axioms
-/
#guard_msgs in
#print axioms Grid.DirectedConvention.BeingConvention.GridConvention.interior_order_denial_unfit_for_live_utterer

/--
info: 'WAA.Grid.DirectedConvention.BeingConvention.GridConvention.intraWeldArrowLadder_obeys' does not depend on any axioms
-/
#guard_msgs in
#print axioms Grid.DirectedConvention.BeingConvention.GridConvention.intraWeldArrowLadder_obeys

/--
info: 'WAA.Grid.DirectedConvention.BeingConvention.GridConvention.intraWeldArrowLadder_obeys_succ' does not depend on any axioms
-/
#guard_msgs in
#print axioms Grid.DirectedConvention.BeingConvention.GridConvention.intraWeldArrowLadder_obeys_succ

/--
info: 'WAA.Grid.DirectedConvention.BeingConvention.GridConvention.intraWeldArrowLadder_no_level_final' does not depend on any axioms
-/
#guard_msgs in
#print axioms Grid.DirectedConvention.BeingConvention.GridConvention.intraWeldArrowLadder_no_level_final

/--
info: 'WAA.Grid.DirectedConvention.BeingConvention.GridConvention.doerDeedLadder_obeys' does not depend on any axioms
-/
#guard_msgs in
#print axioms Grid.DirectedConvention.BeingConvention.GridConvention.doerDeedLadder_obeys

/--
info: 'WAA.Grid.DirectedConvention.BeingConvention.GridConvention.doerDeedLadder_obeys_succ' does not depend on any axioms
-/
#guard_msgs in
#print axioms Grid.DirectedConvention.BeingConvention.GridConvention.doerDeedLadder_obeys_succ

/--
info: 'WAA.Grid.DirectedConvention.BeingConvention.GridConvention.doerDeedLadder_no_level_final' does not depend on any axioms
-/
#guard_msgs in
#print axioms Grid.DirectedConvention.BeingConvention.GridConvention.doerDeedLadder_no_level_final

/--
info: 'WAA.Grid.DirectedConvention.BeingConvention.GridConvention.Nishitani.intraWeldArrow_sunyata' does not depend on any axioms
-/
#guard_msgs in
#print axioms Grid.DirectedConvention.BeingConvention.GridConvention.Nishitani.intraWeldArrow_sunyata

/--
info: 'WAA.Grid.DirectedConvention.BeingConvention.GridConvention.Nishitani.doerDeed_sunyata' does not depend on any axioms
-/
#guard_msgs in
#print axioms Grid.DirectedConvention.BeingConvention.GridConvention.Nishitani.doerDeed_sunyata

/--
info: 'WAA.Grid.map_responseVariesWithCall_iff' does not depend on any axioms
-/
#guard_msgs in
#print axioms Grid.map_responseVariesWithCall_iff

/--
info: 'WAA.Grid.DirectedConvention.BeingConvention.GridConvention.map_intraWeldArrowRow_obeys' does not depend on any axioms
-/
#guard_msgs in
#print axioms Grid.DirectedConvention.BeingConvention.GridConvention.map_intraWeldArrowRow_obeys

/--
info: 'WAA.Grid.DirectedConvention.BeingConvention.GridConvention.map_doerDeedRow_obeys' does not depend on any axioms
-/
#guard_msgs in
#print axioms Grid.DirectedConvention.BeingConvention.GridConvention.map_doerDeedRow_obeys

/--
info: 'WAA.Grid.DirectedConvention.BeingConvention.GridConvention.map_contentIntraWeldArrowRow_obeys_of_variation' does not depend on any axioms
-/
#guard_msgs in
#print axioms Grid.DirectedConvention.BeingConvention.GridConvention.map_contentIntraWeldArrowRow_obeys_of_variation

/--
info: 'WAA.Grid.DirectedConvention.BeingConvention.GridConvention.map_intraWeldArrowLadder_obeys' does not depend on any axioms
-/
#guard_msgs in
#print axioms Grid.DirectedConvention.BeingConvention.GridConvention.map_intraWeldArrowLadder_obeys

/--
info: 'WAA.Grid.DirectedConvention.BeingConvention.GridConvention.map_intraWeldArrowLadder_obeys_succ' does not depend on any axioms
-/
#guard_msgs in
#print axioms Grid.DirectedConvention.BeingConvention.GridConvention.map_intraWeldArrowLadder_obeys_succ

/--
info: 'WAA.Grid.DirectedConvention.BeingConvention.GridConvention.map_intraWeldArrowLadder_no_level_final' does not depend on any axioms
-/
#guard_msgs in
#print axioms Grid.DirectedConvention.BeingConvention.GridConvention.map_intraWeldArrowLadder_no_level_final

/--
info: 'WAA.Grid.DirectedConvention.BeingConvention.GridConvention.map_doerDeedLadder_obeys' does not depend on any axioms
-/
#guard_msgs in
#print axioms Grid.DirectedConvention.BeingConvention.GridConvention.map_doerDeedLadder_obeys

/--
info: 'WAA.Grid.DirectedConvention.BeingConvention.GridConvention.map_doerDeedLadder_obeys_succ' does not depend on any axioms
-/
#guard_msgs in
#print axioms Grid.DirectedConvention.BeingConvention.GridConvention.map_doerDeedLadder_obeys_succ

/--
info: 'WAA.Grid.DirectedConvention.BeingConvention.GridConvention.map_doerDeedLadder_no_level_final' does not depend on any axioms
-/
#guard_msgs in
#print axioms Grid.DirectedConvention.BeingConvention.GridConvention.map_doerDeedLadder_no_level_final

/--
info: 'WAA.Grid.DirectedConvention.BeingConvention.GridConvention.ladderRungGrid_beings_sunyata' does not depend on any axioms
-/
#guard_msgs in
#print axioms Grid.DirectedConvention.BeingConvention.GridConvention.ladderRungGrid_beings_sunyata

/--
info: 'WAA.Grid.DirectedConvention.BeingConvention.GridConvention.ladderRungGrid_no_level_final' does not depend on any axioms
-/
#guard_msgs in
#print axioms Grid.DirectedConvention.BeingConvention.GridConvention.ladderRungGrid_no_level_final

end WAA
