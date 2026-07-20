import Lean
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
import WeldAndArrow.Doctrines.EffectiveTerminusNegative
import WeldAndArrow.Doctrines.Shusho

namespace WAA

/-- One declaration and the exact set of axioms it is permitted to use. -/
structure AxiomAuditEntry where
  name : Lean.Name
  allowed : List Lean.Name := []
deriving Repr

/-- The single source of truth for the project's axiom audit. -/
def axiomAuditLedger : List AxiomAuditEntry := [
  { name := ``no_agent_recovery_of_field_collision },
  { name := ``Grid.DirectedConvention.DirectionCoarsening.no_timeDirection_within_tick },
  { name := ``Grid.DirectedConvention.DirectionCoarsening.no_timeDirection_of_resolutionBounded_subsingleton },
  { name := ``Grid.relabel_rePitch },
  { name := ``Grid.no_natural_agent_recovery_from_config },
  { name := ``ConfigLeakWitness.registerClock_config_recovers_agent },
  { name := ``ConfigLeakWitness.no_agent_recovery_from_config_of_share_collision },
  { name := ``strict_asymm },
  { name := ``strict_trans },
  { name := ``Grid.transpose_transpose },
  { name := ``DirectionNegative.no_direction_recovery_from_conditionsEither,
    allowed := [``propext, ``Quot.sound] },
  { name := ``CoverageNegative.directionVoid_needs_coverage },
  { name := ``CoverageNegative.waaEffectiveTerminus_needs_coverage },
  { name := ``Grid.stateToolFits_iff_atBot },
  { name := ``Grid.map_actual_iff },
  { name := ``Grid.map_isShareDrop_iff },
  { name := ``Grid.map_transpose },
  { name := ``Grid.staticized_transpose },
  { name := ``Grid.map_staticized },
  { name := ``Grid.DirectedConvention.DirectionCoarsening.mapDir_resolutionBounded_iff },
  { name := ``DirectionCoarseningWitness.registerClock_unitTick_not_resolutionBounded },
  { name := ``DirectionCoarseningWitness.unit_directionVoid_via_mergeToUnit },
  { name := ``DirectionCoarseningWitness.fullyCoarseRegisterClock_no_timeDirection },
  { name := ``DirectionCoarseningWitness.registerClock_directionCoarsening_independence },
  { name := ``Grid.DirectedConvention.map_landsWithShareDrop_iff },
  { name := ``Grid.DirectedConvention.BeingConvention.BeingCoarsening.map_selfConditioningTag_iff },
  { name := ``Grid.DirectedConvention.BeingConvention.BeingCoarsening.map_fiberAtPoleOn_iff },
  { name := ``Grid.DirectedConvention.BeingConvention.BeingCoarsening.total_sameFiber },
  { name := ``Grid.DirectedConvention.BeingConvention.BeingCoarsening.id_not_sameFiber_of_ne },
  { name := ``Grid.map_waaBullSeven_iff },
  { name := ``Grid.map_waaBullTen_iff },
  { name := ``Grid.bullSeven_not_bullEight },
  { name := ``Grid.bullTen_to_bullNine },
  { name := ``CorrelationsNegative.pratyekabuddha_countermodel },
  { name := ``CorrelationsNegative.no_stage_boundary_recovery },
  { name := ``Grid.classQuiet_no_clench_in_class },
  { name := ``Fetter.kind_lower_iff_cut_by_nonReturn },
  { name := ``Grid.arhatPathQuiet_iff_quietOn_univ },
  { name := ``Grid.all_fetters_cut_at_arhat },
  { name := ``Grid.identityView_cut_iff_noDefiledVoicing },
  { name := ``Grid.conceit_excluded_of_quietOn },
  { name := ``Grid.waaIrreversibleRegime_conditional },
  { name := ``Grid.lower_fetters_covered_by_rites_view_resolve },
  { name := ``Grid.waaStreamWinner_iff_streamEntry_cutClasses },
  { name := ``Grid.waaNonReturner_iff_nonReturn_cut },
  { name := ``Grid.waaSerialFactorRegime_conditional },
  { name := ``Grid.waaOnceReturner_attenuation_witness, allowed := [``propext] },
  { name := ``FactorsNegative.no_hold_conceit_boundary_recovery },
  { name := ``FactorsNegative.factor_order_underdetermined, allowed := [``propext] },
  { name := ``FettersNegative.seen_run_underdetermines_fetterCut, allowed := [``propext] },
  { name := ``Grid.DirectedConvention.waaPathOught_conditional },
  { name := ``Grid.DirectedConvention.waaFaithOught_conditional },
  { name := ``Grid.DirectedConvention.waa_says_true_of_faith },
  { name := ``Grid.DirectedConvention.noDelusion_of_noNescience_of_terminus },
  { name := ``Grid.DirectedConvention.waaFullyEnlightened_of_fullyEnlightenedEnacted },
  { name := ``FaithNegative.noNescience_strictly_stronger_witness,
    allowed := [``propext] },
  { name := ``FaithNegative.aklishta_ajnana_witness },
  { name := ``FaithNegative.arhat_retains_nescience_witness,
    allowed := [``propext] },
  { name := ``FaithNegative.Sealed.silent_buddha_models,
    allowed := [``propext] },
  { name := ``Grid.DirectedConvention.no_waa_path_at_pole },
  { name := ``Grid.DirectedConvention.BeingConvention.GridConvention.rowOf_obeys },
  { name := ``Grid.DirectedConvention.BeingConvention.GridConvention.pole_validates_all_claims },
  { name := ``Grid.DirectedConvention.BeingConvention.GridConvention.denied_misfits_live_offer },
  { name := ``Grid.DirectedConvention.BeingConvention.GridConvention.rowOf_obeys_iff_errorFree },
  { name := ``Grid.DirectedConvention.BeingConvention.GridConvention.reEmptied_obeys_of_errorFree },
  { name := ``rung_not_pole_witness },
  { name := ``standing_does_not_determine_dated },
  { name := ``Grid.DirectedConvention.map_waaAversionContext_iff },
  { name := ``OrthogonalityNegative.waaEffectiveTerminus_stronger_than_terminus },
  { name := ``MisFeedNegative.fence_and_gate },
  { name := ``misFeed_entries_carry_decomposition },
  { name := ``Grid.grade_independent_of_conditions },
  { name := ``Grid.rePitch_forgets },
  { name := ``Grid.stone_of_no_call },
  { name := ``Grid.respondsToEveryCall_of_no_call },
  { name := ``Grid.allStone_of_no_being },
  { name := ``ContentNegative.emptyCallGrid_false_stone_and_respondsToEveryCall },
  { name := ``ContentNegative.emptyBeingGrid_no_liveTier },
  { name := ``ContentNegative.contentBeingsRow_obeys_emptyBeing },
  { name := ``Grid.DirectedConvention.PrudentialPrivilegeNegative.prudentialPrivilege_failure_modes },
  { name := ``Grid.ConsequentialistConvention.dropCountInFiber_le_dropCount,
    allowed := [``propext] },
  { name := ``Grid.ConsequentialistConvention.dropCount_eq_sum_dropCountInFiber,
    allowed := [``propext] },
  { name := ``Grid.ConsequentialistConvention.map_dropCountInFiberSum,
    allowed := [``propext] },
  { name := ``ObjectiveNegative.split_dropCount_sum_eq_mergedDropCount },
  { name := ``ObjectiveNegative.no_grid_data_objective_for_my_drops },
  { name := ``TransferNegative.adaptive_track_record_underdetermines_new_effect },
  { name := ``Grid.DirectedConvention.not_effectivenessEnacted_of_undelivered },
  { name := ``EffectiveTerminusNegative.no_effectiveTerminus_recovery_from_run },
  { name := ``DeliveryArrogationNegative.command_utterance_not_fits },
  { name := ``Grid.DirectedConvention.landing_call_in_modality },
  { name := ``LedgerCase.decree_engineers_calls_not_receptions, allowed := [``propext] },
  { name := ``LedgerCase.purge_loop_runs_on, allowed := [``propext] },
  { name := ``InteriorDirectionNegative.transposeCR_involutive },
  { name := ``InteriorDirectionNegative.unorderedCRContent_transpose_invariant,
    allowed := [``propext] },
  { name := ``InteriorDirectionNegative.transpose_swaps_readings },
  { name := ``DoerDeedNegative.priority_readings_disagree },
  { name := ``DoerDeedNegative.no_priority_recovery },
  { name := ``ContentNegative.constantResponseGrid_no_variation },
  { name := ``ContentNegative.constantResponseWeld_no_live_share },
  { name := ``ContentNegative.contentIntraWeldArrowRow_not_fused_constantResponse },
  { name := ``ContentNegative.contentIntraWeldArrowRow_not_obeys_constantResponse },
  { name := ``Grid.DirectedConvention.BeingConvention.GridConvention.intraWeldArrowRow_obeys },
  { name := ``Grid.DirectedConvention.BeingConvention.GridConvention.intraWeldArrowRow_not_freeze },
  { name := ``Grid.DirectedConvention.BeingConvention.GridConvention.no_order_collapse_self_refuting },
  { name := ``Grid.DirectedConvention.BeingConvention.GridConvention.doerDeedRow_obeys },
  { name := ``Grid.DirectedConvention.BeingConvention.GridConvention.doerDeedRow_not_freeze },
  { name := ``Grid.DirectedConvention.BeingConvention.GridConvention.no_prior_doer_collapse_self_refuting },
  { name := ``Grid.DirectedConvention.BeingConvention.GridConvention.contentLayerRow_obeys_of_variation },
  { name := ``Grid.DirectedConvention.BeingConvention.GridConvention.contentIntraWeldArrowRow_obeys_of_variation },
  { name := ``Grid.DirectedConvention.BeingConvention.GridConvention.interior_order_denial_unfit_for_live_utterer },
  { name := ``Grid.DirectedConvention.BeingConvention.GridConvention.intraWeldArrowLadder_obeys },
  { name := ``Grid.DirectedConvention.BeingConvention.GridConvention.intraWeldArrowLadder_obeys_succ },
  { name := ``Grid.DirectedConvention.BeingConvention.GridConvention.intraWeldArrowLadder_no_level_final },
  { name := ``Grid.DirectedConvention.BeingConvention.GridConvention.doerDeedLadder_obeys },
  { name := ``Grid.DirectedConvention.BeingConvention.GridConvention.doerDeedLadder_obeys_succ },
  { name := ``Grid.DirectedConvention.BeingConvention.GridConvention.doerDeedLadder_no_level_final },
  { name := ``Grid.DirectedConvention.BeingConvention.GridConvention.Metaphysics.intraWeldArrow_sunyata },
  { name := ``Grid.DirectedConvention.BeingConvention.GridConvention.Metaphysics.doerDeed_sunyata },
  { name := ``Grid.map_responseVariesWithCall_iff },
  { name := ``Grid.DirectedConvention.BeingConvention.GridConvention.map_intraWeldArrowRow_obeys },
  { name := ``Grid.DirectedConvention.BeingConvention.GridConvention.map_doerDeedRow_obeys },
  { name := ``Grid.DirectedConvention.BeingConvention.GridConvention.map_contentIntraWeldArrowRow_obeys_of_variation },
  { name := ``Grid.DirectedConvention.BeingConvention.GridConvention.map_intraWeldArrowLadder_obeys },
  { name := ``Grid.DirectedConvention.BeingConvention.GridConvention.map_intraWeldArrowLadder_obeys_succ },
  { name := ``Grid.DirectedConvention.BeingConvention.GridConvention.map_intraWeldArrowLadder_no_level_final },
  { name := ``Grid.DirectedConvention.BeingConvention.GridConvention.map_doerDeedLadder_obeys },
  { name := ``Grid.DirectedConvention.BeingConvention.GridConvention.map_doerDeedLadder_obeys_succ },
  { name := ``Grid.DirectedConvention.BeingConvention.GridConvention.map_doerDeedLadder_no_level_final },
  { name := ``Grid.DirectedConvention.BeingConvention.GridConvention.ladderRungGrid_beings_sunyata },
  { name := ``Grid.DirectedConvention.BeingConvention.GridConvention.ladderRungGrid_no_level_final }
]

open Lean Elab Command Meta

syntax (name := verifyAxiomAudit) "#verify_axiom_audit" : command

unsafe def evalAxiomAuditLedger : Term.TermElabM (List AxiomAuditEntry) := do
  evalExpr (List AxiomAuditEntry)
    (mkApp (mkConst ``List [Level.zero]) (mkConst ``AxiomAuditEntry))
    (mkConst ``axiomAuditLedger)

private def renderNames (names : List Lean.Name) : String :=
  "[" ++ String.intercalate ", " (names.map (fun name => name.toString)) ++ "]"

@[command_elab verifyAxiomAudit] unsafe def elabVerifyAxiomAudit : CommandElab :=
    fun _stx => do
  let entries <- liftTermElabM evalAxiomAuditLedger
  let env <- getEnv
  let mut failures : Array String := #[]
  for entry in entries do
    if !env.contains entry.name then
      failures := failures.push s!"{entry.name}: declaration is not in the environment"
    else
      let actual := (← Lean.collectAxioms entry.name).toList
      let unexpected := actual.filter (fun name => !entry.allowed.contains name)
      let absent := entry.allowed.filter (fun name => !actual.contains name)
      unless unexpected.isEmpty && absent.isEmpty do
        failures := failures.push
          s!"{entry.name}: unexpected {renderNames unexpected}; expected-but-absent {renderNames absent}; allowed {renderNames entry.allowed}; actual {renderNames actual}"
  unless failures.isEmpty do
    let details := failures.foldl (fun acc item => acc ++ "\n" ++ item) ""
    throwError m!"axiom audit failed:{details}"

#verify_axiom_audit

end WAA
