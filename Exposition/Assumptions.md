<!-- GENERATED from WeldAndArrow/Meta/AssumptionLedger.lean by `lake exe exposition_gen` - do not edit -->

# Assumptions

Generated from `WeldAndArrow/Meta/AssumptionLedger.lean` by `lake exe exposition_gen`. `WeldAndArrow/Meta/AxiomAudit.lean` holds the compile-checked axiom ledger; statement prose is canonical here.

## A. What Is Asserted

### A.1 No prior agent

A weld is the primitive occurrence. `Grid.index` and `Grid.share` are projections from a completed `RawWeld`, not fields recovered from a separate performer or act. `no_agent_recovery_of_field_collision` records the internal obstruction: the same call-response field residue can be produced by distinct actual agents.

**Checked anchors (Signature):** `WAA.RawWeld` (proof), `WAA.Grid.index` (proof), `WAA.Grid.share` (proof), `WAA.no_agent_recovery_of_field_collision` (witness)

### A.2 Nothing self-indexed is stored

`Config` stores only `tendency : Contrib`. It has no owner, being, weld, or field-residue slot. `rePitch` uses the received weld's share and ignores the prior configuration value. The checked claim is architectural and definability-level: the record has no `Being`-typed slot, relabelling agents acts trivially on configurations and commutes with `rePitch`, and no relabelling-equivariant recovery of an agent from a configuration exists. It is not an information-flow claim; see the declined entry below.

**Checked anchors (Signature):** `WAA.Config` (proof), `WAA.Config.tendency` (proof), `WAA.Grid.rePitch` (proof), `WAA.RawWeld.mapAgent` (proof)

**Downstream elaboration:** `WAA.Config.relabel_fixed` (proof), `WAA.Grid.relabel_rePitch` (proof), `WAA.Grid.no_natural_agent_recovery_from_config` (witness), `WAA.ConfigLeakWitness.no_agent_recovery_from_config_of_share_collision` (witness)

### A.3 The self-pole index is just live share

`HasSelfPoleIndex w` is `not AtBot (share w)`, and when the predicate is live the carried `selfPoleIndex` is the weld's agent tag.

**Checked anchors (Signature):** `WAA.Grid.HasSelfPoleIndex` (proof), `WAA.Grid.selfPoleIndex_eq_agent_of_hasSelfPoleIndex` (proof), `WAA.Grid.no_self_pole_index_of_atBot` (proof)

### A.4 Stone and terminus split function from share

A `Stone` mounts no response. A `Terminus` may mount responses, but every mounted response is at the pole-class. `AtPoleClass` intentionally includes the vacuous stone case.

**Checked anchors (Signature):** `WAA.Grid.Stone` (proof), `WAA.Grid.Terminus` (proof), `WAA.Grid.AtPoleClass` (proof), `WAA.Grid.stone_is_terminus_vacuously` (proof), `WAA.clockGrid_function_share_split_witness` (witness)

### A.5 Self-lines are permitted, not built in

The bare signature does not impose irreflexivity on `conditions`; a model may supply reflexive delivery, and then the directed vocabulary can read a self-line.

**Checked anchors (Signature):** `WAA.Grid.conditions` (proof), `WAA.Grid.DirectedConvention.DeliveredTo` (proof), `WAA.Grid.DirectedConvention.LandsAt` (proof), `WAA.AssumptionLocalWitnesses.signature_self_line_permitted` (witness)

**Downstream elaboration:** `WAA.SelfLineWitness.selfLine_landsAt_self` (witness), `WAA.SelfLineWitness.selfLine_waaOwnershipFace_self` (witness)

## B. What Is Deliberately Declined

### B.1 No arrow in `conditions`

The signature assumes no asymmetry, irreflexivity, or transitivity for `conditions`. `ConditionsEither` is the symmetric field fact; direction enters only in `Grid.DirectedConvention`. The downstream `DirectionNegative` witness elaborates this as non-recovery from symmetric closure.

**Checked anchors (Signature):** `WAA.Grid.ConditionsEither` (proof), `WAA.Grid.conditionsEither_symm` (proof), `WAA.Grid.DirectedConvention.TimeDirection` (proof), `WAA.Grid.transpose` (witness), `WAA.Grid.transpose_conditionsEither_iff` (witness), `WAA.Grid.DirectedConvention.transpose_deliveredTo_iff` (witness), `WAA.RawWeld.transposeCR` (witness), `WAA.AssumptionLocalWitnesses.no_direction_recovery_from_conditionsEither` (witness), `WAA.InteriorDirectionNegative.no_interior_direction_recovery` (witness)

**Downstream elaboration:** `WAA.DirectionNegative.no_direction_recovery_from_conditionsEither` (witness)

### B.2 No `PreorderTop`

The signature supplies only `PreorderBot`. The share-zero pole is an attained bottom order-class (`AtBot`); the total-share or solipsist pole is an asymptote, not an element of the interface. `StrongSelfConditioningTag` is named and shelved in the being convention for the same reason.

**Checked anchors (Signature):** `WAA.PreorderBot` (proof), `WAA.AtBot` (proof), `WAA.Grid.DirectedConvention.BeingConvention.BeingCoarsening.StrongSelfConditioningTag` (proof), `WAA.AssumptionLocalWitnesses.nat_preorderBot_has_no_top` (witness)

### B.3 No privileged person-partition

A being boundary is supplied by a diagnosis-time `BeingCoarsening`, not stored as a field of `Grid`. The signature already admits both identity and total coarsenings for any grid; the downstream `BeingNegative` witness elaborates this as non-recovery of a unique partition from grid data.

**Checked anchors (Signature):** `WAA.Grid.DirectedConvention.BeingConvention.BeingCoarsening` (proof), `WAA.Grid.DirectedConvention.BeingConvention.BeingCoarsening.InFiber` (proof), `WAA.Grid.DirectedConvention.BeingConvention.BeingCoarsening.SameFiber` (proof), `WAA.Grid.DirectedConvention.BeingConvention.BeingCoarsening.id` (witness), `WAA.Grid.DirectedConvention.BeingConvention.BeingCoarsening.total` (witness), `WAA.Grid.DirectedConvention.BeingConvention.BeingCoarsening.total_sameFiber` (witness), `WAA.Grid.DirectedConvention.BeingConvention.BeingCoarsening.id_not_sameFiber_of_ne` (witness), `WAA.AssumptionLocalWitnesses.partition_merge_split_disagree` (witness)

**Downstream elaboration:** `WAA.BeingNegative.no_partition_recovery` (witness)

### B.4 Direction resolution is display, not signature furniture

A clock's finite delivery-axis resolution is supplied by a diagnosis-time `DirectionCoarsening`, not by a `Grid` field and not by any pole or legitimacy predicate.

**Checked anchors (Signature):** `WAA.Grid.DirectedConvention.DirectionCoarsening` (proof), `WAA.Grid.DirectedConvention.DirectionCoarsening.SameTick` (proof), `WAA.Grid.DirectedConvention.DirectionCoarsening.ResolutionBounded` (proof), `WAA.Grid.DirectedConvention.DirectionCoarsening.no_timeDirection_within_tick` (proof), `WAA.Grid.DirectedConvention.DirectionCoarsening.no_timeDirection_of_resolutionBounded_subsingleton` (proof), `WAA.Grid.DirectedConvention.DirectionCoarsening.transpose_subTickDelivery` (witness)

**Downstream elaboration:** `WAA.DirectionCoarseningWitness.registerClock_unitTick_not_resolutionBounded` (witness), `WAA.DirectionCoarseningWitness.unit_directionVoid_via_mergeToUnit` (witness), `WAA.DirectionCoarseningWitness.fullyCoarseRegisterClock_no_timeDirection` (witness), `WAA.DirectionCoarseningWitness.registerClock_directionCoarsening_independence` (witness)

### B.5 Contribution values are display, not operational tokens

The Signature layer itself uses only order and pole vocabulary around `share`. The downstream `DisplayReparam` / `InvarianceNegative` modules give the full transport discipline: order- and pole-preserving display changes preserve the legal predicates, while equality to the chosen bottom does not.

**Checked anchors (Signature):** `WAA.Grid.share_eq_grade_check` (proof), `WAA.AtBot` (proof), `WAA.OrderEq` (proof), `WAA.Grid.Terminus` (proof)

**Downstream elaboration:** `WAA.DisplayReparam` (proof), `WAA.DisplayReparam.atBot_iff` (proof), `WAA.InvarianceNegative.oldEqTerminus_not_invariant` (witness)

### B.6 The enlightenment ladder names standing and enacted vacuity

The operational, assertable effectiveness content is per-occurrence: `WaaEffectiveOccurrence` states an actual pole-deed landing as a share-drop against a live prior tendency. The descriptive universal `WaaEffectiveTerminus` remains legal as run-display and direct-path hypothesis, but no estimator from actual-run response/share data decides it. Standing `WaaFullyEnlightened` adds positive own-act-time `WaaNoNescience` over speech-or-mind productions. A quiet arhat may still fail that cognitive conjunct; sealed silent and true-thinking buddhas witness its two silent faces. `WaaFullyEnlightenedEnacted` separately adds an effective deed witness and a production-tied speech occurrence.

**Checked anchors (Signature):** None.

**Downstream elaboration:** `WAA.Grid.DirectedConvention.WaaEffectiveOccurrence` (proof), `WAA.Grid.DirectedConvention.WaaEffectivenessEnacted` (proof), `WAA.Grid.DirectedConvention.not_effectivenessEnacted_of_undelivered` (proof), `WAA.Grid.DirectedConvention.WaaFullyEnlightened` (proof), `WAA.Grid.DirectedConvention.WaaNoNescience` (proof), `WAA.Grid.DirectedConvention.WaaFullyEnlightenedEnacted` (proof), `WAA.FaithNegative.noNescience_strictly_stronger_witness` (witness), `WAA.FaithNegative.arhat_retains_nescience_witness` (witness), `WAA.FaithNegative.Sealed.silent_buddha_models` (witness), `WAA.EffectiveTerminusNegative.actual_run_data_underdetermines_effectiveTerminus` (witness), `WAA.Grid.DirectedConvention.BeingConvention.GridConvention.waa_effective_occurrence_voice_assertable` (proof), `WAA.Grid.DirectedConvention.BeingConvention.GridConvention.waa_standing_effectiveness_voice_displayable` (proof)

### B.7 No blanket noninterference for the contribution carrier

Grading may depend on the agent — `gradingCollisionGrid` grades by being deliberately (cetanā) — so a model's stored tendency may extensionally coincide with an agent tag; `registerClockGrid` witnesses the coincidence. The signature therefore declines the information-flow reading of non-storage. `Grid.rePitch_forgets` bounds the coincidence to a single reception's footprint: nothing accumulates into a diachronic bearer, and the configuration is fibered over no being. The asserted claim is typing plus relabelling equivariance.

**Checked anchors (Signature):** `WAA.gradingCollisionGrid` (witness), `WAA.registerClockGrid` (witness)

**Downstream elaboration:** `WAA.ConfigLeakWitness.registerClock_config_recovers_agent` (witness), `WAA.Config.relabel_fixed` (proof), `WAA.Grid.relabel_rePitch` (proof), `WAA.Grid.rePitch_forgets` (proof)

### B.8 No recovered door boundary

`DoorReading` totally classifies fine welds as body, speech, or mind, but that diagnosis is supplied rather than recovered from response or grade data. Totality and adequacy to the canonical three doors are modeling claims.

**Checked anchors (Signature):** None.

**Downstream elaboration:** `WAA.Grid.DoorReading` (proof), `WAA.DoorsNegative.no_door_boundary_recovery` (witness)

### B.9 No recovered voicing

`SpeechReading` supplies optional content independently of door. Thoughts and bodily intimations are representable, while only speech productions cross into testimony; neither voicing nor its production weld is recovered from visible grid data or content alone.

**Checked anchors (Signature):** None.

**Downstream elaboration:** `WAA.Grid.SpeechReading` (proof), `WAA.Grid.ProducedUtterance` (proof), `WAA.DoorsNegative.no_voicing_recovery` (witness), `WAA.DoorsNegative.no_production_recovery` (witness)

### B.10 No recovered view content

`ViewReading.ownerClaim` supplies which claims count as stored-owner views. The checked coarsening-freeze model is a correlation for one such reading, not a derivation of content from the grid.

**Checked anchors (Signature):** None.

**Downstream elaboration:** `WAA.Grid.ViewReading` (proof), `WAA.FettersNegative.no_view_content_recovery` (witness), `WAA.FettersNegative.ownerClaim_coarsening_freeze_correlation` (witness)

## C. Conveniences and Stand-Ins

### C.1 Hand-rolled order classes

`Preorder` and `PreorderBot` are hand-rolled to keep assumptions visible and dependency-free. They play the local role Mathlib order classes would play, without importing Mathlib.

**Checked anchors (Signature):** `WAA.Preorder` (proof), `WAA.PreorderBot` (proof), `WAA.shareBot` (proof), `WAA.shareBot_le` (proof)

### C.2 `_before` is retained but currently ignored by `rePitch`

`rePitch` keeps a `_before` slot because the operation is conceptually a re-pitch from a prior configuration. The current implementation ignores that slot; the proof anchor below is a tripwire for the day that changes.

**Checked anchors (Signature):** `WAA.Grid.rePitch` (proof)

> Note: The signature file keeps an `rfl` example showing that two prior configurations produce the same re-pitch for the same received weld.

### C.3 The scalar is display over a partial order

`WaaMismatchGrade` lives in `Doctrines`, so this Signature module does not import it; the Signature-side checked fact is that `share` is the only contribution value exported by a weld.

**Checked anchors (Signature):** `WAA.Grid.share` (proof), `WAA.Grid.share_eq_grade_check` (proof)

**Downstream elaboration:** `WAA.Grid.WaaMismatchGrade` (proof), `WAA.Grid.waaMismatchGrade_eq_share` (proof)

### C.4 `Models.lean` witnesses are illustrative

The clock and register-clock models anchor possibility checks and taxonomy examples; they are not uniqueness claims.

**Checked anchors (Signature):** `WAA.clockGrid` (witness), `WAA.registerClockGrid` (witness), `WAA.registerClock_macro_sentient` (witness), `WAA.registerClock_macro_selfConditioning` (witness)

## Axiom audit

`#verify_axiom_audit` compares each declaration's collected axiom set with this allowlist during every build.

| Declaration | Allowed axioms |
|---|---|
| `WAA.no_agent_recovery_of_field_collision` | None |
| `WAA.Grid.DirectedConvention.DirectionCoarsening.no_timeDirection_within_tick` | None |
| `WAA.Grid.DirectedConvention.DirectionCoarsening.no_timeDirection_of_resolutionBounded_subsingleton` | None |
| `WAA.Grid.relabel_rePitch` | None |
| `WAA.Grid.no_natural_agent_recovery_from_config` | None |
| `WAA.ConfigLeakWitness.registerClock_config_recovers_agent` | None |
| `WAA.ConfigLeakWitness.no_agent_recovery_from_config_of_share_collision` | None |
| `WAA.strict_asymm` | None |
| `WAA.strict_trans` | None |
| `WAA.Grid.transpose_transpose` | None |
| `WAA.DirectionNegative.no_direction_recovery_from_conditionsEither` | `propext`, `Quot.sound` |
| `WAA.CoverageNegative.directionVoid_needs_coverage` | None |
| `WAA.CoverageNegative.waaEffectiveTerminus_needs_coverage` | None |
| `WAA.Grid.stateToolFits_iff_atBot` | None |
| `WAA.Grid.map_actual_iff` | None |
| `WAA.Grid.map_isShareDrop_iff` | None |
| `WAA.Grid.map_transpose` | None |
| `WAA.Grid.staticized_transpose` | None |
| `WAA.Grid.map_staticized` | None |
| `WAA.Grid.DirectedConvention.DirectionCoarsening.mapDir_resolutionBounded_iff` | None |
| `WAA.DirectionCoarseningWitness.registerClock_unitTick_not_resolutionBounded` | None |
| `WAA.DirectionCoarseningWitness.unit_directionVoid_via_mergeToUnit` | None |
| `WAA.DirectionCoarseningWitness.fullyCoarseRegisterClock_no_timeDirection` | None |
| `WAA.DirectionCoarseningWitness.registerClock_directionCoarsening_independence` | None |
| `WAA.Grid.DirectedConvention.map_landsWithShareDrop_iff` | None |
| `WAA.Grid.DirectedConvention.BeingConvention.BeingCoarsening.map_selfConditioningTag_iff` | None |
| `WAA.Grid.DirectedConvention.BeingConvention.BeingCoarsening.map_fiberAtPoleOn_iff` | None |
| `WAA.Grid.DirectedConvention.BeingConvention.BeingCoarsening.total_sameFiber` | None |
| `WAA.Grid.DirectedConvention.BeingConvention.BeingCoarsening.id_not_sameFiber_of_ne` | None |
| `WAA.Grid.map_waaBullSeven_iff` | None |
| `WAA.Grid.map_waaBullTen_iff` | None |
| `WAA.Grid.bullSeven_not_bullEight` | None |
| `WAA.Grid.bullTen_to_bullNine` | None |
| `WAA.CorrelationsNegative.pratyekabuddha_countermodel` | None |
| `WAA.CorrelationsNegative.no_stage_boundary_recovery` | None |
| `WAA.Grid.classQuiet_no_clench_in_class` | None |
| `WAA.Fetter.kind_lower_iff_cut_by_nonReturn` | None |
| `WAA.Grid.arhatPathQuiet_iff_quietOn_univ` | None |
| `WAA.Grid.all_fetters_cut_at_arhat` | None |
| `WAA.Grid.identityView_cut_iff_noDefiledVoicing` | None |
| `WAA.Grid.conceit_excluded_of_quietOn` | None |
| `WAA.Grid.waaIrreversibleRegime_conditional` | None |
| `WAA.Grid.lower_fetters_covered_by_rites_view_resolve` | None |
| `WAA.Grid.waaStreamWinner_iff_streamEntry_cutClasses` | None |
| `WAA.Grid.waaNonReturner_iff_nonReturn_cut` | None |
| `WAA.Grid.waaSerialFactorRegime_conditional` | None |
| `WAA.Grid.waaOnceReturner_attenuation_witness` | `propext` |
| `WAA.FactorsNegative.no_hold_conceit_boundary_recovery` | None |
| `WAA.FactorsNegative.factor_order_underdetermined` | `propext` |
| `WAA.FettersNegative.seen_run_underdetermines_fetterCut` | `propext` |
| `WAA.Grid.DirectedConvention.waaPathOught_conditional` | None |
| `WAA.Grid.DirectedConvention.waaFaithOught_conditional` | None |
| `WAA.Grid.DirectedConvention.waa_says_true_of_faith` | None |
| `WAA.Grid.DirectedConvention.noDelusion_of_noNescience_of_terminus` | None |
| `WAA.Grid.DirectedConvention.waaFullyEnlightened_of_fullyEnlightenedEnacted` | None |
| `WAA.FaithNegative.noNescience_strictly_stronger_witness` | `propext` |
| `WAA.FaithNegative.aklishta_ajnana_witness` | None |
| `WAA.FaithNegative.arhat_retains_nescience_witness` | `propext` |
| `WAA.FaithNegative.Sealed.silent_buddha_models` | `propext` |
| `WAA.Grid.DirectedConvention.no_waa_path_at_pole` | None |
| `WAA.Grid.DirectedConvention.BeingConvention.GridConvention.rowOf_obeys` | None |
| `WAA.Grid.DirectedConvention.BeingConvention.GridConvention.pole_validates_all_claims` | None |
| `WAA.Grid.DirectedConvention.BeingConvention.GridConvention.denied_misfits_live_offer` | None |
| `WAA.Grid.DirectedConvention.BeingConvention.GridConvention.rowOf_obeys_iff_errorFree` | None |
| `WAA.Grid.DirectedConvention.BeingConvention.GridConvention.reEmptied_obeys_of_errorFree` | None |
| `WAA.rung_not_pole_witness` | None |
| `WAA.standing_does_not_determine_dated` | None |
| `WAA.Grid.DirectedConvention.map_waaAversionContext_iff` | None |
| `WAA.OrthogonalityNegative.waaEffectiveTerminus_stronger_than_terminus` | None |
| `WAA.MisFeedNegative.fence_and_gate` | None |
| `WAA.misFeed_entries_carry_decomposition` | None |
| `WAA.Grid.grade_independent_of_conditions` | None |
| `WAA.Grid.rePitch_forgets` | None |
| `WAA.Grid.stone_of_no_call` | None |
| `WAA.Grid.respondsToEveryCall_of_no_call` | None |
| `WAA.Grid.allStone_of_no_being` | None |
| `WAA.ContentNegative.emptyCallGrid_false_stone_and_respondsToEveryCall` | None |
| `WAA.ContentNegative.emptyBeingGrid_no_liveTier` | None |
| `WAA.ContentNegative.contentBeingsRow_obeys_emptyBeing` | None |
| `WAA.Grid.DirectedConvention.PrudentialPrivilegeNegative.prudentialPrivilege_failure_modes` | None |
| `WAA.Grid.ConsequentialistConvention.dropCountInFiber_le_dropCount` | `propext` |
| `WAA.Grid.ConsequentialistConvention.dropCount_eq_sum_dropCountInFiber` | `propext` |
| `WAA.Grid.ConsequentialistConvention.map_dropCountInFiberSum` | `propext` |
| `WAA.ObjectiveNegative.split_dropCount_sum_eq_mergedDropCount` | None |
| `WAA.ObjectiveNegative.no_grid_data_objective_for_my_drops` | None |
| `WAA.TransferNegative.adaptive_track_record_underdetermines_new_effect` | None |
| `WAA.Grid.DirectedConvention.not_effectivenessEnacted_of_undelivered` | None |
| `WAA.EffectiveTerminusNegative.no_effectiveTerminus_recovery_from_run` | None |
| `WAA.DeliveryArrogationNegative.command_utterance_not_fits` | None |
| `WAA.Grid.DirectedConvention.landing_call_in_modality` | None |
| `WAA.LedgerCase.decree_engineers_calls_not_receptions` | `propext` |
| `WAA.LedgerCase.purge_loop_runs_on` | `propext` |
| `WAA.InteriorDirectionNegative.transposeCR_involutive` | None |
| `WAA.InteriorDirectionNegative.unorderedCRContent_transpose_invariant` | `propext` |
| `WAA.InteriorDirectionNegative.transpose_swaps_readings` | None |
| `WAA.DoerDeedNegative.priority_readings_disagree` | None |
| `WAA.DoerDeedNegative.no_priority_recovery` | None |
| `WAA.ContentNegative.constantResponseGrid_no_variation` | None |
| `WAA.ContentNegative.constantResponseWeld_no_live_share` | None |
| `WAA.ContentNegative.contentIntraWeldArrowRow_not_fused_constantResponse` | None |
| `WAA.ContentNegative.contentIntraWeldArrowRow_not_obeys_constantResponse` | None |
| `WAA.Grid.DirectedConvention.BeingConvention.GridConvention.intraWeldArrowRow_obeys` | None |
| `WAA.Grid.DirectedConvention.BeingConvention.GridConvention.intraWeldArrowRow_not_freeze` | None |
| `WAA.Grid.DirectedConvention.BeingConvention.GridConvention.no_order_collapse_self_refuting` | None |
| `WAA.Grid.DirectedConvention.BeingConvention.GridConvention.doerDeedRow_obeys` | None |
| `WAA.Grid.DirectedConvention.BeingConvention.GridConvention.doerDeedRow_not_freeze` | None |
| `WAA.Grid.DirectedConvention.BeingConvention.GridConvention.no_prior_doer_collapse_self_refuting` | None |
| `WAA.Grid.DirectedConvention.BeingConvention.GridConvention.contentLayerRow_obeys_of_variation` | None |
| `WAA.Grid.DirectedConvention.BeingConvention.GridConvention.contentIntraWeldArrowRow_obeys_of_variation` | None |
| `WAA.Grid.DirectedConvention.BeingConvention.GridConvention.interior_order_denial_unfit_for_live_utterer` | None |
| `WAA.Grid.DirectedConvention.BeingConvention.GridConvention.intraWeldArrowLadder_obeys` | None |
| `WAA.Grid.DirectedConvention.BeingConvention.GridConvention.intraWeldArrowLadder_obeys_succ` | None |
| `WAA.Grid.DirectedConvention.BeingConvention.GridConvention.intraWeldArrowLadder_no_level_final` | None |
| `WAA.Grid.DirectedConvention.BeingConvention.GridConvention.doerDeedLadder_obeys` | None |
| `WAA.Grid.DirectedConvention.BeingConvention.GridConvention.doerDeedLadder_obeys_succ` | None |
| `WAA.Grid.DirectedConvention.BeingConvention.GridConvention.doerDeedLadder_no_level_final` | None |
| `WAA.Grid.DirectedConvention.BeingConvention.GridConvention.Metaphysics.intraWeldArrow_sunyata` | None |
| `WAA.Grid.DirectedConvention.BeingConvention.GridConvention.Metaphysics.doerDeed_sunyata` | None |
| `WAA.Grid.map_responseVariesWithCall_iff` | None |
| `WAA.Grid.DirectedConvention.BeingConvention.GridConvention.map_intraWeldArrowRow_obeys` | None |
| `WAA.Grid.DirectedConvention.BeingConvention.GridConvention.map_doerDeedRow_obeys` | None |
| `WAA.Grid.DirectedConvention.BeingConvention.GridConvention.map_contentIntraWeldArrowRow_obeys_of_variation` | None |
| `WAA.Grid.DirectedConvention.BeingConvention.GridConvention.map_intraWeldArrowLadder_obeys` | None |
| `WAA.Grid.DirectedConvention.BeingConvention.GridConvention.map_intraWeldArrowLadder_obeys_succ` | None |
| `WAA.Grid.DirectedConvention.BeingConvention.GridConvention.map_intraWeldArrowLadder_no_level_final` | None |
| `WAA.Grid.DirectedConvention.BeingConvention.GridConvention.map_doerDeedLadder_obeys` | None |
| `WAA.Grid.DirectedConvention.BeingConvention.GridConvention.map_doerDeedLadder_obeys_succ` | None |
| `WAA.Grid.DirectedConvention.BeingConvention.GridConvention.map_doerDeedLadder_no_level_final` | None |
| `WAA.Grid.DirectedConvention.BeingConvention.GridConvention.ladderRungGrid_beings_sunyata` | None |
| `WAA.Grid.DirectedConvention.BeingConvention.GridConvention.ladderRungGrid_no_level_final` | None |
