/-
================================================================================
  WeldAndArrow.Identification.Commentary
  Reading notes for the layered Lean development
================================================================================

This comment-only module records the paper-facing readings for the formal
layers. It imports nothing and asserts nothing.
-/

/-
================================================================================
  §C Commentary
================================================================================

C.0 Naming and Scope

Names beginning `Waa` mark identifiers that assert a system-POV reading: what
the concept looks like from this grid, not what the concept is in a detached
doctrinal voice. The marker covers ownership, appropriation, whose-ness,
reach-back, sowing-side aiming, four-truths mismatch vocabulary, and sraddha
conditional vocabulary such as `WaaMismatchGrade`, `WaaMismatchLive`,
`WaaAversionContext`, `WaaFullyEnlightened`, and the tariki/jiriki line
readings. Doctrine names are carried by module names and commentary headings;
checked reading identifiers use the single `Waa` marker.

Unprefixed names remain the neutral delivery, order, token-projection, and
tier-placement vocabulary, including `SameAgentDelivery` and
`CrossAgentDelivery`. `Grid.DirectedConvention` marks vocabulary that consumes
the directional reading of `conditions`; the primitive signature itself does
not add asymmetry, irreflexivity, or transitivity premises to `conditions`.

C.1 Signature/Order.lean, Signature/Grid.lean, Signature/BeingConvention.lean,
    Signature/Models.lean, Signature/Claims.lean

`Config` is the formal place where "nothing self-indexed is stored" is enforced:
it carries only a `Contrib`-valued tendency and no owner, being, or weld field.
This is the type-level version of the paper's internal mis-feed discipline.

Seeds, potency, and environs talk in the paper are read here as field-side
delivery lines (`conditions`) and candidate receptions, not as capacities stored
in a being. The alaya/bija-as-stored-state reading is deliberately not taken.

The direction-freedom of `conditions` is a modelling decision tied to Theory:
Karma, "The arrow retyped: direction as display". `ConditionsEither` records the
symmetrized field fact, while `Grid.DirectedConvention` names the reading layer
that consumes ordered roles. The thermodynamic/arrow-of-time gloss motivates the
reading but is never a premise of a theorem.

`RawWeld`, `Grid.index`, and `Grid.share` encode the MMK 8 point that there is no
separate prior act or performer inside the formal signature: the index and share
are projections from a completed weld. `no_agent_recovery_of_field_collision`
is the internal recovery obstruction corresponding to that gloss.

`SelfLineWitness` records that self-lines are permitted by the signature and
can satisfy the ownership-face vocabulary when the model supplies reflexive
delivery. The paper's shushō-ittō discussion is a reading of that permission,
not a premise.

The hand-rolled `Preorder` is used for dependency-freedom and to keep the exact
assumptions visible. Mathlib has the counterparts `Preorder`, `OrderBot`, and
`IsBot`; the local `AtBot` is the order-class of the chosen bottom and is
equivalent in role to Mathlib's `IsBot` predicate for that element.

There is no `PreorderTop`: the solipsist/total-share gloss in the paper is an
asymptote, not an attained element. By contrast, `PreorderBot` supplies an
attained bottom so `AtBot` can express the share-zero pole as an order-class.

`Stone`, `Terminus`, `AtPoleClass`, and `stone_is_terminus_vacuously` implement
the function/share split discussed in Theory: Attainment. A stone has no mounted
response; a terminus has mounted responses whose grade lies at the pole-class.

`rePitch` keeps `_before` in the signature because the operation is conceptually
on a prior configuration, even though the current simple implementation depends
only on the received weld. `IsShareDrop` is the strict order comparison
`Strict (G.share received) before.tendency`.

`Signature/BeingConvention.lean` records the reading in which fine tags may be
diagnosed as macro beings. Its examples accommodate the paper's sentient,
hare's-horn, buddha, and generated-boundary cases without adding a privileged
partition to `Grid`. `Signature/Models.lean` holds the concrete clock and
register-clock witnesses consumed by later taxonomy checks.

The separate/fuse interface (`ClaimLanguage`, `Distinction`,
`RecordedUtterance`, `Tier`) is the small formal surface needed for the fox,
Baizhang, shō/shu, genjō, and verdict-tier discussions. The formal module keeps
only the abstract interface; this commentary retains the textual motivation.

C.2 Consequences/Basic.lean, Consequences/Taxonomy.lean,
    Consequences/Ladder.lean, and Consequences/ContentRows.lean

The consequence layer proves neutral facts about the definitions: function/share
facts, share-drop obstruction at the pole, delivery and landing projections, and
tier diagnostics. The generated table rows live in `Consequences/Taxonomy.lean`;
the re-emptying machinery lives in `Consequences/Ladder.lean`; and the
content-bearing layer rows live in `Consequences/ContentRows.lean`. The paper's
readings of these facts live here as commentary only; the theorem statements
consume only the neutral definitions.

The strictness facts are now in `Signature/Order.lean` as `Strict`, `strict_irrefl`,
`not_strict_of_orderEq`, and `no_strict_of_all_orderEq`. The arrow-of-time gloss
uses `Grid.DirectedConvention.TimeDirection`, an abbreviation of `Strict`.
`strict_shareBot_of_hasSelfPoleIndex` and its re-rooted
`timeDirection_of_hasSelfPoleIndex` reading make a live share itself the
direction witness against bottom. `DirectionVoid` names the absence of any
strict comparison, while `AllStone` names the grid-wide absence of response
function.

`RowTag`, `RowClaim`, `rowLanguage`, and `rowOf` now generate the table's
schema rows with pole-affirming semantics. `beforeAfterRow`, `beingsRow`, and
`gridLensRow` are compatibility names for `.layer` tags in that schema. Their
collapse and freeze checks remain hypothesis-free; their obedience theorems
carry only the local `AtBot` stability needed for non-live genjo fusion. The
full row list is Lean data as `tableOrder`.

The `contentLayerLanguage` keeps the convention-live side as the live-share
condition and gives row-specific content to the denial side. Its obedience
theorems are aptness-conditional by design: where the denial is simply true,
the convention row should not be held. This track deliberately keeps
`LayerClaim`: global denials such as all-stone or direction-void cannot be
made pole-affirming by truth at a particular genjo weld. `RecordedUtterance`
supplies the actuality needed for the content utterance checks, while
`denied_misfits_live_offer` and `fox_utterance_misfits_live_offer` perform the
same live-tier check for the schema language.

The `reEmptied` transformer and `ladder` iterate the separate/fuse rule without
adding a claim that quantifies over all levels. `ErrorFree`,
`reEmptied_obeys_of_errorFree`, and `ladder_obeys_of_errorFree` record the
refutation-only route by which the implemented `finalBelow` side lets the
ladder climb without an added stability premise above the seed. The "completed
ladder" remains an instructive absence: level quantification appears only in
meta-theorems such as `ladder_obeys`, `no_level_final`, and the existential
guard `no_final_level`. Concrete witnesses such as
`shareZero_not_functionZero_witness`, `rung_not_pole_witness`,
`backsliding_witness`, `backsliding_rePitchSequence_witness`,
`standing_does_not_determine_dated`, `subitism_possibility_witness`,
`waaSuddenArrival_witness`, `waaGradualArrival_witness`,
`rate_invisible_to_config`,
`cetana_grading_tracks_weld_not_field_witness`,
`cetana_live_share_without_object_standing_witness`, and the
`registerClock_staticized_*` checks keep the row anchors model-checked.
`standing_does_not_determine_dated` and `subitism_possibility_witness` share
the same clock-grid witness deliberately: the first serves the disposition/act
retype, while the second names the sudden/gradual possibility claim.
`waaSuddenArrival_witness` gives the doctrine-facing one-step form with
actuality, `waaGradualArrival_witness` gives the register-clock staged form,
and `rate_invisible_to_config` deliberately reuses `rePitch_forgets` as the
rate-invariance anchor.
`withRespondsTo` and `staticized` are the futility operation: delivery-loss is
real (`futility_delivery_loss_real`) while object-axis standing is unchanged
(`Grid.DirectedConvention.staticized_objectAxisStanding_iff`).

C.2a Identification/Absences.lean

`InstructiveAbsence` mirrors the paper's section 3 list as inspectable data.
The enum is not an editorial layer: entries remain members while the paper keeps
them in section 3. `AbsenceStatus` records the mutable world-facing fact, so the
third arrival is `retiredAsCheck` rather than deleted or renumbered. The same
rule applies to future retirements: constructors track the section list, while
`status` carries whether an entry still stands.

The anchors are citations and shape checks, not new doctrine. Empty table cells
are recorded beside `tableOrder` as `hasCollapseOccupant` and
`hasFreezeOccupant`; `emptyCells_anchor` checks that a dash remains metadata
while row refutations remain theorem facts. `foxNeverTestsPole_anchor` cites the
concrete fox model's `fox_never_tests_pole`; the recorded-utterance and
agent-side checks keep the worked case away from both share-zero and the
pole-class. `thirdArrival_not_waaMismatchLive` reuses the terminus-response
four-truth theorem: the retired absence is kept as the dukkha-free check. The
fourth-truth, no-safe-stage, and prudential-privilege anchors cite
`waaPathOught_conditional`, `no_final_level`, and
`PrudentialPrivilegeNegative.not_prudentialPrivilege`. The declined case,
why-calls-land, and no-measure entries deliberately have only data/status pins:
their missing theorem is the content the paper assigns them.

C.3 Meta/Invariance.lean and Meta/InvarianceNegative.lean

`DisplayReparam` is the admission criterion for predicates that mention the
contribution carrier: they must transport across order-preserving and
pole-preserving changes of display convention. This is the formal counterpart
of treating contribution values as display conventions rather than operational
tokens.

The condition-transpose operation and its being-coarsening companion now live in
the signature layer, beside the `conditions`, `DeliveredTo`, and
`BeingCoarsening` vocabulary they transport. `Meta/Invariance.lean` remains the
central home for `DisplayReparam` and all `map_*` transport lemmas.

`Meta/InvarianceNegative.lean` holds the countermodels. `InvarianceNegative`
explains why equality with the chosen bottom is not the system predicate:
equality-to-bottom fails to transport, while `AtBot` and `Terminus` do.

`DirectionNegative` is the countermodel behind Theory: Karma, "the arrow
retyped": two grids agree on `ConditionsEither` and disagree on `conditions`, so
the symmetric field structure does not recover direction. The physics and
thermodynamics language motivates the reading, but no theorem depends on it.

`BeingNegative` is the parallel countermodel for designation: one fine grid
allows both merge and split macro readings, so a unique being-boundary is not
recoverable from the grid data alone.

`ContentNegative` supplies the countermodels for the aptness hypotheses on
content rows: an all-stone/no-live grid and the two-bottom direction-void
carrier make the relevant denials true at non-live act-time, so fusion fails
there.

C.4 Doctrines/FourTruths.lean, Doctrines/Sraddha.lean,
    Doctrines/Faith.lean, Doctrines/Ethics.lean, and the sibling negative modules

`WaaMismatchGrade` is definitionally `share`; this is the formal honesty clause
for dukkha-talk as covariation rather than a second measure. `WaaMismatchLive`
adds occurrence actuality to the self-pole-index condition, so stones fall
outside the domain by `not_actual_of_stone`, and terminus responses fall to the
pole-class by the existing terminus theorem.

`WaaAversionContext` treats sraddha reception per call: it packages a live
prior tendency and an actual live-mismatch reception, not a stored faith
possession. `WaaFullyEnlightened` deliberately has two conjuncts: terminus
typing and universal shortfall closure for delivered deeds. The physician
simile belongs exactly there: the grid can prove `waaPathOught_conditional`,
but the antecedents are faith-shaped and are never discharged by field facts.
The faith-object therefore cannot be replaced by anything the fetter lattice
names: the total-rectangle cut lacks function by
`FettersNegative.total_cut_carries_no_function`, and even the live fiber reading
lacks effectiveness by
`FettersNegative.total_cut_with_function_not_waaFullyEnlightened`.

`WaaFaithPrinciple` abstracts the sraddha antecedent to testimony: faith in
enlightenment transmits truth to recorded utterances, with
`waaPathClaimLanguage` instantiating the `ClaimLanguage` interface for the
physician's sentence. `FaithNegative` shows the principle exceeds its own
faith-object, so the "never discharged by field facts" clause survives the
abstraction.

`WaaEthicsStance` bundles the two undischarged antecedents -- principle and
faith -- as the agent's contribution; `WaaEthicalCode` is the fourth-truth
ought generalized over the faith-object's recorded testimony, still an
implication type only. The deontic work is done by the receiver's own
`WaaAversionContext`, not by testimony's truth: the physician's sentence is
practical only where shortfall is live. `EthicsNegative` keeps the code honest
three ways: empty at the pole, unsatisfiable over false testimony, and relative
to the faith-object.

`Doctrines/SraddhaNegative.lean` keeps that conditional honest.
`SraddhaNegative` shows that dropping faith or dropping the live-aversion
antecedent loses the landing, and `OrthogonalityNegative` shows that a
responsive terminus need not be `WaaFullyEnlightened`.
The opposite regime face is checked by
`waaFullyEnlightened_of_responsiveTerminus_of_undelivered`: with no delivered
own deeds, the closure conjunct holds vacuously. Teaching and non-teaching are
delivery facts around a terminus, not two being-natures stored in it.

C.5 Doctrines/Deliberation.lean

`ConsequentialistConvention` is a descriptive reading layer. `DropCount` and
`DropCountInFiber` count share-drop receptions across finite actual runs without
adding probability, utility, or a command register. `ObjectiveNegative` reuses
the merge/split being-convention pattern to show that "my drops" is not a
function of grid data alone.

`backsliding_witness` gives the direct same-grid shape: a share-drop reception
to the pole-class followed by a later actual live-share weld by the same
being. `backsliding_rePitchSequence_witness` routes the same shape through
`ReceptionPair.rePitchSequence`. `rePitch_forgets` and
`accumulated_attainment_constant_of_same_final` restate backsliding in the form
a maximizer needs: no accumulated attainment variable is stored in `Config`.
`TransferNegative` records the adaptive track-record obstruction and the
`ResponseInvariant` contrast case. `grade_independent_of_conditions` and
`share_independent_of_conditions` keep the cetana claim at signature level:
grade and share do not consume downstream delivery conditions. The concrete
cetana witnesses are `cetana_grading_tracks_weld_not_field_witness` (same
field residue, different share) and
`cetana_live_share_without_object_standing_witness` (live share where standing
fails). The AN 6.63 correlation itself and the comparative no-common-event
reading remain prose-bound. `DeliveryArrogationNegative` instantiates the
`ClaimLanguage` machinery for a command-shaped delivery claim and checks that a
recorded plan fails `FitsOfferedTier` where delivery is absent.

C.6 Identification/Placements.lean, Identification/Registers.lean, and
    Identification/Disclaimers.lean

The contemporary placements and disclaimer-5 register sorting are paper-facing
taxonomies kept in the office/placement pattern: data plus `rfl` pins, not a
semantic interpretation of grid vocabulary. `SortedFact.register` is total over
the table instances, so exhaustiveness of the three registers is carried by the
definition rather than asserted as a separate theorem. The
`nothing_selfIndexed_carried` check is the enumerated face of the same
discipline enforced architecturally by `Config`: no owner or self-index field is
stored between deeds.

C.7 Doctrines/Ledger.lean

The ledger case is run in code rather than read into it; this section is the
reading, and the module's own header is the map. `MountsOnlyIn` is the
function-side register/modality predicate - deliberately neutral vocabulary,
like `MountsAt` and `ResponseInvariant`, because a receiver's open register is
a fact about `respondsTo`, not a Waa reading. `landing_call_in_modality` is
the response-shape fact the paper calls a theorem: any landing at a
modality-restricted receiver carries a call in the modality, so the form of
the answer that reaches the ledger is fixed by the ledger. The proof is
near-definitional by design; `LedgerCase` discharges the non-vacuity duty the
way `clockGrid` does for the function/share split. Hakuin's corrective, upaya,
and the wisdom of the code remain display.

`fiber_landing_call_in_modality` is the compression clause: where every fine
tag under a macro tag shares the register, one answer reaches the fiber. The
hypothesis is stated on `κ.proj` directly; `InFiber` unfolds to the same
equation. Together with `sectorCoarsening` and `BeingNegative`, this is "the
state's Row 2 is a display convention over the officials' welds" with its
legality and its illegality both on record: legal as diagnosis-time coarsening,
unrecoverable as grid-carried partition.

`receptionCommandLanguage` is the deliberate sibling of
`deliveryCommandLanguage` (C.5). The Deliberation negative shows a command over
delivery failing where delivery is absent; the ledger's decree is the scale
case with the opposite delivery polarity - delivered everywhere, landing
nowhere it purports to command. `decree_engineers_calls_not_receptions` keeps
both halves in one statement: suppression is grid-legal call-engineering, and
the reception register stays uncommanded.

The census's two named faces (`ledger_census_misfits_live_offer`,
`ledger_prognosis_misfits_live_offer`) delegate to `denied_misfits_live_offer`
at `.perCallGlobal` and `.standingDated`, exactly as the fox's marquee theorem
does at `.foxWeld`. No `RowTag` is added: the module's checked form of "three
errors, zero new cells" is that its taxonomy content is entirely delegation.
The third error's anchors are section 2 of the module plus the Deliberation
negative; the exit-collapse's corrective is model-checked as
`purge_object_axis_subtraction_nil` with `corpus_still_delivered`.

The Huichang face reuses the futility operation unchanged: `staticized`,
`futility_delivery_loss_real`, `staticized_responseInvariant`, and
`staticized_objectAxisStanding_iff` are consumed, not reproved.
`purge_loop_runs_on` is the one genuinely new futility-face check: the
non-staticized reception is still actual, which is the "loop ran on" clause
stated as a model fact.

Grades in `LedgerCase` are uniformly live and no being is pole-typed: the case
asserts nothing about Baizhang's attainment, and the model is built so it
cannot accidentally do so. The pedigree flag on the Pure Rules attribution is
carried in the module header; the theorems consume the shape only. What the
module declines is what the paper declines: no theorem asserts that the code
saved Chan, that the state was wrong, or that the survival was worth having -
the first is the historians', the second is ungradeable by the no-value clause,
the third is valence borrowed from the object.

C.7a Consequences/FoxCase.lean and Doctrines/FoxCase.lean

`FoxCase.foxGrid` runs the paper's paradigm case as a concrete `Grid Nat`.
Life 0 is the old man's answering life, later naturals are fox-life tags, and
the display convention "the fox" is `foxSeriesCoarsening`, a diagnosis-time
merge rather than a stored being. `foxSeries_macro_sentient`,
`foxSeries_macro_selfConditioning`, and `fox_consecutive_lives_distinct` are
the coarsening checks: the macro tag is legal and live, while the fine lives
remain distinct.

The per-beat checks are deliberately small. `fox_sentence_live_selfPole`
records the old answer as actual and live; `fox_arrow_index_free` instantiates
the grade/share independence of delivery; `fox_returns_delivered` gives the
return line from the sentence into later lives; `fox_reception_clenched`,
`fox_config_carries_only_tendency`, and `fox_rePitch_forgets` keep the
receptions actual, live, and non-storing; `fox_release_rung_not_pole`,
`fox_reachBack_full_at_release`, and `fox_nothing_kept` record the turning-word
release as a share-drop, not a pole-arrival or possession. `fox_never_tests_pole`
is intentionally true by construction: no grade in the model is zero, so the
absence of pole-arrival is a displayed boundary of the koan, not a hidden
answer to the terminus question.

The Dogen doubling checks are grid-internal only. `oldMan_utterance_misfits`
delegates the old answer to the fox row's live-tier misfit;
`daishugyo_diagnosis_fits`, `jinshinInga_instruction_fits`,
`jinshinInga_floor_voicing_would_misfit`, and `dogen_doubling_both_fit` type
the two speech-act faces and the counterfactual floor-voicing. They do not
prove the historical claim that this paper follows Daishugyo against the late
Dogen; that disagreement stays prose. The dukkha-facing name
`fox_dukkha_per_life` lives one layer down in `Doctrines/FoxCase.lean` because
it consumes `WaaMismatchGrade` from `FourTruths`.

C.8 Doctrines/Correlations.lean, Doctrines/CorrelationsNegative.lean,
    Doctrines/SuddenGradual*.lean, Doctrines/Fetters.lean, and
    Doctrines/FettersNegative.lean

`Doctrines/Correlations.lean` treats the Ten Bulls, Five Ranks, and stage
schemes as checked correlations over existing machinery. `StageScheme` is just
`BeingCoarsening`; the warning belongs to holding a coarsening as grid-carried
structure, not to any one ladder. `CorrelationsNegative.no_stage_boundary_recovery`
duplicates the being-boundary no-recovery pattern for stage schemes so the
uniform freeze clause is witnessed without importing `Meta` upward into
`Doctrines`.

`Doctrines/SuddenGradual.lean` names the §2 sudden/gradual split without new
cells. `WaaSuddenArrival` is the actual one-step share-drop to the pole-class,
and `waaSuddenArrival_witness` reuses the clock-grid possibility shape.
`WaaGradualArrival` folds a `ShareDropRun` through `rePitchRun`, with
`waaGradualArrival_witness` on `registerClockGrid`. `rate_invisible_to_config`
is exactly `rePitch_forgets`; the run corollaries say config-factoring scores
cannot read the earlier rate once the final reception is fixed.
`SuddenGradualNegative.subitism_frequency_underdetermined` supplies the
honesty clause: response/grade/share data agree while delivery of the
pole-reaching weld differs.

For the Ten Bulls, Bulls 1-6 are a `ShareDropRun`; Bull 7 is
`WaaBullSeven`, probe-constancy plus a live self-pole index. The theorem
`bullSeven_not_bullEight` checks that this half-weld is not the empty-circle
pole-class. Bull 8 is `AtPoleClass`, Bull 9 is `ResponsiveTerminus`, and Bull 10
is the existential cross-fiber delivery predicate `WaaBullTen`. The stronger
`StrongWaaBullTen` is named and shelved: delivery into every sentient fiber is a
stronger bodhisattva reading than the picture asserts. The pratyekabuddha
countermodel shows Bull 9 without Bull 10.

The Five Ranks are data plus reading pins; `kenChuTo_implies_waaBullTen` names
the 到/Bull 10 shape under the same coarsening. This is a retype of ranks as
utterance-diagnosis and index-placement, not a second stage ladder.

`FiberAtPoleOn`, `LiveFiberAtPoleOn`, `FiberAtPoleOnWithin`, and the tag-axis
within vocabulary sit in `Signature/BeingConvention.lean` because they are
neutral fiber restrictions. The restriction now has two axes: call-class and
fine tag-class. `FiberAtPoleOnWithin` is the product, monotone in both
coordinates; the old call-axis and the new tag-axis are its total-class
specializations. Fetters merely consume them: `FetterReading` supplies the
provocation classes as model-side data, `SomaReading` supplies the tag-region
with the same diagnosis-time status, and `FetterCutWithin` means the fiber is
at pole on that fetter's call-class inside that tag-region. Thus a cut is
cessation of enactment in a region, not possession of an anti-fetter.
`classQuiet_no_clench_in_class` and `conceit_excluded_within` are the checked
soul-guards: where the relevant cut holds, no actual weld in that region
carries a live self-pole index. `FettersNegative.no_region_boundary_recovery`
is the freedom witness on the tag axis.

The path scheme is nested class quietness. `Path.cutClasses` gives the stream,
once-return, non-return, and arhat call-classes; once-return adds no new cut
class, matching the prose weakening clause. `arhatPathQuiet_iff_fiberAtPole`
says the arhat class is total, so arhat path-quietness is ordinary
`FiberAtPole`. The within-family adds the tag cut. Sravaka-arhat is
`PathQuietWithin` at `SomaReading.speechThoughtTag`; the total calls/total tags
point is neutral, theorem-identical to ordinary `FiberAtPole` by
`arhatWithin_univTags_iff_fiberAtPole`. Vasana remains residual clench enacted
in the complement region after the call-axis closes, an existing-cell reading.

The buddha reading enters only as a three-rung ladder above that neutral point.
Rung 1 is the total-rectangle cut, the share axis alone; the all-stone witness
`FettersNegative.total_cut_carries_no_function` shows that it has no function
conjunct. Rung 2 is the live terminus reading, `LiveFiberAtPole`, with
`sentientTag_iff_actualFiberInhabited` as the bridge from response-function to
actual fiber inhabitation. `FettersNegative.total_cut_with_function_not_waaFullyEnlightened`
checks that rung 2 still lacks effectiveness. Rung 3 is
`WaaFullyEnlightened`, rung 2's quietness plus universal shortfall closure, and
it enters the faith and ethics files only as hypothesis.

Pratyekabuddha is typed at rung 2 as a regime fact with two faces, not as a
second attainment. Face A is uncooperative delivery: a deed is delivered but no
share drop lands, so `OrthogonalityNegative.waaFullyEnlightened_stronger_than_terminus`
shows failure of `WaaFullyEnlightened`. Face B is sealed delivery:
`waaFullyEnlightened_of_responsiveTerminus_of_undelivered` makes full
enlightenment hold vacuously when no own deed is delivered at all. The
samyaksambuddha reading is rung 3, the faith-object. The guard clause is
therefore strict: the model hosts a non-teaching terminus as a regime fact,
never as a being who opts out of being read. This is the taxonomy-freeze cell
for "the private buddha declining his own occurrence at others' Row 2" read
without the freeze: non-teaching is the field declining to deliver, never the
being withdrawing object-axis standing.

The older arhat anchors remain and have region duals:
`identityView_excluded_at_arhatFiber`, `conceit_excluded_at_arhatFiber`,
`arhatFiber_of_termini`, `identityView_excluded_at_speechThoughtRegion`,
`conceit_excluded_within`, and `regionFiber_of_termini`.

Identity-view is the coarsening-freeze enacted: the macro tag held as stored
owner. Its cut is quietness on the identity-view provocation class, so
stream-entry is typed as the cessation of the same attachment the uniform
coarsening clause warns against.

Irreversibility is three-layered on both axes. Whole-region `FetterCut` and
`FetterCutWithin` are internally irreversible by quantifier logic: if a later
clenched weld in the relevant rectangle exists, the cut never held. Run-assigned
path tags are only display over seen data, and
`FettersNegative.seen_run_underdetermines_fetterCut` with
`FettersNegative.seen_run_underdetermines_fetterCutWithin` gives the fresh-call
transfer countermodel. A forward guarantee is hostable only as the conditionals
`waaIrreversibleRegime_conditional` and
`waaIrreversibleRegimeWithin_conditional`, parallel in voice to the sraddha
conditional. The orthogonality note is checked by
`unquiet_region_still_functions_witness`: region cuts speak to share; the uncut
region's tags act as fully as the cut region's tags.

C.9 Doctrines/OtherPower.lean and Doctrines/OtherPowerNegative.lean

Other-power is now a checked delivery-regime correlation rather than a prose
appendix to §2. `SameAgentDelivery` and `CrossAgentDelivery` are unprefixed
because they are grid-recoverable facts about a delivery line: the line is
delivered, and the two agent tags are equal or unequal. `WaaJirikiLine` and
`WaaTarikiLine` carry the system-POV reading of those neutral facts.

`reception_typing_ignores_sower` is near-definitional: swapping only
`conditions` leaves a reception's grade, share, and actuality untouched.
`waaReachBack_filled_either_regime` records the one-act-grammar point: once an
actual reception is present, either regime supplies the same ordinary
reach-back relation by projection from delivery.

`TarikiCase` supplies the non-vacuity witness. The name is response-invariant
(`name_responseInvariant`), function-mounted rather than stone
(`name_not_stone`), and share-zero at its welds (`name_share_bot`).
`name_object_axis_entire` delivers the name's weld to every invoker reception,
while `universal_fixed_call_lands_without_reading` assembles the corresponding
`HasShareDropLanding`. This is the effective corner opposite the zero-effect
orthogonality witness: adaptivity and effectiveness are independent. The
invoker's side remains an ordinary deed, checked by
`invoker_reception_is_deed`.

The module deliberately declines polemic. `OtherPowerNegative` gives the two
freedom witnesses: `regime_does_not_determine_share` shows that same-agent and
cross-agent lines each allow live and pole-class receptions, while
`share_does_not_determine_regime` shows that equal reception share does not
recover the regime.

C.10 Doctrines/Gradeability.lean

`SeveredTranscript` is agent plus response rather than response alone because
the strongest natural form of a quotation is still attributed. If even that
stronger record cannot recover grade, then the bare response-only case is
covered a fortiori. The type deliberately carries no `call`, no `offeredAt`,
and no `actual`, so it cannot be fed to `RecordedUtterance.FitsOfferedTier`;
there is no positioned utterance for the taxonomy to classify.

`Grid.Weld.sever` and `Grid.RecordedUtterance.sever` are forgetting maps. The
negative theorem `GradeabilityNegative.no_grade_recovery_from_severed` uses the
standard collision pattern: two actual welds with the same severed transcript
and different shares force any correct estimator to assign one value two ways.
`backslideGrid` supplies the concrete carrier in the missing-call direction:
one agent gives the same response to gentle and harsh calls, with different
shares. This is named by
`GradeabilityNegative.gradeability_severed_underdetermination_witness` and
instantiated as `GradeabilityNegative.severed_transcript_ungradeable`.

`recordedUtterance_grade_determined` is the positive half as an `rfl` pin: a
recorded utterance carries the whole weld, so its grade factors through the
record by definition. The koan-form identification, the normative rule "may
grade only where the call is carried", the quotable/gradeable genre contrast,
and the Hakuin-epigram pedigree flag remain prose. The code checks the
underdetermination fact and the carried-call architecture only.
-/
