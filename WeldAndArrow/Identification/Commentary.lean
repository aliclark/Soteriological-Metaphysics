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
reach-back, sowing-side aiming, four-truths vocabulary, and sraddha
conditional vocabulary such as `WaaMismatchGrade`, `WaaDukkha`,
`WaaAversionContext`, `WaaEffectiveTerminus`, and the tariki/jiriki line
readings. Doctrine names are carried by module names and commentary headings;
checked reading identifiers use the single `Waa` marker.

Unprefixed names remain the neutral delivery, order, token-projection, and
tier-placement vocabulary, including `SameAgentDelivery` and
`CrossAgentDelivery`. `Grid.DirectedConvention` marks vocabulary that consumes
the directional reading of `conditions`; the primitive signature itself does
not add asymmetry, irreflexivity, or transitivity premises to `conditions`.

C.1 Signature/Order.lean, Signature/Grid.lean,
    Signature/SentienceConvention.lean, Signature/BeingConvention.lean,
    Signature/Models.lean, Signature/Claims.lean

`Signature/Assumptions.lean` is the canonical, compile-checked list of the
Signature layer's assumptions; this commentary supplies the paper-facing
motivation around those inputs.

`Config` is the formal place where "nothing self-indexed is stored" is enforced:
it carries only a `Contrib`-valued tendency and no owner, being, or weld field.
This is the type-level version of the paper's internal mis-feed discipline.
Its exact scope is architectural and definability-level:
`Config.relabel_fixed`, `Grid.relabel_rePitch`, and
`Grid.no_natural_agent_recovery_from_config` check the uniform claim. The
information-flow reading is declined by Assumption Ledger B.7, with
`ConfigLeakWitness.registerClock_config_recovers_agent` recording why.
`Identification/Registers.lean` records the register table for the same sorting:
field facts are carried, weld facts are spent, and grade statements are stated.

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
delivery. The compile-checked pins for the input-side assumptions live in
`Signature/Assumptions.lean`; their canonical prose and downstream anchor
metadata live in `Meta/AssumptionLedger.lean`. The paper's shushō-ittō
discussion is a reading of that permission, not a premise.

The hand-rolled `Preorder` is used for dependency-freedom and to keep the exact
assumptions visible. Mathlib has the counterparts `Preorder`, `OrderBot`, and
`IsBot`; the local `AtBot` is the order-class of the chosen bottom and is
equivalent in role to Mathlib's `IsBot` predicate for that element.

There is no `PreorderTop`: the solipsist/total-share gloss in the paper is an
asymptote, not an attained element. By contrast, `PreorderBot` supplies an
attained bottom so `AtBot` can express the share-zero pole as an order-class.

Actual call/response is universal. `respondsTo = none` remains only at the
actual/hypothetical seam and is not aggregated into a being-kind.
`ActualAgentInhabited` supplies non-vacuity, `Terminus` is the universal
share-pole condition, and `AtPoleClass` is exactly `Terminus`. The retired
`Stone`, `AllStone`, and `MountsSomewhere` predicates have no compatibility
aliases.

`Signature/SentienceConvention.lean` supplies `SentienceReading`, a predicate
on welds constrained by no grid field. `SentientAct` and `InsentientAct` cross
the live-share/pole partition to form `OrdinaryAct`, `TerminusAct`,
`InsentientAppropriation`, and `StoneAct`. `actual_act_fourfold` is the
constructive partition theorem under explicit local decidability, while
`sentience_share_square_inhabited` witnesses all four cells. Constant-true and
constant-false readings split a witnessed actual weld into `SentientAct` and
`InsentientAct`; `no_sentience_recovery` then shows that the same
`SentienceGridData` cannot recover its act classification under both readings.

`rePitch` keeps `_before` in the signature because the operation is conceptually
on a prior configuration, even though the current simple implementation depends
only on the received weld. `IsShareDrop` is the strict order comparison
`Strict (G.share received) before.tendency`.

`Signature/BeingConvention.lean` records the reading in which fine tags may be
diagnosed as macro beings. Relative to `S`, `SentientTag S`, `StoneTag S`, and
`Intermittent S` summarize marked, wholly unmarked-pole, and mixed fibers.
`ActualFiberInhabited` remains mark-free for consumers that need occurrence
rather than phenomenality. `Signature/Models.lean` holds the clock,
register-clock, and inhabited sentience/share square witnesses.

`Signature/DirectionConvention.lean` records the parallel delivery-axis reading
in which a model may be diagnosed through finite clock resolution. A
`DirectionCoarsening` supplies ticks over welds without adding a field to
`Grid`; `ResolutionBounded` says only that same-tick welds have
order-equivalent shares in the chosen display. The point is deliberately
display-side: sub-tick delivery cannot carry strict `TimeDirection`, but no
terminus, sentience, pole-class, or self-index predicate consumes the
coarsening.

The separate/fuse interface (`ClaimLanguage`, `Distinction`,
`RecordedUtterance`, `Tier`) is the small formal surface needed for the fox,
Baizhang, shō/shu, genjō, and verdict-tier discussions. The formal module keeps
only the abstract interface; this commentary retains the textual motivation.

C.2 Consequences/Basic.lean, Consequences/Taxonomy.lean,
    Consequences/Compounds.lean, Consequences/Ladder.lean, and
    Consequences/ContentRows.lean; Identification/Ownership.lean

The consequence layer proves neutral facts about the definitions: function/share
facts, share-drop obstruction at the pole, delivery and landing projections, and
tier diagnostics. The generated table rows live in `Consequences/Taxonomy.lean`;
the re-emptying machinery lives in `Consequences/Ladder.lean`; and the
content-bearing layer rows live in `Consequences/ContentRows.lean`. The paper's
readings of these facts live here as commentary only; the theorem statements
consume only the neutral definitions.

The strictness facts are now in `Signature/Order.lean` as `Strict`,
`strict_irrefl`, `strict_asymm`, `strict_trans`,
`strict_of_le_of_strict`, `strict_of_strict_of_le`,
`not_strict_of_orderEq`, and `no_strict_of_all_orderEq`. The arrow-of-time gloss
uses `Grid.DirectedConvention.TimeDirection`, an abbreviation of `Strict`.
`strict_shareBot_of_hasSelfPoleIndex` and its re-rooted
`timeDirection_of_hasSelfPoleIndex` reading make a live share itself the
direction witness against bottom. `DirectionVoid` names the absence of any
strict comparison. No aggregate predicate turns the signature's `none` region
into a doctrinal population.

`RowTag`, `RowClaim`, `rowLanguage`, and `rowOf` now generate the table's
schema rows with floor-apophatic semantics. At `floor` no row claim holds;
`no_row_claim_holds_at_floor` is the silence pin, and
`floor_claims_indiscernible` makes fusion degeneracy of the claim-space rather
than joint truth. Conventional force begins only at act-time:
`fitting_offer_is_actTime` is the MMK 24.10 pin. At a pole-class act-time the
denial side still earns diagnostic truth by `pole_validates_all_claims`; that
不昧 face is unchanged. `beforeAfterRow`, `beingsRow`, `gridLensRow`, and
`weldRow` are compatibility names for `.layer` tags in the schema. Their
collapse and freeze checks remain hypothesis-free; their obedience theorems
carry only the local `AtBot` stability needed for non-live genjō fusion. The
full row list is Lean data as `tableOrder`. No positive `Truth` or `Thus`
predicate of the floor is introduced; `InstructiveAbsence.floorTruthPredicate`
registers that refusal.

The standing-sentience row replaces the retired undefined/zero edge row.
Its freeze is sentience held as a nature; its collapse is sentience identified
with grid-visible function. The row machinery checks the distinction shape,
while `no_sentience_recovery` supplies the substantive recovery obstruction
where an actual weld witnesses the question.

`intraWeldArrow` is a `ConventionLayer`, not a bare row tag, because it names
the convention by which the two faces of a weld are ordered. Its content denial
is response-invariance: if no being's response varies with call, the call-face
does no work, so there is no interior order to read. The conditional obedience
theorem therefore asks for `∃ b, G.ResponseVariesWithCall b`, parallel to the
directed-time row's strictness witness. A single recorded utterance of the
content denial does not by itself extract two different responses from two
calls, so the shipped utterance theorem is the schema-level live-tier misfit
form, routed through `denied_misfits_live_offer`.

`doerDeed` is a schema-only `RowTag`. The tempting content form, "the doer is
prior to the deed", would require adding a priority structure to the opaque
signature, thereby installing exactly the furniture MMK 8 is being used to
deny. The floor-furniture flank is instead carried by
`DoerDeedNegative.no_priority_recovery`, a witness that the same visible grid
data support both a prior-doer reading and a mutual-dependence reading. Fusion
remains ordinary row trivialization: the code nowhere says that doer and deed
merge into one thing.

The generator-discipline check is the same one that motivated `weldRow`: a
generated row should name the convention whose collapse/freeze it diagnoses.
`intraWeldArrow` names the face-order convention; `doerDeed` names the
doer/deed ordering, with the `RawWeld` being component as its concrete anchor
but without promoting priority to a field. The labels "coming-from" and
"going-to" are display names for transposed readings of the two weld faces,
not new tier names.

`ReflexivityWitness.ladderRungGrid` is deliberately only one legal grid: it
instantiates `Being` with `Nat` read as rung labels and then reruns the beings
ladder. This does not define beings as rungs, and it leaves
`BeingNegative.no_partition_recovery` untouched.

`Consequences/Compounds.lean` records the compound-position decompositions as
the same kind of paper-facing data plus `rfl` pins used by placements and the
table order. Its components are classificatory rather than probative: citing a
cell does not prove a row collapses or freezes, because the generated rows
already carry their own refutations. The type-level guard is that components
can cite only `TableRow`s already in the Grade-1 table; facets mark distinct
prose faces of repeated rows, roles separate stacked cells from Grade-1 cells
riding alongside, and legal elements carry no verdict voice.
`CompoundPosition.ledgerPicture` is the fifth entry: possession-freeze and
transposed-as-mechanism are stacked cells, command-style delivery-arrogation is
the conditional `.alongside` cell, and the causal skeleton is carried as a
legal element. The `.command` facet is row-neutral like the others; it only
keeps the command face from collapsing into the exit-premise's plain
delivery-index citation.

The `contentLayerLanguage` keeps the convention-live side as the live-share
condition and gives row-specific content to the denial side. Its obedience
theorems are aptness-conditional by design: where the denial is simply true,
the convention row should not be held. This track deliberately keeps
`LayerClaim`: global denials such as no-actual-weld, direction-void, no-live-tier,
or no-actual-weld cannot be made conventionally apt by truth at a particular
genjō weld. Its floor clause is silent like every other `ClaimLanguage` in the
development. `RecordedUtterance` supplies the actuality needed for the content
utterance checks, while `denied_misfits_live_offer` and
`fox_utterance_misfits_live_offer` perform the same live-tier check for the
schema language.

The `reEmptied` transformer and `ladder` iterate the separate/fuse rule without
adding a claim that quantifies over all levels. `ErrorFree`,
`reEmptied_obeys_of_errorFree`, and `ladder_obeys_of_errorFree` record the
refutation-only route by which the implemented `finalBelow` side lets the
ladder climb without an added stability premise above the seed. The "completed
ladder" remains an instructive absence: level quantification appears only in
meta-theorems such as `ladder_obeys`, `no_level_final_of_obeys`, and the
existential guard `no_final_level_of_errorFree`. Concrete witnesses such as
`sentience_share_square_inhabited`, `no_sentience_recovery`,
`rung_not_pole_witness`,
`backsliding_witness`, `backsliding_rePitchSequence_witness`,
`standing_does_not_determine_dated`, `subitism_possibility_witness`,
`waaSuddenArrival_witness`, `waaGradualArrival_witness`,
`rate_invisible_to_config`,
`cetana_grading_tracks_weld_not_field_witness`,
`cetana_live_share_without_object_standing_witness` keep the row anchors
model-checked.
`standing_does_not_determine_dated` and `subitism_possibility_witness` share
the same clock-grid witness deliberately: the first serves the disposition/act
retype, while the second names the sudden/gradual possibility claim.
`waaSuddenArrival_witness` gives the doctrine-facing one-step form with
actuality, `waaGradualArrival_witness` gives the register-clock staged form,
and `rate_invisible_to_config` deliberately reuses `rePitch_forgets` as the
rate-invariance anchor.
`MemoryWitness.memory_witness` uses the same register-clock shape to display
recall as reception: `recall_waaOwnershipFace` names the delivered trace,
`falseMemory_waaVacuousOwnershipFace` names the unfilled second place, and
`recall_spent` names the `rePitch_forgets` spentness. The memory names stay
separate even where their concrete welds coincide with the prudence witness, so
the two pressure-tests can cite the same registers without depending on each
other.
`withRespondsTo` and `withConditions` remain neutral countermodel tooling.
`staticized` and the futility theorem family are retired; death and killing are
routed in prose through the subject/object freeze and fox collapse instead.

C.2a Identification/Absences.lean

`InstructiveAbsence` mirrors the paper's section 3 list as inspectable data.
The enum is not an editorial layer: entries remain members while the paper keeps
them in section 3. `AbsenceStatus` records the mutable world-facing fact, so the
third arrival is `retiredAsCheck` rather than deleted or renumbered. The same
rule applies to future retirements: constructors track the section list, while
`status` carries whether an entry still stands.
`undefinedZeroRowRetired` records the loss of the old edge-row exemplar and
anchors its replacement by the generated standing-sentience row.

The anchors are citations and shape checks, not new doctrine. Empty table cells
are recorded beside `tableOrder` as `hasCollapseOccupant` and
`hasFreezeOccupant`; `emptyCells_anchor` checks that a dash remains metadata
while row refutations remain theorem facts. `foxNeverTestsPole_anchor` cites the
concrete fox model's `fox_never_tests_pole`; the recorded-utterance and
agent-side checks keep the worked case away from both share-zero and the
pole-class. `thirdArrival_not_waaMismatchLive` reuses the terminus-response
four-truth theorem: the retired absence is kept as the dukkha-free check. The
fourth-truth, no-safe-stage, and prudential-privilege anchors cite
`waaPathOught_conditional`, `no_final_level_of_errorFree`, and
`PrudentialPrivilegeNegative.not_prudentialPrivilege`. The declined case,
why-calls-land, and no-measure entries deliberately have only data/status pins:
their missing theorem is the content the paper assigns them.

C.3 Meta/Invariance.lean and Meta/InvarianceNegative.lean

`DisplayReparam` is the admission criterion for predicates that mention the
contribution carrier: they must transport across order-preserving and
pole-preserving changes of display convention. This is the formal counterpart
of treating contribution values as display conventions rather than operational
tokens.

`AgentReparam` and `Grid.relabel` are the Being-side twin of that discipline.
A predicate mentioning fine agent tags owes a `relabel_*` transport lemma or an
explicit co-variance statement such as `relabel_index`, marking it as weld-
register vocabulary. `relabel_sameAgentDelivery_iff` makes the important case
explicit: same-agent delivery remains agent-sensitive while depending only on
the tag pattern, not the tag names. This change records the admission rule and
satisfies it for the relabelling lemma set introduced here; it does not impose a
retroactive transport obligation across every existing Being-facing predicate.

The condition-transpose operation and its being-coarsening companion now live in
the signature layer, beside the `conditions`, `DeliveredTo`, and
`BeingCoarsening` vocabulary they transport. `Meta/Invariance.lean` remains the
central home for `DisplayReparam` and all `map_*` transport lemmas.
`transpose_transpose`, `map_transpose`, and the sentience-reading transports
pin the independent axes: reversing delivery and changing display preserve the
supplied mark only through its explicit transported reading. Grid surgery has
no doctrinal transport law.
`DirectionCoarsening.transpose_subTickDelivery` is the delivery-axis companion:
tick equality survives transposition, while the delivery line reverses.
`DirectionCoarsening.displayMapDir`, `mapDir_sameTick_iff`, and
`mapDir_resolutionBounded_iff` centralize its display transport.

`Meta/InvarianceNegative.lean` holds the countermodels. `InvarianceNegative`
explains why equality with the chosen bottom is not the system predicate:
equality-to-bottom fails to transport, while `AtBot` and `Terminus` do.

`DirectionNegative` is the countermodel behind Theory: Karma, "the arrow
retyped": two grids agree on `ConditionsEither` and disagree on `conditions`, so
the symmetric field structure does not recover direction. The physics and
thermodynamics language motivates the reading, but no theorem depends on it.

`InteriorDirectionNegative` is the same demotion one grain down. `RawWeld`
keeps its named `call` and `response` fields because those names are useful
display labels, just as `index` remains a useful projection after the
self-pole demotion. `RawWeld.transposeCR` is only a smuggling detector on
same-carrier call/response examples: unordered pair-content cannot recover
which face is call, so the intra-weld arrow is not before-and-after furniture
inside the weld.

`DirectionCoarseningWitness` adds the finite-resolution check. The raw
register clock cannot be given a universal tick with `ResolutionBounded` over
the injective `Nat` display; a lawful fully coarse display uses the one-point
carrier, whose `DirectionVoid` is obtained through the existing legal
all-equivalent display collapse. The independence witness keeps the register
clock's macro sentience and self-conditioning separate from any direction
coarsening or resolution-bound hypothesis.

`BeingNegative` is the parallel countermodel for designation: one fine grid
allows both merge and split macro readings, so a unique being-boundary is not
recoverable from the grid data alone.

`WeldNegative` lowers the same freedom witness from who-counts-as-one-being to
what-counts-as-one-act. Its `WeldSegmentation` is deliberately local to the
negative witness: segmentation is a diagnosis-time reading over completed
welds, not a new `RawWeld` field and not a new `Grid` parameter. The layer
route for `weldRow` follows from that choice. The weld-grain is a convention
the lens can diagnose exactly like directed time, beings, and the grid-lens;
a bare `RowTag` would have named a row without naming the convention whose
freeze and collapse the row is supposed to catch.

`ContentNegative` supplies the countermodels for the aptness hypotheses on
content rows: a no-actual-weld/no-live grid and the two-bottom direction-void
carrier make the relevant denials true at non-live act-time, so fusion fails
there. The empty-domain witnesses separate additional vacuities:
`emptyBeingGrid_no_liveTier` and
`contentBeingsRow_obeys_emptyBeing` show that no beings leave no act-time tier
on which the content row can fail to fuse.

`CoverageNegative` certifies the coverage hypotheses on
`directionVoid_of_surjective` and `map_waaEffectiveTerminus_of_surjective`:
strictness outside the image of a display reparameterization can make
direction-voidness and faith-closure fail to preserve, parallel in duty to the
aptness countermodels above.

C.3a Doctrines/Doors.lean and Doctrines/DoorsNegative.lean

`DoorReading` supplies a total diagnosis of each fine weld as body, speech, or
mind. `SpeechReading` adds optional claim voicing without a coherence field:
thoughts and expressive bodily deeds remain representable, while restrictions
belong to the predicates that use them. `ProducedUtterance` ties a voiced claim
to an actual weld; only its speech-door form can be converted to a testimonial
record. `DoorsNegative` checks independently that door boundaries, voicing, and
the production weld cannot be recovered from visible grid or content data.

`QuietOn` replaces the old coarsening/tag rectangle in the arhat and fetter
machinery. Canonical arhat display is total fine-being quiet, equivalently
quietness through all three doors. `WaaDefiledFalsehood` is the speech-door
schema of own-act-time falsity plus a live self-pole; identifying it with
canonical deliberate lying is a modeling claim, not a definition. Mind-door
quiet removes defiled thought but does not establish thought-truth—the latter
is the no-nescience boundary in C.4.

C.4 Doctrines/FourTruths.lean, Doctrines/Sraddha.lean,
    Doctrines/Faith.lean, Doctrines/Ethics.lean, and the sibling negative modules

`WaaMismatchGrade` is definitionally `share`; this is the formal honesty clause
for mismatch-talk as covariation rather than a second measure.
`ClenchMismatch` is the actual live-share structure. `WaaDukkha S` adds the
supplied mark, so `clenchMismatch_of_waaDukkha` forgets the phenomenal reading
but no converse is derivable without `S.sentient w`. Insentient appropriation
occupies the structural cell without dukkha; both pole cells exclude mismatch.

`WaaAversionContext` treats sraddha reception per call: it packages a live
prior tendency and an actual clench-mismatch reception, not a stored faith
possession. `WaaEffectiveTerminus` deliberately has two conjuncts: terminus
typing and universal shortfall closure for delivered deeds. The physician
simile belongs exactly there: the grid can prove `waaPathOught_conditional`,
but the antecedents are faith-shaped and are never discharged by field facts.
This direct, non-testimonial route needs effectiveness only. The full
faith-object cannot be replaced by anything the fetter lattice names: the
total-rectangle cut may lack any actual occurrence by
`FettersNegative.total_cut_carries_no_actual_occurrence`, and even adding
actual-agent inhabitation lacks effectiveness by
`FettersNegative.total_cut_with_actual_occurrence_not_waaEffectiveTerminus`.

The old floor-proximity grounding of testimony is withdrawn: floor silence
transmits nothing selective. `ProducedUtterance` now ties content to an actual
voicing weld, and `toRecorded` admits only a speech-door production at that
weld's own act-time. `ProductionFidelity` therefore cannot detach attribution
from production. Mind-door thoughts never enter `RecordedUtterance`,
`Fidelity`, `Faith`, or `Ethics`.

The character conjunct is deliberately wider than testimony.
`WaaNoNescience` requires positive own-act-time truth for every pole-share
speech-or-mind production by the being. For a terminus producer,
`noDelusion_of_noNescience_of_terminus` recovers the former speech-only
`WaaNoDelusion` comparison. The converse fails:
`FaithNegative.noNescience_strictly_stronger_witness` has true speech and one
false pole-share thought. `FaithNegative.aklishta_ajnana_witness` checks that
the false thought is innocent because pole share leaves no live self-pole;
`FaithNegative.arhat_retains_nescience_witness` gives the third ladder fence:
full three-door arhat quiet does not yet remove cognitive obscuration.

Sealed own-delivery can still satisfy the material shortfall conditional, and
absence of speech keeps the testimonial occurrence conjunct empty. Standing
full enlightenment, however, is no longer forced to be mind-vacuous:
`FaithNegative.Sealed.silent_buddha_models` supplies one silent reading with no
thought and another with a true mind production. Both lack speech and deed
occurrences. `WaaFullyEnlightenedEnacted` names the further samyaksambuddha
rung by adding `WaaEffectivenessEnacted` and a tied
`WaaFaithfulSpeechOccurrence`; the old untied act-time witness has disappeared.

The positive no-nescience grounding matches the existing MN 58-shaped
machinery: truth is act-time `TrueAt`, benefit is shortfall closure for a live
aversion, and timeliness is fitting the offered tier. Constructively, "never
wrong" and "right" do not coincide: deriving truth from mere absence of a
misfit would require the unearned step `¬¬ TrueAt → TrueAt`. An ethics of
testimony should preserve that gap. Faith in the physician hands over a
witnessable positive prescription, not a lifetime absence of refutation
laundered through excluded middle. The same discipline that keeps the floor
apophatic therefore keeps testimony positive in the conventional register.
Identity and transmission remain open:
`Factive` says the faith attitude is factive, while per-utterance `Fidelity`
says this record is an uncorrupted occurrence of the attributed speech.
Neither is ever derived from grid or field facts. This is the Kalāma restraint:
śraddhā remains a held hypothesis, consistent with
`EffectiveTerminusNegative`, rather than a certification manufactured by the
formalism. A floor-offered record is vacuously outside `MisfitsOfferedTier` but
transmits no content, because the testimonial route explicitly requires an
act-time offer.

`WaaEthicsStance` bundles factivity and faith in the two-obscurations object and
requires admitted fidelity records to arise from speech productions.
`WaaEthicalCode` is the fourth-truth ought generalized over such testimony,
still an implication type only. The is-ought work is receiver-side: testimony
supplies the is, while the receiver's live `WaaAversionContext` supplies the
want. This is a hypothetical-imperative dissolution, not a refutation, of
Hume's point. `EthicsNegative` keeps the code empty at the pole and
unsatisfiable over an admitted false speech production. A false mind
production is fenced out before the testimonial route begins.

`Doctrines/SraddhaNegative.lean` keeps that conditional honest.
`SraddhaNegative` shows that dropping faith or dropping the live-aversion
antecedent loses the landing, and `OrthogonalityNegative` shows that a
responsive terminus need not be `WaaEffectiveTerminus`.
The opposite regime face is checked by
`waaEffectiveTerminus_of_responsiveTerminus_of_undelivered`: with no delivered
own deeds, the closure conjunct holds vacuously. Teaching and non-teaching are
delivery facts around a terminus, not two being-natures stored in it.
`Doctrines/Shusho.lean` retypes the operational content as
`WaaEffectiveOccurrence`: an actual pole-deed landing as a share-drop against
a live prior tendency. The standing universal survives only as display and
direct-path hypothesis; `WaaEffectivenessEnacted` and
`not_effectivenessEnacted_of_undelivered` fence the sealed-regime vacuity from
an enacted occurrence and provide the deed component of
`WaaFullyEnlightenedEnacted`. The separate standing faith-object is the
two-obscurations `WaaFullyEnlightened` bundle; the enacted top adds its named
speech witness. `EffectiveTerminusNegative` turns the old prose warning into a
collision: changing only `conditions` leaves actual response/share data fixed
while flipping `WaaEffectiveTerminus`.

C.5 Doctrines/Deliberation.lean

`ConsequentialistConvention` is a descriptive reading layer. `DropCount` and
`DropCountInFiber` count share-drop receptions across finite actual runs without
adding probability, utility, or a command register. Their transport lemmas in
`Meta/Invariance.lean` discharge the C.3 admission criterion for using them as
display readings. `dropCountInFiber_le_dropCount` gives the per-fiber bound,
and `dropCount_eq_sum_dropCountInFiber` says a complete noduplicate tag list
adds the fibers back to the total; `map_dropCountInFiberSum` transports the
sum. `ObjectiveNegative` reuses the merge/split being-convention pattern to
show that "my drops" is not a function of grid data alone, with
`split_dropCount_sum_eq_mergedDropCount` as the concrete census check.

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

The disclaimer ledger is synchronized with the supplied-sentience reading:
entries 12, 24, and 25 name the revised stone-act, structural/supplied-dukkha,
and edgeless-domain boundaries, while entries 63 and 64 record grain-indexed
predicate aptness and per-weld supplied sentience. Their `rfl` number pins keep
the paper numbering explicit without turning that numbering into doctrine.

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
negative. The former purge/staticization block is retired. Huichang's
death-and-futility face is now a prose routing: subtraction of a standing
dharma is the subject/object freeze; "emptiness, so suppression changes
nothing" is the fox collapse. The checked residue is the narrower
`decree_engineers_calls_not_receptions`; historical survival remains display.

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

The Dōgen doubling now has a production-side vocabulary. Daishugyō diagnoses:
it reads the sentence weld's live share, while its floor face is both error-free
by silence and structurally unproduced. Jinshin inga instructs: the fitting
instruction is an actual speech production, and a terminus producer would put
that weld at pole without arrogation. `oldMan_defiledFalsehood` and
`jinshinInga_floor_voicing_defiled` converge on the same schema for the old
answer and the counterfactual floor voicing. These checks narrow the historical
contra and type its remainder. `daishugyo_floor_face_unproduced` is the formal
face of an observational equivalence: a register-foreclosing and an
ontologically foreclosing reading of the late Dōgen agree on every production,
because any production separating them would instantiate the defiled-falsehood
schema the checks convict. Whether the floor face may be held therefore remains
prose interpretation — now typed as undischargeable by any find that keeps the
fascicles' own discipline, rather than merely undischarged. The module adds no
holding predicate and returns no verdict. `fox_clenchMismatch_per_life` records
the structural witness. `fox_dukkha_per_life S` takes the sentience mark as an
explicit hypothesis and lives one layer down in `Doctrines/FoxCase.lean`.

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
pole-class. Bull 8 is `AtPoleClass`, now exactly `Terminus`; Bull 9 is
`ResponsiveTerminus`; and Bull 10 is the reading-relative existential
cross-fiber delivery predicate `WaaBullTen S`. The stronger `StrongWaaBullTen S`
is named and shelved. `not_waaBullTen_allInsentient` owns the consequence that
the marketplace is empty under the constant-false reading. The pratyekabuddha
countermodel shows Bull 9 without Bull 10.

The Five Ranks are data plus reading pins; `kenChuTo_implies_waaBullTen` names
the 到/Bull 10 shape under the same coarsening. This is a retype of ranks as
utterance-diagnosis and index-placement, not a second stage ladder.

`FetterReading` now supplies weld-classes directly. `FetterCut` is fine-being
`QuietOn` for the selected provocation class: cessation of enactment in that
class, not possession of an anti-fetter. The retired two-axis rectangle is
recoverable as the special weld-class `cs w.call ∧ ts w.agent`, recorded by
`fiberAtPoleOnWithin_iff_quietOn_rectangle`; no Soma layer remains in the
fetter API. `classQuiet_no_clench_in_class` is the checked soul-guard.

`ViewReading.ownerClaim` supplies identity-view content rather than deriving it
from coarsening data. `FettersNegative.no_view_content_recovery` is the freedom
witness; `ownerClaim_coarsening_freeze_correlation` checks the intended
freeze-content correlation in one supplied model. View factors through mind,
rites through body, and defiled falsehood through speech. Doubt and the upper
fetters remain door-neutral supplied classes.

The path scheme is nested class quietness. `Path.cutClasses` gives the stream,
once-return, non-return, and arhat call-classes; once-return adds no new cut
class, matching the prose weakening clause. `Fetter.kind_lower_iff_cut_by_nonReturn`
pins the table coherence: exactly the lower fetters are cut by non-return.
`all_fetters_cut_at_arhat` upgrades the arhat case from samples to
`∀ f : Fetter`. `arhatPathQuiet_iff_quietOn_univ` says the arhat class is total.
The door-typed `WaaSravakaArhat` is speech-and-mind quiet; `WaaVasana` is a live
body-door occurrence. `sravakaArhat_not_arhat_witness` checks that regional
figure against canonical three-door quiet. Response-form vāsanā at pole share
remains registered future work.

The buddha reading enters as a ladder above that neutral point. Rung 1 is total
three-door quiet, the share axis alone;
`FettersNegative.total_cut_carries_no_actual_occurrence` shows that it has no
occurrence conjunct. Rung 2 adds `ActualAgentInhabited`.
`FettersNegative.total_cut_with_actual_occurrence_not_waaEffectiveTerminus`
checks that rung 2 still lacks effectiveness. Rung 3 is
`WaaEffectiveTerminus`, terminus plus universal shortfall closure, and
it enters the direct śraddhā route as hypothesis. The shushō-ittō face is now
explicit as `WaaEffectiveOccurrence`; the standing rung is a descriptive
display, never the act-time verdict. Rung 4 is the cognitive fence:
`FaithNegative.arhat_retains_nescience_witness` shows that quiet occurrence does
not imply `WaaNoNescience`. The two-obscurations `WaaFullyEnlightened` bundle
adds that speech-or-mind truth condition above effectiveness.

At the enlightenment joint, pratyekabuddha is the sealed-and-silent standing
bundle, not a second attainment. `FaithNegative.Sealed.silent_buddha_models`
checks both a no-thought model and a true-thinking model; each retains empty
speech and deed occurrence faces.
The uncooperative delivered case remains a lower negative boundary: when a
deed arrives but no share drop lands,
`OrthogonalityNegative.waaEffectiveTerminus_stronger_than_terminus` shows that
even effective termination fails. Samyaksambuddha is instead
`WaaFullyEnlightenedEnacted`, where a delivered effective occurrence and a
faithful fitting act-time sentence witness the two standing conditionals.
Non-teaching is still a field fact, never a being who opts out of being read:
the private-buddha freeze is avoided because the model records what was or was
not delivered, not a refusal of object-axis standing.

The arhat anchors are now the fine-being door forms:
`arhat_iff_three_doors_quiet`, `conceit_excluded_of_quietOn`,
`identityView_cut_iff_noDefiledVoicing`, and
`no_defiledFalsehood_of_arhat`. Series quiet remains derived display through
`seriesQuiet_iff_forall_fine`.

Identity-view is the coarsening-freeze enacted: the macro tag held as stored
owner. Its cut is quietness on the identity-view provocation class, so
stream-entry is typed as the cessation of the same attachment the uniform
coarsening clause warns against.

`Doctrines/Factors.lean` adds the path-factor reading over that same fetter
table. `PathFactor.blockerClass` is derived from `DoorReading` and
`FetterReading`, so the factor
scheme is a regrouping of the canonical classes rather than a second taxonomy:
rites is the floor component, view covers identity-view and doubt, and resolve
covers sensual desire and ill will. `FactorHeld` and `FactorReleased` are a
new factor-relation frame. Hold is a witnessed live fine weld in the
factor's blocker class; release is fine-being `QuietOn` for that class. Hold is
not an error by itself, since a stage-appropriate hold is correct. The error
taxonomy remains freeze/collapse on utterance distinctions, and clench remains
the share-frame live-index vocabulary. The raft simile lands exactly at
`factorReleased_rites_iff_ritesGrasp_cut`: rites-grasp is the grasping mode of
the first hold, and cutting it is the first release.

The bridge reading over the existing cells is deliberately prose-only: freeze
is a hold maintained past its use, while collapse is a release enacted before
its use. Each stage's characteristic mistakes can therefore be diagnosed as
overstayed hold and premature release on that stage's factor. The four
hold/release combinations, and the eight once-return-to-non-return gradations
they generate when applied across the view and resolve pairs, are
diagnosis-time readings over welds and classes, never stored ranks.
`WaaResolveAttenuation` gives once-return positive content without adding a cut
class: a resolve-class share-drop run can be strict while still stopping short
of the pole. `WaaSerialFactorRegime` is the matching "usually in order"
conditional; `FactorsNegative.factor_order_underdetermined` blocks
deriving that order from the grid alone.

One level up, the Theravada-side risk is overstaying the hold on the scheme
itself: rank, the shit-stick, the coarsening read as carried structure. The
Mahayana-side risk is premature release of diagnosis: the lens-dismissal cell,
checked elsewhere as `lens_denial_collapse_self_refuting`. Emptiness is not
the absence of the coarsening, but the refusal to hold it as grid-carried.
Lineages differ in where the supplied reading puts its weight, not in type
signature; stage-boundary non-recovery remains checked by
`CorrelationsNegative.no_stage_boundary_recovery`.

Speech and conduct are named as `PathFactor.speech` and `PathFactor.conduct`.
The speech blocker is active as the speech-door weld-class. Conduct remains
inert pending body-door intimation content; the residue ledger owns that
boundary.

Irreversibility is three-layered. Whole-class `FetterCut` is internally
irreversible by quantifier logic: if a later clenched weld in the selected
class exists, the cut never held. Run-assigned
path tags are only display over seen data, and
`FettersNegative.seen_run_underdetermines_fetterCut` gives the fresh-weld
countermodel. A forward guarantee is hostable only as
`waaIrreversibleRegime_conditional`, parallel in voice to the sraddha
conditional. The orthogonality note is checked by
`unquiet_door_still_functions_witness`: door quiet speaks to share, not whether
an actual occurrence exists at another door. No such fact recovers sentience.

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
(`name_responseInvariant`), actual-agent inhabited
(`name_actualAgentInhabited`), and share-zero at its welds (`name_share_bot`).
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
recover the regime. That is enough for the svakarma demotion: restricting
delivery to same-agent lines is a regime wall, not a change in reception
typing.

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

C.11 Meta/VerdictLedger.lean

`generatorRecord` is the theorem-file verdict history rendered as data, not as
a semantic interpretation of the generator. Its entries are episode-grained:
Zahavi, the disposition/act cell, the arrow, and the intra-weld arrow are four
retypes, so `generatorRecord_retype_count` is a check over the list rather
than a stored multiplicity. The `anchors` field records the heterogeneity the
paragraph needs: Zahavi and the disposition/act retype are prose-anchored, the
arrow pins `DirectionNegative`, the intra-weld arrow pins
`InteriorDirectionNegative`, and the answered cases name their theorem
anchors.

`restraintKind` is the legal coarsening. It projects the nine entries to the
six display kinds, while `generatorRecord_restraintKind_seen_count` and
`restraintKind_exhaustive_on_record` check the image. The ledger still adds no
new-cell entry: `generatorRecord_newCell_count` is zero, so it records the
generator's self-restraint independently of the weld-grain row added by the
convention-layer schema.

`misFeed_entries_carry_decomposition` checks only the structural half of the
falsifier: entries tagged as requiring a mis-feed decomposition carry one. The
rate-trend clause and the claims that the retypes were forced, timely, and
historically prior remain prose, because they quantify over the history rather
than over the current record.

C.12 Exposition/Glossary.lean

`Exposition/Glossary.lean` is the canonical glossary source. The three markdown
glossaries are retired in favor of generated output from
`WeldAndArrow/Exposition/Gen/Glossary.lean`; the paper-facing table lives at
`Exposition/Glossary.md`.

The module checks office discipline, not exposition itself. `glossary.length`
pins the curated table size, the term strings are `Nodup`, every `seeAlso`
target resolves to an earlier row, and `#verify_glossary_anchors` checks that
all named Lean anchors exist in the environment. Empty anchors are allowed for
terms whose public gloss is prose-only. Gloss accuracy, canonical nuance, and
the adequacy of each gloss for newcomers remain prose obligations; expert
caveats live in the Disclaimers.

C.13 Doctrines/Icchantika.lean

`Icchantika` is entered as a declined foreclosure case rather than as a stored
negative kind. The formal reading is deliberately literal and run-shaped:
the agent has an actual occurrence, and every actual response is live at the
self-pole index. That makes the being anti-terminus on its run,
so `not_waaEffectiveTerminus_of_icchantika` gives the honest agent-role bar:
this run cannot seat the icchantika as the enlightened agent, because
`WaaEffectiveTerminus` includes terminus typing.

The receiver-side result points the other way.
`aversionContext_of_icchantika_reception` says an actual icchantika reception
with live prior tendency supplies the `WaaAversionContext` antecedent, and
`icchantika_reachable` routes that antecedent through the existing sraddha
conditional. Thus the icchantika is maximally available as receiver exactly
where it is unseatable as terminus-agent on the same run.

`icchantika_release_not_foreclosed` is the anti-rank check. A concrete
icchantika-typed receiver can itself be part of a share-drop landing from a
higher prior tendency, so the run's clenched profile does not recover a
permanent no-landing verdict. This is the same discipline as backsliding in
reverse: attainment is not stored, and neither is non-attainment. The fighting
stance is a seed, not a rank.
-/
