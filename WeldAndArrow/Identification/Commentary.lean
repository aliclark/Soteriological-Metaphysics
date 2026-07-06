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
`WaaAversionContext`, and `WaaFullyEnlightened`. Doctrine names are carried by
module names and commentary headings; checked reading identifiers use the single
`Waa` marker.

Unprefixed names remain the neutral delivery, order, token-projection, and
tier-placement vocabulary. `Grid.DirectedConvention` marks vocabulary that
consumes the directional reading of `conditions`; the primitive signature itself
does not add asymmetry, irreflexivity, or transitivity axioms to `conditions`.

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
not an axiom.

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
`cetana_grading_tracks_weld_not_field_witness`,
`cetana_live_share_without_object_standing_witness`, and the
`registerClock_staticized_*` checks keep the row anchors model-checked.
`standing_does_not_determine_dated` and `subitism_possibility_witness` share
the same clock-grid witness deliberately: the first serves the disposition/act
retype, while the second names the sudden/gradual possibility claim.
`withRespondsTo` and `staticized` are the futility operation: delivery-loss is
real (`futility_delivery_loss_real`) while object-axis standing is unchanged
(`Grid.DirectedConvention.staticized_objectAxisStanding_iff`).

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
admits both merge and split macro readings, so a unique being-boundary is not
recoverable from the grid data alone.

`ContentNegative` supplies the countermodels for the aptness hypotheses on
content rows: an all-stone/no-live grid and the two-bottom direction-void
carrier make the relevant denials true at non-live act-time, so fusion fails
there.

C.4 Doctrines/FourTruths.lean, Doctrines/Sraddha.lean,
    Doctrines/Faith.lean, and the sibling negative modules

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

`WaaFaithPrinciple` abstracts the sraddha antecedent to testimony: faith in
enlightenment transmits truth to recorded utterances, with
`waaPathClaimLanguage` instantiating the `ClaimLanguage` interface for the
physician's sentence. `FaithNegative` shows the principle exceeds its own
faith-object, so the "never discharged by field facts" clause survives the
abstraction.

`Doctrines/SraddhaNegative.lean` keeps that conditional honest.
`SraddhaNegative` shows that dropping faith or dropping the live-aversion
antecedent loses the landing, and `OrthogonalityNegative` shows that a
responsive terminus need not be `WaaFullyEnlightened`.

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

C.7 Doctrines/Correlations.lean, Doctrines/CorrelationsNegative.lean,
    Doctrines/Fetters.lean, and Doctrines/FettersNegative.lean

`Doctrines/Correlations.lean` treats the Ten Bulls, Five Ranks, and stage
schemes as checked correlations over existing machinery. `StageScheme` is just
`BeingCoarsening`; the warning belongs to holding a coarsening as grid-carried
structure, not to any one ladder. `CorrelationsNegative.no_stage_boundary_recovery`
duplicates the being-boundary no-recovery pattern for stage schemes so the
uniform freeze clause is witnessed without importing `Meta` upward into
`Doctrines`.

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

`FiberAtPoleOn` and `LiveFiberAtPoleOn` sit in `Signature/BeingConvention.lean`
because they are neutral class-restricted fiber vocabulary. Fetters merely
consume them: `FetterReading` supplies the provocation classes as model-side
data, and `FetterCut` means the fiber is at pole on that fetter's class. Thus a
cut is cessation of enactment in the class, not possession of an anti-fetter.
`classQuiet_no_clench_in_class` is the checked soul-guard: where the class cut
holds, no actual weld in that class carries a live self-pole index.

The path scheme is nested class quietness. `Path.cutClasses` gives the stream,
once-return, non-return, and arhat call-classes; once-return adds no new cut
class, matching the prose weakening clause. `arhatPathQuiet_iff_fiberAtPole`
says the arhat class is total, so arhat path-quietness is ordinary
`FiberAtPole`. The older arhat anchors remain: `identityView_excluded_at_arhatFiber`,
`conceit_excluded_at_arhatFiber`, and `arhatFiber_of_termini`.

Identity-view is the coarsening-freeze enacted: the macro tag held as stored
owner. Its cut is quietness on the identity-view provocation class, so
stream-entry is typed as the cessation of the same attachment the uniform
coarsening clause warns against.

Irreversibility is three-layered. Whole-fiber `FetterCut` is internally
irreversible by quantifier logic: if a later clenched class-weld exists, the cut
never held. Run-assigned path tags are only display over seen data, and
`FettersNegative.seen_run_underdetermines_fetterCut` gives the fresh-call
transfer countermodel. A forward guarantee is hostable only as the conditional
`waaIrreversibleRegime_conditional`, parallel in voice to the sraddha
conditional.
-/
