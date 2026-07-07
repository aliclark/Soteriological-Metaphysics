# A Plain-English Reading of the Lean Theorems

**Scope.** This document states, in plain English, what the Lean declarations in
`Signature/*`, `Consequences/{Basic,Taxonomy,Ladder,ContentRows}.lean`, `Doctrines/*`,
`Identification/*`, and `Meta/*` assert. It reads the checked Lean surface:
definitions, theorem statements, and proof status where that matters.
Interpretive prose remains secondary to the formal statements.

For the canonical input-side assumption list, see
`WeldAndArrow/Signature/Assumptions.lean`; this document reads theorem outputs.

The project is pinned to `leanprover/lean4:v4.31.0` in `lean-toolchain`.

**Conventions.** A theorem proved by `rfl` or `Iff.rfl` is true by unfolding
definitions. A theorem whose proof is a projection, contradiction, or witness
assembly is described as such. A "weld" is always the triple `RawWeld` /
`G.Weld`; "actual" always means the equation
`respondsTo w.agent w.call = some w.response`.

Identifiers beginning `Waa` mark system-POV readings: what the concept looks
like from this grid, not what the concept is in detached doctrinal voice. The
single marker covers ownership, appropriation, whose-ness, reach-back,
sowing-side aiming, four-truths mismatch vocabulary, and sraddha conditional
vocabulary. Doctrine words live in module names and prose; checked reading
identifiers use `Waa`.

The unprefixed vocabulary is neutral order/delivery vocabulary, including Row-2
index-placement names such as `HasSelfPoleIndex`, `selfPoleIndex`, and
`Tier.hasLiveShare`.

In generated or prose presentations, the `Signature` layer is titled **Theory**
and the `Consequences` layer is titled **Theorems**, matching the paper's part
titles. The Lean module names state the role; the prose names state the
correspondence.

`Grid.DirectedConvention` is the second marking. It contains vocabulary that
reads direction into the direction-free relation `conditions`: delivery,
landing, environs lines, share-drop lines, aiming, and the ownership-face
predicates. The signature itself still carries no asymmetry, irreflexivity, or
transitivity for `conditions`. Role-asymmetry is not temporal asymmetry: the
`deed` and `reception` slots are different roles, but the reception slot means
"where the welding happens", not "the later one".

`Grid.DirectedConvention.TimeDirection` is an abbreviation of `Strict`; all
strictness theorems apply to it transparently. The formal modules keep their
comments mathematical and point to `Identification/Commentary.lean` C.1-C.12 for
the paper-facing readings.

The namespace tree now records ontological ordering. Floor/genjō and the bare
signature sit outside the convention layers. `Grid.DirectedConvention` reads
the arrow; `Grid.DirectedConvention.BeingConvention` reads fine tags as
macro-scale beings; `Grid.DirectedConvention.BeingConvention.GridConvention`
contains the pole-affirming row schema, the content-layer companion language,
the ladder API, and the generated table-order data across the `Consequences`
files. Names are placed by what their reading presupposes, not by what their
definition consumes.

---

## 0. Preliminaries

**Order structure.** `Preorder` is a hand-rolled reflexive and transitive
relation `≼`; no totality and no antisymmetry are assumed. `Incomparable a b`
means neither `a ≼ b` nor `b ≼ a`. `OrderEq a b` means `a ≼ b` and `b ≼ a`.
`Strict a b` means `a ≼ b` and not `b ≼ a`.

The preorder facts are:

- `incomparable_symm`, `not_le_of_incomparable`, and `not_ge_of_incomparable`.
- `strict_irrefl`: strict direction is never reflexive.
- `strict_asymm` and `strict_trans`: strict direction is asymmetric and
  transitive as soon as it is read from the preorder.
- `strict_of_le_of_strict` and `strict_of_strict_of_le`: strict comparison
  composes with weak comparison on either side.
- `not_strict_of_orderEq` and `no_strict_of_all_orderEq`: order-equivalence
  kills direction, pointwise or carrier-wide.

`PreorderBot` adds a designated bottom element, written `shareBot`, with
`shareBot ≼ a` for every `a`. `AtBot a` means `a ≼ shareBot`. Since
`shareBot ≼ a` is always available, `AtBot a` says that `a` is
order-equivalent to the designated bottom. The pole is therefore an
order-class, not identity with one token.

The project stays self-contained and does not import Mathlib. Mathlib's
counterparts are `Preorder`, `OrderBot`, and `IsBot`; local `AtBot` is the
order-class of the bottom and plays the role Mathlib's `IsBot` would play for
that chosen element.

The basic bottom lemmas are:

- `shareBot_le`: the designated bottom is below every value.
- `atBot_shareBot`: `shareBot` is at the pole-class.
- `atBot_of_eq_shareBot`: equality with the representative implies `AtBot`.
- `orderEq_shareBot_of_atBot`, `atBot_of_orderEq_shareBot`, and
  `orderEq_shareBot_iff_atBot`: `AtBot a` and `OrderEq a shareBot` are
  equivalent formulations.

**The signature.** A `Grid Contrib` consists of three types (`Being`, `Call`,
`Response`), a response function `respondsTo`, a Row-2 display function
`grade`, and a relation `conditions` on welds. `ConditionsEither w1 w2` is the
symmetric closure `conditions w1 w2 ∨ conditions w2 w1`;
`conditionsEither_symm` swaps the disjuncts. `ConditionsEitherChain` is the
reflexive-transitive closure of that symmetric relation. There is no separate
two-component drive object in the signature.

A weld is the triple `⟨agent, call, response⟩`. `Actual w` means the response
really is mounted. `index w` is `w.agent`. `share w` is
`grade w.agent w.call w.response`.

`HasSelfPoleIndex w` means `¬ AtBot (share w)`. `WaaAppropriates w` is
definitionally the same proposition. `selfPoleIndex w h` returns `w.agent` and
uses the proof argument only for typing.

**Function-side predicates.**

- `MountsAt b c`, `MountsSomewhere b`, and `RespondsToEveryCall b` record
  increasing response-function strength.
- `Stone b` means no call receives a response from `b`.
- `Terminus b` means every mounted response by `b` has pole-class grade.
- `LiveTerminus b` adds that some response-function is present.
- `ResponsiveTerminus b` says every call receives a pole-class response.
- `AtPoleClass b` is `Stone b ∨ Terminus b`.
- `ProbeConstant b cs` says any two actual responses by `b` at calls in `cs`
  have order-equivalent grades.
- `ResponseInvariant b` and `ResponseVariesWithCall b` describe response-shape
  only.

**BeingConvention definitions.** `BeingCoarsening G Macro` is a diagnosis-time
projection `G.Being → Macro`; it is not stored in the signature.

Under a coarsening `κ`:

- `InFiber b w` means the weld's fine agent projects to macro tag `b`.
- `SameFiber p q` is equality of projected macro tags.
- `FiberInhabited b` and `ActualFiberInhabited b` are the non-vacuity guards.
- `SentientTag b` means some fine tag in the fiber mounts a response somewhere.
- `not_sentientTag_iff_fiber_all_stone` proves that non-sentience is exactly
  the all-stone fiber; there is no separate `InsentientTag`.
- `FiberAtPole b`, `FiberAtPoleOn b cs`, `FiberAtPoleOnWithin b cs ts`,
  and `FiberAtPoleWithin b ts` are whole-fiber, call-class, product, and
  tag-region pole readings. `ActualFiberInhabitedWithin`,
  `LiveFiberAtPoleWithin`, and `SelfAptTagWithin` are the tag-axis live and
  self-apt companions.
- `SelfAptTag b`, `LiveSelfAptTag b`, and `Patchy b` are the whole-fiber
  self-apt and mixed readings.
- `fiberAtPole_of_fiber_termini`, `no_live_index_under_fiberAtPole`,
  `selfAptTag_indices_are_per_weld_only`, and the live exclusivity theorems are
  the checked fiber facts.
- `SelfConditioningTag b` is the minimal internal delivery-line witness.
  `StrongSelfConditioningTag b` is defined as a shelved asymptote.
- `Delegation b` packages an actual fine weld in the macro fiber; its share is
  definitionally the delegate weld's share.

**DirectionConvention definitions.** `DirectionCoarsening G Tick` is the
delivery-axis twin of `BeingCoarsening`: a diagnosis-time tick projection over
welds, not a field of `Grid`. `SameTick` is tick equality and is symmetric;
`ResolvedDelivery` is delivered across distinct ticks; `SubTickDelivery` is
delivered inside one tick.

`ResolutionBounded` is a model-supplied display coherence condition: same-tick
welds have order-equivalent shares. It is not a legitimacy, pole, or sentience
predicate. `no_timeDirection_within_tick` proves that sub-tick delivery carries
no strict `TimeDirection`, and
`no_timeDirection_of_resolutionBounded_subsingleton` is the one-tick limit over
weld shares. Transposition leaves `SameTick` and `ResolutionBounded` unchanged
while `transpose_subTickDelivery` reverses only the delivery line.

**Configurations and share-drops.** `Config` has one field,
`tendency : Contrib`; it stores no `Being`, no `Weld`, and no owner.
`rePitch before received` returns the config with tendency `share received`;
`before` is unused in the value. `IsShareDrop before received` means
`Strict (share received) before.tendency`, i.e. `share received ≼
before.tendency` and not `before.tendency ≼ share received`.

**DirectedConvention definitions.** The directional reading layer contains:

- `WaaReachBackFull`, `DeliveredTo`, `NotDeliveredTo`, and `WaaAimedAt`.
- `LandsAt`, `ObjectAxisStanding`, `LandsWithShareDrop`, and
  `HasShareDropLanding`.
- `EnvironsLine` and `ShareDropLine`.
- `ShortfallClosedAt`, `WaaFullyEnlightened`, `WaaAversionContext`, and
  `WaaPathOught`.
- `WaaPathClaim`, `WaaFaithPrinciple`, and `WaaFaithOught`.
- `WaaReportFace`, `WaaOwnershipFace`, `WaaVacuousOwnershipFace`, and
  `WaaDiachronicWhose`.

All of these are definitions over `conditions`, `Actual`, `IsShareDrop`, and
`WaaAppropriates`; none adds a new axiom to `conditions`.

**Four truths and sraddha.** `WaaMismatchGrade w` is definitionally `share w`.
`WaaMismatchLive w` means an actual occurrence with a live self-pole index; with
actuality supplied, `waaMismatchLive_iff_hasSelfPoleIndex` gives the exact typing
condition. `not_waaMismatchLive_of_stone` keeps stones outside the occurrence
domain, and `waaMismatch_atBot_of_terminus_response` sends terminus responses to
the pole-class. The fourth truth the grid can only display: Lean now proves
the implication whose antecedents it never asserts. The detached injunction
remains absent from the system's assertable voice.

**Tiers and distinctions.** A `Tier` is `floor` or `actTime w`.
`Tier.hasLiveShare` is `False` at `floor` and `HasSelfPoleIndex w` at
`actTime w`. Distinctions, claim languages, recorded utterances, error grades,
and generator outcomes define the separate/fuse diagnostic vocabulary over
tiers.

**Identification layer.** `StateToolFits w` means `¬ HasSelfPoleIndex w`; with
the definitions above this is double-negated pole-class membership. The exact
iff with `AtBot` therefore requires decidability of the one proposition
`AtBot a`, not decidable equality on all of `Contrib`.

---

## 1. Signature Layer (`Signature/*`)

`no_self_pole_index_of_atBot`: if `AtBot (share w)`, then `w` has no live
self-pole index. This is direct contradiction with
`HasSelfPoleIndex w := ¬ AtBot (share w)`.

`no_self_pole_index_of_eq_shareBot`: equality `share w = shareBot` is first
converted to `AtBot (share w)`, then the previous theorem applies.

`selfPoleIndex_eq_agent_of_hasSelfPoleIndex`: the evidence-carried index is
`w.agent`. Definitional (`rfl`).

`strict_shareBot_of_hasSelfPoleIndex`: a live self-pole index gives
`Strict shareBot (share w)`. The proof packages `shareBot_le` with the
definition `HasSelfPoleIndex w := ¬ AtBot (share w)`.

`strict_shareBot_iff_not_atBot`: being strictly above the designated bottom is
equivalent to not being in the bottom order-class.

`not_waaAppropriates_of_atBot` and `not_waaAppropriates_of_eq_shareBot`: the
same no-index facts under the definitional name `WaaAppropriates`.

`share_eq_grade_check`: `share w = grade w.agent w.call w.response`.
Definitional (`rfl`).

`atBot_of_terminus_response`: if `b` is a `Terminus` and
`respondsTo b c = some r`, then the weld `⟨b, c, r⟩` has `AtBot` share.

`no_self_pole_index_of_terminus_response` and
`not_waaAppropriates_of_terminus_response`: a terminus response has no live
self-pole index and does not WAA-appropriate.

`stone_is_terminus_vacuously`: every `Stone` is a `Terminus`. This is vacuous: the
response hypothesis in `Terminus` can never be satisfied for a stone.

`AllStone` says every being in the grid is stone-typed. `DirectionVoid` says
the contribution carrier has no strict comparisons anywhere.

`not_stone_of_mountsSomewhere`, `liveTerminus_not_stone`, and
`responsiveTerminus_live_of_call` are witness/projection facts over response
function.

`Grid.DirectedConvention.deliveredTo_or_not`: for a particular pair of welds,
if `conditions deed reception` is decidable, then either
`DeliveredTo G deed reception` or `NotDeliveredTo G deed reception`.

`Grid.DirectedConvention.deliveredTo_iff_waaReachBackFull`: definitional
(`Iff.rfl`), since both names are `conditions`.

`Grid.DirectedConvention.objectAxisStanding_of_landsAt`: a landing gives
object-axis standing, witnessed by the reception in hand.

`Grid.DirectedConvention.objectAxisStanding_of_hasShareDropLanding`: a
share-drop landing gives object-axis standing through its landing component.

`not_collapse_of_obeysSeparateFuse`: the first clause of `ObeysSeparateFuse`
contradicts the equivalence required by `Collapse` at any live tier.

`not_freeze_of_obeysSeparateFuse`: the second clause of `ObeysSeparateFuse` at
`floor` gives the equivalence denied by `Freeze`.

`not_freeze_of_same_claim`: a distinction whose two sides are the same claim
cannot freeze.

`no_agent_recovery_of_field_collision`: if two distinct beings can actually
produce the same call-response pair, no function from field residue
`Call × Response` can correctly recover the agent for every actual weld.

**`clockGrid`.** The concrete grid uses `Nat` with bottom `0`; `rigid` responds
nowhere, `adaptive` responds with `chime` when the listener is present,
`grade` is constantly `0`, and `conditions` is always false.

- `rigid_is_stone`: `rigid` responds nowhere.
- `adaptive_is_terminus`: `adaptive` is a terminus.
- `adaptive_not_stone`: `adaptive` responds at `present`.
- `clockGrid_function_share_split_witness`: the concrete grid contains a stone
  and a non-stone terminus.

**`registerClockGrid`.** The second concrete grid uses natural-numbered fine
registers as beings. Each register answers the tick by handing off to the next
register; delivery follows that hand-off. `registerClockCoarsening` merges the
fine registers into one macro tag at diagnosis-time. The checked facts are
`registerClock_macro_sentient` and `registerClock_macro_selfConditioning`.

**`backslideGrid` and `gradingCollisionGrid`.** `backslideGrid` has one being
answering a gentle call at share `0` and a harsh call at share `5`, giving the
concrete carrier for the same-being backsliding witnesses.
`gradingCollisionGrid` has two actual welds with the same call-response residue
and different shares, giving the concrete carrier for the cetana field-residue
witness.

---

## 2. Consequences and Taxonomy (`Consequences/Basic.lean`, `Consequences/Taxonomy.lean`, `Consequences/Ladder.lean`, `Consequences/ContentRows.lean`)

**Function/share and poles.** `share_eq_grade` is definitional. The response
facts `mountsAt_of_actual`, `mountsSomewhere_of_actual`,
`not_stone_of_actual`, `not_actual_of_stone`,
`not_mountsSomewhere_of_stone`, and `not_stone_of_response` are direct
witness/projection/contradiction consequences of `Actual`, `MountsAt`, and
`Stone`.

`atPoleClass_of_stone` and `atPoleClass_of_terminus` introduce the two
disjuncts of `AtPoleClass`. `atPoleClass_and_not_stone_of_liveTerminus`
combines the terminus disjunct with `liveTerminus_not_stone`.
`not_stone_of_responsiveTerminus_of_call` uses the supplied call to get live
function.

**Re-pitch and share-drops.** `rePitch_tendency_eq_share` is definitional:
the re-pitched tendency is the received weld's share.
`isShareDrop_iff_rePitch_tendency_drop` is definitional after substituting the
re-pitched tendency for `share received`.
`rePitch_tendency_le_before_of_shareDrop` and
`not_before_le_rePitch_tendency_of_shareDrop` project the two conjuncts of
`IsShareDrop`. `rePitch_tendency_atBot_of_terminus_response` sends a terminus
response into the pole-class.

**Conditions and response replacement.** `withConditions` replaces only the
delivery relation. Its `withConditions_respondsTo`, `withConditions_grade`, and
`withConditions_share` lemmas are definitional, and
`grade_independent_of_conditions` / `share_independent_of_conditions` state the
cetana anchor: grade and share are blind to downstream delivery. Dually,
`withRespondsTo` replaces only the response function; `withRespondsTo_grade`,
`withRespondsTo_share`, and `withRespondsTo_conditions` are definitional.
`staticized b` removes the responses of one being and leaves grade and delivery
in place. The futility facts are `futility_delivery_loss_real`,
`staticized_responseInvariant`, `futility_object_axis_subtraction_nil`, and
`Grid.DirectedConvention.staticized_objectAxisStanding_iff`.

**The environs lens.** The directional theorem block lives under
`Grid.DirectedConvention`.

`environsLine_of_shareDropLine`, `isShareDrop_of_shareDropLine`, and
`deliveredTo_of_environsLine` are projections.

`not_isShareDrop_of_tendency_atBot`: if the prior tendency is already
`AtBot`, then no received weld is a strict share-drop against it. The proof
uses `before.tendency ≼ shareBot ≼ share received` to contradict the second
conjunct of `IsShareDrop`.

`not_isShareDrop_of_eq_shareBot_tendency`: equality with the representative
bottom is a bridge into the previous theorem.

`Grid.DirectedConvention.no_shareDropLine_of_tendency_atBot`: with an `AtBot`
prior tendency, no `ShareDropLine` exists, because its share-drop conjunct is
impossible.

`Grid.DirectedConvention.no_shareDropLine_of_eq_shareBot_tendency`: equality
bridge into the previous theorem.

`Grid.DirectedConvention.hasShareDropLanding_of_shareDropLine_actual`: a
share-drop line whose reception is actual assembles the existential
`HasShareDropLanding` witness. This is the checked core of effectiveness talk
as display.

`ShortfallClosedAt` states local, delivered-pair shortfall closure for a live
prior tendency. `WaaFullyEnlightened` adds this universal closure conjunct to
`ResponsiveTerminus`; `responsiveTerminus_of_waaFullyEnlightened` and
`shortfallClosedAt_of_waaFullyEnlightened` project the two parts.

**Delivery and share-drop landing.** The reach/aiming biconditionals are
definitional (`Iff.rfl`). The remaining delivery theorems are projections from
`LandsAt`, `LandsWithShareDrop`, or `HasShareDropLanding`, plus existential
witnesses:

- `deliveredTo_of_landsAt`, `actual_of_landsAt`
- `landsAt_of_landsWithShareDrop`, `isShareDrop_of_landsWithShareDrop`
- `deliveredTo_of_landsWithShareDrop`, `actual_of_landsWithShareDrop`
- `exists_landsAt_of_hasShareDropLanding`
- `exists_actual_reception_of_hasShareDropLanding`
- `exists_shareDrop_reception_of_hasShareDropLanding`

**Reception pairs.** `first_actual` and `second_actual` project stored proofs.
`firstConditionsSecond_iff_deliveredTo` is definitional and states the pair's
directed relation via `Grid.DirectedConvention.DeliveredTo`. The two
`rePitchSequence_*_tendency` theorems are definitional and show the sequence's
tendencies are the two weld shares.

**Tiers and separate/fuse.**

- `floor_has_no_live_share`: no live share at `floor`.
- `actTime_hasLiveShare_iff_hasSelfPoleIndex`: definitional.
- `not_actTime_hasLiveShare_of_atBot`: an act-time tier whose weld is at the
  pole-class has no live share.
- `not_actTime_hasLiveShare_of_eq_shareBot`: equality bridge into the previous
  theorem.
- `not_collapse_floor`, `hasLiveShare_of_collapse`,
  `hasLiveShare_of_separated`, `not_collapse_of_separated`,
  `fused_of_obeysSeparateFuse`, `separated_of_obeysSeparateFuse`, and
  `not_freeze_of_fused_floor` are the direct separate/fuse diagnostics.

`answersCall_eq_weld_call` and `fitsOfferedTier_iff_trueAt` are definitional.
`verdict_voice_assertable` and `shortfall_voice_displayable` confirm the two
`ErrorGrade.voice` assignments.
`waa_conditional_voice_assertable` and
`waa_detached_ought_voice_displayable` pin the new conditional/detached split:
the implication is verdict-voiced, while the detached injunction is only
shortfall-voiced.

**Generated table rows.** Under
`Grid.DirectedConvention.BeingConvention.GridConvention`, `RowTag` names the
schema-generated table rows, including the five `ConventionLayer` rows via
`.layer`. `RowClaim` has `inForce r` and `denied r`, and `rowLanguage G` gives
them pole-affirming semantics: at `floor` every row claim holds; at `actTime w`
the conventional side holds, while the denial side holds exactly when
`AtBot (G.share w)`.

`rowOf G r` instantiates `Distinction G` from this language.
`rowOf_separated_at_live`, `rowOf_collapse_self_refuting`, `rowOf_not_freeze`,
`denied_holds_only_where_no_live_share`, `rowOf_errorFree`, and
`pole_validates_all_claims` are hypothesis-free. `rowOf_obeys` and
`rowOf_obeys_iff_errorFree` carry only the local decidability/stability needed
to turn non-live act-time into `AtBot`. `denied_misfits_live_offer` is the
recorded-utterance check; `fox_utterance_misfits_live_offer` specializes it to
the marquee fox row.

The old pilot names are compatibility names for schema tags:
`beforeAfterRow G`, `intraWeldArrowRow G`, `beingsRow G`, `gridLensRow G`, and
`weldRow G` are `rowOf G (.layer ...)`; `doerDeedRow G` is the schema-only
MMK 8 row. Their collapse and freeze names keep hypothesis-free statements;
their `*_obeys` names carry the stability hypothesis. `tableOrder` records the
full table shape as Lean data: nineteen schema rows, one ladder row, and six
prose rows. Schema-row cell occupancy is also data now:
`hasCollapseOccupant` and `hasFreezeOccupant` record where the
paper's table has an occupant rather than a dash, and
`perCallGlobal_empty_collapse_cell_anchor` checks the per-call/global dash
without turning it into new grid semantics.

**Concrete consequence witnesses.** The small model checks now include
`shareZero_not_functionZero_witness`, `rung_not_pole_witness`,
`backsliding_witness`, `backsliding_rePitchSequence_witness`,
`standing_does_not_determine_dated`, `subitism_possibility_witness`,
`cetana_grading_tracks_weld_not_field_witness`,
`cetana_live_share_without_object_standing_witness`,
`registerClock_staticized_zero_stone`,
`registerClock_staticized_objectAxisStanding_iff`, and
`pole_tier_buddha_inhabited`, with the fox run-through now checked in
`FoxCase.foxGrid`. These are witness assemblies over the concrete grids, mostly
by unfolding and `decide`.

**Content-bearing rows.** `contentLayerLanguage` uses the same `LayerClaim`
syntax but gives content to denials: no strict direction, no response variation
with call, all beings stone, no live tier anywhere, or no actual welds.
`contentBeforeAfterRow`, `contentIntraWeldArrowRow`, `contentBeingsRow`,
`contentGridLensRow`, and `contentWeldRow` are the content rows. Their
obedience theorems are conditional:
`contentBeforeAfterRow_obeys_of_direction`,
`contentIntraWeldArrowRow_obeys_of_variation`,
`contentBeingsRow_obeys_of_being`,
`contentGridLensRow_obeys_of_liveTier`, and
`contentWeldRow_obeys_of_actual` require exactly the witness that makes the
denial false at non-live act-time. These content rows keep the diagnostic
live-side because their global denials cannot be made true by a particular
pole-class weld; they answer aptness-to-hold, not truth-at-tier.

`beings_denial_fits_only_floor` and
`time_denial_unfit_for_appropriating_utterer` are utterance-level
self-refutation results. The beings theorem uses the `RecordedUtterance`
actuality field to get a non-stone utterer; the time theorem uses the live
share as a strict direction witness. The intra-weld utterance theorem is the
weaker schema-language live-tier check,
`interior_order_denial_unfit_for_live_utterer`; one recorded utterance does not
by itself supply two distinct responses.

**Re-emptying ladder.** `LadderSide`, `reEmptied`, and `ladder` generate the
next distinction from the previous one. `reEmptied_obeysSeparateFuse` proves
that obedience propagates, while `ErrorFree`, `errorFree_of_obeys`,
`reEmptied_obeys_of_errorFree`, `ladder_obeys_of_errorFree`, and
`ladder_errorFree_of_errorFree` show the stronger refutation-only route above
an error-free seed. `no_level_final`, `no_final_level`, and
`ladder_collapse_self_refuting` rule out freeze and collapse at generated
levels. `beingsLadder`, `beforeAfterLadder`, `intraWeldArrowLadder`,
`gridLensLadder`, `weldLadder`, and `doerDeedLadder` are schema seeds; their
`_obeys_succ` facts are hypothesis-free, while all-level `*_obeys` names
include the seed's stability hypothesis. `contentBeingsLadder` is the content
instance under the non-stone aptness hypothesis.

---

## 3. Doctrines (`Doctrines/FourTruths.lean`, `Doctrines/Sraddha*.lean`, `Doctrines/Faith*.lean`, `Doctrines/Ethics*.lean`, `Doctrines/Deliberation.lean`, `Doctrines/Gradeability.lean`, `Doctrines/Ledger.lean`, `Doctrines/Correlations*.lean`, `Doctrines/SuddenGradual*.lean`, `Doctrines/OtherPower*.lean`, `Doctrines/Fetters*.lean`, `Doctrines/Factors*.lean`)

`waaMismatchGrade_eq_share` is definitional. `waaMismatchGrade_le_of_share_le` is the
ordinal covariation theorem: any share comparison is the corresponding
mismatch-grade comparison.

`WaaMismatchLive` is actual occurrence plus live self-pole index.
`waaMismatchLive_iff_hasSelfPoleIndex` removes the actuality conjunct when the
occurrence is already known actual. `not_waaMismatchLive_of_stone` uses
`not_actual_of_stone`; `waaMismatch_atBot_of_terminus_response` reuses
`atBot_of_terminus_response`.

`WaaAversionContext` packages a live prior tendency and an actual
live-mismatch reception. `waa_path_landing` proves the checked conditional:
`WaaFullyEnlightened`, a deed by that being, delivery to the reception, and
the aversion context imply `HasShareDropLanding`. `WaaPathOught` is only this
implication type, and `waaPathOught_conditional` proves it.

`no_waa_path_at_pole` proves that no share-drop landing can be constructed
from an `AtBot` prior tendency. `no_waa_aversion_context_at_pole` shows the
live-aversion antecedent fails there. `Doctrines/SraddhaNegative.lean` supplies
concrete countermodels for dropping faith or dropping aversion.

`OrthogonalityNegative` reuses the `SraddhaNegative` zero-effectiveness grid:
a responsive terminus can fail `WaaFullyEnlightened` because the delivered
deed has no share-drop landing for the receiver's live prior tendency.
`waaFullyEnlightened_stronger_than_terminus` proves the strictness.
`waaFullyEnlightened_of_responsiveTerminus_of_undelivered` gives the sealed
regime face: if no own deed is delivered, the shortfall-closure conjunct holds
vacuously for any responsive terminus.

**Faith.** `WaaPathClaim` packages the local claim that a prior configuration,
deed, and reception satisfy `ShortfallClosedAt`; `waaPathClaimLanguage` makes
that claim a `ClaimLanguage`. `WaaFaithPrinciple` is the testimonial
antecedent: faith in a fully enlightened being makes that being's recorded
utterances fit their offered tier. `waa_says_true_of_faith` is the direct
projection of the principle, while
`fitsOfferedTier_of_waaFullyEnlightened_ownDeed` records the old own-deed
fragment where full enlightenment itself supplies the claim truth.
`waa_path_landing_of_faithPrinciple` and `waaFaithOught_conditional` rederive
the landing through recorded testimony. `FaithNegative` shows that neither
faith as the enlightenment premise itself nor free faith validates the
principle.

**Ethics.** `WaaEthicsStance` bundles the faith principle with faith in one
faith-object; `WaaEthicalCode` generalizes the fourth-truth ought across that
object's recorded testimony while remaining an implication type.
`waaEthicalCode_conditional` is the hypothesis-free conditional. The voice
pair is split by `waa_ethics_conditional_voice_assertable` and
`waa_ethics_detached_voice_displayable`: the conditional is verdict-voiced, the
detached injunction shortfall-voiced. `EthicsNegative` supplies
`no_ethics_bearing_at_pole`, `no_stance_over_false_testimony`, and
`ethicalCode_relative_to_faith_object`.

**Deliberation.** `ConsequentialistConvention` is a descriptive reading layer.
`DropCount` and `DropCountInFiber` count share-drop receptions across finite
actual runs without adding probability, utility, or a command register.
They are legal display readings: `map_dropCount` and `map_dropCountInFiber`
show that reparameterizing the contribution display does not change either
count. `dropCountInFiber_le_dropCount` gives the per-fiber bound, while
`dropCount_eq_sum_dropCountInFiber` says that a noduplicate complete supplied
tag list adds the fiber counts back to the total. The local sum itself
transports by `map_dropCountInFiberSum`, and
`ObjectiveNegative.split_dropCount_sum_eq_mergedDropCount` checks the
`[false, true]` split against the merged objective example.
`ObjectiveNegative` reuses the merge/split being-convention pattern to show
that "my drops" is not a function of grid data alone.

`rePitch_forgets` and
`accumulated_attainment_constant_of_same_final` restate backsliding in the form
a maximizer needs: no accumulated attainment variable is stored in `Config`.
`backsliding_witness` and `backsliding_rePitchSequence_witness` give the
same-grid same-being witness form directly.
`TransferNegative` records the adaptive track-record obstruction and the
`ResponseInvariant` contrast case. `grade_independent_of_conditions` and
`share_independent_of_conditions` keep the cetana claim at signature level:
grade and share do not consume downstream delivery conditions; the two concrete
cetana witnesses check same-field/different-share and live-share/no-standing
cases. `DeliveryArrogationNegative` instantiates the
`ClaimLanguage` machinery for a command-shaped delivery claim and checks that a
recorded plan fails `FitsOfferedTier` where delivery is absent.

**Gradeability.** `SeveredTranscript` is the strongest severed quotation form:
an attributed agent-response pair with no call, no offered tier, and no
actuality proof. `Grid.Weld.sever` and `Grid.RecordedUtterance.sever` forget
the call; `severedVerdict` pins the generator's standing response to such data
as `declined`. `GradeabilityNegative.no_grade_recovery_from_severed` proves
that, under a same-agent/same-response collision with different shares, no
function from severed transcripts can recover the grade for every actual weld.
`gradeability_severed_underdetermination_witness` reuses `backslideGrid` as
the concrete missing-call carrier, and `severed_transcript_ungradeable`
instantiates the generic theorem there. The positive half is
`recordedUtterance_grade_determined`, an `rfl` fact that a recorded utterance's
grade is the grade of the whole weld it carries. The normative input rule and
the koan-form genre claim remain prose.

**Ledger.** `MountsOnlyIn b M` says `b` mounts responses only at calls in
`M`. `modality_of_actual` and `landing_call_in_modality` are the
response-shape facts: an actual weld, and hence any landing, at a
modality-restricted receiver carries a call in the modality; both are
projection/rewrite proofs. `not_actual_outside_modality` and
`no_landing_outside_modality` are the contrapositives.
`fiber_landing_call_in_modality` lifts the fact to a coarsening fiber whose
fine tags all satisfy `MountsOnlyIn` for the same `M`.

`ReceptionCommand` and `receptionCommandLanguage` mirror the Deliberation
delivery-command language with `LandsAt` as the satisfaction condition;
`receptionCommand_unfit_of_no_landing` is the corresponding unfit theorem.

`ledger_census_misfits_live_offer` and `ledger_prognosis_misfits_live_offer`
are named faces of `denied_misfits_live_offer` at `.perCallGlobal` and
`.standingDated`; the module adds no `RowTag`.

`LedgerCase.ledgerGrid` is a three-being, three-call, three-response grid over
`Nat` with constant live grade `1`; `conditions` delivers exactly the welds
whose response is `code` or `comply`. The checked model facts:
`official_mountsOnlyIn_economic`, `official_not_stone`,
`official_landing_only_economic`, `floor_speech_never_lands_at_official`; the
three landings of `codeWeld` with `one_act_two_receivers` and
`code_ruler_not_exempt` (a self-line reception by the issuer);
`sectorCoarsening` with `state_tag_sentient`, `state_fiber_shares_register`,
and `state_fiber_landing_economic`; `decree_engineers_calls_not_receptions`
(delivery holds, the commanded reception is not actual, the recorded decree
fails `FitsOfferedTier`); and the purge block `purgedGrid :=
ledgerGrid.staticized master` with `purge_delivery_loss_real`,
`purge_adaptive_to_static`, `purge_loop_runs_on`,
`purge_object_axis_subtraction_nil`, and `corpus_still_delivered`, all reusing
the futility operation.

`FoxCase.foxGrid` is a natural-numbered life series: life 0 answers the
question, later lives receive the fruit, and the turning word releases at
share 1 rather than at the pole. The checked model facts are
`fox_sentence_live_selfPole`, `fox_arrow_index_free`,
`fox_returns_delivered`, `fox_reception_clenched`, `fox_release_rung_not_pole`,
`fox_reachBack_full_at_release`, `fox_nothing_kept`, and
`fox_never_tests_pole`. `foxSeriesCoarsening` merges the fine lives into the
display tag "the fox" while `fox_consecutive_lives_distinct` keeps the fine
series individuated. The Dogen gloss is typed by
`daishugyo_diagnosis_fits`, `jinshinInga_instruction_fits`,
`jinshinInga_floor_voicing_would_misfit`, and `dogen_doubling_both_fit`; these
check only the grid-internal speech-act gloss, not the historical contra.
`Doctrines/FoxCase.lean` adds `fox_dukkha_per_life`, because that theorem
consumes the Four Truths mismatch vocabulary.

**Correlations.** `StageScheme` is `BeingCoarsening`; `FiftyTwoStageScheme`
adds no signature field. `ShareDropRun` and `BullAscent` type Bulls 1-6 as
per-call drops. `WaaBullSeven` is probe-constancy plus a live self-pole index,
with `bullSeven_not_bullEight` checking that this half-weld is not the
pole-class. Bull 8 is `AtPoleClass`, Bull 9 is `ResponsiveTerminus`, and Bull
10 is `WaaBullTen`, an existential cross-fiber delivery into another sentient
fiber. `StrongWaaBullTen` names the stronger all-sentient-fibers asymptote
without using it. `bullTen_to_bullNine`, `bullNine_to_terminus`, and
`bullNine_to_bullEight` give the checked chain, while
`CorrelationsNegative.pratyekabuddha_countermodel` shows Bull 9 without Bull
10. `CorrelationsNegative.no_stage_boundary_recovery` is the stage-scheme
version of the no-recovered-partition witness.

`FiveRank`, `RankReading`, and `rankLanguage` keep the Five Ranks as
utterance-diagnosis data. `kenChuTo_implies_waaBullTen` records the 到/Bull 10
shape under the same coarsening.

**Sudden/gradual.** `WaaSuddenArrival` packages an actual one-step share-drop
from live prior tendency to the pole-class; `waaSuddenArrival_witness` names
the clock-grid face of the older `subitism_possibility_witness`. `rePitchRun`
folds a finite list of received welds, and `WaaGradualArrival` reads a staged
`ShareDropRun` that reaches the pole-class; `waaGradualArrival_witness` checks
the two-step register-clock case. `rate_invisible_to_config`,
`rePitchRun_forgets_same_final`, and
`score_of_rePitchRun_constant_of_same_final` are the no-rate-preference
statements: anything that factors through the final `Config` cannot see the
earlier rate once the final reception is fixed.
`SuddenGradualNegative.subitism_frequency_underdetermined` supplies the
honesty clause by varying delivery while response, grade, and share data agree.

**Other-power.** `SameAgentDelivery` and `CrossAgentDelivery` add neutral
delivery-regime vocabulary: the line is delivered, and the deed/reception agent
tags are equal or unequal. `WaaJirikiLine` and `WaaTarikiLine` are only the
system-POV readings of those facts. `reception_typing_ignores_sower` is
near-definitional by design: changing only `conditions` leaves a reception's
grade, share, and actuality unchanged. `waaReachBack_filled_either_regime`
projects the shared reach-back conjunct from either same-agent or cross-agent
delivery.

`TarikiCase` discharges non-vacuity the way `LedgerCase` does: a fixed-call
source is response-invariant (`name_responseInvariant`), function-mounted
(`name_not_stone`), and share-zero at its welds (`name_share_bot`); its object
axis reaches every invoker reception (`name_object_axis_entire`). The effective
limit is checked by `universal_fixed_call_lands_without_reading`, while
`invoker_reception_is_deed` keeps the receiver's act grammar ordinary and
live. `OtherPowerNegative.regime_does_not_determine_share` and
`OtherPowerNegative.share_does_not_determine_regime` witness the no-polemic
clause: neither regime nor share recovers the other.

**Fetters.** `FiberAtPoleOn`, `LiveFiberAtPoleOn`, `FiberAtPoleOnWithin`, and
`FiberAtPoleWithin` are neutral fiber predicates in
`Signature/BeingConvention.lean`. `FetterReading` supplies model-side
provocation classes, `SomaReading` supplies model-side tag-regions, and
`FetterCutWithin` means quietness at pole on the relevant call-class inside
the supplied tag-class. `Fetter.kind_lower_iff_cut_by_nonReturn` records the
enumeration coherence: exactly the lower fetters are cut by non-return.
`Path.cutClasses` gives the nested path profiles;
`PathQuietWithin`, `arhatPathQuietWithin_iff_fiberAtPoleWithin`, and
`arhatWithin_univTags_iff_fiberAtPole` close the two-axis lattice back to
ordinary `FiberAtPole` at total calls and total tags. That top point is the
total-rectangle cut, not the buddha reading by itself. The layered reading has
three checked rungs: rung 1 is share-only and stone-inclusive
(`FettersNegative.total_cut_carries_no_function`); rung 2 is the live terminus
reading, with `sentientTag_iff_actualFiberInhabited` bridging function to
actual fiber inhabitation; rung 3 is `WaaFullyEnlightened`, and
`FettersNegative.total_cut_with_function_not_waaFullyEnlightened` checks that
rung 2 still lacks effectiveness. The regime-relational face is two-sided:
zero-effect delivery can make full enlightenment fail, while
`waaFullyEnlightened_of_responsiveTerminus_of_undelivered` makes it hold
vacuously under sealed delivery. The checked anchors are
`classQuiet_no_clench_in_class`, `identityView_excluded_at_arhatFiber`,
`conceit_excluded_at_arhatFiber`, `all_fetters_cut_at_arhatFiber`,
`arhatFiber_of_termini`,
`identityView_excluded_at_speechThoughtRegion`, `conceit_excluded_within`,
`regionFiber_of_termini`, and `unquiet_region_still_functions_witness`.

The forward-looking face is conditional and diagnostic: `RunQuiet` and
`RunQuietWithin` are finite track-record quietness,
`waaIrreversibleRegime_conditional` and
`waaIrreversibleRegimeWithin_conditional` promote them only under supplied
regimes, and `FettersNegative.seen_run_underdetermines_fetterCut`,
`FettersNegative.seen_run_underdetermines_fetterCutWithin`, and
`FettersNegative.no_region_boundary_recovery` give the fresh-call and
tag-boundary underdetermination witnesses.

**Factors.** `PathFactor` names the factor-side regrouping of the canonical
fetter table. `PathFactor.blockerClass` derives rites, view, and resolve
blocker classes from `FetterReading`; speech and conduct are named but inert
with `False` classes. The coherence theorems
`ritesView_union_covers_streamEntry_fetters`,
`resolve_covers_nonReturn_fetters`, and
`lower_fetters_covered_by_rites_view_resolve` check that the active factor
classes cover exactly the intended stream-entry and lower-fetter unions.

`FactorHeld` is a seen-run existential over actual in-fiber welds with live
self-pole index in the factor class. `FactorReleased` is the corresponding
whole-class `FiberAtPoleOn` cut. `not_factorHeld_of_factorReleased` gives the
refutation direction; `factorReleased_rites_iff_ritesGrasp_cut`,
`factorReleased_view_iff`, and `factorReleased_resolve_iff` connect the factor
release predicates back to the fetter cuts.

The stage readings are `WaaStreamEnterer`, `WaaStreamWinner`,
`WaaOnceReturner`, and `WaaNonReturner`. The fruit positions are proved
equivalent to the old path cut classes by
`waaStreamWinner_iff_streamEntry_cutClasses` and
`waaNonReturner_iff_nonReturn_cut`, while
`waaNonReturner_of_arhatFiber` consumes the existing arhat fiber anchor.
`ShareDropRunOn`, `WaaResolveAttenuation`,
`waaOnceReturner_attenuation_witness`, and `attenuation_not_release` give
once-return positive content as a strict resolve-class drop that stops short
of pole release.

`RunsExhibitFactorOrder`, `WaaSerialFactorRegime`, and
`waaSerialFactorRegime_conditional` state the "usually runs in order" claim
only as a supplied-regime conditional. `waaSuddenArrival_consistent_with_factorScheme`
records compatibility between one-step pole arrival and the factor fruit
readings under the existing pole-fiber hypothesis.

**FactorsNegative.** `no_hold_conceit_boundary_recovery` shows that the
hold/conceit line is not recovered from shared response/grade/share data.
`seen_run_underdetermines_factorOrder` gives one seen run whose factor order
depends on the supplied reading. `lineage_underdetermined_by_seen_run`
specializes the stage-boundary freedom witness to switching between a
Theravada-shaped factor tag and a Bulls-shaped tag over the same grid and run.

---

## 4. Identification Layer (`Identification/*`)

**Field residues.** `CorrectFieldRecovery recover` says that every actual
weld's field residue recovers its index.
`correctFieldRecovery_forces_same_index_of_same_field` proves that two actual
welds with equal field residue must then have equal indices.
`no_agent_recovery_from_same_field_distinct_index` and
`no_agent_recovery_from_same_call_response` package the corresponding
impossibility results.

**Ownership-face definitions.** The ownership/report/vacuity/whose predicates
live under `Grid.DirectedConvention`. `WaaReportFace`,
`WaaOwnershipFace`, `WaaVacuousOwnershipFace`, and
`WaaDiachronicWhose` are conjunctions over delivery, actuality, and
WAA-appropriation. Their theorems are projections, introductions,
contradictions with non-delivery, or definitional biconditionals:

- `waaReportFace_of_waaOwnershipFace`
- `actual_of_waaOwnershipFace`
- `waaAppropriates_of_waaOwnershipFace`
- `waaOwnershipFace_intro`
- `not_waaOwnershipFace_of_vacuous`
- `not_waaOwnershipFace_of_waaVacuousOwnershipFace`
- `waaDiachronicWhose_iff_delivery_and_waaAppropriates`

The concrete memory display is
`Grid.DirectedConvention.MemoryWitness.memory_witness` over
`registerClockGrid`. It names the registers `pastDeed`, `recall`, and
`confabulatedDeed`; the delivered side is checked by `trace_delivered`,
`recall_waaOwnershipFace`, and `recall_waaDiachronicWhose`; the false-memory
side is checked by `confabulated_not_delivered` and
`falseMemory_waaVacuousOwnershipFace`. `vacuity_not_inner_mark` projects the
same recall-side WAA-appropriation from both faces while closing the
non-delivered contrast, and `recall_spent` is the `rePitch_forgets` instance
that makes the recall weld spent at recall-time.

**Token reflexivity.** `selfAnchored`: `index w = w.agent`. Definitional
(`rfl`).

**Pole-typing.** `StateToolFits w` means `¬ HasSelfPoleIndex w`.
`stateToolFits_of_atBot` and `stateToolFits_of_eq_shareBot` are the direct
pole-class and equality-bridge facts. Assuming
`[Decidable (AtBot (G.share w))]`, `atBot_of_stateToolFits` and
`stateToolFits_iff_atBot` give the exact iff with pole-class membership.
`stateToolFits_of_terminus_response` applies the result to terminus responses.

`Grid.DirectedConvention.not_waaOwnershipFace_of_stateToolFits`: if the
state-tool fits a reception, the WAA-ownership-face cannot fire there, because
ownership-face includes WAA-appropriation.

**Rule and office facts.** `obeysRule_fuses_at_floor` and
`obeysRule_separates_at_actTime` are direct uses of the separate/fuse theorems.
`assignedTier` assigns each `WaaOwnershipOffice` to the weld's act-time tier.
The two facts that this unfolds to `Tier.actTime w` and has exactly the weld's
`HasSelfPoleIndex` condition are `assignedTier_eq_actTime` and
`assignedTier_hasLiveShare_iff`. `retype_constructor_exists` checks the
generator's retype constructor. The placement and disclaimer checks are named
below.

**Register sorting.** `Register`, `SortedFact`, and `SortedFact.register` record
disclaimer 5's three-register sorting as inspectable data. The pins are
`causalSeries_register`, `delivery_register`, `seed_register`,
`arrogationTendency_register`, `agentIndex_register`, `forMeNess_register`,
`receptionReachBack_register`, and `rowTwoPlacement_register`.
`nothing_selfIndexed_carried` checks the refined premise that the self-indexed
facts are not carried in the stored field register.

**Instructive absences.** `InstructiveAbsence` records the current section 3
list as Lean data, with `InstructiveAbsence.number` pinning the paper order
1-10. `AbsenceStatus` states the membership rule explicitly: constructors track
the section 3 list, while `InstructiveAbsence.status` tracks whether the world
has retired an entry. The status pins are `emptyCells_standing`,
`declinedCase_standing`, `foxNeverTestsPole_standing`, `thirdArrival_retired`,
`whyCallsLand_standing`, `fourthTruthWithheld_standing`,
`noSafeStage_standing`, `prudentialPrivilege_standing`, and
`noMeasure_standing`.

The anchors are intentionally thin: `emptyCells_anchor`,
`foxNeverTestsPole_anchor`, `foxNeverTestsPole_recordedUtterance_not_atBot`,
`foxNeverTestsPole_recordedUtterance_not_atPoleClass`,
`foxNeverTestsPole_oldMan_misfit_anchor`,
`thirdArrival_function_mounted_no_share`, `thirdArrival_not_waaMismatchLive`,
`fourthTruthWithheld_conditional`, `fourthTruthWithheld_detached_voice`,
`noSafeStage_anchor`, `prudentialPrivilege_underivable_anchor`,
`icchantikaDeclined_agent_anchor`, `icchantikaDeclined_receiver_anchor`, and
`icchantikaDeclined_nonforeclosure_anchor`. The declined deaf-blind case,
why-calls-land, and no-measure absences are pin-level data only; no theorem is
manufactured for what the paper leaves ceded.

**Self-line witness.** `SelfLineWitness.selfLineGrid` is a minimal `Nat` grid
with one being, one call, one response, total response, grade `1`, and
`conditions _ _ := True`. The checked examples show:

- `selfLine_conditions_self`: `conditions w w` holds.
- `selfLine_landsAt_self`: `Grid.DirectedConvention.LandsAt selfLineGrid w w`
  holds.
- `selfLine_waaOwnershipFace_self`:
  `Grid.DirectedConvention.WaaOwnershipFace selfLineGrid w w` holds.

The scope is narrow and deliberate: the signature permits self-lines; it does
not say that any real regime contains them. Irreflexivity of delivery is a
regime fact to be supplied by a model, not a structural axiom.

The contemporary placement checks are `siderits_waaPlacement`,
`ganeri_waaPlacement`, `zahavi_waaPlacement`, and `sartre_waaPlacement`.

**Disclaimers.** `Disclaimer.number` now runs through 57. The recent entries are
`beingConvention` (35), `pilotGeneratedRows` (36), `beingTrichotomy` (37),
`hareHornRegister` (38), `modalRealismFreeze` (39), and
`aptnessConditionality` (40), `sraddhaConditional` (41), and
`faithBothConjuncts` (42). The table-generation entries append after those
existing pins: `generatedTableStructure` (43), `poleAffirmingSemantics` (44),
`proseRows` (45), and `errorFreeReading` (46). `misFeedFence` (47) records the
avyākata fence-and-gate pair. The correlation entries are `tenBullsTyped` (48),
`fiveRanksRetype` (49), `stageSchemeCoarsening` (50), and
`fetterCutTyping` (51). `twoAxisFetterLattice` (52) records the product
call/tag fetter lattice, `enlightenmentLadder` (53) records the neutral
total-rectangle cut and three-rung ladder, and
`ethicsBundledConditionalCode` (54) with `codeHonestyClauses` (55) records the
ethics-code tail. `verdictRecordData` (56) records the generator's
episode-grained verdict history as Lean data, including the retype entries in
`generatorRecord` (`Meta/VerdictLedger.lean`), and `compoundCellStacks` (57)
records the five compound-position decompositions over existing `TableRow`s,
with facets, roles, voices, legal elements, and core-cell counts in
`Consequences/Compounds.lean`.
`waaKarmaIdentification_number` pins `waaKarmaIdentification = 9`, and
`modalRealismFreeze_number` pins `modalRealismFreeze = 39`.
`aptnessConditionality_number` pins `aptnessConditionality = 40`;
`sraddhaConditional_number` and `faithBothConjuncts_number` pin the two new
Sraddha entries, while `generatedTableStructure_number`,
`poleAffirmingSemantics_number`, `proseRows_number`,
`errorFreeReading_number`, and
`misFeedFence_number` pin the table and mis-feed entries; the newer
correlation and disclaimer pins are `tenBullsTyped_number`, `fiveRanksRetype_number`,
`stageSchemeCoarsening_number`, `fetterCutTyping_number`,
`twoAxisFetterLattice_number`, `enlightenmentLadder_number`,
`ethicsBundledConditionalCode_number`, `codeHonestyClauses_number`,
`verdictRecordData_number`, and `compoundCellStacks_number`.

---

## 5. Meta/Nishitani.lean, Meta/ReflexivityWitness.lean, Meta/Invariance.lean, and Meta/InvarianceNegative.lean

**Śūnyatā wrappers.** `Meta/Nishitani.lean` defines `Sunyata d` as the absence
of any frozen level in `ladder d`. The new row instantiations
`intraWeldArrow_sunyata` and `doerDeed_sunyata` join the existing beings,
time, weld, and content-beings instantiations as direct consumers of the
ladder no-final-freeze theorems.

**Reflexivity witness.** `Meta/ReflexivityWitness.lean` defines
`ladderRungGrid`, a single legal `Grid Nat` whose `Being` carrier is read as
rung labels. `ladderRungGrid_beings_sunyata` instantiates `beings_sunyata`,
and `ladderRungGrid_no_level_final` reruns the beings ladder over that grid.
The file is a witness, not a new universal claim about beings.

**Admission criterion.** Any future predicate over `grade` owes a transport
lemma here, or it counts as operational residue. The file proves that the
current grade-facing predicates are invariant under display reparameterization.

`DisplayReparam Contrib Contrib'` consists of a function `toFun`, an order
preservation/reflection theorem `a ≼ b ↔ toFun a ≼ toFun b`, and a proof that
`toFun shareBot` is `AtBot` in the target carrier.

`DisplayReparam.atBot_iff` proves `AtBot (toFun a) ↔ AtBot a`.
`DisplayReparam.orderEq_iff` proves that order-equivalence is preserved and
reflected.
`DisplayReparam.directionVoid_reflect` is hypothesis-free, while
`directionVoid_of_surjective` needs target-carrier coverage;
`CoverageNegative.directionVoid_needs_coverage` shows why.
`DisplayReparam.id` is the identity reparameterization, with `id_toFun` as its
definitional projection lemma. `DisplayReparam.comp` composes
reparameterizations, with `comp_toFun` as its definitional projection lemma.

`Config.map` sends a tendency through `toFun`; `Config.map_tendency` is
definitional.

`Grid.map` leaves `Being`, `Call`, `Response`, `respondsTo`, and `conditions`
unchanged, and maps `grade` through `toFun`.

Definitional transport facts:

- `map_grade` and `map_share`
- `map_actual_iff`, `map_mountsAt_iff`, `map_mountsSomewhere_iff`,
  `map_respondsToEveryCall_iff`, `map_responseVariesWithCall_iff`, and
  `map_stone_iff`
- `Grid.DirectedConvention.map_deliveredTo_iff`,
  `Grid.DirectedConvention.map_landsAt_iff`, and
  `Grid.DirectedConvention.map_environsLine_iff`

Grade-facing transport facts:

- `map_terminus_iff`, `map_liveTerminus_iff`, `map_responsiveTerminus_iff`,
  and `map_atPoleClass_iff`
- `map_hasSelfPoleIndex_iff`
- `map_waaMismatchGrade` and `map_waaMismatchLive_iff`
- `map_probeConstant_iff`
- `map_waaBullSeven_iff` and `map_waaBullTen_iff`
- `map_stateToolFits_iff`
- `Tier.map` and `map_tier_hasLiveShare_iff`
- `map_rePitch`
- `map_isShareDrop_iff`
- `ActualWeld.map`, `ConsequentialistConvention.DeliberationSample.map`,
  `ConsequentialistConvention.map_dropCount`, and
  `ConsequentialistConvention.map_dropCountInFiber`
- `Grid.DirectedConvention.map_landsWithShareDrop_iff`
- `Grid.DirectedConvention.map_hasShareDropLanding_iff`
- `Grid.DirectedConvention.map_shareDropLine_iff`
- `Grid.DirectedConvention.map_shortfallClosedAt_iff`
- `Grid.DirectedConvention.map_waaAversionContext_iff`
- `Grid.DirectedConvention.map_waaFullyEnlightened_reflect` and
  `map_waaFullyEnlightened_of_surjective`; the latter's coverage hypothesis is
  witnessed by `CoverageNegative.waaFullyEnlightened_needs_coverage`
- `Grid.DirectedConvention.WaaPathClaim.map`,
  `map_waaPathClaim_holds_iff`, `map_waaFullyEnlightened_iff`,
  `map_faith_object_eq`, and `map_waaFaithPrinciple_reflect`; the
  coverage-carrying entries share that same witness
- `BeingCoarsening.displayMap` and its `map_*_iff` lemmas for
  `InFiber`, `SameFiber`, `FiberInhabited`, `ActualFiberInhabited`,
  `SentientTag`, `FiberAtPole`, `ActualFiberInhabitedOn`,
  `ActualFiberInhabitedWithin`, `FiberAtPoleOn`, `FiberAtPoleOnWithin`,
  `FiberAtPoleWithin`, `LiveFiberAtPole`, `LiveFiberAtPoleOn`,
  `LiveFiberAtPoleWithin`, `SelfAptTag`, `SelfAptTagWithin`,
  `LiveSelfAptTag`, `Patchy`, `SelfConditioningTag`, and
  `StrongSelfConditioningTag`
- `DirectionCoarsening.displayMapDir`, `mapDir_sameTick_iff`,
  `mapDir_resolutionBounded_iff`, and
  `resolutionBounded_of_reparam_collapses`
- The grid-convention row transports:
  `map_intraWeldArrowRow_obeys`, `map_doerDeedRow_obeys`,
  `map_contentIntraWeldArrowRow_obeys_of_variation`,
  `map_intraWeldArrowLadder_obeys`,
  `map_intraWeldArrowLadder_obeys_succ`,
  `map_intraWeldArrowLadder_no_level_final`,
  `map_doerDeedLadder_obeys`, `map_doerDeedLadder_obeys_succ`, and
  `map_doerDeedLadder_no_level_final`

Together these say that all current pole, probe, tier, configuration,
direction-coarsening, share-drop, and share-drop-line predicates are legal
display predicates: changing the carrier by a reparameterization changes
notation, not truth.

**Direction-smuggling detector.** The transpose operation now lives in the
signature layer, beside the vocabulary it transports. `Grid.transpose` reverses
only the argument order of `conditions`. `transpose_conditionsEither_iff`
proves that `ConditionsEither` survives the reversal.
`Grid.DirectedConvention.transpose_deliveredTo_iff` proves that directed
delivery reverses. `BeingCoarsening.transpose_selfConditioningTag` shows the
directed refinement reversing exactly at the delivery line while fiber
membership and actuality stay put. This gives future delivery-facing results a
quick test: if they claim direction, they owe model-supplied asymmetry or
irreflexivity.
The axis operations are pinned as orthogonal: `transpose_transpose` is the
involution, `map_transpose` commutes display reparameterization with
transposition, `staticized_transpose` commutes function removal with
transposition, and `map_staticized` commutes display reparameterization with
function removal. These are definitional equalities, so the detector is not
carrying extra operational content.
`DirectionCoarsening.transpose_subTickDelivery` is the delivery-axis companion:
tick equality survives transposition, while the delivery line reverses.

**Negative examples.** `Meta/InvarianceNegative.lean` holds these countermodels.
`InvarianceNegative.TwoBottom` is a two-element carrier
where every element is order-equivalent to every other element, with `chosen`
as the designated `shareBot`. `mergeToUnit` maps both elements to the single
unit value and is a `DisplayReparam`. `twoBottomGrid` has one being, one call,
one response, responds everywhere, and grades every response as `other`.

The named checks show:

- `twoBottomGrid_terminus`: `twoBottomGrid.Terminus ()` holds.
- `not_oldEqTerminus_twoBottomGrid`: the obsolete equality-token predicate
  fails before reparameterization.
- `oldEqTerminus_map_mergeToUnit`: the obsolete equality-token predicate holds
  after the merge.
- `oldEqTerminus_not_invariant`: the new `Terminus` transports across the
  merge, while the old equality-token predicate would not have transported.

This is the formal certificate that replacing equality with `AtBot` was a real
de-operationalisation, not a naming preference.

**`DirectionNegative`.** `forwardGrid` and `backwardGrid` are one-being,
two-call grids identical except that `conditions` is reversed.
`conditionsEither_agrees` shows they have the same symmetric closure at every
pair; `conditions_disagree` exhibits a pair where the directions differ;
`no_direction_recovery_from_conditionsEither` concludes that no function of the
symmetric closure is correct on both grids. This is the formal certificate that
direction is not carried by the correlational structure.
`not_strict_twoBottom` records the carrier-wide strictness failure on the
two-bottom negative carrier.

**`InteriorDirectionNegative`.** `RawWeld.transposeCR` swaps the call and
response faces when they share a carrier. `transposeCR_involutive`,
`unorderedCRContent_transpose_invariant`, and `transpose_swaps_readings` pin
the transposition behavior: unordered content is unchanged while the display
labels reverse. `no_interior_direction_recovery` uses the same collision shape
one grain down: unordered call/response content does not recover which face is
call. This is the formal certificate that the intra-weld arrow is display, not
a field-carried before/after.

**`DirectionCoarseningWitness`.** `registerClockUnitTick` gives the raw
register clock one universal tick. `registerClock_unitTick_not_resolutionBounded`
proves this cannot be coherent over the injective `Nat` display: registers `0`
and `1` share a tick but do not have order-equivalent shares.

The positive slow-clock limit is modeled on a lawful one-point display:
`fullyCoarseRegisterClockGrid` keeps the register-clock response and delivery
shape while grading every weld in `Unit`. `unit_directionVoid_via_mergeToUnit`
gets `DirectionVoid Unit` through the existing legal display collapse from the
all-equivalent `TwoBottom` carrier, and
`fullyCoarseRegisterClock_no_timeDirection` applies the one-tick
resolution-bound theorem to the fully coarse grid. The theorem
`registerClock_directionCoarsening_independence` is the soul-guard: macro
sentience and self-conditioning for the register clock do not consume either a
direction coarsening or a resolution-bound hypothesis.

**`ContentNegative`.** `allStoneGrid` is a no-response grid whose beings are
all stone-typed and whose act-time tiers have no live share. It proves
`contentBeingsRow_not_obeys_allStone` and
`contentGridLensRow_not_obeys_noLive`. The existing two-bottom carrier gives
`twoBottomGrid_directionVoid`, and
`contentBeforeAfterRow_not_obeys_twoBottom` shows the directed-time content row
also needs its strict-direction aptness hypothesis. The empty-domain witnesses
separate two vacuities: `emptyCallGrid_false_stone_and_respondsToEveryCall`
shows that an empty call axis collapses stone with call-entire response, while
`emptyBeingGrid_no_liveTier` and `contentBeingsRow_obeys_emptyBeing` show that
an empty being axis has no act-time counterexample and the beings row fuses
vacuously. `constantResponseGrid_no_variation` and
`contentIntraWeldArrowRow_not_obeys_constantResponse` are the intra-weld
content countermodel: if every call gets the same response, the response-
variation aptness hypothesis is load-bearing.

**`CoverageNegative`.** `embedIntoNat` sends the one-point carrier to `0` in
`Nat`, leaving all target strictness at and above `1` outside the image.
`directionVoid_needs_coverage` shows that carrier-wide direction-voidness does
not push forward when the target has strict comparisons outside the image.
`phantomGrid` gives the parallel faith-closure witness:
`waaFullyEnlightened_needs_coverage` shows that the mapped carrier introduces
live tendencies the source never quantified over, so full enlightenment does
not preserve without coverage.

**`MisFeedNegative` in `Identification/Residues.lean`.** `IndexSeekingForm` is the type of candidate
answer-functions for the index-seeking question-shape: one designation per
field residue (`Call × Response`), each purporting to name the residue's
self-pole index. `AnswersCorrectly` is the success condition for the form:
correctness at every actual weld. `FieldCollision` packages the hypothesis:
two actual welds with the same field residue and distinct agents.

`no_indexSeeking_success_of_collision` is the fence: under a collision, no
answer-function for the form succeeds. The quantifier ranges over every
candidate answer-function, so the non-derivability is a property of the
question-shape, not of one failing instance. It is the same internal route as
the wrinkle-1 recovery theorems (`CorrectFieldRecovery`,
`no_agent_recovery_from_same_call_response`), specialized to the
designation-universe the avyākata reading needs.

`collisionGrid` is the non-vacuity witness: a concrete grid in which two beings
actually produce the same call-response pair, so the fence's hypothesis is
exhibited rather than assumed, the same duty `clockGrid` discharges for the
function/share split.

`deliveryTwinAnswers` is the gate: in the same concrete model, the
delivery-typed twin question has a checked answer-function. The claim is
model-local by design: it shows the fence does not enclose delivery-questions,
and asserts nothing about their answerability in general, which the standing
no-verdicts deny.

Three layers are stated in order of decreasing formality: the question-shape is
fenced schematically over the modeled designation-universe; the collision
hypothesis is witnessed concretely; and the adequacy of that universe to the
avyākata's natural-language questions is a modeling claim, argued in prose and
owned as such. The third layer cannot be discharged in Lean, and the paper does
not pretend otherwise; it is an aptness claim of the same standing as the
content-row hypotheses beside `ContentNegative`.

**`BeingNegative`.** The signature-level `BeingCoarsening.id` and
`BeingCoarsening.total` already show that identity and universal merge
partitions are legal for any grid; `total_sameFiber` and
`id_not_sameFiber_of_ne` pin the disagreement for any distinct fine tags.
Downstream, `twoBeingGrid` has two fine tags with identical response, grade,
and symmetric delivery behavior. `κmerge` reads them as one macro tag; `κsplit`
keeps them split. `merge_same_fiber` and `split_not_same_fiber` show the
readings disagree at `false`/`true`, and `no_partition_recovery` proves no
function of the shared grid data recovers both. This is the formal certificate
that the being-boundary is a reading, not grid-carried structure.

**`WeldNegative`.** `twoWeldGrid` has two fine call-response pairings over the
same response, grade, and symmetric delivery data. `σmerge` reads them as one
macro act; `σsplit` splits them by weld-grain. `merge_same_pairing` and
`split_not_same_pairing` show the readings disagree, and
`no_weld_boundary_recovery` proves no function of the shared grid data
recovers both. This is the formal certificate that weld individuation is a
segmentation convention, not grid-carried structure.

**`DoerDeedNegative`.** The doer/deed witness reuses a small two-call grid
data shape and supplies two readings over it: `beingPriorReading` and
`mutualReading`. `priority_readings_disagree` pins the collision, and
`no_priority_recovery` proves no function of the visible grid data recovers a
unique priority relation. This is why `doerDeedRow` remains schema-only rather
than adding a priority primitive to `Grid`.

**Verdict ledger.** `Meta/VerdictLedger.lean` records the verdict-history
paragraph as `generatorRecord`. The four retypes are four entries; the
checked count is `generatorRecord_retype_count`, and
`generatorRecord_newCell_count` records that no new row is added. The six-kind
view is the projection `restraintKind`, checked by
`generatorRecord_restraintKind_seen_count` and
`restraintKind_exhaustive_on_record`. Lean anchors are pinned by examples that
name `DirectionNegative`, `InteriorDirectionNegative`, the transposition pair,
the fox theorem, and `MisFeedNegative.fence_and_gate`. The checkable half of the falsifier is
`misFeed_entries_carry_decomposition`; the rate-trend half remains prose.

**Glossary.** `Meta/Glossary.lean` is the canonical source for glossary data.
Each `GlossaryEntry` records a term, provenance kind, newcomer-facing gloss,
checked Lean anchors, and backward-only `seeAlso` references. Lean checks the
table length, term uniqueness, `seeAlso` resolution to earlier rows, and anchor
resolvability through `#verify_glossary_anchors`. The glosses' accuracy and
canonical caveats remain prose; the Disclaimers carry expert-facing departures.
`GlossaryGen.lean` renders the table to `Exposition/Glossary.md`.

---

## 6. Meta/Audit.lean

`Meta/Audit.lean` imports `Meta/Invariance.lean`,
`Meta/InvarianceNegative.lean`, `Meta/ReflexivityWitness.lean`,
`Meta/VerdictLedger.lean`,
`Doctrines/SraddhaNegative.lean`,
`Doctrines/FaithNegative.lean`, and `Doctrines/Deliberation.lean`, plus the
new correlations, fetters, and factors negative modules, then pins selected
`#print axioms` outputs with `#guard_msgs`.

The audited declarations are:

- `no_agent_recovery_of_field_collision`
- `DirectionNegative.no_direction_recovery_from_conditionsEither`
- `CoverageNegative.directionVoid_needs_coverage`
- `CoverageNegative.waaFullyEnlightened_needs_coverage`
- `Grid.stateToolFits_iff_atBot`
- `Grid.map_actual_iff`
- `Grid.map_isShareDrop_iff`
- `strict_asymm`, `strict_trans`, and `Grid.transpose_transpose`
- `Grid.map_transpose`, `Grid.staticized_transpose`, and `Grid.map_staticized`
- `Grid.DirectedConvention.DirectionCoarsening.mapDir_resolutionBounded_iff`
- `DirectionCoarseningWitness.registerClock_unitTick_not_resolutionBounded`
- `DirectionCoarseningWitness.unit_directionVoid_via_mergeToUnit`
- `DirectionCoarseningWitness.fullyCoarseRegisterClock_no_timeDirection`
- `DirectionCoarseningWitness.registerClock_directionCoarsening_independence`
- `Grid.DirectedConvention.map_landsWithShareDrop_iff`
- `Grid.DirectedConvention.BeingConvention.BeingCoarsening.map_selfConditioningTag_iff`
- `Grid.DirectedConvention.BeingConvention.BeingCoarsening.map_fiberAtPoleOn_iff`
- `Grid.DirectedConvention.BeingConvention.BeingCoarsening.total_sameFiber`
- `Grid.DirectedConvention.BeingConvention.BeingCoarsening.id_not_sameFiber_of_ne`
- `Grid.map_waaBullSeven_iff`
- `Grid.map_waaBullTen_iff`
- `Grid.bullSeven_not_bullEight`
- `Grid.bullTen_to_bullNine`
- `CorrelationsNegative.pratyekabuddha_countermodel`
- `CorrelationsNegative.no_stage_boundary_recovery`
- `Grid.classQuiet_no_clench_in_class`
- `Fetter.kind_lower_iff_cut_by_nonReturn`
- `Grid.arhatPathQuiet_iff_fiberAtPole`
- `Grid.all_fetters_cut_at_arhatFiber`
- `Grid.identityView_excluded_at_arhatFiber`
- `Grid.conceit_excluded_at_arhatFiber`
- `Grid.waaIrreversibleRegime_conditional`
- `Grid.lower_fetters_covered_by_rites_view_resolve`
- `Grid.waaStreamWinner_iff_streamEntry_cutClasses`
- `Grid.waaNonReturner_iff_nonReturn_cut`
- `Grid.waaSerialFactorRegime_conditional`
- `Grid.waaOnceReturner_attenuation_witness`
- `FactorsNegative.no_hold_conceit_boundary_recovery`
- `FactorsNegative.seen_run_underdetermines_factorOrder`
- `FactorsNegative.lineage_underdetermined_by_seen_run`
- `FettersNegative.seen_run_underdetermines_fetterCut`
- `Grid.DirectedConvention.waaPathOught_conditional`
- `Grid.DirectedConvention.waaFaithOught_conditional`
- `Grid.DirectedConvention.map_waaFaithPrinciple_reflect`
- `FaithNegative.waaFaithPrinciple_id_fails`
- `Grid.DirectedConvention.no_waa_path_at_pole`
- `Grid.DirectedConvention.map_waaAversionContext_iff`
- `MisFeedNegative.fence_and_gate`
- `misFeed_entries_carry_decomposition`
- `OrthogonalityNegative.waaFullyEnlightened_stronger_than_terminus`
- `Grid.stone_of_no_call`, `Grid.respondsToEveryCall_of_no_call`, and
  `Grid.allStone_of_no_being`
- `ContentNegative.emptyCallGrid_false_stone_and_respondsToEveryCall`,
  `ContentNegative.emptyBeingGrid_no_liveTier`, and
  `ContentNegative.contentBeingsRow_obeys_emptyBeing`
- The new intra-weld/doer-deed/reflexivity surface:
  `InteriorDirectionNegative.transposeCR_involutive`,
  `InteriorDirectionNegative.unorderedCRContent_transpose_invariant`,
  `InteriorDirectionNegative.transpose_swaps_readings`,
  `DoerDeedNegative.no_priority_recovery`,
  `ContentNegative.contentIntraWeldArrowRow_not_obeys_constantResponse`,
  `intraWeldArrowRow_*`, `doerDeedRow_*`,
  `contentIntraWeldArrowRow_obeys_of_variation`,
  `intraWeldArrowLadder_*`, `doerDeedLadder_*`,
  `Nishitani.intraWeldArrow_sunyata`, `Nishitani.doerDeed_sunyata`,
  the new `map_*` row/ladder theorems, and the two `ladderRungGrid_*`
  reflexivity witness theorems
- `Grid.ConsequentialistConvention.dropCountInFiber_le_dropCount`,
  `Grid.ConsequentialistConvention.dropCount_eq_sum_dropCountInFiber`, and
  `Grid.ConsequentialistConvention.map_dropCountInFiberSum`
- `ObjectiveNegative.split_dropCount_sum_eq_mergedDropCount`

The pinned result is: no audited theorem depends on `sorry` or
`Classical.choice`. All audited declarations are axiom-free except
`DirectionNegative.no_direction_recovery_from_conditionsEither`, which depends
on exactly `[propext, Quot.sound]`, and
`InteriorDirectionNegative.unorderedCRContent_transpose_invariant`, plus
`FettersNegative.seen_run_underdetermines_fetterCut`,
`Grid.waaOnceReturner_attenuation_witness`,
`FactorsNegative.seen_run_underdetermines_factorOrder`, and
`Grid.DirectedConvention.map_waaFaithPrinciple_reflect`, plus the three
census theorems `Grid.ConsequentialistConvention.dropCountInFiber_le_dropCount`,
`Grid.ConsequentialistConvention.dropCount_eq_sum_dropCountInFiber`, and
`Grid.ConsequentialistConvention.map_dropCountInFiberSum`, which depend on
`[propext]`.

The Lake build targets the library `WeldAndArrow` by default and also defines
the non-default `lean_exe` target `glossary_gen`; there is no `Main.lean`.

---

## 7. Logical Strength

The definitional identities include `share_eq_grade`, `selfAnchored`,
`rePitch_tendency_eq_share`, the delivery/aiming biconditionals,
`isShareDrop_iff_rePitch_tendency_drop`, the recorded-utterance identities,
`recordedUtterance_grade_determined`, the reception-pair tendency lemmas, and
the basic `map_*` identities in `Meta/Invariance.lean`.

The elementary consequences are projections, witness assemblies,
contradictions, and short order arguments. The important non-definitional order
arguments are the `AtBot` share-drop obstruction, `strict_irrefl`, and the
display-reparameterization transport lemmas. The `FoxCase` checks sit here too:
their proofs unfold concrete responses, project existing identities, or close
short `Nat` order goals with `decide`.

The conditional impossibility results are the agent-recovery theorems, the
direction negative witness, the intra-weld direction witness, the
being-boundary negative witness, the weld-boundary negative witness, the
sraddha orthogonality witness, the severed-transcript gradeability negative,
and the other-power regime/share negative. The concrete model and carrier
results include `clockGrid`, `registerClockGrid`, `backslideGrid`,
`gradingCollisionGrid`, `WeldNegative.twoWeldGrid`, `FoxCase.foxGrid`, and
`TarikiCase.tarikiGrid`, plus the `InteriorDirectionNegative` two-face raw
weld carrier: they witness, respectively, function/share splitting,
diagnosis-time macro coarsening, same-being backsliding plus
severed-transcript grade underdetermination, same-field/different-share
grading, weld-boundary underdetermination, the fox run-through with no
pole-arrival, fixed-call landing without a second act grammar, and intra-weld
orientation underdetermination. The self-line witness is a permission witness,
not an existence claim about any real regime.

One structural caution remains: `Terminus` is vacuously true of every `Stone`;
use `LiveTerminus` or `ResponsiveTerminus` when non-vacuous response-function
matters.
