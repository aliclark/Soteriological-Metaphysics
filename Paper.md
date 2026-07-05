# A Plain-English Reading of the Lean Theorems

**Scope.** This document states, in plain English, what the Lean declarations in
`Theory.lean`, `Theorems.lean`, `Identification.lean`, `Invariance.lean`, and
`Audit.lean`
assert. It reads the checked Lean surface: definitions, theorem statements, and
proof status where that matters. Interpretive prose remains secondary to the
formal statements.

The project is pinned to `leanprover/lean4:v4.31.0` in `lean-toolchain`.

**Conventions.** A theorem proved by `rfl` or `Iff.rfl` is true by unfolding
definitions. A theorem whose proof is a projection, contradiction, or witness
assembly is described as such. A "weld" is always the triple `RawWeld` /
`G.Weld`; "actual" always means the equation
`respondsTo w.agent w.call = some w.response`.

Identifiers beginning `Waa` mark names that assert the paper's identification content:
ownership, appropriation, whose-ness, reach-back, or sowing-side aiming. The
unprefixed vocabulary is neutral order/delivery vocabulary, including Row-2
index-placement names such as `HasSelfPoleIndex`, `selfPoleIndex`, and
`Tier.hasLiveShare`.

`Grid.DirectedConvention` is the second marking. It contains vocabulary that
reads direction into the direction-free relation `conditions`: delivery,
landing, environs lines, share-drop lines, aiming, and the ownership-face
predicates. The signature itself still carries no asymmetry, irreflexivity, or
transitivity for `conditions`. Role-asymmetry is not temporal asymmetry: the
`deed` and `reception` slots are different roles, but the reception slot means
"where the welding happens", not "the later one".

`Grid.DirectedConvention.TimeDirection` is an abbreviation of `Strict`; all
strictness theorems apply to it transparently. The formal modules
`Theory.lean`, `Theorems.lean`, and `Invariance.lean` keep their comments
mathematical and point to `Identification.lean` Commentary C.1-C.3 for the
paper-facing readings.

The namespace tree now records ontological ordering. Floor/genjō and the bare
signature sit outside the convention layers. `Grid.DirectedConvention` reads
the arrow; `Grid.DirectedConvention.BeingConvention` reads fine tags as
macro-scale beings; `Grid.DirectedConvention.BeingConvention.GridConvention`
contains the concrete convention-layer claim language used by the pilot
taxonomy rows. Names are placed by what their reading presupposes, not by what
their definition consumes.

---

## 0. Preliminaries

**Order structure.** `Preorder` is a hand-rolled reflexive and transitive
relation `≼`; no totality and no antisymmetry are assumed. `Incomparable a b`
means neither `a ≼ b` nor `b ≼ a`. `OrderEq a b` means `a ≼ b` and `b ≼ a`.
`Strict a b` means `a ≼ b` and not `b ≼ a`.

The preorder facts are:

- `incomparable_symm`, `not_le_of_incomparable`, and `not_ge_of_incomparable`.
- `strict_irrefl`: strict direction is never reflexive.
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
- `FiberAtPole b`, `SelfAptTag b`, and `Patchy b` are fiber-level readings.
  `LiveFiberAtPole` and `LiveSelfAptTag` add actual-fiber inhabitation.
- `fiberAtPole_of_fiber_termini`, `no_live_index_under_fiberAtPole`,
  `selfAptTag_indices_are_per_weld_only`, and the live exclusivity theorems are
  the checked fiber facts.
- `SelfConditioningTag b` is the minimal internal delivery-line witness.
  `StrongSelfConditioningTag b` is defined as a shelved asymptote.
- `Delegation b` packages an actual fine weld in the macro fiber; its share is
  definitionally the delegate weld's share.

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
- `WaaReportFace`, `WaaOwnershipFace`, `WaaVacuousOwnershipFace`, and
  `WaaDiachronicWhose`.

All of these are definitions over `conditions`, `Actual`, `IsShareDrop`, and
`WaaAppropriates`; none adds a new axiom to `conditions`.

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

## 1. Theory.lean

`no_self_pole_index_of_atBot`: if `AtBot (share w)`, then `w` has no live
self-pole index. This is direct contradiction with
`HasSelfPoleIndex w := ¬ AtBot (share w)`.

`no_self_pole_index_of_eq_shareBot`: equality `share w = shareBot` is first
converted to `AtBot (share w)`, then the previous theorem applies.

`selfPoleIndex_eq_agent_of_hasSelfPoleIndex`: the evidence-carried index is
`w.agent`. Definitional (`rfl`).

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

---

## 2. Theorems.lean

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

**Pilot convention-layer rows.** Under
`Grid.DirectedConvention.BeingConvention.GridConvention`, `ConventionLayer` has
`directedTime`, `beings`, and `gridLens`. `LayerClaim` has
`conventionLive l` and `layerDenied l`. `layerLanguage G` interprets all layer
claims as true at `floor`, the live convention as `HasSelfPoleIndex w` at
`actTime w`, and denials as false at act-time.

`beforeAfterRow G` and `beingsRow G` instantiate `Distinction G` from this
language. `beforeAfterRow_obeys` and `beingsRow_obeys` prove
`ObeysSeparateFuse` by cases on the tier. `layerDenied_holds_only_where_no_live_share`
is the branch-sawing lemma: if a denial holds, the tier has no live share.
`no_time_collapse_self_refuting` and `no_beings_collapse_self_refuting` rule
out collapse for the two rows, and `beforeAfterRow_not_freeze` /
`beingsRow_not_freeze` rule out freeze for the checked rows.

---

## 3. Identification.lean

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

The contemporary placement checks are `siderits_waaPlacement`,
`ganeri_waaPlacement`, `zahavi_waaPlacement`, and `sartre_waaPlacement`.

**Disclaimers.** `Disclaimer.number` now runs through 39. The new entries are
`beingConvention` (35), `pilotGeneratedRows` (36), `beingTrichotomy` (37),
`hareHornRegister` (38), and `modalRealismFreeze` (39).
`waaKarmaIdentification_number` pins `waaKarmaIdentification = 9`, and
`modalRealismFreeze_number` pins `modalRealismFreeze = 39`.

---

## 4. Invariance.lean

**Admission criterion.** Any future predicate over `grade` owes a transport
lemma here, or it counts as operational residue. The file proves that the
current grade-facing predicates are invariant under display reparameterization.

`DisplayReparam Contrib Contrib'` consists of a function `toFun`, an order
preservation/reflection theorem `a ≼ b ↔ toFun a ≼ toFun b`, and a proof that
`toFun shareBot` is `AtBot` in the target carrier.

`DisplayReparam.atBot_iff` proves `AtBot (toFun a) ↔ AtBot a`.
`DisplayReparam.orderEq_iff` proves that order-equivalence is preserved and
reflected.
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
  `map_respondsToEveryCall_iff`, and `map_stone_iff`
- `Grid.DirectedConvention.map_deliveredTo_iff`,
  `Grid.DirectedConvention.map_landsAt_iff`, and
  `Grid.DirectedConvention.map_environsLine_iff`

Grade-facing transport facts:

- `map_terminus_iff`, `map_liveTerminus_iff`, `map_responsiveTerminus_iff`,
  and `map_atPoleClass_iff`
- `map_hasSelfPoleIndex_iff`
- `map_probeConstant_iff`
- `map_stateToolFits_iff`
- `Tier.map` and `map_tier_hasLiveShare_iff`
- `map_rePitch`
- `map_isShareDrop_iff`
- `Grid.DirectedConvention.map_landsWithShareDrop_iff`
- `Grid.DirectedConvention.map_shareDropLine_iff`
- `BeingCoarsening.displayMap` and its `map_*_iff` lemmas for
  `InFiber`, `SameFiber`, `FiberInhabited`, `ActualFiberInhabited`,
  `SentientTag`, `FiberAtPole`, `LiveFiberAtPole`, `SelfAptTag`,
  `LiveSelfAptTag`, `Patchy`, `SelfConditioningTag`, and
  `StrongSelfConditioningTag`

Together these say that all current pole, probe, tier, configuration,
share-drop, and share-drop-line predicates are legal display predicates:
changing the carrier by a reparameterization changes notation, not truth.

**Direction-smuggling detector.** `Grid.transpose` reverses only the argument
order of `conditions`. `transpose_conditionsEither_iff` proves that
`ConditionsEither` survives the reversal.
`Grid.DirectedConvention.transpose_deliveredTo_iff` proves that directed
delivery reverses. `BeingCoarsening.transpose_selfConditioningTag` shows the
new directed refinement reversing exactly at the delivery line while fiber
membership and actuality stay put. This gives future delivery-facing results a
quick test: if they claim direction, they owe model-supplied asymmetry or
irreflexivity.

**Negative example.** `InvarianceNegative.TwoBottom` is a two-element carrier
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

**`BeingNegative`.** `twoBeingGrid` has two fine tags with identical response,
grade, and symmetric delivery behavior. `κmerge` reads them as one macro tag;
`κsplit` keeps them split. `merge_same_fiber` and `split_not_same_fiber` show
the readings disagree at `false`/`true`, and `no_partition_recovery` proves no
function of the shared grid data recovers both. This is the formal certificate
that the being-boundary is a reading, not grid-carried structure.

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

---

## 5. Audit.lean

`Audit.lean` imports `Invariance.lean` and pins selected `#print axioms`
outputs with `#guard_msgs`.

The audited declarations are:

- `no_agent_recovery_of_field_collision`
- `DirectionNegative.no_direction_recovery_from_conditionsEither`
- `Grid.stateToolFits_iff_atBot`
- `Grid.map_actual_iff`
- `Grid.map_isShareDrop_iff`
- `Grid.DirectedConvention.map_landsWithShareDrop_iff`
- `Grid.DirectedConvention.BeingConvention.BeingCoarsening.map_selfConditioningTag_iff`

The pinned result is: no audited theorem depends on `sorry` or
`Classical.choice`. All audited declarations are axiom-free except
`DirectionNegative.no_direction_recovery_from_conditionsEither`, which depends
on exactly `[propext, Quot.sound]`.

The Lake build now targets the library `WeldAndArrow`; there is no `lean_exe`
target and no `Main.lean`.

---

## 6. Logical Strength

The definitional identities include `share_eq_grade`, `selfAnchored`,
`rePitch_tendency_eq_share`, the delivery/aiming biconditionals,
`isShareDrop_iff_rePitch_tendency_drop`, the recorded-utterance identities,
the reception-pair tendency lemmas, and the basic `map_*` identities in
`Invariance.lean`.

The elementary consequences are projections, witness assemblies,
contradictions, and short order arguments. The important non-definitional order
arguments are the `AtBot` share-drop obstruction, `strict_irrefl`, and the
display-reparameterization transport lemmas.

The conditional impossibility results are the agent-recovery theorems, the
direction negative witness, and the being-boundary negative witness. The
concrete model results are `clockGrid` and `registerClockGrid`: the first
exhibits a `Stone` and a non-stone `Terminus` in one finite grid; the second
exhibits a diagnosis-time macro coarsening over internal registers. The
self-line witness is a permission witness, not an existence claim about any
real regime.

One structural caution remains: `Terminus` is vacuously true of every `Stone`;
use `LiveTerminus` or `ResponsiveTerminus` when non-vacuous response-function
matters.
