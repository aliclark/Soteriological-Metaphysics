# A Plain-English Reading of the Lean Theorems

**Scope.** This document states, in plain English, exactly what each theorem in `Theory.lean`, `Theorems.lean`, and `Identification.lean` asserts as a formal proposition. It ignores comments and docstrings, and it ignores Lean definitions that are mere renamings or abbreviations except where a theorem's meaning depends on them. Interpretive glosses from the surrounding prose (e.g. what a theorem is "about" philosophically) are deliberately excluded: the readings below are of the Lean statements only.

**Conventions.** Where a theorem is proved by `rfl` or `Iff.rfl`, its two sides are *definitionally equal*: the statement is true by unfolding definitions, and the reading says so. Where a hypothesis appears in a theorem's signature but is never used in the statement or proof, this is noted, because the theorem then holds regardless of that hypothesis. "Weld" below always means a triple; "actual" always means the specific equation given in the preliminaries.

---

## 0. Preliminaries: the vocabulary the theorems are stated in

These are the definitions a reader needs in order to know what the theorem statements mean. They are given in neutral mathematical language.

**Naming convention.** The `waa_` prefix marks identifiers whose names assert part of the paper's karma-identification -- ownership, appropriation, whose-ness, or reach-back -- as opposed to neutral delivery/order structure.

**Order structure.** A `Preorder` on a type α is a binary relation ≼ that is reflexive and transitive; it is hand-rolled, not Mathlib's `Preorder`, to stay dependency-free. Totality and antisymmetry are deliberately not assumed. `Incomparable a b` is defined as: not (a ≼ b) and not (b ≼ a). A `PreorderBot` additionally designates one element, called `bot`, such that bot ≼ a for every a. `shareZero` is notation for this designated element. Note that because antisymmetry is not assumed, other elements may also sit below everything; "= shareZero" and "≠ shareZero" throughout mean literal equality/inequality with the *designated* element, not order-theoretic minimality or non-minimality.

**The signature.** Fix a type `Contrib` carrying a `PreorderBot`; a Grid `G` over `Contrib` consists of:

- three types: `Being`, `Call`, `Response`;
- a function `respondsTo : Being → Call → Option Response` (i.e. for each being and call, either no response or exactly one designated response);
- a function `driveOf : Being → Call → Response → DriveComposition`, where a `DriveComposition` is a pair of `Contrib` values named `callDriven` and `selfDriven` (no relation between the two components is assumed);
- a binary relation `conditions` on welds (see next).

A **weld** (`RawWeld` / `G.Weld`) is an ordered triple ⟨agent, call, response⟩ with agent : Being, call : Call, response : Response. Any triple is a weld; being a weld does not presuppose that the being actually gives that response.

**Basic projections and predicates on welds.**

- `Actual w` means: `respondsTo w.agent w.call = some w.response` — the response recorded in the triple is exactly the response the `respondsTo` function assigns to that being at that call.
- `index w` is defined as `w.agent` (a projection; nothing more).
- `share w` is defined as `(driveOf w.agent w.call w.response).selfDriven`.
- `HasSelfPoleIndex w` means: `share w ≠ shareZero`.
- `waa_Appropriates w` is defined to be `HasSelfPoleIndex w` (the same proposition under WAA's reconstruction name).
- `selfPoleIndex w h` (for h a proof of `HasSelfPoleIndex w`) is defined as `w.agent`; the proof argument is not used in the value.
- `fieldOf w` is the pair `(w.call, w.response)`.

**Function-side predicates on beings.**

- `MountsAt b c`: there exists r with `respondsTo b c = some r`.
- `MountsSomewhere b`: there exists c with `MountsAt b c`.
- `RespondsToEveryCall b`: for every c, `MountsAt b c`.
- `Stone b`: for every c, not `MountsAt b c` (the being responds to no call).
- `Terminus b`: for every c and r, if `respondsTo b c = some r` then `(driveOf b c r).selfDriven = shareZero`. Note this is a universally quantified conditional; it is vacuously true of any being that responds to nothing.
- `LiveTerminus b`: `MountsSomewhere b` and `Terminus b`.
- `ResponsiveTerminus b`: `RespondsToEveryCall b` and `Terminus b`.
- `AtZeroSharePole b`: `Stone b` or `Terminus b`.
- `ProbeConstant b cs` (cs a class of calls): for any two calls in cs at which b actually mounts responses, the `selfDriven` components of the two drive-compositions are equal.
- `ResponseInvariant b`: whenever b responds at two calls, the two responses are equal.
- `ResponseVariesWithCall b`: there exist two calls at which b responds with unequal responses.

**Configurations, re-pitch, share-drops.**

- A `Config` is a structure containing exactly one field: `tendency : Contrib`.
- `rePitch before received` (before : Config, received : Weld) is the Config whose tendency is `share received`. The argument `before` does not occur in the result: the output is a function of the received weld alone.
- `IsShareDrop before received` means: `share received ≼ before.tendency` **and** not (`before.tendency ≼ share received`) — i.e. the received weld's share sits strictly below the prior tendency in the preorder sense (below in one direction, not below in the other).

**Delivery-side definitions.** The delivery predicates below are direct names for `conditions`, except for the vacuous case, which is its negation:

- `waa_ReachBackFull deed reception` := `conditions deed reception`.
- `DeliveredTo deed reception` := `conditions deed reception`.
- `waa_AimedAt deed reception` := `conditions deed reception`.
- `waa_ReachBackVacuous deed reception` := **not** `conditions deed reception`.

And built on these:

- `LandsAt deed reception`: `DeliveredTo deed reception` and `Actual reception`.
- `ObjectAxisStanding deed`: there exists a reception with `DeliveredTo deed reception`.
- `LandsWithShareDrop before deed reception`: `LandsAt deed reception` and `IsShareDrop before reception`.
- `EffectiveFor before deed`: there exists a reception with `LandsWithShareDrop before deed reception`.
- `AtLeastAsEffective before deed₁ deed₂`: for every reception₂ with `LandsWithShareDrop before deed₂ reception₂`, there exists a reception₁ with `LandsWithShareDrop before deed₁ reception₁`. Note the conclusion does not mention reception₂, so this proposition is logically equivalent to the implication "`EffectiveFor before deed₂` implies `EffectiveFor before deed₁`"; it asserts no matching or correspondence between individual landings.

**Actual pairs.**

- An `ActualWeld` is a weld bundled with a proof that it is actual.
- A `ReceptionPair` is an ordered pair of `ActualWeld`s (`first`, `second`).
- `FirstConditionsSecond p` := `waa_ReachBackFull p.first.weld p.second.weld` (i.e. `conditions` between the two underlying welds).
- `rePitchSequence before p` is the pair of Configs (rePitch before p.first.weld, rePitch (rePitch before p.first.weld) p.second.weld). Given rePitch's definition, this equals the pair of Configs with tendencies (share p.first.weld, share p.second.weld).

**Tiers and distinctions.**

- A `Tier` is either `floor` or `actTime w` for a weld w.
- `Tier.hasNonzeroShare` is `False` at `floor`, and is the proposition `share w ≠ shareZero` at `actTime w`. (So at `actTime w` it is literally the proposition `HasSelfPoleIndex w`.)
- A `ClaimLanguage L` consists of a type `Claim` and a relation `Holds : Tier → Claim → Prop`. `TrueAt L t p` := `L.Holds t p`.
- A `Distinction d` is a claim language together with two claims, `sideA` and `sideB`. Write "the two sides are equivalent at t" for the biconditional `TrueAt t sideA ↔ TrueAt t sideB`.
- `Fused d t`: **if** t has no nonzero share, **then** the two sides are equivalent at t. (At `floor` the antecedent "not False" is always provable, so `Fused d floor` is equivalent to: the two sides are equivalent at the floor.)
- `Collapse d t`: t has nonzero share **and** the two sides are equivalent at t.
- `Freeze d`: the two sides are **not** equivalent at the floor.
- `Separated d t`: t has nonzero share **and** the two sides are **not** equivalent at t.
- `ObeysSeparateFuse d`: (for every tier with nonzero share, the two sides are not equivalent there) **and** (for every tier without nonzero share, the two sides are equivalent there).

Note that `Collapse`, `Freeze`, and `Separated` are semantic conditions on a distinction relative to the language's satisfaction relation; none of them mentions any utterance, speaker, or assertion.

**Recorded utterances.** A `RecordedUtterance` bundles a weld, a proof that it is actual, a tier `offeredAt`, and a claim `content`. `answersCall u` := `u.weld.call`. `FitsOfferedTier u` := `TrueAt u.offeredAt u.content`.

**Verdict machinery (enumerations).** `VerdictVoice` has two constructors, `assertable` and `displayable`. `ErrorGrade` has two constructors, `verdict` and `shortfall`; `ErrorGrade.voice` is the function mapping `verdict ↦ assertable` and `shortfall ↦ displayable`. `GeneratorOutcome` is an inductive type with four constructors: `collapse` (carrying a distinction, a tier, and a proof of Collapse), `freeze` (carrying a distinction and a proof of Freeze), `declined` (carrying nothing), and `retype` (carrying two distinctions).

**Identification-layer definitions.**

- `FieldFact` := the product type `Call × Response`. `FieldRecovery` := functions `FieldFact → Being`.
- `CorrectFieldRecovery recover`: for every **actual** weld w, `recover (fieldOf w) = index w`.
- `waa_ReportFace deed reception` := `DeliveredTo deed reception`.
- `waa_OwnershipFace deed reception` := `LandsAt deed reception` and `waa_Appropriates reception`.
- `waa_VacuousOwnershipFace deed reception` := `waa_ReachBackVacuous deed reception` and `Actual reception` and `waa_Appropriates reception`.
- `waa_DiachronicWhose deed reception` := `DeliveredTo deed reception` and `waa_Appropriates reception`.
- `SelfAnchored w` := the equation `index w = w.agent`.
- `StateToolFits w` := not `HasSelfPoleIndex w`, i.e. not (share w ≠ shareZero).
- `waa_OwnershipOffice` is a six-element enumeration (`waa_cetana`, `waa_reception`, `waa_practice`, `waa_remorse`, `waa_absolution`, `waa_dedication`). `dischargeTier office w` := `Tier.actTime w`, for every office (the office argument is unused).
- `ContemporaryPosition` is a four-element enumeration (siderits, ganeri, zahavi, sartre); `ContemporaryPlacement` is a four-element enumeration (seriesQuestions, nearestAlly, retype, occupant); `waa_placement` is the function siderits ↦ seriesQuestions, ganeri ↦ nearestAlly, zahavi ↦ retype, sartre ↦ occupant.
- `Disclaimer` is a thirty-four-element enumeration; `Disclaimer.number` maps its constructors to the numerals 1 through 34 in declaration order.

---

## 1. Theorems in `Theory.lean`

`no_self_pole_index_of_shareZero`: for any weld w, if share w = shareZero, then it is not the case that share w ≠ shareZero. (Direct: a proposition and its negation cannot both hold.)

`selfPoleIndex_eq_agent_of_hasSelfPoleIndex`: for any weld w with a proof h of HasSelfPoleIndex w, `selfPoleIndex w h = w.agent`. Definitional (`rfl`): `selfPoleIndex` is defined to return `w.agent` and ignores h.

`no_waa_appropriation_of_shareZero`: for any weld w, if share w = shareZero then not `waa_Appropriates w`. Since `waa_Appropriates` is by definition `HasSelfPoleIndex`, this is the previous fact restated.

(An anonymous `example`: share w = (driveOf w.agent w.call w.response).selfDriven — definitionally true, since that is share's definition.)

`shareZero_of_terminus_response`: if b is a Terminus and respondsTo b c = some r, then share ⟨b, c, r⟩ = shareZero. This is exactly the Terminus definition applied to (c, r), rephrased through the definition of share.

`no_self_pole_index_of_terminus_response`: under the same hypotheses, ⟨b, c, r⟩ does not satisfy HasSelfPoleIndex. Follows by combining the previous two facts.

`no_waa_appropriation_of_terminus_response`: under the same hypotheses, ⟨b, c, r⟩ does not satisfy `waa_Appropriates`. Same fact under `waa_Appropriates`' definitional identity with HasSelfPoleIndex.

`stone_is_terminus`: every Stone is a Terminus. This holds **vacuously**: a Stone responds to nothing, so the Terminus condition's hypothesis `respondsTo b c = some r` is never satisfiable, and the universally quantified conditional is true. The theorem therefore records that Terminus, as defined, is satisfied by all Stones; it does not assert any positive share-zero responding.

`not_stone_of_mountsSomewhere`: if b mounts some response at some call, b is not a Stone. Direct contradiction between the existential and the universal negation.

`liveTerminus_not_stone`: a LiveTerminus is not a Stone. Follows from its MountsSomewhere component and the previous theorem.

`responsiveTerminus_live_of_call`: if b is a ResponsiveTerminus and **some call c is supplied as a hypothesis**, then b is a LiveTerminus. The call c witnesses MountsSomewhere. Without a call in hand (e.g. if the Call type were empty), this theorem gives nothing; the call hypothesis is essential.

`no_self_pole_index_of_terminus_weld`: for any weld w, given a proof that w is Actual **(this hypothesis is unused)** and given share w = shareZero, w does not satisfy HasSelfPoleIndex. The conclusion follows from the share-zero hypothesis alone; actuality plays no role in the proof or the logical content.

`share_independent_of_config`: for every Config `_before`, and every pair of welds `_first` and `later`,

> share later = (driveOf later.agent later.call later.response).selfDriven.

Read strictly: the equation is *the definition of share* applied to `later`, so it holds definitionally (`rfl`), and the Config argument and the first weld argument are unused binders — the equation is the same proposition whatever they are. The theorem's formal content is thus: `share` of any weld equals the selfDriven component of that weld's own drive-composition, a fact independent of any Config. The further point that no function in the signature computes a later share *from* a Config is a true observation about the file's signature (no such function is declared anywhere), but it is exhibited by the shape of the definitions, not itself the proposition this theorem proves.

`waa_reachBack_full_or_vacuous`: for welds deed and reception, **given a decidability instance for the proposition `conditions deed reception`**, either waa_ReachBackFull deed reception or waa_ReachBackVacuous deed reception. This is "P or not-P" for that specific proposition, obtained from the supplied decision procedure; the file does not assert the disjunction in the absence of decidability.

`deliveredTo_iff_waa_reachBackFull`: DeliveredTo deed reception ↔ waa_ReachBackFull deed reception. Definitional (`Iff.rfl`): both are the same relation `conditions` under two names.

`objectAxisStanding_of_landsAt`: if LandsAt deed reception, then ObjectAxisStanding deed. The reception in hand witnesses the existential.

`effectiveFor_has_objectAxisStanding`: if EffectiveFor before deed, then ObjectAxisStanding deed. Extract the witnessing reception; its landing includes delivery.

`atLeastAsEffective_refl`: AtLeastAsEffective before deed deed, for every before and deed. Each share-drop landing witnesses itself.

`atLeastAsEffective_trans`: AtLeastAsEffective is transitive (for a fixed before): if a is at-least-as-effective as b and b as c, then a as c.

`not_collapse_of_obeysSeparateFuse`: if d obeys the separate/fuse rule, then for every tier t, not Collapse d t. Proof shape: Collapse at t supplies both nonzero share at t and equivalence of the sides at t; the rule's first clause says nonzero share at t implies non-equivalence — contradiction.

`not_freeze_of_obeysSeparateFuse`: if d obeys the separate/fuse rule, then not Freeze d. The rule's second clause at the floor (where "no nonzero share" is provable, since nonzero share at the floor is False) yields equivalence of the sides at the floor, contradicting Freeze.

(An anonymous `example`: a distinction whose sideA and sideB are the *same* claim cannot Freeze — the biconditional at the floor is then p ↔ p, which holds.)

**Concrete instance (`clockGrid`) and its theorems.** `clockGrid` is a Grid over Contrib = Nat (with the usual ≤ and bottom 0), whose Being type has two elements (`rigid`, `adaptive`), Call type two elements (`present`, `absent`), and Response type one element (`chime`); respondsTo sends rigid to `none` on every call, adaptive to `some chime` on `present` and `none` on `absent`; driveOf is constantly the pair (callDriven = 1, selfDriven = 0); `conditions` is constantly False.

- `rigid_is_stone`: in clockGrid, `rigid` is a Stone — it mounts no response at either call.
- `adaptive_is_terminus`: in clockGrid, `adaptive` is a Terminus — every response it actually mounts has selfDriven = 0 (immediate, since driveOf is constant with selfDriven = 0; the proof is `rfl` at each instance).
- `adaptive_not_stone`: in clockGrid, `adaptive` is not a Stone — it mounts `chime` at `present`.
- (An anonymous `example` conjoins the three: in this one concrete Grid, rigid is Stone, adaptive is Terminus, and adaptive is not Stone. This exhibits that Stone and Terminus are not coextensive in every Grid.)

`no_agent_recovery_of_field_collision`: **given** two beings a₁ ≠ a₂, a call c, and a response r such that both ⟨a₁, c, r⟩ and ⟨a₂, c, r⟩ are Actual, there is no function `recover : Call × Response → Being` satisfying: for every actual weld w, recover (fieldOf w) = index w. Proof: such a recover would have to output both a₁ and a₂ on the same input (c, r). Read strictly, this is a **conditional** non-existence result: it applies only to Grids that in fact contain two distinct beings actually giving the same response to the same call, and it rules out only recovery functions of the stated *correctness* specification (functions of that type trivially exist whenever Being is nonempty).

---

## 2. Theorems in `Theorems.lean`

**Preorder facts.**

`incomparable_symm`: if a and b are incomparable, so are b and a. (Swap the two conjuncts.)

`not_le_of_incomparable`: if a and b are incomparable, then not (a ≼ b). (First conjunct.)

`not_ge_of_incomparable`: if a and b are incomparable, then not (b ≼ a). (Second conjunct.)

**Function/share and the two poles.**

`share_eq_selfDriven`: share w = (driveOf w.agent w.call w.response).selfDriven. Definitional (`rfl`); this restates share's definition.

`mountsAt_of_actual`: if w is Actual, then w.agent mounts a response at w.call (witnessed by w.response).

`mountsSomewhere_of_actual`: if w is Actual, then w.agent mounts a response somewhere (witnessed by w.call).

`not_stone_of_actual`: if w is Actual, then w.agent is not a Stone.

`not_actual_of_stone`: if b is a Stone, then for any call c and response r, ⟨b, c, r⟩ is not Actual.

`not_mountsSomewhere_of_stone`: a Stone does not mount a response anywhere.

`not_stone_of_response`: if respondsTo b c = some r for some c, r, then b is not a Stone.

`atZeroSharePole_of_stone`: a Stone is AtZeroSharePole (left disjunct).

`atZeroSharePole_of_terminus`: a Terminus is AtZeroSharePole (right disjunct).

`atZeroSharePole_and_not_stone_of_liveTerminus`: a LiveTerminus is AtZeroSharePole and is not a Stone.

`not_stone_of_responsiveTerminus_of_call`: if b is a ResponsiveTerminus and a call c is supplied, then b is not a Stone. (Again the supplied call is what witnesses responding somewhere.)

**Re-pitch and share-drops.**

`rePitch_tendency_eq_share`: (rePitch before received).tendency = share received, for every before. Definitional (`rfl`); this is rePitch's definition, and simultaneously records that the result does not depend on `before`.

`isShareDrop_iff_rePitch_tendency_drop`: IsShareDrop before received ↔ [(rePitch before received).tendency ≼ before.tendency and not (before.tendency ≼ (rePitch before received).tendency)]. Definitional (`Iff.rfl`): substituting `share received` for the re-pitched tendency, the right side is literally the definition of IsShareDrop.

`rePitch_tendency_le_before_of_shareDrop`: if IsShareDrop before received, then (rePitch before received).tendency ≼ before.tendency. (First conjunct of IsShareDrop, rewritten through rePitch's definition.)

`not_before_le_rePitch_tendency_of_shareDrop`: under the same hypothesis, not (before.tendency ≼ (rePitch before received).tendency). (Second conjunct.)

`rePitch_tendency_eq_shareZero_of_terminus_response`: if b is a Terminus and respondsTo b c = some r, then (rePitch before ⟨b, c, r⟩).tendency = shareZero, for any before. (Combine rePitch's definition with `shareZero_of_terminus_response`.)

**Delivery, reach-back, effectiveness.** The first three below are definitional biconditionals (`Iff.rfl`), since waa_ReachBackFull, DeliveredTo, and waa_AimedAt are all defined as `conditions` and waa_ReachBackVacuous as its negation:

`waa_reachBackFull_iff_deliveredTo`: waa_ReachBackFull deed reception ↔ DeliveredTo deed reception.

`waa_reachBackVacuous_iff_not_deliveredTo`: waa_ReachBackVacuous deed reception ↔ not DeliveredTo deed reception.

`waa_aimedAt_iff_deliveredTo`: waa_AimedAt deed reception ↔ DeliveredTo deed reception.

`not_waa_reachBackVacuous_of_full`: if waa_ReachBackFull deed reception, then not waa_ReachBackVacuous deed reception. (P and not-P cannot both hold.)

`not_waa_reachBackFull_of_vacuous`: the converse-direction restatement: if waa_ReachBackVacuous, then not waa_ReachBackFull.

`deliveredTo_of_landsAt`: LandsAt implies its DeliveredTo conjunct.

`actual_of_landsAt`: LandsAt implies its Actual-reception conjunct.

`landsAt_of_landsWithShareDrop`: LandsWithShareDrop implies its LandsAt conjunct.

`isShareDrop_of_landsWithShareDrop`: LandsWithShareDrop implies its IsShareDrop conjunct.

`deliveredTo_of_landsWithShareDrop`: LandsWithShareDrop implies DeliveredTo (by composing the two projections above).

`actual_of_landsWithShareDrop`: LandsWithShareDrop implies the reception is Actual.

`exists_landsAt_of_effectiveFor`: if EffectiveFor before deed, then some reception satisfies LandsAt deed reception.

`exists_actual_reception_of_effectiveFor`: if EffectiveFor before deed, then some reception is Actual. (Note the conclusion, read literally, asserts only the existence of *an* actual weld — the one produced is the witnessing reception, but the stated proposition is just "∃ reception, Actual reception".)

`exists_shareDrop_reception_of_effectiveFor`: if EffectiveFor before deed, then some reception satisfies IsShareDrop before reception.

`effectiveFor_of_atLeastAsEffective`: if deed₁ is AtLeastAsEffective as deed₂ (relative to before) and deed₂ is EffectiveFor before, then deed₁ is EffectiveFor before. (This is exactly the implication that, as noted in the preliminaries, AtLeastAsEffective amounts to.)

**Reception pairs.**

`first_actual` / `second_actual`: the first (respectively second) member of a ReceptionPair is Actual. (These are the stored proofs, projected out.)

`firstConditionsSecond_iff_deliveredTo`: FirstConditionsSecond p ↔ DeliveredTo p.first.weld p.second.weld. Definitional (`Iff.rfl`).

`rePitchSequence_first_tendency`: the first component of rePitchSequence before p has tendency equal to share p.first.weld. Definitional (`rfl`).

`rePitchSequence_second_tendency`: the second component has tendency equal to share p.second.weld. Definitional (`rfl`). (Together these record that the sequence's outputs depend only on the two welds' shares, not on `before`.)

**Tiers, utterances, separate/fuse.**

`floor_has_no_nonzero_share`: the floor tier does not have nonzero share. (Nonzero share at the floor is defined as False.)

`actTime_hasNonzeroShare_iff_hasSelfPoleIndex`: nonzero share at tier actTime w ↔ HasSelfPoleIndex w. Definitional (`Iff.rfl`): both sides are the proposition share w ≠ shareZero.

`not_actTime_hasNonzeroShare_of_shareZero`: if share w = shareZero, tier actTime w has no nonzero share.

`not_collapse_floor`: no distinction Collapses at the floor. (Collapse requires nonzero share, and the floor has none.)

`hasNonzeroShare_of_collapse`: Collapse d t implies t has nonzero share. (First conjunct.)

`hasNonzeroShare_of_separated`: Separated d t implies t has nonzero share. (First conjunct.)

`not_collapse_of_separated`: if Separated d t, then not Collapse d t. (Separated asserts the sides are inequivalent at t; Collapse asserts they are equivalent at t; contradiction.)

`fused_of_obeysSeparateFuse`: if d obeys the rule, then d is Fused at **every** tier t. (Fused is a conditional whose antecedent is "no nonzero share at t"; the rule's second clause supplies exactly the needed consequent whenever the antecedent holds.)

`separated_of_obeysSeparateFuse`: if d obeys the rule and t has nonzero share, then Separated d t. (Pair the nonzero-share hypothesis with the rule's first clause.)

`not_freeze_of_fused_floor`: if d is Fused at the floor, then not Freeze d. (At the floor the Fused conditional's antecedent is provable, yielding the floor equivalence Freeze denies.)

`answersCall_eq_weld_call`: answersCall u = u.weld.call. Definitional (`rfl`).

`fitsOfferedTier_iff_trueAt`: FitsOfferedTier u ↔ TrueAt u.offeredAt u.content. Definitional (`Iff.rfl`).

Anonymous `example` checks confirm that `voice` maps `verdict` to `assertable` and `shortfall` to `displayable`; these are encoding checks, not named theorems.

---

## 3. Theorems in `Identification.lean`

**Field residues and index recovery.**

`correctFieldRecovery_forces_same_index_of_same_field`: if `recover` is a CorrectFieldRecovery, and w₁, w₂ are Actual welds with fieldOf w₁ = fieldOf w₂ (same call-and-response pair), then index w₁ = index w₂ (same agent). Proof: both indices equal recover applied to the shared field pair.

`no_agent_recovery_from_same_field_distinct_index`: if there exist two Actual welds with equal field residues but distinct indices, then no CorrectFieldRecovery exists. (Contrapositive packaging of the previous theorem.)

`no_agent_recovery_from_same_call_response`: the same statement specialized to the concrete witness shape: two distinct beings a₁ ≠ a₂ both Actually answering the same call c with the same response r rule out any CorrectFieldRecovery. As with `no_agent_recovery_of_field_collision` in Theory.lean, this is conditional on such a pair existing in the Grid at hand, and rules out only recovery functions meeting the stated correctness specification.

**Sower/reaper, reach-back, WAA-ownership-face.**

`waa_reportFace_of_waa_ownershipFace`: waa_OwnershipFace deed reception implies waa_ReportFace deed reception (i.e. DeliveredTo — the delivery conjunct inside LandsAt).

`actual_of_waa_ownershipFace`: waa_OwnershipFace implies the reception is Actual.

`waa_appropriation_of_waa_ownershipFace`: waa_OwnershipFace implies waa_Appropriates reception (i.e. share reception ≠ shareZero).

`waa_ownershipFace_intro`: LandsAt deed reception together with waa_Appropriates reception yields waa_OwnershipFace deed reception. (This is the definition's two conjuncts, assembled.)

`not_waa_ownershipFace_of_vacuous`: if waa_ReachBackVacuous deed reception (i.e. not `conditions`), then not waa_OwnershipFace deed reception. (waa_OwnershipFace contains DeliveredTo, which is `conditions`.)

`not_waa_ownershipFace_of_waa_vacuousOwnershipFace`: a waa_VacuousOwnershipFace is not a waa_OwnershipFace (its first conjunct is waa_ReachBackVacuous; apply the previous theorem). Note that the other two conjuncts of waa_VacuousOwnershipFace (Actual reception, waa_Appropriates reception) play no role in the conclusion.

`waa_diachronicWhose_iff_delivery_and_waa_appropriation`: waa_DiachronicWhose deed reception ↔ (DeliveredTo deed reception and waa_Appropriates reception). Definitional (`Iff.rfl`): the right side is the definition.

**Token-reflexivity.**

`selfAnchored`: every weld satisfies SelfAnchored, i.e. index w = w.agent. Definitional (`rfl`): `index` is defined as the agent projection, so the equation holds for every weld by unfolding. The theorem's formal content is exactly this projection identity and nothing stronger.

**Pole-typing and the verdict's tier.**

`stateToolFits_of_shareZero`: if share w = shareZero, then StateToolFits w (i.e. not (share w ≠ shareZero)).

`shareZero_of_stateToolFits`: **assuming decidable equality on Contrib**, if StateToolFits w, then share w = shareZero. This is the elimination of a double negation (not-not-equal to equal), and the decidability assumption is what licenses the case split; the theorem is not stated without it.

`stateToolFits_iff_shareZero`: **assuming decidable equality on Contrib**, StateToolFits w ↔ share w = shareZero. (The two directions above, paired.)

`stateToolFits_of_terminus_response`: if b is a Terminus and respondsTo b c = some r, then StateToolFits ⟨b, c, r⟩.

`no_waa_ownershipFace_of_stateToolFits`: if StateToolFits reception, then for any deed, not waa_OwnershipFace deed reception. (waa_OwnershipFace's second conjunct is waa_Appropriates, i.e. HasSelfPoleIndex, which StateToolFits negates.)

`misfeed_not_floor_claim`: no distinction Collapses at the floor. (This is `not_collapse_floor` under a new name; the word "mis-feed" occurs only in the name, not in the proposition.)

`obeysRule_fuses_at_floor`: if d obeys the separate/fuse rule, d is Fused at the floor. (Instance of `fused_of_obeysSeparateFuse` at t = floor.)

`obeysRule_separates_at_actTime`: if d obeys the rule and HasSelfPoleIndex w, then Separated d (actTime w). (Instance of `separated_of_obeysSeparateFuse`, using the definitional identity of nonzero-share-at-actTime with HasSelfPoleIndex.)

**Office-spine and contemporary placements.**

`dischargeTier_actTime`: for every office and weld, dischargeTier office w = Tier.actTime w. Definitional (`rfl`): dischargeTier is defined as the constant function to actTime w, ignoring the office.

`dischargeTier_hasNonzeroShare_iff`: nonzero share at dischargeTier office w ↔ HasSelfPoleIndex w. Definitional (`Iff.rfl`), by the previous identity plus the definition of nonzero share at actTime.

Anonymous `example` checks confirm the four `waa_placement` assignments as encoded; nothing is derived beyond the function's definition.

`retype_is_generatorOutcome`: for any two distinctions old and new, there exists a GeneratorOutcome equal to `retype old new`. The witness is the term `retype old new` itself; the formal content is only that the `retype` constructor exists and can be applied to any pair of distinctions.

**Disclaimers.**

Anonymous `example` checks confirm the disclaimer numbering as encoded, including `waa_karmaIdentification = 9` and `orthogonalityPrice = 34`; nothing is derived.

---

## 4. Summary of logical strength, for the reviewer

Three strata are present, and a faithful reading keeps them apart.

**Definitional identities** (proved by `rfl`/`Iff.rfl`): these include `share_eq_selfDriven`, `share_independent_of_config`, `selfAnchored`, `rePitch_tendency_eq_share`, the `_iff_` renaming lemmas among `waa_ReachBackFull`/`DeliveredTo`/`waa_AimedAt`, `isShareDrop_iff_rePitch_tendency_drop`, `waa_diachronicWhose_iff...`, `answersCall_eq_weld_call`, `fitsOfferedTier_iff_trueAt`, the `dischargeTier` lemmas, and the ReceptionPair tendency lemmas. Their assertoric content is that a definition unfolds to what it was defined as. Several of them additionally *exhibit* an independence fact by their shape — e.g. `share_independent_of_config` and `rePitch_tendency_eq_share` each carry an unused Config binder, making visible that the equated quantity does not depend on it — but the independence is a feature of the definitions displayed by the statement, not a nontrivial derivation. Anonymous `example` checks confirm the ErrorGrade voice assignments, placement assignments, and disclaimer numbering as encoded; they are not named theorems.

**Elementary logical consequences**: projections of conjunctions, witnesses for existentials, contradictions between a proposition and its negation, transitivity/reflexivity checks, and the separate/fuse diagnostics (`not_collapse_of_obeysSeparateFuse`, `not_freeze_of_obeysSeparateFuse`, `fused_of_obeysSeparateFuse`, `separated_of_obeysSeparateFuse`, `not_collapse_floor`, `not_freeze_of_fused_floor`, `not_collapse_of_separated`). These are short first-order deductions from the definitions; none requires classical logic. The two that otherwise would (`waa_reachBack_full_or_vacuous`, `shareZero_of_stateToolFits`) take explicit decidability hypotheses instead.

**Conditional impossibility and concrete-instance results**: the agent-recovery theorems (`correctFieldRecovery_forces_same_index_of_same_field`, `no_agent_recovery_from_same_field_distinct_index`, `no_agent_recovery_from_same_call_response`, `no_agent_recovery_of_field_collision`) prove that no correctness-satisfying recovery function exists **in any Grid containing** two actual welds with the same field residue and different agents; and the `clockGrid` theorems (`rigid_is_stone`, `adaptive_is_terminus`, `adaptive_not_stone`) establish facts about one finite, explicitly constructed Grid, showing in particular that `Terminus b ∧ ¬Stone b` is satisfiable (which the vacuous `stone_is_terminus` alone could not show).

Finally, two structural cautions any reviewer should have in view: (i) `Terminus` is vacuously true of every `Stone`, so any theorem with a bare `Terminus` hypothesis also applies to non-responders — the non-vacuous notions are `LiveTerminus` and `ResponsiveTerminus`; and (ii) `AtLeastAsEffective` is, despite its ∀/∃ surface form, logically equivalent to the bare implication between the two deeds' `EffectiveFor` propositions, because its conclusion does not depend on the quantified reception.
