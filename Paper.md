# A Plain-English Reading of the Lean Theorems

**Scope.** This document states, in plain English, what the Lean declarations in `Theory.lean`, `Theorems.lean`, `Identification.lean`, and `Invariance.lean` assert. It reads the checked Lean surface: definitions, theorem statements, and proof status where that matters. Interpretive prose remains secondary to the formal statements.

**Conventions.** A theorem proved by `rfl` or `Iff.rfl` is true by unfolding definitions. A theorem whose proof is a projection, contradiction, or witness assembly is described as such. A "weld" is always the triple `RawWeld` / `G.Weld`; "actual" always means the equation `respondsTo w.agent w.call = some w.response`.

---

## 0. Preliminaries

**Order structure.** `Preorder` is a hand-rolled reflexive and transitive relation `≼`; no totality and no antisymmetry are assumed. `Incomparable a b` means neither `a ≼ b` nor `b ≼ a`. `OrderEq a b` means `a ≼ b` and `b ≼ a`.

`PreorderBot` adds a designated bottom element, written `shareZero`, with `shareZero ≼ a` for every `a`. `AtBot a` means `a ≼ shareZero`. Since `shareZero ≼ a` is always available, `AtBot a` says that `a` is order-equivalent to the designated bottom. The pole is therefore an order-class, not identity with one token.

The basic order lemmas are:

- `orderEq_refl`, `orderEq_symm`, `orderEq_trans`: order-equivalence is reflexive, symmetric, and transitive.
- `shareZero_le`: the designated bottom is below every value.
- `atBot_shareZero`: `shareZero` is at the pole-class.
- `atBot_of_eq_shareZero`: equality with the designated representative implies `AtBot`.
- `orderEq_shareZero_of_atBot`, `atBot_of_orderEq_shareZero`, `orderEq_shareZero_iff_atBot`: `AtBot a` and `OrderEq a shareZero` are equivalent formulations.

**The signature.** A `Grid Contrib` consists of three types (`Being`, `Call`, `Response`), a response function `respondsTo : Being → Call → Option Response`, a Row-2 display function `grade : Being → Call → Response → Contrib`, and a delivery relation `conditions` on welds. There is no separate two-component drive object in the signature.

A weld is the triple `⟨agent, call, response⟩`. `Actual w` means `respondsTo w.agent w.call = some w.response`. `index w` is the projection `w.agent`. `share w` is `grade w.agent w.call w.response`.

`HasSelfPoleIndex w` means `¬ AtBot (share w)`. `waa_Appropriates w` is definitionally the same proposition. `selfPoleIndex w h` returns `w.agent` and ignores the proof argument except for typing.

**Function-side predicates.**

- `MountsAt b c`: there exists `r` with `respondsTo b c = some r`.
- `MountsSomewhere b`: there is some call at which `b` mounts.
- `RespondsToEveryCall b`: every call receives some response.
- `Stone b`: no call receives a response from `b`.
- `Terminus b`: every mounted response by `b` has `AtBot (grade b c r)`.
- `LiveTerminus b`: `MountsSomewhere b ∧ Terminus b`.
- `ResponsiveTerminus b`: `RespondsToEveryCall b ∧ Terminus b`.
- `AtZeroSharePole b`: `Stone b ∨ Terminus b`.
- `ProbeConstant b cs`: any two actual responses by `b` at calls in `cs` have order-equivalent grades.
- `ResponseInvariant b`: whenever `b` responds at two calls, the responses are equal.
- `ResponseVariesWithCall b`: there are two calls at which `b` responds differently.

**Configurations and share-drops.** `Config` has one field, `tendency : Contrib`; it stores no `Being`, no `Weld`, and no owner. `rePitch before received` returns the config with tendency `share received`; `before` is unused in the value. `IsShareDrop before received` means `share received ≼ before.tendency` and not `before.tendency ≼ share received`.

**Delivery-side definitions.** `waa_ReachBackFull`, `DeliveredTo`, and `waa_AimedAt` are all `conditions` under different names. `NotDeliveredTo` is its negation. `LandsAt deed reception` means delivery plus actual reception. `LandsWithShareDrop` adds `IsShareDrop`. `EffectiveFor before deed` existentially packages a share-dropping landing.

`EnvironsLine b deed reception` means the deed is actual, the candidate reception has agent `b`, and `conditions deed reception` holds. `ReleaseLine before b deed reception` adds `IsShareDrop before reception`.

**Tiers and distinctions.** A `Tier` is `floor` or `actTime w`. `Tier.hasNonzeroShare` is `False` at `floor` and `HasSelfPoleIndex w` at `actTime w`. Distinctions, claim languages, recorded utterances, error grades, and generator outcomes retain their previous shape: they define the separate/fuse diagnostic vocabulary over tiers.

**Identification layer.** `StateToolFits w` means `¬ HasSelfPoleIndex w`; with the new definitions this is double-negated pole-class membership. The exact iff with `AtBot` therefore requires decidability of the one proposition `AtBot a`, not decidable equality on all of `Contrib`.

---

## 1. `Theory.lean`

`no_self_pole_index_of_atBot`: if `AtBot (share w)`, then `w` has no live self-pole index. This is direct contradiction with `HasSelfPoleIndex w := ¬ AtBot (share w)`.

`no_self_pole_index_of_eq_shareZero`: equality `share w = shareZero` is first converted to `AtBot (share w)`, then the previous theorem applies.

`selfPoleIndex_eq_agent_of_hasSelfPoleIndex`: the evidence-carried index is `w.agent`. Definitional (`rfl`).

`no_waa_appropriation_of_atBot` and `no_waa_appropriation_of_eq_shareZero`: the same no-index facts under the definitional name `waa_Appropriates`.

Anonymous example: `share w = grade w.agent w.call w.response`. Definitional (`rfl`).

`atBot_of_terminus_response`: if `b` is a `Terminus` and `respondsTo b c = some r`, then the weld `⟨b, c, r⟩` has `AtBot` share. This is exactly the `Terminus` definition applied to `c` and `r`.

`no_self_pole_index_of_terminus_response` and `no_waa_appropriation_of_terminus_response`: a terminus response has no live self-pole index and does not WAA-appropriate, by combining the previous theorem with the `AtBot` no-index lemmas.

`stone_is_terminus`: every `Stone` is a `Terminus`. This is vacuous: the response hypothesis in `Terminus` can never be satisfied for a stone.

`not_stone_of_mountsSomewhere`: mounting somewhere contradicts `Stone`.

`liveTerminus_not_stone`: a live terminus is not a stone, because its `MountsSomewhere` component witnesses function.

`responsiveTerminus_live_of_call`: a responsive terminus is a live terminus once a call `c` is supplied; that call witnesses `MountsSomewhere`. If the call type is empty, the theorem has no call to apply.

`deliveredTo_or_not`: for a particular pair of welds, if `conditions deed reception` is decidable, then either `DeliveredTo deed reception` or `NotDeliveredTo deed reception`.

`deliveredTo_iff_waa_reachBackFull`: definitional (`Iff.rfl`), since both names are `conditions`.

`objectAxisStanding_of_landsAt`: a landing gives object-axis standing, witnessed by the reception in hand.

`effectiveFor_has_objectAxisStanding`: effectiveness gives a share-dropping landing; its landing component supplies object-axis standing.

`not_collapse_of_obeysSeparateFuse`: the first clause of `ObeysSeparateFuse` contradicts the equivalence required by `Collapse` at any live tier.

`not_freeze_of_obeysSeparateFuse`: the second clause of `ObeysSeparateFuse` at `floor` gives the equivalence denied by `Freeze`.

Anonymous example: a distinction whose two sides are the same claim cannot freeze.

`no_agent_recovery_of_field_collision`: if two distinct beings can actually produce the same call-response pair, no function from field residue `Call × Response` can correctly recover the agent for every actual weld.

**`clockGrid`.** The concrete grid uses `Nat` with bottom `0`; `rigid` responds nowhere, `adaptive` responds with `chime` when the listener is present, `grade` is constantly `0`, and `conditions` is always false. The former "call-driven = 1" component is no longer formal data.

- `rigid_is_stone`: `rigid` responds nowhere.
- `adaptive_is_terminus`: `adaptive` is a terminus. The proof is now `Nat.le_refl 0`, because `Terminus` asks for `AtBot 0`, not equality by `rfl`.
- `adaptive_not_stone`: `adaptive` responds at `present`.
- Anonymous example: the concrete grid contains a stone and a non-stone terminus.

---

## 2. `Theorems.lean`

**Preorder facts.** `incomparable_symm` swaps the two conjuncts of incomparability. `not_le_of_incomparable` and `not_ge_of_incomparable` project the corresponding negated comparisons.

**Function/share and poles.**

`share_eq_grade`: `share w = grade w.agent w.call w.response`. Definitional (`rfl`).

`mountsAt_of_actual`, `mountsSomewhere_of_actual`, `not_stone_of_actual`, `not_actual_of_stone`, `not_mountsSomewhere_of_stone`, and `not_stone_of_response` are direct witness/projection/contradiction consequences of `Actual`, `MountsAt`, and `Stone`.

`atZeroSharePole_of_stone` and `atZeroSharePole_of_terminus` introduce the two disjuncts of `AtZeroSharePole`. `atZeroSharePole_and_not_stone_of_liveTerminus` combines the terminus disjunct with `liveTerminus_not_stone`. `not_stone_of_responsiveTerminus_of_call` uses the supplied call to get live function.

**Re-pitch and share-drops.**

`rePitch_tendency_eq_share`: the re-pitched tendency is the received weld's share. Definitional (`rfl`); `before` is unused.

`isShareDrop_iff_rePitch_tendency_drop`: definitional (`Iff.rfl`), substituting the re-pitched tendency for `share received`.

`rePitch_tendency_le_before_of_shareDrop` and `not_before_le_rePitch_tendency_of_shareDrop` project the two conjuncts of `IsShareDrop`.

`rePitch_tendency_atBot_of_terminus_response`: a terminus response re-pitches the tendency into the pole-class. The conclusion is `AtBot`, not equality with `shareZero`.

**The environs lens.**

`environsLine_of_releaseLine`, `isShareDrop_of_releaseLine`, and `deliveredTo_of_environsLine` are projections.

`not_isShareDrop_of_tendency_atBot`: if the prior tendency is already `AtBot`, then no received weld is a strict share-drop against it. The proof uses `before.tendency ≼ shareZero ≼ share received` to contradict the second conjunct of `IsShareDrop`.

`not_isShareDrop_of_eq_shareZero_tendency`: equality with the designated bottom is a bridge into the previous theorem.

`no_releaseLine_of_tendency_atBot`: with an `AtBot` prior tendency, no `ReleaseLine` exists, because its share-drop conjunct is impossible.

`no_releaseLine_of_eq_shareZero_tendency`: equality bridge into the previous theorem.

`effectiveFor_of_releaseLine_actual`: a release-line whose reception is actual assembles the existential `EffectiveFor` witness.

**Delivery and effectiveness.** The reach/aiming biconditionals are definitional (`Iff.rfl`). The remaining delivery theorems are projections from `LandsAt`, `LandsWithShareDrop`, or `EffectiveFor`, plus existential witnesses:

- `deliveredTo_of_landsAt`, `actual_of_landsAt`
- `landsAt_of_landsWithShareDrop`, `isShareDrop_of_landsWithShareDrop`
- `deliveredTo_of_landsWithShareDrop`, `actual_of_landsWithShareDrop`
- `exists_landsAt_of_effectiveFor`, `exists_actual_reception_of_effectiveFor`, `exists_shareDrop_reception_of_effectiveFor`

**Reception pairs.** `first_actual` and `second_actual` project stored proofs. `firstConditionsSecond_iff_deliveredTo` is definitional (`Iff.rfl`). The two `rePitchSequence_*_tendency` theorems are definitional (`rfl`) and show the sequence's tendencies are the two weld shares.

**Tiers and separate/fuse.**

`floor_has_no_nonzero_share`: no nonzero share at `floor`.

`actTime_hasNonzeroShare_iff_hasSelfPoleIndex`: definitional (`Iff.rfl`), because act-time nonzero share is `HasSelfPoleIndex`.

`not_actTime_hasNonzeroShare_of_atBot`: an act-time tier whose weld is at the pole-class has no nonzero share.

`not_actTime_hasNonzeroShare_of_eq_shareZero`: equality bridge into the previous theorem.

`not_collapse_floor`, `hasNonzeroShare_of_collapse`, `hasNonzeroShare_of_separated`, `not_collapse_of_separated`, `fused_of_obeysSeparateFuse`, `separated_of_obeysSeparateFuse`, and `not_freeze_of_fused_floor` are the direct separate/fuse diagnostics: they project the live-share component, use the rule clauses, or contradict equivalence with non-equivalence.

`answersCall_eq_weld_call` and `fitsOfferedTier_iff_trueAt` are definitional. Anonymous examples confirm the two `ErrorGrade.voice` assignments.

---

## 3. `Identification.lean`

**Field residues.** `CorrectFieldRecovery recover` says that every actual weld's field residue recovers its index. `correctFieldRecovery_forces_same_index_of_same_field` proves that two actual welds with equal field residue must then have equal indices. `no_agent_recovery_from_same_field_distinct_index` and `no_agent_recovery_from_same_call_response` package the corresponding impossibility results.

**Ownership-face definitions.** `waa_ReportFace`, `waa_OwnershipFace`, `waa_VacuousOwnershipFace`, and `waa_DiachronicWhose` are conjunctions over delivery, actuality, and WAA-appropriation. Their theorems are projections, introductions, contradictions with non-delivery, or definitional biconditionals:

- `waa_reportFace_of_waa_ownershipFace`
- `actual_of_waa_ownershipFace`
- `waa_appropriation_of_waa_ownershipFace`
- `waa_ownershipFace_intro`
- `not_waa_ownershipFace_of_vacuous`
- `not_waa_ownershipFace_of_waa_vacuousOwnershipFace`
- `waa_diachronicWhose_iff_delivery_and_waa_appropriation`

**Token reflexivity.** `selfAnchored`: `index w = w.agent`. Definitional (`rfl`).

**Pole-typing.**

`StateToolFits w` means `¬ HasSelfPoleIndex w`.

`stateToolFits_of_atBot`: `AtBot (share w)` gives `StateToolFits w`.

`stateToolFits_of_eq_shareZero`: equality bridge into `stateToolFits_of_atBot`.

`atBot_of_stateToolFits`: assuming `[∀ a : Contrib, Decidable (AtBot a)]`, `StateToolFits w` implies `AtBot (share w)`. This is the only classical-looking step: it case-splits on one pole-class comparison, not on equality over the carrier.

`stateToolFits_iff_atBot`: under the same decidability assumption, `StateToolFits w ↔ AtBot (share w)`.

`stateToolFits_of_terminus_response`: terminus responses satisfy `StateToolFits`.

`no_waa_ownershipFace_of_stateToolFits`: if the state-tool fits a reception, the WAA-ownership-face cannot fire there, because ownership-face includes WAA-appropriation.

**Rule and office facts.** `obeysRule_fuses_at_floor` and `obeysRule_separates_at_actTime` are direct uses of the separate/fuse theorems. `dischargeTier_actTime` and `dischargeTier_hasNonzeroShare_iff` are definitional. The placement and disclaimer examples are encoding checks for the listed constructors and numbers.

---

## 4. `Invariance.lean`

**Admission criterion.** Any future predicate over `grade` owes a transport lemma here, or it counts as operational residue. The file proves that the current grade-facing predicates are invariant under display reparameterization.

`DisplayReparam Contrib Contrib'` consists of a function `toFun`, an order preservation/reflection theorem `a ≼ b ↔ toFun a ≼ toFun b`, and a proof that `toFun shareZero` is `AtBot` in the target carrier.

`DisplayReparam.atBot_iff`: `AtBot (toFun a) ↔ AtBot a`. The reverse direction uses order preservation and `atBot_bot`; the forward direction uses the fact that the target `shareZero` is below `toFun shareZero`.

`DisplayReparam.orderEq_iff`: order-equivalence is preserved and reflected.

`Config.map` sends a tendency through `toFun`; `Config.map_tendency` is definitional (`rfl`).

`Grid.map` leaves `Being`, `Call`, `Response`, `respondsTo`, and `conditions` unchanged, and maps `grade` through `toFun`.

Definitional transport facts:

- `map_grade`: mapped grade is `toFun` of the old grade.
- `map_share`: mapped share is `toFun` of the old share.
- `map_actual_iff`, `map_mountsAt_iff`, `map_mountsSomewhere_iff`, `map_respondsToEveryCall_iff`, `map_stone_iff`, `map_deliveredTo_iff`, `map_landsAt_iff`, `map_environsLine_iff`: function-side and delivery-side predicates do not inspect the contribution carrier, so they unfold unchanged.

Grade-facing transport facts:

- `map_terminus_iff`, `map_liveTerminus_iff`, `map_responsiveTerminus_iff`, `map_atZeroSharePole_iff`
- `map_hasSelfPoleIndex_iff`
- `map_probeConstant_iff`
- `map_stateToolFits_iff`
- `Tier.map` and `map_tier_hasNonzeroShare_iff`
- `map_rePitch`
- `map_isShareDrop_iff`
- `map_landsWithShareDrop_iff`
- `map_releaseLine_iff`

Together these say that all current pole, probe, tier, configuration, share-drop, and release-line predicates are legal display predicates: changing the carrier by a reparameterization changes notation, not truth.

**Negative example.** `InvarianceNegative.TwoBottom` is a two-element carrier where every element is order-equivalent to every other element, with `chosen` as the designated `shareZero`. `mergeToUnit` maps both elements to the single unit value and is a `DisplayReparam`. `twoBottomGrid` has one being, one call, one response, responds everywhere, and grades every response as `other`.

The examples show:

- `twoBottomGrid.Terminus ()` holds, because `other` is `AtBot`.
- `OldEqTerminus twoBottomGrid ()` fails, where `OldEqTerminus` is the obsolete equality-token version requiring `grade = shareZero`.
- `OldEqTerminus (twoBottomGrid.map mergeToUnit) ()` holds after the merge, because both old bottom tokens become the same unit token.
- The new `Terminus` transports across the merge, while the old equality-token predicate would not have transported.

This is the formal certificate that replacing `= shareZero` with `AtBot` was a real de-operationalisation, not a naming preference.

---

## 5. Logical Strength

The definitional identities include `share_eq_grade`, `selfAnchored`, `rePitch_tendency_eq_share`, the delivery/aiming biconditionals, `isShareDrop_iff_rePitch_tendency_drop`, the recorded-utterance and discharge-tier identities, the reception-pair tendency lemmas, and the basic `map_*` identities in `Invariance.lean`.

The elementary consequences are projections, witness assemblies, contradictions, and short order arguments. The important non-definitional order arguments are the `AtBot` share-drop obstruction and the display-reparameterization transport lemmas.

The conditional impossibility results are the agent-recovery theorems and the invariance negative example. The concrete model result is still `clockGrid`: it exhibits a `Stone` and a non-stone `Terminus` in one finite grid.

One structural caution remains: `Terminus` is vacuously true of every `Stone`; use `LiveTerminus` or `ResponsiveTerminus` when non-vacuous response-function matters.
