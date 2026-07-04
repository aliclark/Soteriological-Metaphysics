/-
================================================================================
  The Weld and the Arrow — II. Theorems
  Checked consequences of `WeldAndArrow.Theory`
================================================================================

This file keeps the theorem layer conservative. It imports the primitive
signature and proves consequences that already follow from the definitions in
`Theory.lean`: function/share facts, re-pitch facts, delivery/effectiveness
facts, actual-pair projections, and the separate/fuse diagnostics.
-/

import WeldAndArrow.Theory

namespace WAA

section Preorder

variable {α : Type} [Preorder α]

/-- Incomparability is symmetric. -/
theorem incomparable_symm {a b : α} (h : Incomparable a b) :
    Incomparable b a :=
  ⟨h.right, h.left⟩

/-- Incomparability rules out the left-to-right comparison. -/
theorem not_le_of_incomparable {a b : α} (h : Incomparable a b) :
    ¬ a ≼ b :=
  h.left

/-- Incomparability rules out the right-to-left comparison. -/
theorem not_ge_of_incomparable {a b : α} (h : Incomparable a b) :
    ¬ b ≼ a :=
  h.right

end Preorder

namespace Grid

variable {Contrib : Type} [PreorderBot Contrib]
variable (G : Grid Contrib)

/- ==============================================================================
   Function, share, and the two poles
============================================================================== -/

/-- Row 2 is exactly the self-driven component of the drive-composition. -/
theorem share_eq_selfDriven (w : G.Weld) :
    G.share w = (G.driveOf w.agent w.call w.response).selfDriven :=
  rfl

/-- An actual weld witnesses response-function at its own call. -/
theorem mountsAt_of_actual (w : G.Weld) (h : G.Actual w) :
    G.MountsAt w.agent w.call :=
  ⟨w.response, h⟩

/-- An actual weld witnesses response-function somewhere for its agent. -/
theorem mountsSomewhere_of_actual (w : G.Weld) (h : G.Actual w) :
    G.MountsSomewhere w.agent :=
  ⟨w.call, G.mountsAt_of_actual w h⟩

/-- A being with an actual weld is not stone-typed. -/
theorem not_stone_of_actual (w : G.Weld) (h : G.Actual w) :
    ¬ G.Stone w.agent :=
  G.not_stone_of_mountsSomewhere w.agent (G.mountsSomewhere_of_actual w h)

/-- A stone has no actual weld at any call. -/
theorem not_actual_of_stone
    (b : G.Being) (hstone : G.Stone b) {c : G.Call} {r : G.Response} :
    ¬ G.Actual ⟨b, c, r⟩ :=
  fun hactual => hstone c ⟨r, hactual⟩

/-- A stone mounts nowhere. -/
theorem not_mountsSomewhere_of_stone (b : G.Being) (hstone : G.Stone b) :
    ¬ G.MountsSomewhere b :=
  fun hmounts => G.not_stone_of_mountsSomewhere b hmounts hstone

/-- A concrete response at a call rules out stone-typing. -/
theorem not_stone_of_response
    {b : G.Being} {c : G.Call} {r : G.Response}
    (hresp : G.respondsTo b c = some r) :
    ¬ G.Stone b :=
  fun hstone => hstone c ⟨r, hresp⟩

/-- A stone witnesses the stone side of the zero-share pole. -/
theorem atZeroSharePole_of_stone (b : G.Being) (hstone : G.Stone b) :
    G.AtZeroSharePole b :=
  Or.inl hstone

/-- A terminus witnesses the terminus side of the zero-share pole. -/
theorem atZeroSharePole_of_terminus (b : G.Being) (hterm : G.Terminus b) :
    G.AtZeroSharePole b :=
  Or.inr hterm

/-- A live terminus sits at the zero-share pole and is not stone-typed. -/
theorem atZeroSharePole_and_not_stone_of_liveTerminus
    (b : G.Being) (h : G.LiveTerminus b) :
    G.AtZeroSharePole b ∧ ¬ G.Stone b :=
  ⟨G.atZeroSharePole_of_terminus b h.right, G.liveTerminus_not_stone b h⟩

/-- A responsive terminus is not stone-typed whenever the call-domain has a witness. -/
theorem not_stone_of_responsiveTerminus_of_call
    (b : G.Being) (c : G.Call) (h : G.ResponsiveTerminus b) :
    ¬ G.Stone b :=
  G.liveTerminus_not_stone b (G.responsiveTerminus_live_of_call b c h)

/- ==============================================================================
   Re-pitch and share-drops
============================================================================== -/

/-- Re-pitching carries forward exactly the received weld's share. -/
theorem rePitch_tendency_eq_share
    (before : Config Contrib) (received : G.Weld) :
    (G.rePitch before received).tendency = G.share received :=
  rfl

/-- A share-drop can be read as the corresponding strict drop in the re-pitched tendency. -/
theorem isShareDrop_iff_rePitch_tendency_drop
    (before : Config Contrib) (received : G.Weld) :
    G.IsShareDrop before received ↔
      ((G.rePitch before received).tendency ≼ before.tendency ∧
        ¬ (before.tendency ≼ (G.rePitch before received).tendency)) :=
  Iff.rfl

/-- The re-pitched tendency of a share-drop event is no greater than the prior tendency. -/
theorem rePitch_tendency_le_before_of_shareDrop
    {before : Config Contrib} {received : G.Weld}
    (h : G.IsShareDrop before received) :
    (G.rePitch before received).tendency ≼ before.tendency :=
  h.left

/-- A share-drop event is not ordered back above its prior tendency. -/
theorem not_before_le_rePitch_tendency_of_shareDrop
    {before : Config Contrib} {received : G.Weld}
    (h : G.IsShareDrop before received) :
    ¬ (before.tendency ≼ (G.rePitch before received).tendency) :=
  h.right

/-- A terminus response re-pitches the carried tendency to share-zero. -/
theorem rePitch_tendency_eq_shareZero_of_terminus_response
    (before : Config Contrib) {b : G.Being} {c : G.Call} {r : G.Response}
    (hterm : G.Terminus b) (hresp : G.respondsTo b c = some r) :
    (G.rePitch before ⟨b, c, r⟩).tendency = shareZero :=
  G.shareZero_of_terminus_response hterm hresp

/- ==============================================================================
   The environs lens
============================================================================== -/

/-- A release-line is an environs-line. -/
theorem environsLine_of_releaseLine
    {before : Config Contrib} {b : G.Being} {deed reception : G.Weld}
    (h : G.ReleaseLine before b deed reception) :
    G.EnvironsLine b deed reception :=
  h.left

/-- A release-line's reception is share-ceding against the supplied
    tendency. -/
theorem isShareDrop_of_releaseLine
    {before : Config Contrib} {b : G.Being} {deed reception : G.Weld}
    (h : G.ReleaseLine before b deed reception) :
    G.IsShareDrop before reception :=
  h.right

/-- An environs-line is a delivery-fact. -/
theorem deliveredTo_of_environsLine
    {b : G.Being} {deed reception : G.Weld}
    (h : G.EnvironsLine b deed reception) :
    G.DeliveredTo deed reception :=
  h.right.right

/-- No reception is share-ceding against a pole-typed tendency: at
    `before.tendency = shareZero`, `bot_le` supplies exactly the
    comparison `IsShareDrop`'s second conjunct denies. -/
theorem not_isShareDrop_of_tendency_eq_shareZero
    {before : Config Contrib} (h : before.tendency = shareZero)
    (received : G.Weld) :
    ¬ G.IsShareDrop before received := by
  intro hdrop
  exact hdrop.right (h.symm ▸ PreorderBot.bot_le (G.share received))

/-- The lens goes quiet at the pole: an environs read against a share-zero
    tendency contains no release-lines — nothing left to release, a
    feature of the reading, not a defect. -/
theorem no_releaseLine_of_tendency_eq_shareZero
    {before : Config Contrib} (h : before.tendency = shareZero)
    (b : G.Being) (deed reception : G.Weld) :
    ¬ G.ReleaseLine before b deed reception :=
  fun hline =>
    G.not_isShareDrop_of_tendency_eq_shareZero h reception hline.right

/-- Bridge to effectiveness talk: a release-line whose reception is actual
    witnesses the deed's effectiveness for that tendency. -/
theorem effectiveFor_of_releaseLine_actual
    {before : Config Contrib} {b : G.Being} {deed reception : G.Weld}
    (hline : G.ReleaseLine before b deed reception)
    (hact : G.Actual reception) :
    G.EffectiveFor before deed :=
  ⟨reception, ⟨⟨hline.left.right.right, hact⟩, hline.right⟩⟩

/- ==============================================================================
   Delivery, reach-back, and effectiveness
============================================================================== -/

/-- A full reach-back is the same field-side fact as delivery. -/
theorem waa_reachBackFull_iff_deliveredTo (deed reception : G.Weld) :
    G.waa_ReachBackFull deed reception ↔ G.DeliveredTo deed reception :=
  Iff.rfl

/-- An aimed call is just delivery, stated from the sowing side. -/
theorem waa_aimedAt_iff_deliveredTo (deed reception : G.Weld) :
    G.waa_AimedAt deed reception ↔ G.DeliveredTo deed reception :=
  Iff.rfl

/-- Landing includes delivery. -/
theorem deliveredTo_of_landsAt
    {deed reception : G.Weld} (h : G.LandsAt deed reception) :
    G.DeliveredTo deed reception :=
  h.left

/-- Landing includes actuality of the reception. -/
theorem actual_of_landsAt
    {deed reception : G.Weld} (h : G.LandsAt deed reception) :
    G.Actual reception :=
  h.right

/-- A share-drop landing includes an ordinary landing. -/
theorem landsAt_of_landsWithShareDrop
    {before : Config Contrib} {deed reception : G.Weld}
    (h : G.LandsWithShareDrop before deed reception) :
    G.LandsAt deed reception :=
  h.left

/-- A share-drop landing includes the receiver-side share-drop judgement. -/
theorem isShareDrop_of_landsWithShareDrop
    {before : Config Contrib} {deed reception : G.Weld}
    (h : G.LandsWithShareDrop before deed reception) :
    G.IsShareDrop before reception :=
  h.right

/-- A share-drop landing is delivered. -/
theorem deliveredTo_of_landsWithShareDrop
    {before : Config Contrib} {deed reception : G.Weld}
    (h : G.LandsWithShareDrop before deed reception) :
    G.DeliveredTo deed reception :=
  G.deliveredTo_of_landsAt (G.landsAt_of_landsWithShareDrop h)

/-- A share-drop landing is received by an actual weld. -/
theorem actual_of_landsWithShareDrop
    {before : Config Contrib} {deed reception : G.Weld}
    (h : G.LandsWithShareDrop before deed reception) :
    G.Actual reception :=
  G.actual_of_landsAt (G.landsAt_of_landsWithShareDrop h)

/-- Effectiveness gives an actual landing. -/
theorem exists_landsAt_of_effectiveFor
    {before : Config Contrib} {deed : G.Weld}
    (h : G.EffectiveFor before deed) :
    ∃ reception, G.LandsAt deed reception :=
  h.elim (fun reception hland =>
    ⟨reception, G.landsAt_of_landsWithShareDrop hland⟩)

/-- Effectiveness gives an actual receiving weld. -/
theorem exists_actual_reception_of_effectiveFor
    {before : Config Contrib} {deed : G.Weld}
    (h : G.EffectiveFor before deed) :
    ∃ reception, G.Actual reception :=
  h.elim (fun reception hland =>
    ⟨reception, G.actual_of_landsWithShareDrop hland⟩)

/-- Effectiveness gives a receiver-side share-drop witness. -/
theorem exists_shareDrop_reception_of_effectiveFor
    {before : Config Contrib} {deed : G.Weld}
    (h : G.EffectiveFor before deed) :
    ∃ reception, G.IsShareDrop before reception :=
  h.elim (fun reception hland =>
    ⟨reception, G.isShareDrop_of_landsWithShareDrop hland⟩)

/- ==============================================================================
   Actual pairs
============================================================================== -/

namespace ReceptionPair

variable {G : Grid Contrib}

/-- The first member of a reception pair is actual. -/
theorem first_actual (p : ReceptionPair G) :
    G.Actual p.first.weld :=
  p.first.actual

/-- The second member of a reception pair is actual. -/
theorem second_actual (p : ReceptionPair G) :
    G.Actual p.second.weld :=
  p.second.actual

/-- The pair's named relation is just delivery from first to second. -/
theorem firstConditionsSecond_iff_deliveredTo (p : ReceptionPair G) :
    p.FirstConditionsSecond ↔ G.DeliveredTo p.first.weld p.second.weld :=
  Iff.rfl

/-- The first re-pitch in a pair sequence carries the first weld's share. -/
theorem rePitchSequence_first_tendency
    (before : Config Contrib) (p : ReceptionPair G) :
    (rePitchSequence (G := G) before p).fst.tendency = G.share p.first.weld :=
  rfl

/-- The second re-pitch in a pair sequence carries the second weld's share. -/
theorem rePitchSequence_second_tendency
    (before : Config Contrib) (p : ReceptionPair G) :
    (rePitchSequence (G := G) before p).snd.tendency = G.share p.second.weld :=
  rfl

end ReceptionPair

/- ==============================================================================
   Tiers, utterances, and separate/fuse diagnostics
============================================================================== -/

/-- The floor tier has no nonzero share. -/
theorem floor_has_no_nonzero_share :
    ¬ Tier.hasNonzeroShare G (Tier.floor : Tier G) :=
  fun h => h

/-- Act-time nonzero share is exactly the live self-pole index predicate. -/
theorem actTime_hasNonzeroShare_iff_hasSelfPoleIndex (w : G.Weld) :
    Tier.hasNonzeroShare G (Tier.actTime w) ↔ G.HasSelfPoleIndex w :=
  Iff.rfl

/-- Share-zero act-time tiers have no nonzero share. -/
theorem not_actTime_hasNonzeroShare_of_shareZero
    {w : G.Weld} (h : G.share w = shareZero) :
    ¬ Tier.hasNonzeroShare G (Tier.actTime w) :=
  G.no_self_pole_index_of_shareZero w h

/-- Collapse is impossible at the floor. -/
theorem not_collapse_floor (d : Distinction G) :
    ¬ d.Collapse (Tier.floor : Tier G) :=
  fun hcollapse => G.floor_has_no_nonzero_share hcollapse.left

/-- Collapse carries its nonzero-share witness. -/
theorem hasNonzeroShare_of_collapse
    {d : Distinction G} {t : Tier G} (h : d.Collapse t) :
    Tier.hasNonzeroShare G t :=
  h.left

/-- Separation carries its nonzero-share witness. -/
theorem hasNonzeroShare_of_separated
    {d : Distinction G} {t : Tier G} (h : d.Separated t) :
    Tier.hasNonzeroShare G t :=
  h.left

/-- Separation rules out collapse at the same tier. -/
theorem not_collapse_of_separated
    {d : Distinction G} {t : Tier G} (h : d.Separated t) :
    ¬ d.Collapse t :=
  fun hcollapse => h.right hcollapse.right

/-- Obeying the rule supplies the fusion clause at every tier. -/
theorem fused_of_obeysSeparateFuse
    {d : Distinction G} (h : d.ObeysSeparateFuse) (t : Tier G) :
    d.Fused t :=
  h.right t

/-- Obeying the rule gives separation at every live nonzero-share tier. -/
theorem separated_of_obeysSeparateFuse
    {d : Distinction G} (h : d.ObeysSeparateFuse)
    {t : Tier G} (ht : Tier.hasNonzeroShare G t) :
    d.Separated t :=
  ⟨ht, h.left t ht⟩

/-- Fusion at the floor rules out freeze. -/
theorem not_freeze_of_fused_floor
    {d : Distinction G} (h : d.Fused (Tier.floor : Tier G)) :
    ¬ d.Freeze :=
  fun hfreeze => hfreeze (h G.floor_has_no_nonzero_share)

namespace RecordedUtterance

variable {G : Grid Contrib} {L : ClaimLanguage G}

/-- The answered call is the call carried by the utterance's weld. -/
theorem answersCall_eq_weld_call (u : RecordedUtterance G L) :
    answersCall u = u.weld.call :=
  rfl

/-- Fitting the offered tier is exactly truth at that tier. -/
theorem fitsOfferedTier_iff_trueAt (u : RecordedUtterance G L) :
    FitsOfferedTier u ↔ L.TrueAt u.offeredAt u.content :=
  Iff.rfl

end RecordedUtterance

namespace ErrorGrade

/-- Verdict errors speak in the assertable voice. -/
example :
    ErrorGrade.voice ErrorGrade.verdict = VerdictVoice.assertable :=
  rfl

/-- Shortfall errors speak in the displayable voice. -/
example :
    ErrorGrade.voice ErrorGrade.shortfall = VerdictVoice.displayable :=
  rfl

end ErrorGrade

end Grid

end WAA
