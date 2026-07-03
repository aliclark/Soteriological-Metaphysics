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

section WeakOrder

variable {α : Type} [WeakOrder α]

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

end WeakOrder

namespace Grid

variable {Contrib : Type} [WeakOrderBot Contrib]
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

/-- A stone witnesses the stone side of the genjō pole. -/
theorem atGenjoPole_of_stone (b : G.Being) (hstone : G.Stone b) :
    G.AtGenjōPole b :=
  Or.inl hstone

/-- A terminus witnesses the terminus side of the genjō pole. -/
theorem atGenjoPole_of_terminus (b : G.Being) (hterm : G.Terminus b) :
    G.AtGenjōPole b :=
  Or.inr hterm

/-- A live terminus sits at the genjō pole and is not stone-typed. -/
theorem atGenjoPole_and_not_stone_of_liveTerminus
    (b : G.Being) (h : G.LiveTerminus b) :
    G.AtGenjōPole b ∧ ¬ G.Stone b :=
  ⟨G.atGenjoPole_of_terminus b h.right, G.liveTerminus_not_stone b h⟩

/-- A responsive terminus is not stone-typed whenever the call-domain has a witness. -/
theorem not_stone_of_responsiveTerminus_of_call
    (b : G.Being) (c : G.Call) (h : G.ResponsiveTerminus b) :
    ¬ G.Stone b :=
  G.liveTerminus_not_stone b (G.responsiveTerminus_live_of_call b c h)

/- ==============================================================================
   Re-pitch and kenshō
============================================================================== -/

/-- Re-pitching carries forward exactly the received weld's share. -/
theorem rePitch_tendency_eq_share
    (before : Config Contrib) (received : G.Weld) :
    (G.rePitch before received).tendency = G.share received :=
  rfl

/-- Kenshō can be read as the corresponding strict drop in the re-pitched tendency. -/
theorem isKensho_iff_rePitch_tendency_drop
    (before : Config Contrib) (received : G.Weld) :
    G.IsKenshō before received ↔
      ((G.rePitch before received).tendency ≼ before.tendency ∧
        ¬ (before.tendency ≼ (G.rePitch before received).tendency)) :=
  Iff.rfl

/-- The re-pitched tendency of a kenshō event is no greater than the prior tendency. -/
theorem rePitch_tendency_le_before_of_kensho
    {before : Config Contrib} {received : G.Weld}
    (h : G.IsKenshō before received) :
    (G.rePitch before received).tendency ≼ before.tendency :=
  h.left

/-- A kenshō event is not ordered back above its prior tendency. -/
theorem not_before_le_rePitch_tendency_of_kensho
    {before : Config Contrib} {received : G.Weld}
    (h : G.IsKenshō before received) :
    ¬ (before.tendency ≼ (G.rePitch before received).tendency) :=
  h.right

/-- A terminus response re-pitches the carried tendency to share-zero. -/
theorem rePitch_tendency_eq_shareZero_of_terminus_response
    (before : Config Contrib) {b : G.Being} {c : G.Call} {r : G.Response}
    (hterm : G.Terminus b) (hresp : G.respondsTo b c = some r) :
    (G.rePitch before ⟨b, c, r⟩).tendency = shareZero :=
  G.shareZero_of_terminus_response hterm hresp

/- ==============================================================================
   Delivery, reach-back, and effectiveness
============================================================================== -/

/-- A full reach-back is the same field-side fact as delivery. -/
theorem reachBackFull_iff_deliveredTo (deed reception : G.Weld) :
    G.ReachBackFull deed reception ↔ G.DeliveredTo deed reception :=
  Iff.rfl

/-- A vacuous reach-back is exactly non-delivery. -/
theorem reachBackVacuous_iff_not_deliveredTo (deed reception : G.Weld) :
    G.ReachBackVacuous deed reception ↔ ¬ G.DeliveredTo deed reception :=
  Iff.rfl

/-- Full and vacuous reach-back cannot coincide. -/
theorem not_reachBackVacuous_of_full
    {deed reception : G.Weld} (hfull : G.ReachBackFull deed reception) :
    ¬ G.ReachBackVacuous deed reception :=
  fun hvacuous => hvacuous hfull

/-- Vacuity rules out full reach-back. -/
theorem not_reachBackFull_of_vacuous
    {deed reception : G.Weld} (hvacuous : G.ReachBackVacuous deed reception) :
    ¬ G.ReachBackFull deed reception :=
  hvacuous

/-- An aimed call is just delivery, stated from the sowing side. -/
theorem aimedAt_iff_deliveredTo (deed reception : G.Weld) :
    G.AimedAt deed reception ↔ G.DeliveredTo deed reception :=
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

/-- A kenshō landing includes an ordinary landing. -/
theorem landsAt_of_landsWithKensho
    {before : Config Contrib} {deed reception : G.Weld}
    (h : G.LandsWithKenshō before deed reception) :
    G.LandsAt deed reception :=
  h.left

/-- A kenshō landing includes the receiver-side kenshō judgement. -/
theorem isKensho_of_landsWithKensho
    {before : Config Contrib} {deed reception : G.Weld}
    (h : G.LandsWithKenshō before deed reception) :
    G.IsKenshō before reception :=
  h.right

/-- A kenshō landing is delivered. -/
theorem deliveredTo_of_landsWithKensho
    {before : Config Contrib} {deed reception : G.Weld}
    (h : G.LandsWithKenshō before deed reception) :
    G.DeliveredTo deed reception :=
  G.deliveredTo_of_landsAt (G.landsAt_of_landsWithKensho h)

/-- A kenshō landing is received by an actual weld. -/
theorem actual_of_landsWithKensho
    {before : Config Contrib} {deed reception : G.Weld}
    (h : G.LandsWithKenshō before deed reception) :
    G.Actual reception :=
  G.actual_of_landsAt (G.landsAt_of_landsWithKensho h)

/-- Effectiveness gives an actual landing. -/
theorem exists_landsAt_of_effectiveFor
    {before : Config Contrib} {deed : G.Weld}
    (h : G.EffectiveFor before deed) :
    ∃ reception, G.LandsAt deed reception :=
  h.elim (fun reception hland =>
    ⟨reception, G.landsAt_of_landsWithKensho hland⟩)

/-- Effectiveness gives an actual receiving weld. -/
theorem exists_actual_reception_of_effectiveFor
    {before : Config Contrib} {deed : G.Weld}
    (h : G.EffectiveFor before deed) :
    ∃ reception, G.Actual reception :=
  h.elim (fun reception hland =>
    ⟨reception, G.actual_of_landsWithKensho hland⟩)

/-- Effectiveness gives a receiver-side kenshō witness. -/
theorem exists_kensho_reception_of_effectiveFor
    {before : Config Contrib} {deed : G.Weld}
    (h : G.EffectiveFor before deed) :
    ∃ reception, G.IsKenshō before reception :=
  h.elim (fun reception hland =>
    ⟨reception, G.isKensho_of_landsWithKensho hland⟩)

/-- The preorder-style effectiveness comparison preserves effectiveness. -/
theorem effectiveFor_of_atLeastAsEffective
    {before : Config Contrib} {deed1 deed2 : G.Weld}
    (hge : G.AtLeastAsEffective before deed1 deed2)
    (heff : G.EffectiveFor before deed2) :
    G.EffectiveFor before deed1 :=
  heff.elim (fun reception hland => hge reception hland)

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

/-- The floor tier has no arrogation. -/
theorem floor_has_no_arrogation :
    ¬ Tier.hasArrogation G (Tier.floor : Tier G) :=
  fun h => h

/-- Act-time arrogation is exactly the live self-pole index predicate. -/
theorem actTime_hasArrogation_iff_hasSelfPoleIndex (w : G.Weld) :
    Tier.hasArrogation G (Tier.actTime w) ↔ G.HasSelfPoleIndex w :=
  Iff.rfl

/-- Share-zero act-time tiers have no arrogation. -/
theorem not_actTime_hasArrogation_of_shareZero
    {w : G.Weld} (h : G.share w = shareZero) :
    ¬ Tier.hasArrogation G (Tier.actTime w) :=
  G.no_self_pole_index_of_shareZero w h

/-- Collapse is impossible at the floor. -/
theorem not_collapse_floor (d : Distinction G) :
    ¬ d.Collapse (Tier.floor : Tier G) :=
  fun hcollapse => G.floor_has_no_arrogation hcollapse.left

/-- Collapse carries its arrogation witness. -/
theorem hasArrogation_of_collapse
    {d : Distinction G} {t : Tier G} (h : d.Collapse t) :
    Tier.hasArrogation G t :=
  h.left

/-- Separation carries its arrogation witness. -/
theorem hasArrogation_of_separated
    {d : Distinction G} {t : Tier G} (h : d.Separated t) :
    Tier.hasArrogation G t :=
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

/-- Obeying the rule gives separation at every live-arrogation tier. -/
theorem separated_of_obeysSeparateFuse
    {d : Distinction G} (h : d.ObeysSeparateFuse)
    {t : Tier G} (ht : Tier.hasArrogation G t) :
    d.Separated t :=
  ⟨ht, h.left t ht⟩

/-- Fusion at the floor rules out freeze. -/
theorem not_freeze_of_fused_floor
    {d : Distinction G} (h : d.Fused (Tier.floor : Tier G)) :
    ¬ d.Freeze :=
  fun hfreeze => hfreeze (h G.floor_has_no_arrogation)

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

/-- Grammatical errors speak in the assertable voice. -/
theorem grammatical_voice :
    ErrorGrade.voice ErrorGrade.grammatical = VerdictVoice.assertable :=
  rfl

/-- Soteriological errors speak in the displayable voice. -/
theorem soteriological_voice :
    ErrorGrade.voice ErrorGrade.soteriological = VerdictVoice.displayable :=
  rfl

end ErrorGrade

end Grid

end WAA
