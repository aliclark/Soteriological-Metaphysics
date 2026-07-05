/-
================================================================================
  WeldAndArrow.Identification.Ownership
  Ownership faces, token-reflexivity, pole typing, and offices
================================================================================

Reading and motivation: Identification/Commentary.lean, C.2.
-/

import WeldAndArrow.Identification.Residues

namespace WAA

namespace Grid

variable {Contrib : Type} [PreorderBot Contrib]
variable (G : Grid Contrib)

/- ==============================================================================
   §2  Sower/reaper, reach-back, and WAA-ownership-face
============================================================================== -/

namespace DirectedConvention

/-- The field-side report-face of "the sower reaps": the delivery line, before
    any act-time ownership is added. -/
def WaaReportFace (deed reception : G.Weld) : Prop :=
  DeliveredTo G deed reception

/-- The full WAA-ownership-face: delivery reaches an actual reception and that
    reception WAA-appropriates. It is a deed at reception-time, not a standing
    relation. -/
def WaaOwnershipFace (deed reception : G.Weld) : Prop :=
  LandsAt G deed reception ∧ G.WaaAppropriates reception

/-- The source's vacuous reach-back ("an appropriating with nothing arrived
    to appropriate — not a falsehood ... but vacuous"): an actual,
    appropriating reception whose claimed deed never delivered to it. The
    vacuity is a property of this three-conjunct face; bare non-delivery
    alone is `NotDeliveredTo` and carries no appropriation. -/
def WaaVacuousOwnershipFace (deed reception : G.Weld) : Prop :=
  NotDeliveredTo G deed reception ∧ G.Actual reception ∧ G.WaaAppropriates reception

/-- The WAA-ownership-face includes the report-face. -/
theorem waaReportFace_of_waaOwnershipFace
    {deed reception : G.Weld} (h : WaaOwnershipFace G deed reception) :
    WaaReportFace G deed reception :=
  h.left.left

/-- The WAA-ownership-face includes actual reception. -/
theorem actual_of_waaOwnershipFace
    {deed reception : G.Weld} (h : WaaOwnershipFace G deed reception) :
    G.Actual reception :=
  h.left.right

/-- The WAA-ownership-face includes WAA-appropriation at reception-time. -/
theorem waaAppropriates_of_waaOwnershipFace
    {deed reception : G.Weld} (h : WaaOwnershipFace G deed reception) :
    G.WaaAppropriates reception :=
  h.right

/-- Full landing plus WAA-appropriation introduces the WAA-ownership-face. -/
theorem waaOwnershipFace_intro
    {deed reception : G.Weld}
    (hland : LandsAt G deed reception) (happ : G.WaaAppropriates reception) :
    WaaOwnershipFace G deed reception :=
  ⟨hland, happ⟩

/-- Bare non-delivery cannot at the same time be a full WAA-ownership-face for
    that deed and reception. -/
theorem not_waaOwnershipFace_of_vacuous
    {deed reception : G.Weld} (hv : NotDeliveredTo G deed reception) :
    ¬ WaaOwnershipFace G deed reception :=
  fun hown => hv hown.left.left

/-- A vacuous WAA-ownership attempt is not a full WAA-ownership-face. -/
theorem not_waaOwnershipFace_of_waaVacuousOwnershipFace
    {deed reception : G.Weld} (hv : WaaVacuousOwnershipFace G deed reception) :
    ¬ WaaOwnershipFace G deed reception :=
  not_waaOwnershipFace_of_vacuous G hv.left

/-- The diachronic whose-question decomposes into delivery plus fresh
    WAA-appropriation; no third cross-gap owner is part of this definition. -/
def WaaDiachronicWhose (deed reception : G.Weld) : Prop :=
  DeliveredTo G deed reception ∧ G.WaaAppropriates reception

theorem waaDiachronicWhose_iff_delivery_and_waaAppropriates
    (deed reception : G.Weld) :
    WaaDiachronicWhose G deed reception ↔
      DeliveredTo G deed reception ∧ G.WaaAppropriates reception :=
  Iff.rfl

/-- Delivery alone never settles the diachronic whose-question; the fresh
    reception-time appropriation conjunct is still required. -/
theorem no_diachronicWhose_from_series_alone
    {deed reception : G.Weld}
    (hno : ¬ G.WaaAppropriates reception) :
    ¬ WaaDiachronicWhose G deed reception := by
  intro hwhose
  exact hno ((waaDiachronicWhose_iff_delivery_and_waaAppropriates G
    deed reception).mp hwhose).right

/- ==============================================================================
   §2  Prudential privilege negative
============================================================================== -/

namespace PrudentialPrivilegeNegative

open BeingConvention

/-- The present-side fine register. -/
def deedAgent : Nat :=
  1

/-- The future-side fine register. -/
def receptionAgent : Nat :=
  2

/-- The future reception's mounted response. -/
def receptionResponse : Nat :=
  3

/-- The present concern/deed register in the checked prudence witness. -/
def deed : registerClockGrid.Weld :=
  ⟨deedAgent, (), receptionAgent⟩

/-- The future reception register delivered by `deed`. -/
def reception : registerClockGrid.Weld :=
  ⟨receptionAgent, (), receptionResponse⟩

/-- The concrete actual pair used to route the witness through the same
    `ReceptionPair` carrier as the diachronic ownership vocabulary. -/
def pair : ReceptionPair registerClockGrid where
  first := { weld := deed, actual := rfl }
  second := { weld := reception, actual := rfl }

theorem pair_firstConditionsSecond :
    pair.FirstConditionsSecond := by
  rfl

theorem deed_waaAppropriates :
    registerClockGrid.WaaAppropriates deed := by
  dsimp [Grid.WaaAppropriates, Grid.HasSelfPoleIndex, Grid.share,
    registerClockGrid, deed, AtBot, shareBot]
  change ¬ (1 : Nat) ≤ 0
  exact Nat.not_succ_le_zero 0

theorem reception_waaAppropriates :
    registerClockGrid.WaaAppropriates reception := by
  dsimp [Grid.WaaAppropriates, Grid.HasSelfPoleIndex, Grid.share,
    registerClockGrid, reception, AtBot, shareBot]
  change ¬ (2 : Nat) ≤ 0
  exact Nat.not_succ_le_zero 1

/-- Ordinary diachronic ownership can be made at reception-time in the witness:
    delivery plus fresh WAA-appropriation. -/
theorem reception_waaDiachronicWhose :
    WaaDiachronicWhose registerClockGrid deed reception :=
  ⟨rfl, reception_waaAppropriates⟩

/-- The same pair also gives the full WAA-ownership face. -/
theorem reception_waaOwnershipFace :
    WaaOwnershipFace registerClockGrid deed reception :=
  ⟨⟨rfl, rfl⟩, reception_waaAppropriates⟩

/-- Merge reading: every fine register belongs to one macro tag. -/
abbrev kMerge : BeingCoarsening registerClockGrid Unit :=
  registerClockCoarsening

/-- Split reading: each fine register keeps its own macro tag. -/
def kSplit : BeingCoarsening registerClockGrid Nat where
  proj := id

theorem merge_same_fiber :
    kMerge.SameFiber deedAgent receptionAgent :=
  rfl

/-- Pairwise boundary induced by the merge reading. -/
abbrev mergeBoundary (_p _q : Nat) : Prop :=
  True

/-- Pairwise boundary induced by the split reading. -/
abbrev splitBoundary (p q : Nat) : Prop :=
  p = q

theorem merge_boundary_holds :
    mergeBoundary deedAgent receptionAgent :=
  True.intro

theorem split_boundary_fails :
    ¬ ((1 : Nat) = (2 : Nat)) := by
  decide

/-- The grid data visible to a convention-free standing-owner recovery. -/
abbrev W : Type :=
  RawWeld Nat Unit Nat

/-- Function, grade, and delivery data, with no supplied being-convention. -/
abbrev GridData : Type :=
  (Nat -> Unit -> Option Nat) ×
    (Nat -> Unit -> Nat -> Nat) ×
      (W -> W -> Prop)

def gridData : GridData :=
  (registerClockGrid.respondsTo, registerClockGrid.grade,
    registerClockGrid.conditions)

/-- A standing cross-gap "mine" relation over the witness grid. -/
abbrev StandingMine : Type :=
  registerClockGrid.Weld -> registerClockGrid.Weld -> Prop

/-- Agreement with the merge convention at the prudential pair. -/
def AgreesWithMergeAt (mine : StandingMine) : Prop :=
  mine deed reception ↔ mergeBoundary deedAgent receptionAgent

/-- Agreement with the split convention at the same prudential pair. -/
def AgreesWithSplitAt (mine : StandingMine) : Prop :=
  mine deed reception ↔ splitBoundary deedAgent receptionAgent

/-- Prudential privilege, as a checked recovery claim: from the grid data alone,
    recover a standing cross-gap "mine" relation that settles the pair before
    any supplied being-convention. Such a relation would have to agree with
    both legal readings of the same grid data. -/
def PrudentialPrivilege : Prop :=
  ∃ recover : GridData -> StandingMine,
    AgreesWithMergeAt (recover gridData) ∧
      AgreesWithSplitAt (recover gridData)

/-- The prudential privilege recovery claim fails in the register-clock witness:
    the merge and split being-conventions are both legal, but they disagree on
    whether the present deed-register and the future reception-register share a
    fiber. -/
theorem not_prudentialPrivilege :
    ¬ PrudentialPrivilege := by
  rintro ⟨recover, hmerge, hsplit⟩
  have hmine : recover gridData deed reception :=
    hmerge.mpr merge_boundary_holds
  have hnotMine : ¬ recover gridData deed reception := by
    intro h
    exact split_boundary_fails (hsplit.mp h)
  exact hnotMine hmine

/-- Re-pitching the actual pair leaves the final configuration reading only the
    received future weld's share. The prior tendency is not an inheritance
    register for the deed-side owner. -/
theorem rePitchSequence_final_forgets_prior
    (before1 before2 : Config Nat) :
    (ReceptionPair.rePitchSequence (G := registerClockGrid) before1 pair).snd =
      (ReceptionPair.rePitchSequence (G := registerClockGrid) before2 pair).snd :=
  registerClockGrid.rePitch_forgets
    (registerClockGrid.rePitch before1 pair.first.weld)
    (registerClockGrid.rePitch before2 pair.first.weld)
    pair.second.weld

/-- The final tendency of the pair is just the future reception's share. -/
theorem rePitchSequence_final_tendency
    (before : Config Nat) :
    (ReceptionPair.rePitchSequence (G := registerClockGrid) before pair).snd.tendency =
      registerClockGrid.share reception :=
  rfl

/-- The grade side of the witness does not inspect downstream delivery
    conditions. -/
theorem deed_grade_independent_of_conditions
    (conditions1 conditions2 :
      registerClockGrid.Weld -> registerClockGrid.Weld -> Prop) :
    (registerClockGrid.withConditions conditions1).grade
        deed.agent deed.call deed.response =
      (registerClockGrid.withConditions conditions2).grade
        deed.agent deed.call deed.response :=
  registerClockGrid.grade_independent_of_conditions
    conditions1 conditions2 deed.agent deed.call deed.response

/-- The checked prudence package: fresh reception-time ownership is available,
    but standing grid-data privilege, stored inheritance, and delivery-sensitive
    grading are not. -/
theorem prudentialPrivilege_failure_modes :
    WaaDiachronicWhose registerClockGrid deed reception ∧
      ¬ PrudentialPrivilege ∧
        (∀ before1 before2 : Config Nat,
          (ReceptionPair.rePitchSequence (G := registerClockGrid) before1 pair).snd =
            (ReceptionPair.rePitchSequence (G := registerClockGrid) before2 pair).snd) ∧
          (∀ conditions1 conditions2 :
            registerClockGrid.Weld -> registerClockGrid.Weld -> Prop,
            (registerClockGrid.withConditions conditions1).grade
                deed.agent deed.call deed.response =
              (registerClockGrid.withConditions conditions2).grade
                deed.agent deed.call deed.response) :=
  ⟨reception_waaDiachronicWhose, not_prudentialPrivilege,
    rePitchSequence_final_forgets_prior, deed_grade_independent_of_conditions⟩

end PrudentialPrivilegeNegative

end DirectedConvention

/- ==============================================================================
   §2  Token-reflexivity
============================================================================== -/

/-- Token-reflexivity as a projection identity. Deliberately a `def` that
    can never fail (`selfAnchored` proves it for every weld): the content
    is the identity's *shape* — no route to "this act's agent" except
    through the completed weld — displayed, not risked. -/
def SelfAnchored (w : G.Weld) : Prop :=
  G.index w = w.agent

theorem selfAnchored (w : G.Weld) : G.SelfAnchored w := rfl

/- ==============================================================================
   §3  Pole-typing and the verdict's own tier
============================================================================== -/

/-- The state-tool fits exactly when no live self-pole index remains. -/
def StateToolFits (w : G.Weld) : Prop :=
  ¬ G.HasSelfPoleIndex w

/-- The pole-class is the constructive direction of the pole-typing
    corollary: no self-pole index remains for a state-tool to miss. -/
theorem stateToolFits_of_atBot
    {w : G.Weld} (hshare : AtBot (G.share w)) :
    G.StateToolFits w :=
  G.no_self_pole_index_of_atBot w hshare

/-- Literal equality with the designated bottom is a bridge into the
    pole-class pole-typing corollary. -/
theorem stateToolFits_of_eq_shareBot
    {w : G.Weld} (hshare : G.share w = shareBot) :
    G.StateToolFits w :=
  G.stateToolFits_of_atBot (atBot_of_eq_shareBot hshare)

/-- With decidability of the one pole-class comparison, pole-typing can be
    read as an iff: the state-tool fits just where the share is at the
    pole-class. -/
theorem atBot_of_stateToolFits {w : G.Weld}
    [Decidable (AtBot (G.share w))] (hfits : G.StateToolFits w) :
    AtBot (G.share w) := by
  by_cases hshare : AtBot (G.share w)
  · exact hshare
  · exact False.elim (hfits hshare)

/-- With decidability of the one pole-class comparison, pole-typing is an
    exact iff. -/
theorem stateToolFits_iff_atBot (w : G.Weld)
    [Decidable (AtBot (G.share w))] :
    G.StateToolFits w ↔ AtBot (G.share w) :=
  ⟨G.atBot_of_stateToolFits, G.stateToolFits_of_atBot⟩

/-- Terminus responses are reducible in the corollary's sense. -/
theorem stateToolFits_of_terminus_response
    {b : G.Being} {c : G.Call} {r : G.Response}
    (hterm : G.Terminus b) (hresp : G.respondsTo b c = some r) :
    G.StateToolFits ⟨b, c, r⟩ :=
  G.no_self_pole_index_of_terminus_response hterm hresp

namespace DirectedConvention

/-- If the state-tool fits a reception, the WAA-ownership-face cannot fire there. -/
theorem not_waaOwnershipFace_of_stateToolFits
    {deed reception : G.Weld} (hfits : G.StateToolFits reception) :
    ¬ WaaOwnershipFace G deed reception :=
  fun hown => hfits hown.right

end DirectedConvention

-- The paper's "a mis-feed at the floor is not a claim" verdict is carried
-- by `not_collapse_floor`; no separate theorem restates it.

/-- A distinction obeying the separate/fuse rule fuses at the floor. -/
theorem obeysRule_fuses_at_floor
    {d : Distinction G} (h : d.ObeysSeparateFuse) :
    d.Fused (Tier.floor : Tier G) :=
  G.fused_of_obeysSeparateFuse h Tier.floor

/-- The same distinction separates at live act-time diagnosis. -/
theorem obeysRule_separates_at_actTime
    {d : Distinction G} (h : d.ObeysSeparateFuse)
    {w : G.Weld} (hidx : G.HasSelfPoleIndex w) :
    d.Separated (Tier.actTime w) :=
  G.separated_of_obeysSeparateFuse h hidx

/- ==============================================================================
   §4  The office-spine and contemporary placements
============================================================================== -/

end Grid

/-- The WAA-offices karmic ownership holds in the paper's identity-claim. -/
inductive WaaOwnershipOffice
  | cetana
  | reception
  | practice
  | remorse
  | absolution
  | dedication

namespace WaaOwnershipOffice

variable {Contrib : Type} [PreorderBot Contrib] {G : Grid Contrib}

/-- Each office is assigned to a weld's act-time tier (the office
    argument is unused). The paper's further claim — discharged *not by a
    cross-gap state* — is architectural, carried by what `Config` does not
    contain and by the absence of any `Config`-consuming assignment
    function; it is not this definition's proposition. -/
def assignedTier (_office : WaaOwnershipOffice) (w : G.Weld) : Grid.Tier G :=
  Grid.Tier.actTime w

theorem assignedTier_eq_actTime (office : WaaOwnershipOffice) (w : G.Weld) :
    office.assignedTier w = Grid.Tier.actTime w := rfl

/-- Assigning an office to act-time has exactly the weld's live-share
    condition. -/
theorem assignedTier_hasLiveShare_iff
    (office : WaaOwnershipOffice) (w : G.Weld) :
    Grid.Tier.hasLiveShare G (office.assignedTier w) ↔
      G.HasSelfPoleIndex w :=
  Iff.rfl

end WaaOwnershipOffice

/- Reading and motivation: Identification/Commentary.lean, C.1. -/

namespace SelfLineWitness

inductive Being
  | one

inductive Call
  | call

inductive Response
  | response

def selfLineGrid : Grid Nat where
  Being      := Being
  Call       := Call
  Response   := Response
  respondsTo _ _ := some Response.response
  grade _ _ _ := 1
  conditions _ _ := True

def w : selfLineGrid.Weld :=
  ⟨Being.one, Call.call, Response.response⟩

theorem w_has_live_share : selfLineGrid.WaaAppropriates w := by
  intro hbot
  cases hbot

theorem selfLine_conditions_self : selfLineGrid.conditions w w :=
  True.intro

theorem selfLine_landsAt_self : Grid.DirectedConvention.LandsAt selfLineGrid w w :=
  ⟨True.intro, rfl⟩

theorem selfLine_waaOwnershipFace_self :
    Grid.DirectedConvention.WaaOwnershipFace selfLineGrid w w :=
  ⟨⟨True.intro, rfl⟩, w_has_live_share⟩

end SelfLineWitness

end WAA
