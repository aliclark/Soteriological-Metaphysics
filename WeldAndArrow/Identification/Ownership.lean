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

end WAA