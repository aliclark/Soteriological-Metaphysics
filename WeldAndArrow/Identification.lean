/-
================================================================================
  The Weld and the Arrow — III. The Identification and Placements
  Checked identification layer for `Paper/Proofs.md`
================================================================================

This file formalizes the part of the paper that is most naturally checkable:
field residues and index recovery, the sower/reaper split, token-reflexivity,
the office-spine, the pole-typing corollary, contemporary placements, and the
enumerated disclaimers.

As in the earlier files, the prose claims that are genuinely meta-level typing
discipline are kept as type signatures plus small theorems over those
signatures. The file does not pretend that named contemporary positions or the
canonical texts are Lean hypotheses; it gives the internal grid-shape the paper
uses when placing them.
-/

import WeldAndArrow.Theorems

namespace WAA

/- ==============================================================================
   §0  Field residues and index recovery
============================================================================== -/

namespace Grid

variable {Contrib : Type} [PreorderBot Contrib]
variable (G : Grid Contrib)

/-- A field residue: the call and response left when the agent-index is not part
    of the data. -/
abbrev FieldFact : Type := G.Call × G.Response

/-- A field-only recovery candidate tries to recover an agent-index from field
    residues alone. -/
abbrev FieldRecovery : Type := G.FieldFact → G.Being

/-- Correctness for a field-only recovery candidate: for every actual weld, it
    must recover the very index projected from that weld. -/
def CorrectFieldRecovery (recover : G.FieldRecovery) : Prop :=
  ∀ w : G.Weld, G.Actual w → recover (G.fieldOf w) = G.index w

/-- A correct field-only recovery cannot distinguish two actual welds with the
    same field residue; it must assign them the same index. -/
theorem correctFieldRecovery_forces_same_index_of_same_field
    {recover : G.FieldRecovery} (hrec : G.CorrectFieldRecovery recover)
    {w₁ w₂ : G.Weld} (h₁ : G.Actual w₁) (h₂ : G.Actual w₂)
    (hfield : G.fieldOf w₁ = G.fieldOf w₂) :
    G.index w₁ = G.index w₂ :=
  calc
    G.index w₁ = recover (G.fieldOf w₁) := (hrec w₁ h₁).symm
    _ = recover (G.fieldOf w₂) := congrArg recover hfield
    _ = G.index w₂ := hrec w₂ h₂

/-- If two actual welds share the field residue but differ in index, no
    field-only recovery can be correct. This is the modest internal fact that
    field residues under-determine the agent-index. -/
theorem no_agent_recovery_from_same_field_distinct_index
    {w₁ w₂ : G.Weld} (h₁ : G.Actual w₁) (h₂ : G.Actual w₂)
    (hfield : G.fieldOf w₁ = G.fieldOf w₂)
    (hne : G.index w₁ ≠ G.index w₂) :
    ¬ ∃ recover : G.FieldRecovery, G.CorrectFieldRecovery recover :=
  fun ⟨_recover, hrec⟩ =>
    hne (G.correctFieldRecovery_forces_same_index_of_same_field
      hrec h₁ h₂ hfield)

/-- The concrete same-call/same-response witness used in the prose: two
    different beings can actually answer the same call with the same response,
    and the field residue cannot say which one acted. -/
theorem no_agent_recovery_from_same_call_response
    (a₁ a₂ : G.Being) (c : G.Call) (r : G.Response)
    (h₁ : G.Actual ⟨a₁, c, r⟩) (h₂ : G.Actual ⟨a₂, c, r⟩)
    (hne : a₁ ≠ a₂) :
    ¬ ∃ recover : G.FieldRecovery, G.CorrectFieldRecovery recover :=
  G.no_agent_recovery_from_same_field_distinct_index h₁ h₂ rfl hne

/- ==============================================================================
   §2  Sower/reaper, reach-back, and WAA-ownership-face
============================================================================== -/

/-- The field-side report-face of "the sower reaps": the delivery line, before
    any act-time ownership is added. -/
def waa_ReportFace (deed reception : G.Weld) : Prop :=
  G.DeliveredTo deed reception

/-- The full WAA-ownership-face: delivery reaches an actual reception and that
    reception WAA-appropriates. It is a deed at reception-time, not a standing
    relation. -/
def waa_OwnershipFace (deed reception : G.Weld) : Prop :=
  G.LandsAt deed reception ∧ G.waa_Appropriates reception

/-- The source's vacuous reach-back ("an appropriating with nothing arrived
    to appropriate — not a falsehood ... but vacuous"): an actual,
    appropriating reception whose claimed deed never delivered to it. The
    vacuity is a property of this three-conjunct face; bare non-delivery
    alone is `NotDeliveredTo` and carries no appropriation. -/
def waa_VacuousOwnershipFace (deed reception : G.Weld) : Prop :=
  G.NotDeliveredTo deed reception ∧ G.Actual reception ∧ G.waa_Appropriates reception

/-- The WAA-ownership-face includes the report-face. -/
theorem waa_reportFace_of_waa_ownershipFace
    {deed reception : G.Weld} (h : G.waa_OwnershipFace deed reception) :
    G.waa_ReportFace deed reception :=
  h.left.left

/-- The WAA-ownership-face includes actual reception. -/
theorem actual_of_waa_ownershipFace
    {deed reception : G.Weld} (h : G.waa_OwnershipFace deed reception) :
    G.Actual reception :=
  h.left.right

/-- The WAA-ownership-face includes WAA-appropriation at reception-time. -/
theorem waa_appropriation_of_waa_ownershipFace
    {deed reception : G.Weld} (h : G.waa_OwnershipFace deed reception) :
    G.waa_Appropriates reception :=
  h.right

/-- Full landing plus WAA-appropriation introduces the WAA-ownership-face. -/
theorem waa_ownershipFace_intro
    {deed reception : G.Weld}
    (hland : G.LandsAt deed reception) (happ : G.waa_Appropriates reception) :
    G.waa_OwnershipFace deed reception :=
  ⟨hland, happ⟩

/-- Bare non-delivery cannot at the same time be a full WAA-ownership-face for
    that deed and reception. -/
theorem not_waa_ownershipFace_of_vacuous
    {deed reception : G.Weld} (hv : G.NotDeliveredTo deed reception) :
    ¬ G.waa_OwnershipFace deed reception :=
  fun hown => hv hown.left.left

/-- A vacuous WAA-ownership attempt is not a full WAA-ownership-face. -/
theorem not_waa_ownershipFace_of_waa_vacuousOwnershipFace
    {deed reception : G.Weld} (hv : G.waa_VacuousOwnershipFace deed reception) :
    ¬ G.waa_OwnershipFace deed reception :=
  G.not_waa_ownershipFace_of_vacuous hv.left

/-- The diachronic whose-question decomposes into delivery plus fresh
    WAA-appropriation; no third cross-gap owner is part of this definition. -/
def waa_DiachronicWhose (deed reception : G.Weld) : Prop :=
  G.DeliveredTo deed reception ∧ G.waa_Appropriates reception

theorem waa_diachronicWhose_iff_delivery_and_waa_appropriation
    (deed reception : G.Weld) :
    G.waa_DiachronicWhose deed reception ↔
      G.DeliveredTo deed reception ∧ G.waa_Appropriates reception :=
  Iff.rfl

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
theorem stateToolFits_of_eq_shareZero
    {w : G.Weld} (hshare : G.share w = shareZero) :
    G.StateToolFits w :=
  G.stateToolFits_of_atBot (atBot_of_eq_shareZero hshare)

/-- With decidability of the one pole-class comparison, pole-typing can be
    read as an iff: the state-tool fits just where the share is at the
    pole-class. -/
theorem atBot_of_stateToolFits [∀ a : Contrib, Decidable (AtBot a)]
    {w : G.Weld} (hfits : G.StateToolFits w) :
    AtBot (G.share w) := by
  by_cases hshare : AtBot (G.share w)
  · exact hshare
  · exact False.elim (hfits hshare)

/-- With decidability of the one pole-class comparison, pole-typing is an
    exact iff. -/
theorem stateToolFits_iff_atBot [∀ a : Contrib, Decidable (AtBot a)]
    (w : G.Weld) :
    G.StateToolFits w ↔ AtBot (G.share w) :=
  ⟨G.atBot_of_stateToolFits, G.stateToolFits_of_atBot⟩

/-- Terminus responses are reducible in the corollary's sense. -/
theorem stateToolFits_of_terminus_response
    {b : G.Being} {c : G.Call} {r : G.Response}
    (hterm : G.Terminus b) (hresp : G.respondsTo b c = some r) :
    G.StateToolFits ⟨b, c, r⟩ :=
  G.no_self_pole_index_of_terminus_response hterm hresp

/-- If the state-tool fits a reception, the WAA-ownership-face cannot fire there. -/
theorem no_waa_ownershipFace_of_stateToolFits
    {deed reception : G.Weld} (hfits : G.StateToolFits reception) :
    ¬ G.waa_OwnershipFace deed reception :=
  fun hown => hfits hown.right

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
inductive waa_OwnershipOffice
  | waa_cetana
  | waa_reception
  | waa_practice
  | waa_remorse
  | waa_absolution
  | waa_dedication

namespace waa_OwnershipOffice

variable {Contrib : Type} [PreorderBot Contrib] {G : Grid Contrib}

/-- Each office is discharged at a weld's act-time tier (the office
    argument is unused). The paper's further claim — discharged *not by a
    cross-gap state* — is architectural, carried by what `Config` does not
    contain and by the absence of any `Config`-consuming discharge
    function; it is not this definition's proposition. -/
def dischargeTier (_office : waa_OwnershipOffice) (w : G.Weld) : Grid.Tier G :=
  Grid.Tier.actTime w

theorem dischargeTier_actTime (office : waa_OwnershipOffice) (w : G.Weld) :
    office.dischargeTier w = Grid.Tier.actTime w := rfl

/-- Discharging an office at act-time has exactly the weld's live nonzero-share
    condition. -/
theorem dischargeTier_hasNonzeroShare_iff
    (office : waa_OwnershipOffice) (w : G.Weld) :
    Grid.Tier.hasNonzeroShare G (office.dischargeTier w) ↔
      G.HasSelfPoleIndex w :=
  Iff.rfl

end waa_OwnershipOffice

/-- Contemporary positions placed by `Paper/Proofs.md`. -/
inductive ContemporaryPosition
  | siderits
  | ganeri
  | zahavi
  | sartre

/-- Their grid placement. -/
inductive ContemporaryPlacement
  | seriesQuestions
  | nearestAlly
  | retype
  | occupant

namespace ContemporaryPosition

/-- The grid placement assigned to each contemporary position in the paper. -/
def waa_placement : ContemporaryPosition → ContemporaryPlacement
  | .siderits => .seriesQuestions
  | .ganeri => .nearestAlly
  | .zahavi => .retype
  | .sartre => .occupant

example :
    waa_placement ContemporaryPosition.siderits = ContemporaryPlacement.seriesQuestions := rfl

example :
    waa_placement ContemporaryPosition.ganeri = ContemporaryPlacement.nearestAlly := rfl

example :
    waa_placement ContemporaryPosition.zahavi = ContemporaryPlacement.retype := rfl

example :
    waa_placement ContemporaryPosition.sartre = ContemporaryPlacement.occupant := rfl

end ContemporaryPosition

namespace Grid

variable {Contrib : Type} [PreorderBot Contrib]
variable (G : Grid Contrib)

/- Encoding check: the `retype` constructor exists and applies to any pair
   of distinctions (used by the Zahavi placement and the disposition/act
   redrawing). An `example`, not a theorem, for the same reason the voice
   and placement checks are. -/
example
    (oldDistinction newDistinction : Distinction G) :
    ∃ out : GeneratorOutcome G,
      out = GeneratorOutcome.retype oldDistinction newDistinction :=
  ⟨GeneratorOutcome.retype oldDistinction newDistinction, rfl⟩

end Grid

/- ==============================================================================
   §5  Disclaimers
============================================================================== -/

/-- The thirty-four original moves enumerated in `Paper/Proofs.md`. -/
inductive Disclaimer
  | tieringSeparateFuse
  | shoAgencyLent
  | forMeNessInWeld
  | receptionReachBack
  | threeRegisterSorting
  | linjiReading
  | shoVersusSatori
  | genjoArrivals
  | waa_karmaIdentification
  | weldTokenReflexivity
  | mmk17Decomposition
  | stoneOutsideEdge
  | generatedTaxonomy
  | twoErrorGrades
  | shareDropEvent
  | theoryStatus
  | rowTwoIndexPlacement
  | shareDetermination
  | dispositionActRetype
  | passiveSpent
  | clenchSelfShare
  | vacuityFromField
  | memoryPrudence
  | dukkhaFieldSide
  | asymmetricDomain
  | transposition
  | mirrorTerminus
  | threeKillings
  | officesSpine
  | contemporaryPlacement
  | hakuinReading
  | retypeOutcome
  | svakarmaDemotion
  | orthogonalityPrice

namespace Disclaimer

/-- Preserve the paper's numbering without making the number itself carry
    doctrinal weight. -/
def number : Disclaimer → Nat
  | .tieringSeparateFuse => 1
  | .shoAgencyLent => 2
  | .forMeNessInWeld => 3
  | .receptionReachBack => 4
  | .threeRegisterSorting => 5
  | .linjiReading => 6
  | .shoVersusSatori => 7
  | .genjoArrivals => 8
  | .waa_karmaIdentification => 9
  | .weldTokenReflexivity => 10
  | .mmk17Decomposition => 11
  | .stoneOutsideEdge => 12
  | .generatedTaxonomy => 13
  | .twoErrorGrades => 14
  | .shareDropEvent => 15
  | .theoryStatus => 16
  | .rowTwoIndexPlacement => 17
  | .shareDetermination => 18
  | .dispositionActRetype => 19
  | .passiveSpent => 20
  | .clenchSelfShare => 21
  | .vacuityFromField => 22
  | .memoryPrudence => 23
  | .dukkhaFieldSide => 24
  | .asymmetricDomain => 25
  | .transposition => 26
  | .mirrorTerminus => 27
  | .threeKillings => 28
  | .officesSpine => 29
  | .contemporaryPlacement => 30
  | .hakuinReading => 31
  | .retypeOutcome => 32
  | .svakarmaDemotion => 33
  | .orthogonalityPrice => 34

example :
    number Disclaimer.waa_karmaIdentification = 9 := rfl

example :
    number Disclaimer.orthogonalityPrice = 34 := rfl

end Disclaimer

end WAA
