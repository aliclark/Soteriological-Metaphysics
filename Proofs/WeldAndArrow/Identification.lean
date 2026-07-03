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

variable {Contrib : Type} [WeakOrderBot Contrib]
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
   §2  Sower/reaper, reach-back, and ownership-face
============================================================================== -/

/-- The field-side report-face of "the sower reaps": the delivery line, before
    any act-time ownership is added. -/
def ReportFace (deed reception : G.Weld) : Prop :=
  G.DeliveredTo deed reception

/-- The full ownership-face: delivery reaches an actual reception and that
    reception appropriates. It is a deed at reception-time, not a standing
    relation. -/
def OwnershipFace (deed reception : G.Weld) : Prop :=
  G.LandsAt deed reception ∧ G.Appropriates reception

/-- A vacuous ownership attempt: the reception may appropriate, but the field
    drew no delivery-line from this deed to this reception, so it is not a full
    ownership-face for that deed. -/
def VacuousOwnershipFace (deed reception : G.Weld) : Prop :=
  G.ReachBackVacuous deed reception ∧ G.Actual reception ∧ G.Appropriates reception

/-- The ownership-face includes the report-face. -/
theorem reportFace_of_ownershipFace
    {deed reception : G.Weld} (h : G.OwnershipFace deed reception) :
    G.ReportFace deed reception :=
  h.left.left

/-- The ownership-face includes actual reception. -/
theorem actual_of_ownershipFace
    {deed reception : G.Weld} (h : G.OwnershipFace deed reception) :
    G.Actual reception :=
  h.left.right

/-- The ownership-face includes appropriation at reception-time. -/
theorem appropriation_of_ownershipFace
    {deed reception : G.Weld} (h : G.OwnershipFace deed reception) :
    G.Appropriates reception :=
  h.right

/-- Full landing plus appropriation introduces the ownership-face. -/
theorem ownershipFace_intro
    {deed reception : G.Weld}
    (hland : G.LandsAt deed reception) (happ : G.Appropriates reception) :
    G.OwnershipFace deed reception :=
  ⟨hland, happ⟩

/-- A vacuous reach-back cannot at the same time be a full ownership-face for
    that deed and reception. -/
theorem not_ownershipFace_of_vacuous
    {deed reception : G.Weld} (hv : G.ReachBackVacuous deed reception) :
    ¬ G.OwnershipFace deed reception :=
  fun hown => hv hown.left.left

/-- A vacuous ownership attempt is not a full ownership-face. -/
theorem not_ownershipFace_of_vacuousOwnershipFace
    {deed reception : G.Weld} (hv : G.VacuousOwnershipFace deed reception) :
    ¬ G.OwnershipFace deed reception :=
  G.not_ownershipFace_of_vacuous hv.left

/-- The diachronic whose-question decomposes into delivery plus fresh
    appropriation; no third cross-gap owner is part of this definition. -/
def DiachronicWhose (deed reception : G.Weld) : Prop :=
  G.DeliveredTo deed reception ∧ G.Appropriates reception

theorem diachronicWhose_iff_delivery_and_appropriation
    (deed reception : G.Weld) :
    G.DiachronicWhose deed reception ↔
      G.DeliveredTo deed reception ∧ G.Appropriates reception :=
  Iff.rfl

/- ==============================================================================
   §2  Token-reflexivity
============================================================================== -/

/-- Token-reflexivity in the narrow checked sense: the index is projected out of
    this very weld. The absence of a route from `Config` or field-facts into this
    projection is the type discipline enforced by `Theory.lean`. -/
def SelfAnchored (w : G.Weld) : Prop :=
  G.index w = w.agent

theorem selfAnchored (w : G.Weld) : G.SelfAnchored w := rfl

/- ==============================================================================
   §3  Pole-typing and the verdict's own tier
============================================================================== -/

/-- The state-tool fits exactly when no live self-pole index remains. -/
def StateToolFits (w : G.Weld) : Prop :=
  ¬ G.HasSelfPoleIndex w

/-- Share-zero is the constructive direction of the pole-typing corollary:
    no self-pole index remains for a state-tool to miss. -/
theorem stateToolFits_of_shareZero
    {w : G.Weld} (hshare : G.share w = shareZero) :
    G.StateToolFits w :=
  G.no_self_pole_index_of_shareZero w hshare

/-- With decidable equality on the contribution scale, pole-typing can be read
    as an iff: the state-tool fits just where the share is zero. -/
theorem shareZero_of_stateToolFits [DecidableEq Contrib]
    {w : G.Weld} (hfits : G.StateToolFits w) :
    G.share w = shareZero := by
  by_cases hshare : G.share w = shareZero
  · exact hshare
  · exact False.elim (hfits hshare)

/-- With decidable equality on the contribution scale, pole-typing is an
    exact iff. -/
theorem stateToolFits_iff_shareZero [DecidableEq Contrib] (w : G.Weld) :
    G.StateToolFits w ↔ G.share w = shareZero :=
  ⟨G.shareZero_of_stateToolFits, G.stateToolFits_of_shareZero⟩

/-- Terminus responses are reducible in the corollary's sense. -/
theorem stateToolFits_of_terminus_response
    {b : G.Being} {c : G.Call} {r : G.Response}
    (hterm : G.Terminus b) (hresp : G.respondsTo b c = some r) :
    G.StateToolFits ⟨b, c, r⟩ :=
  G.no_self_pole_index_of_terminus_response hterm hresp

/-- If the state-tool fits a reception, the ownership-face cannot fire there. -/
theorem no_ownershipFace_of_stateToolFits
    {deed reception : G.Weld} (hfits : G.StateToolFits reception) :
    ¬ G.OwnershipFace deed reception :=
  fun hown => hfits hown.right

/-- A floor-tier diagnosis cannot be a mis-feed, since the floor carries no live
    arrogation. -/
theorem misfeed_not_floor_claim (d : Distinction G) :
    ¬ d.Collapse (Tier.floor : Tier G) :=
  G.not_collapse_floor d

/-- A distinction obeying the separate/fuse rule fuses at the floor. -/
theorem verdict_fuses_at_floor
    {d : Distinction G} (h : d.ObeysSeparateFuse) :
    d.Fused (Tier.floor : Tier G) :=
  G.fused_of_obeysSeparateFuse h Tier.floor

/-- The same distinction separates at live act-time diagnosis. -/
theorem verdict_separates_at_actTime
    {d : Distinction G} (h : d.ObeysSeparateFuse)
    {w : G.Weld} (hidx : G.HasSelfPoleIndex w) :
    d.Separated (Tier.actTime w) :=
  G.separated_of_obeysSeparateFuse h hidx

/- ==============================================================================
   §4  The office-spine and contemporary placements
============================================================================== -/

end Grid

/-- The offices karmic ownership holds in the paper's identity-claim. -/
inductive OwnershipOffice
  | cetana
  | reception
  | practice
  | remorse
  | absolution
  | dedication

namespace OwnershipOffice

variable {Contrib : Type} [WeakOrderBot Contrib] {G : Grid Contrib}

/-- Each office is discharged at a weld's act-time tier, not by a cross-gap
    state. -/
def dischargeTier (_office : OwnershipOffice) (w : G.Weld) : Grid.Tier G :=
  Grid.Tier.actTime w

theorem dischargeTier_actTime (office : OwnershipOffice) (w : G.Weld) :
    office.dischargeTier w = Grid.Tier.actTime w := rfl

/-- Discharging an office at act-time has exactly the weld's live-arrogation
    condition. -/
theorem dischargeTier_hasArrogation_iff
    (office : OwnershipOffice) (w : G.Weld) :
    Grid.Tier.hasArrogation G (office.dischargeTier w) ↔
      G.HasSelfPoleIndex w :=
  Iff.rfl

end OwnershipOffice

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
def placement : ContemporaryPosition → ContemporaryPlacement
  | .siderits => .seriesQuestions
  | .ganeri => .nearestAlly
  | .zahavi => .retype
  | .sartre => .occupant

theorem siderits_placement :
    placement ContemporaryPosition.siderits = ContemporaryPlacement.seriesQuestions := rfl

theorem ganeri_placement :
    placement ContemporaryPosition.ganeri = ContemporaryPlacement.nearestAlly := rfl

theorem zahavi_placement :
    placement ContemporaryPosition.zahavi = ContemporaryPlacement.retype := rfl

theorem sartre_placement :
    placement ContemporaryPosition.sartre = ContemporaryPlacement.occupant := rfl

end ContemporaryPosition

namespace Grid

variable {Contrib : Type} [WeakOrderBot Contrib]
variable (G : Grid Contrib)

/-- The taxonomy's fourth public outcome, used by the Zahavi placement and by
    the internal disposition/act redrawing, is available as a genuine generator
    outcome for any old/new distinction pair. -/
theorem retype_is_generatorOutcome
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
  | karmaIdentification
  | weldTokenReflexivity
  | mmk17Decomposition
  | stoneOutsideEdge
  | generatedTaxonomy
  | twoErrorGrades
  | kenshoEvent
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
  | .karmaIdentification => 9
  | .weldTokenReflexivity => 10
  | .mmk17Decomposition => 11
  | .stoneOutsideEdge => 12
  | .generatedTaxonomy => 13
  | .twoErrorGrades => 14
  | .kenshoEvent => 15
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

theorem karmaIdentification_number :
    number Disclaimer.karmaIdentification = 9 := rfl

theorem poleTyping_carried_by_orthogonalityPrice :
    number Disclaimer.orthogonalityPrice = 34 := rfl

end Disclaimer

end WAA
