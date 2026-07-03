/-
================================================================================
  The Weld and the Arrow — III. Proofs
  Checked anti-reduction layer for `Paper/Proofs.md`
================================================================================

This file formalizes the part of the paper that is most naturally checkable:
the typed anti-reduction argument, the five-collapse bookkeeping, the
sower/reaper split, the act/fact boundary used against supervenience, the
office-spine, the pole-reducibility corollary, and the enumerated disclaimers.

As in the earlier files, the prose claims that are genuinely meta-level typing
discipline are kept as type signatures plus small theorems over those
signatures. The file does not pretend that Siderits, Austin, Zahavi, or the
canonical texts are Lean hypotheses; it gives the internal grid-shape the paper
uses when addressing them.
-/

import WeldAndArrow.Theorems

namespace WAA

/- ==============================================================================
   §0  The five collapses as public bookkeeping
============================================================================== -/

/-- The five replies the anti-reduction argument must block. -/
inductive CollapseKind
  | verbal
  | soul
  | process
  | diachronic
  | supervenience

/-- The corresponding blocking move, named at the same abstraction level as
    `Paper/Proofs.md`: act-time ownership, no stored bearer, token-reflexivity,
    delivery-plus-reach-back, and act/fact typing. -/
inductive CollapseBlock
  | actTimeOwnership
  | noStoredBearer
  | tokenReflexivity
  | deliveryReachBackSplit
  | actFactTyping

namespace CollapseKind

/-- The paper's five-collapse map. -/
def blockedBy : CollapseKind → CollapseBlock
  | .verbal        => .actTimeOwnership
  | .soul          => .noStoredBearer
  | .process       => .tokenReflexivity
  | .diachronic    => .deliveryReachBackSplit
  | .supervenience => .actFactTyping

theorem verbal_blockedBy :
    blockedBy CollapseKind.verbal = CollapseBlock.actTimeOwnership := rfl

theorem soul_blockedBy :
    blockedBy CollapseKind.soul = CollapseBlock.noStoredBearer := rfl

theorem process_blockedBy :
    blockedBy CollapseKind.process = CollapseBlock.tokenReflexivity := rfl

theorem diachronic_blockedBy :
    blockedBy CollapseKind.diachronic = CollapseBlock.deliveryReachBackSplit := rfl

theorem supervenience_blockedBy :
    blockedBy CollapseKind.supervenience = CollapseBlock.actFactTyping := rfl

end CollapseKind

/- ==============================================================================
   §1  Field-only reduction and the malformed verdict
============================================================================== -/

namespace Grid

variable {Contrib : Type} [WeakOrderBot Contrib]
variable (G : Grid Contrib)

/-- A field-fact in the reductionist's sense: the call and response left when
    the agent-index is forgotten. -/
abbrev FieldFact : Type := G.Call × G.Response

/-- A field-only reducer is the state-tool the paper targets: it tries to recover
    an agent-index from field-facts alone. -/
abbrev FieldReducer : Type := G.FieldFact → G.Being

/-- Correctness for a field-only reducer. This is the honest internal version of
    "read karma off the field": for every actual weld, the reducer must recover
    the very index projected from that weld. -/
def CorrectFieldReducer (recover : G.FieldReducer) : Prop :=
  ∀ w : G.Weld, G.Actual w → recover (G.fieldOf w) = G.index w

/-- A correct field-only reducer cannot distinguish two actual welds with the
    same field residue; it must assign them the same index. -/
theorem correctFieldReducer_forces_same_index_of_same_field
    {recover : G.FieldReducer} (hrec : G.CorrectFieldReducer recover)
    {w₁ w₂ : G.Weld} (h₁ : G.Actual w₁) (h₂ : G.Actual w₂)
    (hfield : G.fieldOf w₁ = G.fieldOf w₂) :
    G.index w₁ = G.index w₂ :=
  calc
    G.index w₁ = recover (G.fieldOf w₁) := (hrec w₁ h₁).symm
    _ = recover (G.fieldOf w₂) := congrArg recover hfield
    _ = G.index w₂ := hrec w₂ h₂

/-- If two actual welds share the field residue but differ in index, no
    field-only reducer can be correct. This is the general checked form of
    "malformed, not merely hard". -/
theorem no_correctFieldReducer_of_same_field_distinct_index
    {w₁ w₂ : G.Weld} (h₁ : G.Actual w₁) (h₂ : G.Actual w₂)
    (hfield : G.fieldOf w₁ = G.fieldOf w₂)
    (hne : G.index w₁ ≠ G.index w₂) :
    ¬ ∃ recover : G.FieldReducer, G.CorrectFieldReducer recover :=
  fun hex =>
    hex.elim (fun _recover hrec =>
      hne (G.correctFieldReducer_forces_same_index_of_same_field
        hrec h₁ h₂ hfield))

/-- The concrete same-call/same-response witness used in the prose: two
    different beings can actually answer the same call with the same response,
    and the field residue cannot say which one acted. -/
theorem no_correctFieldReducer_of_same_call_response
    (a₁ a₂ : G.Being) (c : G.Call) (r : G.Response)
    (h₁ : G.Actual ⟨a₁, c, r⟩) (h₂ : G.Actual ⟨a₂, c, r⟩)
    (hne : a₁ ≠ a₂) :
    ¬ ∃ recover : G.FieldReducer, G.CorrectFieldReducer recover :=
  G.no_correctFieldReducer_of_same_field_distinct_index h₁ h₂ rfl hne

/- ==============================================================================
   §2  Sower/reaper, reach-back, and ownership-face
============================================================================== -/

/-- The report-face of "the sower reaps": delivery, and nothing more. -/
def ReportFace (deed reception : G.Weld) : Prop :=
  G.DeliveredTo deed reception

/-- The ownership-face: delivery reaches an actual reception and that reception
    appropriates. It is a deed at reception-time, not a standing relation. -/
def OwnershipFace (deed reception : G.Weld) : Prop :=
  G.LandsAt deed reception ∧ G.Appropriates reception

/-- A vacuous ownership attempt: the reception may appropriate, but the field
    drew no delivery-line from this deed to this reception. -/
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
   §3  Act/fact typing and token-reflexivity
============================================================================== -/

/-- Token-reflexivity in the narrow checked sense: the index is projected out of
    this very weld. The absence of a route from `Config` or field-facts into this
    projection is the type discipline enforced by `Theory.lean`. -/
def SelfAnchored (w : G.Weld) : Prop :=
  G.index w = w.agent

theorem selfAnchored (w : G.Weld) : G.SelfAnchored w := rfl

/-- The fact-like data the reducer is allowed to carry in the supervenience
    objection: field residues, and occurrence facts. The appropriating itself is
    not added as a new field constructor here. -/
inductive ReductionDatum
  | field (fact : G.FieldFact)
  | occurrence (w : G.Weld) (actual : G.Actual w)

namespace ReductionDatum

/-- Whether a reducer datum still contains a live act-index. Field-facts never
    do; occurrence facts do exactly when the occurrence's own share is nonzero. -/
def HasActIndex : ReductionDatum G → Prop
  | .field _ => False
  | .occurrence w _ => G.HasSelfPoleIndex w

theorem field_has_noActIndex (fact : G.FieldFact) :
    ¬ HasActIndex (G := G) (ReductionDatum.field fact) :=
  fun h => h

theorem occurrence_hasActIndex_iff
    (w : G.Weld) (hactual : G.Actual w) :
    HasActIndex (G := G) (ReductionDatum.occurrence w hactual) ↔
      G.HasSelfPoleIndex w :=
  Iff.rfl

theorem occurrence_has_noActIndex_of_shareZero
    {w : G.Weld} (hactual : G.Actual w) (hshare : G.share w = shareZero) :
    ¬ HasActIndex (G := G) (ReductionDatum.occurrence w hactual) :=
  G.no_self_pole_index_of_shareZero w hshare

end ReductionDatum

/- ==============================================================================
   §4  Pole-reducibility and the verdict's own tier
============================================================================== -/

/-- The state-tool fits exactly when no live self-pole index remains. -/
def StateToolFits (w : G.Weld) : Prop :=
  ¬ G.HasSelfPoleIndex w

/-- Share-zero is the constructive direction of the pole-reducibility corollary:
    no self-pole index remains for a state-tool to miss. -/
theorem stateToolFits_of_shareZero
    {w : G.Weld} (hshare : G.share w = shareZero) :
    G.StateToolFits w :=
  G.no_self_pole_index_of_shareZero w hshare

/-- With decidable equality on the contribution scale, the corollary can be read
    as an iff: the state-tool fits just where the share is zero. -/
theorem shareZero_of_stateToolFits [DecidableEq Contrib]
    {w : G.Weld} (hfits : G.StateToolFits w) :
    G.share w = shareZero := by
  by_cases hshare : G.share w = shareZero
  · exact hshare
  · exact False.elim (hfits hshare)

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

/-- The malformed verdict is never a floor-collapse. -/
theorem malformed_not_floor_claim (d : Distinction G) :
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
   §5  The office-spine and contemporary placements
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

theorem dischargeTier_hasArrogation_iff
    (office : OwnershipOffice) (w : G.Weld) :
    Grid.Tier.hasArrogation G (office.dischargeTier w) ↔
      G.HasSelfPoleIndex w :=
  Iff.rfl

end OwnershipOffice

/-- Contemporary positions placed by the third paper. -/
inductive ContemporaryPosition
  | ganeri
  | zahavi
  | sartre

/-- Their grid placement. -/
inductive ContemporaryPlacement
  | nearestAlly
  | retype
  | occupant

namespace ContemporaryPosition

def placement : ContemporaryPosition → ContemporaryPlacement
  | .ganeri => .nearestAlly
  | .zahavi => .retype
  | .sartre => .occupant

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
   §6  Scoped verdicts and the disclaimers
============================================================================== -/

/-- The anti-reduction verdict fires only when a designation routes through a
    self-index; field-only designations stay hard or easy, but not malformed in
    this paper's sense. -/
inductive DesignationRoute
  | selfIndex
  | fieldOnly

namespace DesignationRoute

def VerdictFires : DesignationRoute → Prop
  | .selfIndex => True
  | .fieldOnly => False

theorem verdict_fires_for_selfIndex :
    VerdictFires DesignationRoute.selfIndex :=
  trivial

theorem verdict_does_not_fire_for_fieldOnly :
    ¬ VerdictFires DesignationRoute.fieldOnly :=
  fun h => h

end DesignationRoute

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
  | malformedVerdict
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
  | actFactTyping
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
  | .malformedVerdict => 9
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
  | .actFactTyping => 29
  | .contemporaryPlacement => 30
  | .hakuinReading => 31
  | .retypeOutcome => 32
  | .svakarmaDemotion => 33
  | .orthogonalityPrice => 34

theorem malformedVerdict_number :
    number Disclaimer.malformedVerdict = 9 := rfl

theorem poleReducibility_carried_by_orthogonalityPrice :
    number Disclaimer.orthogonalityPrice = 34 := rfl

end Disclaimer

end WAA
