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

import WeldAndArrow.Sraddha

/-
================================================================================
  §C Commentary
================================================================================

C.0 Naming and Scope

Names beginning `Waa` mark identifiers whose names assert the paper's
identification content: ownership, appropriation, whose-ness, reach-back, or
sowing-side aiming/dedication. Unprefixed names remain the neutral delivery,
order, token-projection, and tier-placement vocabulary. `Grid.DirectedConvention`
marks vocabulary that consumes the directional reading of `conditions`; the
primitive signature itself does not add asymmetry, irreflexivity, or transitivity
axioms to `conditions`.

C.1 Theory.lean

`Config` is the formal place where "nothing self-indexed is stored" is enforced:
it carries only a `Contrib`-valued tendency and no owner, being, or weld field.
This is the type-level version of the paper's internal mis-feed discipline.

Seeds, potency, and environs talk in the paper are read here as field-side
delivery lines (`conditions`) and candidate receptions, not as capacities stored
in a being. The alaya/bija-as-stored-state reading is deliberately not taken.

The direction-freedom of `conditions` is a modelling decision tied to Theory:
Karma, "The arrow retyped: direction as display". `ConditionsEither` records the
symmetrized field fact, while `Grid.DirectedConvention` names the reading layer
that consumes ordered roles. The thermodynamic/arrow-of-time gloss motivates the
reading but is never a premise of a theorem.

`RawWeld`, `Grid.index`, and `Grid.share` encode the MMK 8 point that there is no
separate prior act or performer inside the formal signature: the index and share
are projections from a completed weld. `no_agent_recovery_of_field_collision`
is the internal recovery obstruction corresponding to that gloss.

The hand-rolled `Preorder` is used for dependency-freedom and to keep the exact
assumptions visible. Mathlib has the counterparts `Preorder`, `OrderBot`, and
`IsBot`; the local `AtBot` is the order-class of the chosen bottom and is
equivalent in role to Mathlib's `IsBot` predicate for that element.

There is no `PreorderTop`: the solipsist/total-share gloss in the paper is an
asymptote, not an attained element. By contrast, `PreorderBot` supplies an
attained bottom so `AtBot` can express the share-zero pole as an order-class.

`Stone`, `Terminus`, `AtPoleClass`, and `stone_is_terminus_vacuously` implement
the function/share split discussed in Theory: Attainment. A stone has no mounted
response; a terminus has mounted responses whose grade lies at the pole-class.

`rePitch` keeps `_before` in the signature because the operation is conceptually
on a prior configuration, even though the current simple implementation depends
only on the received weld. `IsShareDrop` is the strict order comparison
`Strict (G.share received) before.tendency`.

The `BeingConvention` namespace records the reading in which fine tags may be
diagnosed as macro beings. Its examples accommodate the paper's sentient,
hare's-horn, buddha, and generated-boundary cases without adding a privileged
partition to `Grid`.

The separate/fuse interface (`ClaimLanguage`, `Distinction`,
`RecordedUtterance`, `Tier`) is the small formal surface needed for the fox,
Baizhang, shō/shu, genjō, and verdict-tier discussions. The formal module keeps
only the abstract interface; this commentary retains the textual motivation.

C.2 Theorems.lean

The theorem layer proves consequences of the definitions: function/share facts,
share-drop obstruction at the pole, delivery and landing projections, tier
diagnostics, and the generated table rows. The paper's readings of these facts
live here as commentary only; the theorem statements consume only the neutral
definitions.

The strictness facts are now in `Theory.lean` as `Strict`, `strict_irrefl`,
`not_strict_of_orderEq`, and `no_strict_of_all_orderEq`. The arrow-of-time gloss
uses `Grid.DirectedConvention.TimeDirection`, an abbreviation of `Strict`.
`strict_shareBot_of_hasSelfPoleIndex` and its re-rooted
`timeDirection_of_hasSelfPoleIndex` reading make a live share itself the
direction witness against bottom. `DirectionVoid` names the absence of any
strict comparison, while `AllStone` names the grid-wide absence of response
function.

`RowTag`, `RowClaim`, `rowLanguage`, and `rowOf` now generate the table's
schema rows with pole-affirming semantics. `beforeAfterRow`, `beingsRow`, and
`gridLensRow` are compatibility names for `.layer` tags in that schema. Their
collapse and freeze checks remain hypothesis-free; their obedience theorems
carry only the local `AtBot` stability needed for non-live genjo fusion. The
full row list is Lean data as `tableOrder`.

The `contentLayerLanguage` keeps the convention-live side as the live-share
condition and gives row-specific content to the denial side. Its obedience
theorems are aptness-conditional by design: where the denial is simply true,
the convention row should not be held. This track deliberately keeps
`LayerClaim`: global denials such as all-stone or direction-void cannot be
made pole-affirming by truth at a particular genjo weld. `RecordedUtterance`
supplies the actuality needed for the content utterance checks, while
`denied_misfits_live_offer` and `fox_utterance_misfits_live_offer` perform the
same live-tier check for the schema language.

The `reEmptied` transformer and `ladder` iterate the separate/fuse rule without
adding a claim that quantifies over all levels. `ErrorFree`,
`reEmptied_obeys_of_errorFree`, and `ladder_obeys_of_errorFree` record the
refutation-only route by which the implemented `finalBelow` side lets the
ladder climb without an added stability premise above the seed. The "completed
ladder" remains an instructive absence: level quantification appears only in
meta-theorems such as `ladder_obeys`, `no_level_final`, and the existential
guard `no_final_level`. Concrete witnesses such as
`shareZero_not_functionZero_witness`, `rung_not_pole_witness`, and
`standing_does_not_determine_dated` keep the row anchors model-checked.

C.3 Invariance.lean

`DisplayReparam` is the admission criterion for predicates that mention the
contribution carrier: they must transport across order-preserving and
pole-preserving changes of display convention. This is the formal counterpart
of treating contribution values as display conventions rather than operational
tokens.

The `InvarianceNegative` example explains why equality with the chosen bottom
is not the system predicate: equality-to-bottom fails to transport, while
`AtBot` and `Terminus` do.

`DirectionNegative` is the countermodel behind Theory: Karma, "the arrow
retyped": two grids agree on `ConditionsEither` and disagree on `conditions`, so
the symmetric field structure does not recover direction. The physics and
thermodynamics language motivates the reading, but no theorem depends on it.

`BeingNegative` is the parallel countermodel for designation: one fine grid
admits both merge and split macro readings, so a unique being-boundary is not
recoverable from the grid data alone.

`ContentNegative` supplies the countermodels for the aptness hypotheses on
content rows: an all-stone/no-live grid and the two-bottom direction-void
carrier make the relevant denials true at non-live act-time, so fusion fails
there.

`SelfLineWitness` records that self-lines are permitted by the signature. The
paper's shushō-ittō discussion is a reading of that permission, not an axiom.

C.4 FourTruths.lean and Sraddha.lean

`MismatchGrade` is definitionally `share`; this is the formal honesty clause
for dukkha-talk as covariation rather than a second measure. `MismatchLive`
adds occurrence actuality to the self-pole-index condition, so stones fall
outside the domain by `not_actual_of_stone`, and terminus responses fall to the
pole-class by the existing terminus theorem.

`SradAversionContext` treats sraddha reception per call: it packages a live
prior tendency and an actual live-mismatch reception, not a stored faith
possession. `SradFullyEnlightened` deliberately has two conjuncts: terminus
typing and universal shortfall closure for delivered deeds. The physician
simile belongs exactly there: the grid can prove `sradPathOught_conditional`,
but the antecedents are faith-shaped and are never discharged by field facts.

The negative witnesses keep that conditional honest. `SradNegative` shows that
dropping faith or dropping the live-aversion antecedent loses the landing, and
`OrthogonalityNegative` shows that a responsive terminus need not be
`SradFullyEnlightened`.
-/

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
def waaPlacement : ContemporaryPosition → ContemporaryPlacement
  | .siderits => .seriesQuestions
  | .ganeri => .nearestAlly
  | .zahavi => .retype
  | .sartre => .occupant

theorem siderits_waaPlacement :
    waaPlacement ContemporaryPosition.siderits = ContemporaryPlacement.seriesQuestions := rfl

theorem ganeri_waaPlacement :
    waaPlacement ContemporaryPosition.ganeri = ContemporaryPlacement.nearestAlly := rfl

theorem zahavi_waaPlacement :
    waaPlacement ContemporaryPosition.zahavi = ContemporaryPlacement.retype := rfl

theorem sartre_waaPlacement :
    waaPlacement ContemporaryPosition.sartre = ContemporaryPlacement.occupant := rfl

end ContemporaryPosition

namespace Grid

variable {Contrib : Type} [PreorderBot Contrib]
variable (G : Grid Contrib)

/- Encoding check: the `retype` constructor exists and applies to any pair
   of distinctions (used by the Zahavi placement and the disposition/act
   redrawing). An `example`, not a theorem, for the same reason the voice
   and placement checks are. -/
theorem retype_constructor_exists
    (oldDistinction newDistinction : Distinction G) :
    ∃ out : GeneratorOutcome G,
      out = GeneratorOutcome.retype oldDistinction newDistinction :=
  ⟨GeneratorOutcome.retype oldDistinction newDistinction, rfl⟩

end Grid

/- ==============================================================================
   §5  Disclaimers
============================================================================== -/

/-- The original moves plus the being-convention extension enumerated in
    `Paper/Proofs.md`. -/
inductive Disclaimer
  | tieringSeparateFuse
  | shoAgencyLent
  | forMeNessInWeld
  | receptionReachBack
  | threeRegisterSorting
  | linjiReading
  | shoVersusSatori
  | genjoArrivals
  | waaKarmaIdentification
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
  | beingConvention
  | pilotGeneratedRows
  | beingTrichotomy
  | hareHornRegister
  | modalRealismFreeze
  | aptnessConditionality
  | sraddhaConditional
  | faithBothConjuncts
  | generatedTableStructure
  | poleAffirmingSemantics
  | proseRows
  | errorFreeReading

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
  | .waaKarmaIdentification => 9
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
  | .beingConvention => 35
  | .pilotGeneratedRows => 36
  | .beingTrichotomy => 37
  | .hareHornRegister => 38
  | .modalRealismFreeze => 39
  | .aptnessConditionality => 40
  | .sraddhaConditional => 41
  | .faithBothConjuncts => 42
  | .generatedTableStructure => 43
  | .poleAffirmingSemantics => 44
  | .proseRows => 45
  | .errorFreeReading => 46

theorem waaKarmaIdentification_number :
    number Disclaimer.waaKarmaIdentification = 9 := rfl

theorem modalRealismFreeze_number :
    number Disclaimer.modalRealismFreeze = 39 := rfl

theorem aptnessConditionality_number :
    number Disclaimer.aptnessConditionality = 40 := rfl

theorem sraddhaConditional_number :
    number Disclaimer.sraddhaConditional = 41 := rfl

theorem faithBothConjuncts_number :
    number Disclaimer.faithBothConjuncts = 42 := rfl

theorem generatedTableStructure_number :
    number Disclaimer.generatedTableStructure = 43 := rfl

theorem poleAffirmingSemantics_number :
    number Disclaimer.poleAffirmingSemantics = 44 := rfl

theorem errorFreeReading_number :
    number Disclaimer.errorFreeReading = 46 := rfl

end Disclaimer

end WAA
