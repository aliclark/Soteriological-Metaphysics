/-
================================================================================
  WeldAndArrow.Meta.AssumptionLedger
  Canonical assumption prose, checked anchors, and structural checks
================================================================================

The axiom-audit ledger keeps the compile-time tripwire for input-side
declarations. This ledger is the canonical source for the reader-facing
assumption prose and for the checked anchor metadata rendered to
`Exposition/Assumptions.md`.

Lean here buys internal consistency and derivability, not exclusivity or truth:
given the primitives the consequences follow without contradiction; it is not
shown that no other reconstruction would. The ledger and its axiom audit make
the “no added axioms” part concrete through `assumptionAxiomAudit` and
`#verify_axiom_audit`. Its declined entries — no `PreorderTop`, no privileged
person-partition, and direction/scalar as display — record the signature's
active refusal to privilege its own choices rather than a proof that rivals are
impossible.
-/

import Lean
import WeldAndArrow.Signature.Assumptions
import WeldAndArrow.Meta.AxiomAudit
import WeldAndArrow.Meta.InvarianceNegative
import WeldAndArrow.Identification.Ownership
import WeldAndArrow.Doctrines.FourTruths
import WeldAndArrow.Doctrines.EffectiveTerminusNegative
import WeldAndArrow.Doctrines.DoorsNegative

namespace WAA

/- ==============================================================================
   Ledger data
============================================================================== -/

inductive AssumptionSection
  | asserted
  | declined
  | convenience
deriving DecidableEq, Repr, BEq

namespace AssumptionSection

def key : AssumptionSection -> String
  | .asserted => "A"
  | .declined => "B"
  | .convenience => "C"

def label : AssumptionSection -> String
  | .asserted => "What Is Asserted"
  | .declined => "What Is Deliberately Declined"
  | .convenience => "Conveniences and Stand-Ins"

end AssumptionSection

inductive AnchorStatus
  | proof
  | witness
deriving DecidableEq, Repr, BEq

namespace AnchorStatus

def label : AnchorStatus -> String
  | .proof => "proof"
  | .witness => "witness"

end AnchorStatus

inductive AnchorLayer
  | signature
  | downstream
deriving DecidableEq, Repr, BEq

namespace AnchorLayer

def label : AnchorLayer -> String
  | .signature => "Signature"
  | .downstream => "Downstream"

end AnchorLayer

structure AssumptionAnchor where
  name : Lean.Name
  status : AnchorStatus
  layer : AnchorLayer
deriving Repr

structure AssumptionEntry where
  «section» : AssumptionSection
  number : Nat
  title : String
  statement : String
  anchors : List AssumptionAnchor
  note : Option String := none
deriving Repr

def sigProof (name : Lean.Name) : AssumptionAnchor :=
  { name, status := .proof, layer := .signature }

def sigWitness (name : Lean.Name) : AssumptionAnchor :=
  { name, status := .witness, layer := .signature }

def downProof (name : Lean.Name) : AssumptionAnchor :=
  { name, status := .proof, layer := .downstream }

def downWitness (name : Lean.Name) : AssumptionAnchor :=
  { name, status := .witness, layer := .downstream }

/-- The canonical assumption ledger in paper order. -/
def assumptionLedger : List AssumptionEntry := [
  { «section» := .asserted
    number := 1
    title := "No prior agent"
    statement := "A weld is the primitive occurrence. `Grid.index` and `Grid.share` are projections from a completed `RawWeld`, not fields recovered from a separate performer or act. `no_agent_recovery_of_field_collision` records the internal obstruction: the same call-response field residue can be produced by distinct actual agents."
    anchors := [
      sigProof ``RawWeld,
      sigProof ``Grid.index,
      sigProof ``Grid.share,
      sigWitness ``no_agent_recovery_of_field_collision
    ] },
  { «section» := .asserted
    number := 2
    title := "Nothing self-indexed is stored"
    statement := "`Config` stores only `tendency : Contrib`. It has no owner, being, weld, or field-residue slot. `rePitch` uses the received weld's share and ignores the prior configuration value. The checked claim is architectural and definability-level: the record has no `Being`-typed slot, relabelling agents acts trivially on configurations and commutes with `rePitch`, and no relabelling-equivariant recovery of an agent from a configuration exists. It is not an information-flow claim; see the declined entry below."
    anchors := [
      sigProof ``Config,
      sigProof ``Config.tendency,
      sigProof ``Grid.rePitch,
      sigProof ``RawWeld.mapAgent,
      downProof ``Config.relabel_fixed,
      downProof ``Grid.relabel_rePitch,
      downWitness ``Grid.no_natural_agent_recovery_from_config,
      downWitness ``ConfigLeakWitness.no_agent_recovery_from_config_of_share_collision
    ] },
  { «section» := .asserted
    number := 3
    title := "The self-pole index is just live share"
    statement := "`HasSelfPoleIndex w` is `not AtBot (share w)`, and when the predicate is live the carried `selfPoleIndex` is the weld's agent tag."
    anchors := [
      sigProof ``Grid.HasSelfPoleIndex,
      sigProof ``Grid.selfPoleIndex_eq_agent_of_hasSelfPoleIndex,
      sigProof ``Grid.no_self_pole_index_of_atBot
    ] },
  { «section» := .asserted
    number := 4
    title := "Stone and terminus split function from share"
    statement := "A `Stone` mounts no response. A `Terminus` may mount responses, but every mounted response is at the pole-class. `AtPoleClass` intentionally includes the vacuous stone case."
    anchors := [
      sigProof ``Grid.Stone,
      sigProof ``Grid.Terminus,
      sigProof ``Grid.AtPoleClass,
      sigProof ``Grid.stone_is_terminus_vacuously,
      sigWitness ``clockGrid_function_share_split_witness
    ] },
  { «section» := .asserted
    number := 5
    title := "Self-lines are permitted, not built in"
    statement := "The bare signature does not impose irreflexivity on `conditions`; a model may supply reflexive delivery, and then the directed vocabulary can read a self-line."
    anchors := [
      sigProof ``Grid.conditions,
      sigProof ``Grid.DirectedConvention.DeliveredTo,
      sigProof ``Grid.DirectedConvention.LandsAt,
      sigWitness ``AssumptionLocalWitnesses.signature_self_line_permitted,
      downWitness ``SelfLineWitness.selfLine_landsAt_self,
      downWitness ``SelfLineWitness.selfLine_waaOwnershipFace_self
    ] },
  { «section» := .declined
    number := 1
    title := "No arrow in `conditions`"
    statement := "The signature assumes no asymmetry, irreflexivity, or transitivity for `conditions`. `ConditionsEither` is the symmetric field fact; direction enters only in `Grid.DirectedConvention`. The downstream `DirectionNegative` witness elaborates this as non-recovery from symmetric closure."
    anchors := [
      sigProof ``Grid.ConditionsEither,
      sigProof ``Grid.conditionsEither_symm,
      sigProof ``Grid.DirectedConvention.TimeDirection,
      sigWitness ``Grid.transpose,
      sigWitness ``Grid.transpose_conditionsEither_iff,
      sigWitness ``Grid.DirectedConvention.transpose_deliveredTo_iff,
      sigWitness ``RawWeld.transposeCR,
      sigWitness ``AssumptionLocalWitnesses.no_direction_recovery_from_conditionsEither,
      sigWitness ``InteriorDirectionNegative.no_interior_direction_recovery,
      downWitness ``DirectionNegative.no_direction_recovery_from_conditionsEither
    ] },
  { «section» := .declined
    number := 2
    title := "No `PreorderTop`"
    statement := "The signature supplies only `PreorderBot`. The share-zero pole is an attained bottom order-class (`AtBot`); the total-share or solipsist pole is an asymptote, not an element of the interface. `StrongSelfConditioningTag` is named and shelved in the being convention for the same reason."
    anchors := [
      sigProof ``PreorderBot,
      sigProof ``AtBot,
      sigProof ``Grid.DirectedConvention.BeingConvention.BeingCoarsening.StrongSelfConditioningTag,
      sigWitness ``AssumptionLocalWitnesses.nat_preorderBot_has_no_top
    ] },
  { «section» := .declined
    number := 3
    title := "No privileged person-partition"
    statement := "A being boundary is supplied by a diagnosis-time `BeingCoarsening`, not stored as a field of `Grid`. The signature already admits both identity and total coarsenings for any grid; the downstream `BeingNegative` witness elaborates this as non-recovery of a unique partition from grid data."
    anchors := [
      sigProof ``Grid.DirectedConvention.BeingConvention.BeingCoarsening,
      sigProof ``Grid.DirectedConvention.BeingConvention.BeingCoarsening.InFiber,
      sigProof ``Grid.DirectedConvention.BeingConvention.BeingCoarsening.SameFiber,
      sigWitness ``Grid.DirectedConvention.BeingConvention.BeingCoarsening.id,
      sigWitness ``Grid.DirectedConvention.BeingConvention.BeingCoarsening.total,
      sigWitness ``Grid.DirectedConvention.BeingConvention.BeingCoarsening.total_sameFiber,
      sigWitness ``Grid.DirectedConvention.BeingConvention.BeingCoarsening.id_not_sameFiber_of_ne,
      sigWitness ``AssumptionLocalWitnesses.partition_merge_split_disagree,
      downWitness ``BeingNegative.no_partition_recovery
    ] },
  { «section» := .declined
    number := 4
    title := "Direction resolution is display, not signature furniture"
    statement := "A clock's finite delivery-axis resolution is supplied by a diagnosis-time `DirectionCoarsening`, not by a `Grid` field and not by any pole or legitimacy predicate."
    anchors := [
      sigProof ``Grid.DirectedConvention.DirectionCoarsening,
      sigProof ``Grid.DirectedConvention.DirectionCoarsening.SameTick,
      sigProof ``Grid.DirectedConvention.DirectionCoarsening.ResolutionBounded,
      sigProof ``Grid.DirectedConvention.DirectionCoarsening.no_timeDirection_within_tick,
      sigProof ``Grid.DirectedConvention.DirectionCoarsening.no_timeDirection_of_resolutionBounded_subsingleton,
      sigWitness ``Grid.DirectedConvention.DirectionCoarsening.transpose_subTickDelivery,
      downWitness ``DirectionCoarseningWitness.registerClock_unitTick_not_resolutionBounded,
      downWitness ``DirectionCoarseningWitness.unit_directionVoid_via_mergeToUnit,
      downWitness ``DirectionCoarseningWitness.fullyCoarseRegisterClock_no_timeDirection,
      downWitness ``DirectionCoarseningWitness.registerClock_directionCoarsening_independence
    ] },
  { «section» := .declined
    number := 5
    title := "Contribution values are display, not operational tokens"
    statement := "The Signature layer itself uses only order and pole vocabulary around `share`. The downstream `DisplayReparam` / `InvarianceNegative` modules give the full transport discipline: order- and pole-preserving display changes preserve the legal predicates, while equality to the chosen bottom does not."
    anchors := [
      sigProof ``Grid.share_eq_grade_check,
      sigProof ``AtBot,
      sigProof ``OrderEq,
      sigProof ``Grid.Terminus,
      downProof ``DisplayReparam,
      downProof ``DisplayReparam.atBot_iff,
      downWitness ``InvarianceNegative.oldEqTerminus_not_invariant
    ] },
  { «section» := .declined
    number := 6
    title := "The enlightenment ladder names standing and enacted vacuity"
    statement := "The operational, assertable effectiveness content is per-occurrence: `WaaEffectiveOccurrence` states an actual pole-deed landing as a share-drop against a live prior tendency. The descriptive universal `WaaEffectiveTerminus` remains legal as run-display and direct-path hypothesis, but no estimator from actual-run response/share data decides it. Standing `WaaFullyEnlightened` adds positive own-act-time `WaaNoNescience` over speech-or-mind productions. A quiet arhat may still fail that cognitive conjunct; sealed silent and true-thinking buddhas witness its two silent faces. `WaaFullyEnlightenedEnacted` separately adds an effective deed witness and a production-tied speech occurrence."
    anchors := [
      downProof ``Grid.DirectedConvention.WaaEffectiveOccurrence,
      downProof ``Grid.DirectedConvention.WaaEffectivenessEnacted,
      downProof ``Grid.DirectedConvention.not_effectivenessEnacted_of_undelivered,
      downProof ``Grid.DirectedConvention.WaaFullyEnlightened,
      downProof ``Grid.DirectedConvention.WaaNoNescience,
      downProof ``Grid.DirectedConvention.WaaFullyEnlightenedEnacted,
      downWitness ``FaithNegative.noNescience_strictly_stronger_witness,
      downWitness ``FaithNegative.arhat_retains_nescience_witness,
      downWitness ``FaithNegative.Sealed.silent_buddha_models,
      downWitness ``EffectiveTerminusNegative.actual_run_data_underdetermines_effectiveTerminus,
      downProof ``Grid.DirectedConvention.BeingConvention.GridConvention.waa_effective_occurrence_voice_assertable,
      downProof ``Grid.DirectedConvention.BeingConvention.GridConvention.waa_standing_effectiveness_voice_displayable
    ] },
  { «section» := .declined
    number := 7
    title := "No blanket noninterference for the contribution carrier"
    statement := "Grading may depend on the agent — `gradingCollisionGrid` grades by being deliberately (cetanā) — so a model's stored tendency may extensionally coincide with an agent tag; `registerClockGrid` witnesses the coincidence. The signature therefore declines the information-flow reading of non-storage. `Grid.rePitch_forgets` bounds the coincidence to a single reception's footprint: nothing accumulates into a diachronic bearer, and the configuration is fibered over no being. The asserted claim is typing plus relabelling equivariance."
    anchors := [
      sigWitness ``gradingCollisionGrid,
      sigWitness ``registerClockGrid,
      downWitness ``ConfigLeakWitness.registerClock_config_recovers_agent,
      downProof ``Config.relabel_fixed,
      downProof ``Grid.relabel_rePitch,
      downProof ``Grid.rePitch_forgets
    ] },
  { «section» := .declined
    number := 8
    title := "No recovered door boundary"
    statement := "`DoorReading` totally classifies fine welds as body, speech, or mind, but that diagnosis is supplied rather than recovered from response or grade data. Totality and adequacy to the canonical three doors are modeling claims."
    anchors := [
      downProof ``Grid.DoorReading,
      downWitness ``DoorsNegative.no_door_boundary_recovery
    ] },
  { «section» := .declined
    number := 9
    title := "No recovered voicing"
    statement := "`SpeechReading` supplies optional content independently of door. Thoughts and bodily intimations are representable, while only speech productions cross into testimony; neither voicing nor its production weld is recovered from visible grid data or content alone."
    anchors := [
      downProof ``Grid.SpeechReading,
      downProof ``Grid.ProducedUtterance,
      downWitness ``DoorsNegative.no_voicing_recovery,
      downWitness ``DoorsNegative.no_production_recovery
    ] },
  { «section» := .declined
    number := 10
    title := "No recovered view content"
    statement := "`ViewReading.ownerClaim` supplies which claims count as stored-owner views. The checked coarsening-freeze model is a correlation for one such reading, not a derivation of content from the grid."
    anchors := [
      downProof ``Grid.ViewReading,
      downWitness ``FettersNegative.no_view_content_recovery,
      downWitness ``FettersNegative.ownerClaim_coarsening_freeze_correlation
    ] },
  { «section» := .convenience
    number := 1
    title := "Hand-rolled order classes"
    statement := "`Preorder` and `PreorderBot` are hand-rolled to keep assumptions visible and dependency-free. They play the local role Mathlib order classes would play, without importing Mathlib."
    anchors := [
      sigProof ``Preorder,
      sigProof ``PreorderBot,
      sigProof ``shareBot,
      sigProof ``shareBot_le
    ] },
  { «section» := .convenience
    number := 2
    title := "`_before` is retained but currently ignored by `rePitch`"
    statement := "`rePitch` keeps a `_before` slot because the operation is conceptually a re-pitch from a prior configuration. The current implementation ignores that slot; the proof anchor below is a tripwire for the day that changes."
    anchors := [
      sigProof ``Grid.rePitch
    ]
    note := some "The signature file keeps an `rfl` example showing that two prior configurations produce the same re-pitch for the same received weld." },
  { «section» := .convenience
    number := 3
    title := "The scalar is display over a partial order"
    statement := "`WaaMismatchGrade` lives in `Doctrines`, so this Signature module does not import it; the Signature-side checked fact is that `share` is the only contribution value exported by a weld."
    anchors := [
      sigProof ``Grid.share,
      sigProof ``Grid.share_eq_grade_check,
      downProof ``Grid.WaaMismatchGrade,
      downProof ``Grid.waaMismatchGrade_eq_share
    ] },
  { «section» := .convenience
    number := 4
    title := "`Models.lean` witnesses are illustrative"
    statement := "The clock and register-clock models anchor possibility checks and taxonomy examples; they are not uniqueness claims."
    anchors := [
      sigWitness ``clockGrid,
      sigWitness ``registerClockGrid,
      sigWitness ``registerClock_macro_sentient,
      sigWitness ``registerClock_macro_selfConditioning
    ] }
]

/-- Audited declarations that are required to remain entirely axiom-free. -/
def assumptionAxiomAudit : List Lean.Name :=
  (axiomAuditLedger.filter (fun entry => entry.allowed.isEmpty)).map
    (fun entry => entry.name)

/- ==============================================================================
   Structural checks
============================================================================== -/

def assumptionSectionEntries (sec : AssumptionSection) :
    List AssumptionEntry :=
  assumptionLedger.filter (fun entry => entry.«section» == sec)

def assumptionTitles : List String :=
  assumptionLedger.map (fun entry => entry.title)

def assumptionNumberingContiguous (sec : AssumptionSection) : Bool :=
  let entries := assumptionSectionEntries sec
  entries.map (fun entry => entry.number) ==
    (List.range entries.length).map (fun n => n + 1)

example : (assumptionSectionEntries .asserted).length = 5 := rfl
example : (assumptionSectionEntries .declined).length = 10 := rfl
example : (assumptionSectionEntries .convenience).length = 4 := rfl

example : assumptionNumberingContiguous .asserted = true := by
  decide

example : assumptionNumberingContiguous .declined = true := by
  decide

example : assumptionNumberingContiguous .convenience = true := by
  decide

example : assumptionTitles.Nodup := by
  decide

/- ==============================================================================
   Anchor verifier
============================================================================== -/

open Lean Elab Command Meta

syntax (name := verifyAssumptionAnchors) "#verify_assumption_anchors" : command

unsafe def evalAssumptionEntries : Term.TermElabM (List AssumptionEntry) := do
  evalExpr (List AssumptionEntry)
    (mkApp (mkConst ``List [Level.zero]) (mkConst ``AssumptionEntry))
    (mkConst ``assumptionLedger)

unsafe def evalAssumptionAxiomAudit : Term.TermElabM (List Lean.Name) := do
  evalExpr (List Lean.Name)
    (mkApp (mkConst ``List [Level.zero]) (mkConst ``Lean.Name))
    (mkConst ``assumptionAxiomAudit)

@[command_elab verifyAssumptionAnchors] unsafe def elabVerifyAssumptionAnchors :
    CommandElab := fun _stx => do
  let entries <- liftTermElabM evalAssumptionEntries
  let axiomAudit <- liftTermElabM evalAssumptionAxiomAudit
  let env <- getEnv
  let mut missing : Array String := #[]
  for entry in entries do
    for anchor in entry.anchors do
      unless env.contains anchor.name do
        missing := missing.push
          s!"{entry.«section».key}.{entry.number} {entry.title}: {anchor.name}"
  for name in axiomAudit do
    unless env.contains name do
      missing := missing.push s!"axiom audit: {name}"
  unless missing.isEmpty do
    let details := missing.foldl (fun acc item => acc ++ "\n" ++ item) ""
    throwError m!"missing assumption anchors:{details}"

#verify_assumption_anchors

/- The rebirth/cosmology absence is intentionally a downstream, pin-level
   boundary rather than a Signature assumption or a positive theorem. -/
#check InstructiveAbsence.rebirthCosmology_standing
#check InstructiveAbsence.rebirthCosmology_anchor
-- Floor truth is deliberately absent; only silence and indiscernibility remain.
#check InstructiveAbsence.floorTruthPredicate_standing
#check InstructiveAbsence.floorTruthPredicate_anchor

end WAA
