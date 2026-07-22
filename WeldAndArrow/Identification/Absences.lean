/-
================================================================================
  WeldAndArrow.Identification.Absences
  Instructive absence enumeration and anchors
================================================================================

Reading and motivation: Identification/Commentary.lean, C.2a.
-/

import WeldAndArrow.Consequences.Ladder
import WeldAndArrow.Consequences.FoxCase
import WeldAndArrow.Doctrines.Sraddha
import WeldAndArrow.Doctrines.Icchantika
import WeldAndArrow.Doctrines.EthicsNegative
import WeldAndArrow.Identification.Ownership

namespace WAA

/- ------------------------------------------------------------------------------
   Routing table for arguments that formerly consumed function-zero Stone
------------------------------------------------------------------------------ -/

/-- Successor layers available after the function-zero stone edge retires. -/
inductive StoneSuccessorRoute where
  | sentienceMark
  | landingPattern
  | enactedDoors
  | universalFunction
deriving Repr, DecidableEq

/-- Paper-facing arguments whose old "stone mounts nothing" premise requires
    an explicit successor. -/
inductive RetiredStoneArgument where
  | deathFreeze
  | mirrorGloss
  | insentientPreaching
  | quietistArhat
deriving Repr, DecidableEq

/-- Audited routing for every retired stone argument named by the proposal. -/
def RetiredStoneArgument.successors : RetiredStoneArgument →
    List StoneSuccessorRoute
  | .deathFreeze => [.landingPattern, .universalFunction]
  | .mirrorGloss => [.landingPattern]
  | .insentientPreaching => [.universalFunction]
  | .quietistArhat => [.sentienceMark]

theorem deathFreeze_successors :
    RetiredStoneArgument.deathFreeze.successors =
      [.landingPattern, .universalFunction] := rfl

theorem mirrorGloss_successors :
    RetiredStoneArgument.mirrorGloss.successors = [.landingPattern] := rfl

theorem insentientPreaching_successors :
    RetiredStoneArgument.insentientPreaching.successors =
      [.universalFunction] := rfl

theorem quietistArhat_successors :
    RetiredStoneArgument.quietistArhat.successors = [.sentienceMark] := rfl

/- ==============================================================================
   Section 3 instructive absences
============================================================================== -/

/-- Whether a section 3 absence is still open or has been delivered and retained
    as a regression check.

    Membership and status are deliberately separate: `InstructiveAbsence`
    constructors track the paper's section 3 list, while `status` tracks the
    world-facing fact of whether an entry is still standing. Retiring another
    absence should change its status, not delete its constructor or renumber the
    list. -/
inductive AbsenceStatus where
  | standing
  | retiredAsCheck

/-- The section 3 instructive absences: gaps the system generates deliberately,
    each doing diagnostic work rather than marking a lacuna. -/
inductive InstructiveAbsence where
  /-- Empty cells in the Grade-1 table: not every distinction is symmetric.
      The diagnostic work is the table asymmetry itself; errors do not lie on a
      single line. -/
  | emptyCells
  /-- The declined case: the deaf-blind being receives no error verdict. The
      diagnostic work is the refusal to over-generate; the errors nearby belong
      to the diagnostician. -/
  | declinedCase
  /-- What the fox never tests: neither worked utterance occurs at the pole.
      The diagnostic work is to force the terminus question to be answered
      outside the paradigm case. -/
  | foxNeverTestsPole
  /-- The former third arrival: the never-clenched candidate is no third
      structural cell, but a pole weld typed by the supplied mark. The old
      absence remains as a regression check. -/
  | thirdArrival
  /-- Why calls land at all: receptive moments exist on the adaptive side and
      any landing occurs on the fixed-call side. The diagnostic work is to leave
      delivery ceded as a world-fact rather than a theorem manufactured by the
      grid. -/
  | whyCallsLand
  /-- The fourth truth withheld from the theory's voice: the grid displays the
      fourth-truth shape but does not utter the detached command. The diagnostic
      work is the no-value clause itself: room and shape, no pull. -/
  | fourthTruthWithheld
  /-- No stage immune to error: formerly registered as future work.  It is now
      retired as the checked production-level distinction between three-door
      arhat quiet and buddha no-nescience; neither predicate is a stored rank. -/
  | noSafeStage
  /-- Prudential privilege underivable: special first-personal authority over
      future concern is absent as a theorem. The diagnostic work is the
      forward-facing twin of the cross-gap whose being refused. -/
  | prudentialPrivilege
  /-- No measure over the grade: the order is partial and display-facing. The
      diagnostic work is to make the missing scalar deliberate; no probability
      or metric apparatus is owed over grade or delivery. -/
  | noMeasure
  /-- The icchantika declined: a being with live share at every actual weld
      (the terminus's inverse) is reachable as a receiver and un-seatable as an
      enlightened agent on its run, yet receives no permanent "cannot become
      buddha" verdict. The diagnostic work is the refusal to type foreclosure as
      a stored kind; defiance is a seed, not a rank. -/
  | icchantikaDeclined
  /-- The cosmology of rebirth — persistence across biological death, the
      realms, and the mechanism — is ceded as a world-fact. The grammar of
      ownerless continuation (continuity without a carried bearer; the flame
      passed without a self) remains in scope, derived from
      `nothing_selfIndexed_carried` and the field/re-pitch machinery. What is
      ceded includes persistence and the phenomenal sentience of later welds:
      the grid brackets the latter with a supplied per-weld reading.
      The diagnostic work is to mark this boundary rather than manufacture a
      theorem across it. -/
  | rebirthCosmology
  /-- No positive Truth or Thus predicate is defined at the floor. The floor is
      present only through silence, indiscernibility, and the negative
      pole/floor family. The diagnostic work is the registered refusal to turn
      degeneracy into a truth-maker. -/
  | floorTruthPredicate
  /-- The undefined/zero row retired when the function-zero edge retired. Its
      loss of an exemplar is retained as an instructive check, with the
      standing-sentience row occupying the generated-table position. -/
  | undefinedZeroRowRetired

namespace InstructiveAbsence

open Grid
open Grid.DirectedConvention
open Grid.DirectedConvention.BeingConvention
open Grid.DirectedConvention.BeingConvention.GridConvention

/-- Preserve the paper's section 3 order without making the number itself carry
    doctrinal weight. -/
def number : InstructiveAbsence → Nat
  | .emptyCells => 1
  | .declinedCase => 2
  | .foxNeverTestsPole => 3
  | .thirdArrival => 4
  | .whyCallsLand => 5
  | .fourthTruthWithheld => 6
  | .noSafeStage => 7
  | .prudentialPrivilege => 8
  | .noMeasure => 9
  | .icchantikaDeclined => 10
  | .rebirthCosmology => 11
  | .floorTruthPredicate => 12
  | .undefinedZeroRowRetired => 13

/-- Current world-facing status of each paper entry. Constructors remain the
    section 3 ledger; this function records retirement. -/
def status : InstructiveAbsence → AbsenceStatus
  | .thirdArrival => .retiredAsCheck
  | .noSafeStage => .retiredAsCheck
  | .icchantikaDeclined => .standing
  | .rebirthCosmology => .standing
  | .floorTruthPredicate => .standing
  | .undefinedZeroRowRetired => .retiredAsCheck
  | _ => .standing

theorem emptyCells_number :
    number InstructiveAbsence.emptyCells = 1 := rfl

theorem declinedCase_number :
    number InstructiveAbsence.declinedCase = 2 := rfl

theorem foxNeverTestsPole_number :
    number InstructiveAbsence.foxNeverTestsPole = 3 := rfl

theorem thirdArrival_number :
    number InstructiveAbsence.thirdArrival = 4 := rfl

theorem whyCallsLand_number :
    number InstructiveAbsence.whyCallsLand = 5 := rfl

theorem fourthTruthWithheld_number :
    number InstructiveAbsence.fourthTruthWithheld = 6 := rfl

theorem noSafeStage_number :
    number InstructiveAbsence.noSafeStage = 7 := rfl

theorem prudentialPrivilege_number :
    number InstructiveAbsence.prudentialPrivilege = 8 := rfl

theorem noMeasure_number :
    number InstructiveAbsence.noMeasure = 9 := rfl

theorem icchantikaDeclined_number :
    number InstructiveAbsence.icchantikaDeclined = 10 := rfl

theorem rebirthCosmology_number :
    number InstructiveAbsence.rebirthCosmology = 11 := rfl

theorem floorTruthPredicate_number :
    number InstructiveAbsence.floorTruthPredicate = 12 := rfl

theorem undefinedZeroRowRetired_number :
    number InstructiveAbsence.undefinedZeroRowRetired = 13 := rfl

theorem emptyCells_standing :
    status InstructiveAbsence.emptyCells = AbsenceStatus.standing := rfl

theorem declinedCase_standing :
    status InstructiveAbsence.declinedCase = AbsenceStatus.standing := rfl

theorem foxNeverTestsPole_standing :
    status InstructiveAbsence.foxNeverTestsPole = AbsenceStatus.standing := rfl

theorem thirdArrival_retired :
    status InstructiveAbsence.thirdArrival = AbsenceStatus.retiredAsCheck := rfl

theorem whyCallsLand_standing :
    status InstructiveAbsence.whyCallsLand = AbsenceStatus.standing := rfl

theorem fourthTruthWithheld_standing :
    status InstructiveAbsence.fourthTruthWithheld = AbsenceStatus.standing := rfl

theorem noSafeStage_retired :
    status InstructiveAbsence.noSafeStage = AbsenceStatus.retiredAsCheck := rfl

theorem prudentialPrivilege_standing :
    status InstructiveAbsence.prudentialPrivilege = AbsenceStatus.standing := rfl

theorem noMeasure_standing :
    status InstructiveAbsence.noMeasure = AbsenceStatus.standing := rfl

theorem icchantikaDeclined_standing :
    status InstructiveAbsence.icchantikaDeclined = AbsenceStatus.standing := rfl

theorem rebirthCosmology_standing :
    status InstructiveAbsence.rebirthCosmology = AbsenceStatus.standing := rfl

theorem floorTruthPredicate_standing :
    status InstructiveAbsence.floorTruthPredicate = AbsenceStatus.standing := rfl

theorem undefinedZeroRowRetired_retired :
    status InstructiveAbsence.undefinedZeroRowRetired =
      AbsenceStatus.retiredAsCheck := rfl

/- ------------------------------------------------------------------------------
   Anchors
------------------------------------------------------------------------------ -/

/-- Empty cells are table metadata rather than new grid semantics: the
    per-call/global row has no collapse occupant while its collapse and freeze
    refutations remain checked. -/
theorem emptyCells_anchor
    {Contrib : Type} [PreorderBot Contrib] (G : Grid Contrib) :
    hasCollapseOccupant RowTag.perCallGlobal = false ∧
      hasFreezeOccupant RowTag.perCallGlobal = true ∧
        (∀ t, ¬ (perCallGlobalRow G).Collapse t) ∧
          ¬ (perCallGlobalRow G).Freeze :=
  perCallGlobal_empty_collapse_cell_anchor (G := G)

/-- The concrete fox case never tests share-zero at any actual weld. -/
theorem foxNeverTestsPole_anchor :
    ∀ w : FoxCase.foxGrid.Weld,
      FoxCase.foxGrid.Actual w → ¬ AtBot (FoxCase.foxGrid.share w) :=
  FoxCase.fox_never_tests_pole

/-- Any recorded utterance in the concrete fox grid is away from share-zero,
    because recorded utterances carry actual welds. -/
theorem foxNeverTestsPole_recordedUtterance_not_atBot
    (u : Grid.RecordedUtterance FoxCase.foxGrid (rowLanguage FoxCase.foxGrid)) :
    ¬ AtBot (FoxCase.foxGrid.share u.weld) :=
  FoxCase.fox_never_tests_pole u.weld u.actual

/-- An actual fox-case weld is not made by an agent already in the pole-class:
    terminus typing would force share-zero. -/
theorem foxNeverTestsPole_actual_not_atPoleClass
    {w : FoxCase.foxGrid.Weld} (hactual : FoxCase.foxGrid.Actual w) :
    ¬ FoxCase.foxGrid.AtPoleClass w.agent := by
  intro hpole
  exact FoxCase.fox_never_tests_pole w hactual
    (FoxCase.foxGrid.atBot_of_terminus_response hpole hactual)

/-- Any recorded utterance in the concrete fox grid is away from the pole-class
    on its agent side. -/
theorem foxNeverTestsPole_recordedUtterance_not_atPoleClass
    (u : Grid.RecordedUtterance FoxCase.foxGrid (rowLanguage FoxCase.foxGrid)) :
    ¬ FoxCase.foxGrid.AtPoleClass u.weld.agent :=
  foxNeverTestsPole_actual_not_atPoleClass u.actual

/-- The old man's recorded answer remains the fox-row live-tier misfit anchor. -/
theorem foxNeverTestsPole_oldMan_misfit_anchor :
    FoxCase.oldManUtterance.MisfitsOfferedTier :=
  FoxCase.oldMan_utterance_misfits

/-- The delivered third arrival is on the scale at the pole and marked
    sentient only by the supplied clock reading. -/
theorem thirdArrival_sentient_at_pole :
    clockGrid.TerminusAct clockSentienceReading
      ⟨Clock.adaptive, Listener.present, Chime.chime⟩ :=
  sentient_pole_act_witness

/-- The retired absence is kept as the dukkha-free-by-construction check:
    a terminus response has no live mismatch. -/
theorem thirdArrival_not_clenchMismatch :
    ¬ clockGrid.ClenchMismatch
        ⟨Clock.adaptive, Listener.present, Chime.chime⟩ :=
  clockGrid.not_clenchMismatch_of_terminus_response adaptive_is_terminus rfl

/-- The fourth-truth anchor is still only an implication type: the grid proves
    the conditional and does not detach the injunction. -/
theorem fourthTruthWithheld_conditional
    {Contrib : Type} [PreorderBot Contrib] (G : Grid Contrib)
    (g : G.Being) (before : Config Contrib) (deed reception : G.Weld) :
    WaaPathOught G g before deed reception :=
  waaPathOught_conditional G g before deed reception

/-- The detached fourth-truth injunction is displayable, not assertable. -/
theorem fourthTruthWithheld_detached_voice :
    ErrorGrade.voice WaaDetachedOughtVoice = VerdictVoice.displayable :=
  waa_detached_ought_voice_displayable

/-- A terminal safe stage would be a final ladder level; the ladder theorem
    rules that out for an error-free seed. -/
theorem noSafeStage_anchor
    {Contrib : Type} [PreorderBot Contrib] {G : Grid Contrib}
    {d : Grid.Distinction G} (h : Grid.ErrorFree G d) :
    ¬ ∃ n, (ladder d n).Freeze :=
  no_final_level_of_errorFree (G := G) h

/-- The prudential-privilege absence is owned as theorem in the witness module,
    not promoted into a new table row. -/
theorem prudentialPrivilege_underivable_anchor :
    ¬ Grid.DirectedConvention.PrudentialPrivilegeNegative.PrudentialPrivilege :=
  Grid.DirectedConvention.PrudentialPrivilegeNegative.not_prudentialPrivilege

/-- The icchantika decline records the honest agent-side bar without turning it
    into a permanent foreclosure verdict. -/
theorem icchantikaDeclined_agent_anchor
    {Contrib : Type} [PreorderBot Contrib] {G : Grid Contrib} {b : G.Being}
    (h : Icchantika G b) :
    ¬ G.Terminus b ∧ ¬ WaaEffectiveTerminus G b :=
  ⟨icchantika_not_terminus (G := G) h,
    not_waaEffectiveTerminus_of_icchantika (G := G) h⟩

/-- The receiver-side half of the icchantika decline: actual icchantika
    receptions discharge the live-aversion antecedent. -/
theorem icchantikaDeclined_receiver_anchor
    {Contrib : Type} [PreorderBot Contrib] {G : Grid Contrib}
    {before : Config Contrib} {b : G.Being} {reception : G.Weld}
    (hagent : reception.agent = b) (hic : Icchantika G b)
    (hactual : G.Actual reception) (hlive : ¬ AtBot before.tendency) :
    WaaAversionContext G before reception :=
  aversionContext_of_icchantika_reception
    (G := G) hagent hic hactual hlive

/-- The concrete non-foreclosure witness is part of the absence anchor: the
    icchantika run does not recover a permanent "no landing ever" verdict. -/
theorem icchantikaDeclined_nonforeclosure_anchor :
    ∃ (before : Config Nat) (b : IcchantikaCase.grid.Being)
      (deed reception : IcchantikaCase.grid.Weld),
      Icchantika IcchantikaCase.grid b ∧
        reception.agent = b ∧
          IcchantikaCase.grid.Actual reception ∧
            ¬ AtBot before.tendency ∧
              DeliveredTo IcchantikaCase.grid deed reception ∧
                IcchantikaCase.grid.IsShareDrop before reception ∧
                  HasShareDropLanding IcchantikaCase.grid before deed :=
  icchantika_release_not_foreclosed

/-- The rebirth/cosmology boundary is deliberately only a standing ledger pin:
    it introduces no theorem about persistence, realms, or consciousness beyond
    the mounted-response domain. -/
theorem rebirthCosmology_anchor :
    status InstructiveAbsence.rebirthCosmology = AbsenceStatus.standing :=
  rebirthCosmology_standing

/-- The floor-truth refusal is anchored by the two apophatic pins: no row
    claim holds there, while every pair of row claims is indiscernible there. -/
theorem floorTruthPredicate_anchor
    {Contrib : Type} [PreorderBot Contrib] (G : Grid Contrib) :
    (∀ p : RowClaim, ¬ (rowLanguage G).Holds Tier.floor p) ∧
      ∀ p q : RowClaim,
        ((rowLanguage G).Holds Tier.floor p ↔
          (rowLanguage G).Holds Tier.floor q) :=
  ⟨no_row_claim_holds_at_floor G, floor_claims_indiscernible G⟩

/-- The removed edge-row leaves no constructor behind; the replacement table
    position is occupied by the standing-sentience row. -/
theorem undefinedZeroRowRetired_replacement_anchor :
    (tableOrder.drop 16).head? =
      some (TableRow.generated RowTag.standingSentience) := rfl

end InstructiveAbsence

end WAA
