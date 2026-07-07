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
  /-- The third arrival: the never-clenched candidate is delivered from the
      stone side. The diagnostic work now lives as a check: function mounted,
      no share ever claimed, dukkha-free by construction. -/
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
  /-- No stage immune to error: a terminal safe cell would be a rank. The
      diagnostic work is to keep even buddha-immunity per-call rather than
      possessed. -/
  | noSafeStage
  /-- Prudential privilege underivable: special first-personal authority over
      future concern is absent as a theorem. The diagnostic work is the
      forward-facing twin of the cross-gap whose being refused. -/
  | prudentialPrivilege
  /-- No measure over the grade: the order is partial and display-facing. The
      diagnostic work is to make the missing scalar deliberate; no probability
      or metric apparatus is owed over grade or delivery. -/
  | noMeasure
  /-- The icchantika declined: a non-stone being live at every mounted call
      (the terminus's inverse) is reachable as a receiver and un-seatable as an
      enlightened agent on its run, yet receives no permanent "cannot become
      buddha" verdict. The diagnostic work is the refusal to type foreclosure as
      a stored kind; defiance is a seed, not a rank. -/
  | icchantikaDeclined

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

/-- Current world-facing status of each paper entry. Constructors remain the
    section 3 ledger; this function records retirement. -/
def status : InstructiveAbsence → AbsenceStatus
  | .thirdArrival => .retiredAsCheck
  | .icchantikaDeclined => .standing
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

theorem noSafeStage_standing :
    status InstructiveAbsence.noSafeStage = AbsenceStatus.standing := rfl

theorem prudentialPrivilege_standing :
    status InstructiveAbsence.prudentialPrivilege = AbsenceStatus.standing := rfl

theorem noMeasure_standing :
    status InstructiveAbsence.noMeasure = AbsenceStatus.standing := rfl

theorem icchantikaDeclined_standing :
    status InstructiveAbsence.icchantikaDeclined = AbsenceStatus.standing := rfl

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
    actuality rules out the stone side, and terminus-typing would force
    share-zero. -/
theorem foxNeverTestsPole_actual_not_atPoleClass
    {w : FoxCase.foxGrid.Weld} (hactual : FoxCase.foxGrid.Actual w) :
    ¬ FoxCase.foxGrid.AtPoleClass w.agent := by
  intro hpole
  rcases hpole with hstone | hterm
  · exact FoxCase.foxGrid.not_stone_of_actual w hactual hstone
  · exact FoxCase.fox_never_tests_pole w hactual
      (FoxCase.foxGrid.atBot_of_terminus_response hterm hactual)

/-- Any recorded utterance in the concrete fox grid is away from the pole-class
    on its agent side. -/
theorem foxNeverTestsPole_recordedUtterance_not_atPoleClass
    (u : Grid.RecordedUtterance FoxCase.foxGrid (rowLanguage FoxCase.foxGrid)) :
    ¬ FoxCase.foxGrid.AtPoleClass u.weld.agent :=
  foxNeverTestsPole_actual_not_atPoleClass u.actual

/-- The old man's recorded answer remains the fox-row live-tier misfit anchor. -/
theorem foxNeverTestsPole_oldMan_misfit_anchor :
    ¬ FoxCase.oldManUtterance.FitsOfferedTier :=
  FoxCase.oldMan_utterance_misfits

/-- The delivered third arrival is the concrete function/share split: the
    adaptive responder mounts function while its received share is at bottom. -/
theorem thirdArrival_function_mounted_no_share :
    AtBot (clockGrid.share ⟨Clock.adaptive, Listener.present, Chime.chime⟩) ∧
      ¬ clockGrid.Stone Clock.adaptive :=
  shareZero_not_functionZero_witness

/-- The retired absence is kept as the dukkha-free-by-construction check:
    a terminus response has no live mismatch. -/
theorem thirdArrival_not_waaMismatchLive :
    ¬ clockGrid.WaaMismatchLive
        ⟨Clock.adaptive, Listener.present, Chime.chime⟩ :=
  clockGrid.not_waaMismatchLive_of_terminus_response adaptive_is_terminus rfl

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
  no_final_level (G := G) h

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
    ¬ G.Stone b ∧ ¬ G.Terminus b ∧ ¬ WaaFullyEnlightened G b :=
  ⟨icchantika_not_stone (G := G) h,
    icchantika_not_terminus (G := G) h,
    not_waaFullyEnlightened_of_icchantika (G := G) h⟩

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

end InstructiveAbsence

end WAA
