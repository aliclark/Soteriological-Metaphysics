/-
================================================================================
  WeldAndArrow.Doctrines.EthicsNegative
  Negative witnesses for the bundled ethics conditional
================================================================================

Reading and motivation: Identification/Commentary.lean, C.4.
-/

import WeldAndArrow.Doctrines.Ethics

namespace WAA

namespace EthicsNegative

open Grid
open Grid.DirectedConvention

/- ==============================================================================
   Concrete grid for ethics honesty clauses
============================================================================== -/

/-- The beings used by the ethics negative witnesses. -/
inductive Being
  | buddha
  | disciple
  | receiver

/-- The single call used by the ethics negative witnesses. -/
inductive Call
  | call

/-- The single response used by the ethics negative witnesses. -/
inductive Response
  | response

/-- A concrete grid where the buddha is a responsive terminus, while the
    disciple's delivered deed reaches a receiver whose live share does not
    drop. -/
def grid : Grid Nat where
  Being := Being
  Call := Call
  Response := Response
  respondsTo _ _ := some Response.response
  grade b _ _ :=
    match b with
    | .buddha => 0
    | .disciple => 1
    | .receiver => 1
  conditions deed reception :=
    deed.agent = Being.disciple ∧ reception.agent = Being.receiver

/-- The live prior configuration used by the false-testimony witness. -/
def liveBefore : Config Nat :=
  { tendency := 1 }

/-- The pole prior configuration used by the empty-at-the-pole witness. -/
def poleBefore : Config Nat :=
  { tendency := 0 }

/-- The disciple deed delivered in the concrete grid. -/
def discipleDeed : grid.Weld :=
  ⟨Being.disciple, Call.call, Response.response⟩

/-- The receiver weld reached by the disciple deed. -/
def reception : grid.Weld :=
  ⟨Being.receiver, Call.call, Response.response⟩

/-- The buddha weld that records the false testimony. -/
def buddhaWeld : grid.Weld :=
  ⟨Being.buddha, Call.call, Response.response⟩

/-- The live prior tendency is not at the pole. -/
theorem liveBefore_not_atBot :
    ¬ AtBot liveBefore.tendency := by
  intro h
  exact Nat.not_succ_le_zero 0 h

/-- The pole prior tendency is at the pole. -/
theorem poleBefore_atBot :
    AtBot poleBefore.tendency :=
  Nat.le_refl 0

/-- The disciple deed is actual in the concrete grid. -/
theorem discipleDeed_actual :
    grid.Actual discipleDeed :=
  rfl

/-- The receiver weld is actual in the concrete grid. -/
theorem reception_actual :
    grid.Actual reception :=
  rfl

/-- The buddha weld is actual in the concrete grid. -/
theorem buddhaWeld_actual :
    grid.Actual buddhaWeld :=
  rfl

/-- The disciple deed is delivered to the receiver weld. -/
theorem delivered :
    DeliveredTo grid discipleDeed reception :=
  ⟨rfl, rfl⟩

/-- The receiver weld has a live self-pole index. -/
theorem reception_hasSelfPoleIndex :
    grid.HasSelfPoleIndex reception := by
  intro hbot
  exact Nat.not_succ_le_zero 0 hbot

/-- The live receiver-side aversion context holds in the concrete grid. -/
theorem aversionContext :
    WaaAversionContext grid liveBefore reception :=
  { liveBefore := liveBefore_not_atBot
    mismatchLive := ⟨reception_actual, reception_hasSelfPoleIndex⟩ }

/-- The disciple deed has no share-drop landing for the live prior tendency. -/
theorem not_hasShareDropLanding_liveBefore :
    ¬ HasShareDropLanding grid liveBefore discipleDeed := by
  rintro ⟨received, hland⟩
  have hreceiver : received.agent = Being.receiver := hland.left.left.right
  have hdrop : Strict (grid.share received) liveBefore.tendency :=
    hland.right
  have hstrict : Strict (1 : Nat) 1 := by
    simpa [grid, Grid.share, liveBefore, hreceiver] using hdrop
  exact strict_irrefl (1 : Nat) hstrict

/-- The buddha's recorded path claim about the disciple's deed is false:
    delivery occurs, the prior tendency is live, and no share-drop landing
    exists. -/
def falseClaim : RecordedUtterance grid (waaPathClaimLanguage grid) where
  weld := buddhaWeld
  actual := buddhaWeld_actual
  offeredAt := Tier.floor
  content := ⟨liveBefore, discipleDeed, reception⟩

/-- The buddha's false claim does not fit its offered tier. -/
theorem falseClaim_not_fitsOfferedTier :
    ¬ falseClaim.FitsOfferedTier := by
  intro hfit
  change (waaPathClaimLanguage grid).TrueAt falseClaim.offeredAt
    falseClaim.content at hfit
  dsimp [waaPathClaimLanguage, ClaimLanguage.TrueAt, falseClaim,
    ShortfallClosedAt] at hfit
  exact not_hasShareDropLanding_liveBefore
    (hfit liveBefore_not_atBot delivered)

/- ==============================================================================
   Ethics negative witnesses
============================================================================== -/

/-- Even with a stance as a hypothesis, a pole-prior receiver has no live
    aversion antecedent and no share-drop landing. Faith does not manufacture a
    practical claim where no live shortfall exists. -/
theorem no_ethics_bearing_at_pole
    (Faith : Prop -> Prop) (b : Being)
    (_hstance : WaaEthicsStance grid Faith b) :
    ¬ WaaAversionContext grid poleBefore reception ∧
      ¬ HasShareDropLanding grid poleBefore discipleDeed :=
  ⟨no_waa_aversion_context_at_pole grid poleBefore_atBot reception,
    no_waa_path_at_pole grid poleBefore_atBot discipleDeed⟩

/-- No faith operator can support an ethics stance toward the buddha over this
    false testimony: the stance would force the false recorded claim to fit its
    offered tier. -/
theorem no_stance_over_false_testimony
    (Faith : Prop -> Prop) :
    ¬ WaaEthicsStance grid Faith Being.buddha := by
  intro hstance
  exact falseClaim_not_fitsOfferedTier
    (waa_stance_says_true grid hstance falseClaim rfl)

/-- The disciple's own recorded claim, used to witness faith-object relativity. -/
def discipleClaim : RecordedUtterance grid (waaPathClaimLanguage grid) where
  weld := discipleDeed
  actual := discipleDeed_actual
  offeredAt := Tier.floor
  content := ⟨liveBefore, discipleDeed, reception⟩

/-- A buddha-directed ethical code does not cover a disciple-recorded utterance:
    the speaker-equality antecedent is false, so the `b` parameter keeps the
    code relative to its faith-object. -/
theorem ethicalCode_relative_to_faith_object
    (Faith : Prop -> Prop)
    (_hcode : WaaEthicalCode grid Faith Being.buddha) :
    ¬ discipleClaim.weld.agent = Being.buddha := by
  intro h
  exact Being.noConfusion h

end EthicsNegative

end WAA
