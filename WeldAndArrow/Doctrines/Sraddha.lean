/-
================================================================================
  WeldAndArrow.Doctrines.Sraddha
  The checked sraddha conditional
================================================================================

The grid proves the implication. It does not discharge the antecedents and it
does not assert the detached fourth-truth injunction in its own voice.
-/

import WeldAndArrow.Doctrines.FourTruths

namespace WAA

namespace Grid

namespace DirectedConvention

variable {Contrib : Type} [PreorderBot Contrib]
variable (G : Grid Contrib)

/-- The receiver-side aversion context: a live prior tendency together with an
    actual live-mismatch reception. No imported desire primitive is added. -/
structure WaaAversionContext
    (before : Config Contrib) (reception : G.Weld) where
  liveBefore : ¬ AtBot before.tendency
  mismatchLive : G.WaaMismatchLive reception

theorem actual_of_waaAversionContext
    {before : Config Contrib} {reception : G.Weld}
    (h : WaaAversionContext G before reception) :
    G.Actual reception :=
  h.mismatchLive.left

theorem hasSelfPoleIndex_of_waaAversionContext
    {before : Config Contrib} {reception : G.Weld}
    (h : WaaAversionContext G before reception) :
    G.HasSelfPoleIndex reception :=
  h.mismatchLive.right

/-- Given faith-shaped closure, delivery, and the receiver's live aversion
    context, the share-drop landing follows. -/
theorem waa_path_landing
    {g : G.Being} {before : Config Contrib} {deed reception : G.Weld}
    (hfaith : WaaFullyEnlightened G g)
    (hdeed : deed.agent = g)
    (hdel : DeliveredTo G deed reception)
    (hctx : WaaAversionContext G before reception) :
    HasShareDropLanding G before deed :=
  hfaith.right before deed reception hdeed hctx.liveBefore hdel

/-- The fourth-truth ought as an implication type only. The detached consequent
    appears nowhere in this definition. -/
def WaaPathOught
    (g : G.Being) (before : Config Contrib) (deed reception : G.Weld) :
    Prop :=
  WaaFullyEnlightened G g →
    deed.agent = g →
      DeliveredTo G deed reception →
        WaaAversionContext G before reception →
          HasShareDropLanding G before deed

/-- The grid proves only the conditional: faith, delivery, and live aversion
    imply the landing. -/
theorem waaPathOught_conditional
    (g : G.Being) (before : Config Contrib) (deed reception : G.Weld) :
    WaaPathOught G g before deed reception := by
  intro hfaith hdeed hdel hctx
  exact waa_path_landing G hfaith hdeed hdel hctx

/-- At the pole-class, no share-drop landing can be constructed for any deed. -/
theorem no_waa_path_at_pole
    {before : Config Contrib} (hbot : AtBot before.tendency)
    (deed : G.Weld) :
    ¬ HasShareDropLanding G before deed := by
  rintro ⟨reception, hland⟩
  exact G.not_isShareDrop_of_tendency_atBot hbot reception hland.right

/-- At the pole-class, the live-aversion antecedent itself fails. -/
theorem no_waa_aversion_context_at_pole
    {before : Config Contrib} (hbot : AtBot before.tendency)
    (reception : G.Weld) :
    ¬ WaaAversionContext G before reception :=
  fun hctx => hctx.liveBefore hbot

namespace BeingConvention
namespace GridConvention

/-- The checked conditional is a grammatical verdict item. -/
def WaaConditionalVoice : ErrorGrade :=
  ErrorGrade.verdict

/-- The detached injunction is only displayable as shortfall-voiced. -/
def WaaDetachedOughtVoice : ErrorGrade :=
  ErrorGrade.shortfall

theorem waa_conditional_voice_assertable :
    ErrorGrade.voice WaaConditionalVoice = VerdictVoice.assertable :=
  rfl

theorem waa_detached_ought_voice_displayable :
    ErrorGrade.voice WaaDetachedOughtVoice = VerdictVoice.displayable :=
  rfl

end GridConvention
end BeingConvention

end DirectedConvention

end Grid

/- ==============================================================================
   Negative witnesses: both antecedents matter
============================================================================== -/

namespace SraddhaNegative

open Grid.DirectedConvention

inductive Being
  | sraddha
  | receiver

inductive Call
  | call

inductive Response
  | response

/-- A responsive terminus whose delivered deed has no share-drop landing for
    the receiver's live prior tendency. -/
def zeroEffectGrid : Grid Nat where
  Being      := Being
  Call       := Call
  Response   := Response
  respondsTo _ _ := some Response.response
  grade b _ _ :=
    match b with
    | .sraddha => 0
    | .receiver => 1
  conditions deed reception :=
    deed.agent = Being.sraddha ∧ reception.agent = Being.receiver

def liveBefore : Config Nat :=
  { tendency := 1 }

def poleBefore : Config Nat :=
  { tendency := 0 }

def deed : zeroEffectGrid.Weld :=
  ⟨Being.sraddha, Call.call, Response.response⟩

def reception : zeroEffectGrid.Weld :=
  ⟨Being.receiver, Call.call, Response.response⟩

theorem liveBefore_not_atBot :
    ¬ AtBot liveBefore.tendency := by
  intro h
  exact Nat.not_succ_le_zero 0 h

theorem poleBefore_atBot :
    AtBot poleBefore.tendency :=
  Nat.le_refl 0

theorem reception_actual :
    zeroEffectGrid.Actual reception :=
  rfl

theorem delivered :
    DeliveredTo zeroEffectGrid deed reception :=
  ⟨rfl, rfl⟩

theorem reception_hasSelfPoleIndex :
    zeroEffectGrid.HasSelfPoleIndex reception := by
  intro hbot
  exact Nat.not_succ_le_zero 0 hbot

theorem aversionContext :
    WaaAversionContext zeroEffectGrid liveBefore reception :=
  { liveBefore := liveBefore_not_atBot
    mismatchLive := ⟨reception_actual, reception_hasSelfPoleIndex⟩ }

theorem sraddha_responsiveTerminus :
    zeroEffectGrid.ResponsiveTerminus Being.sraddha := by
  constructor
  · intro _c
    exact ⟨Response.response, rfl⟩
  · intro _c _r _hresp
    exact Nat.le_refl 0

theorem not_hasShareDropLanding_liveBefore :
    ¬ HasShareDropLanding zeroEffectGrid liveBefore deed := by
  rintro ⟨received, hland⟩
  have hreceiver : received.agent = Being.receiver := hland.left.left.right
  have hdrop : Strict (zeroEffectGrid.share received) liveBefore.tendency :=
    hland.right
  have hstrict : Strict (1 : Nat) 1 := by
    simpa [zeroEffectGrid, Grid.share, liveBefore, hreceiver] using hdrop
  exact strict_irrefl (1 : Nat) hstrict

theorem not_waaFullyEnlightened :
    ¬ WaaFullyEnlightened zeroEffectGrid Being.sraddha := by
  intro hfaith
  exact not_hasShareDropLanding_liveBefore
    (hfaith.right liveBefore deed reception rfl liveBefore_not_atBot delivered)

/-- Dropping the faith conjunct leaves delivery and aversion insufficient. -/
theorem drop_faith_antecedent_fails :
    zeroEffectGrid.ResponsiveTerminus Being.sraddha ∧
      DeliveredTo zeroEffectGrid deed reception ∧
      WaaAversionContext zeroEffectGrid liveBefore reception ∧
      ¬ HasShareDropLanding zeroEffectGrid liveBefore deed :=
  ⟨sraddha_responsiveTerminus, delivered, aversionContext,
    not_hasShareDropLanding_liveBefore⟩

theorem not_hasShareDropLanding_poleBefore :
    ¬ HasShareDropLanding zeroEffectGrid poleBefore deed :=
  no_waa_path_at_pole zeroEffectGrid poleBefore_atBot deed

/-- Dropping the aversion conjunct leaves a pole-prior case where no
    share-drop landing is constructible. -/
theorem drop_aversion_antecedent_fails :
    AtBot poleBefore.tendency ∧
      DeliveredTo zeroEffectGrid deed reception ∧
      ¬ WaaAversionContext zeroEffectGrid poleBefore reception ∧
      ¬ HasShareDropLanding zeroEffectGrid poleBefore deed :=
  ⟨poleBefore_atBot, delivered,
    no_waa_aversion_context_at_pole zeroEffectGrid poleBefore_atBot reception,
    not_hasShareDropLanding_poleBefore⟩

end SraddhaNegative

end WAA
