/-
================================================================================
  WeldAndArrow.Doctrines.Sraddha
  The checked sraddha conditional
================================================================================

The grid proves the implication. It does not discharge the antecedents and it
does not assert the detached fourth-truth injunction in its own voice.

The faith antecedent is abstracted to a testimony principle in
`Doctrines/Faith.lean`; the conditional here remains the direct,
non-testimonial route.
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
  clenchMismatch : G.ClenchMismatch reception

theorem actual_of_waaAversionContext
    {before : Config Contrib} {reception : G.Weld}
    (h : WaaAversionContext G before reception) :
    G.Actual reception :=
  h.clenchMismatch.left

theorem hasSelfPoleIndex_of_waaAversionContext
    {before : Config Contrib} {reception : G.Weld}
    (h : WaaAversionContext G before reception) :
    G.HasSelfPoleIndex reception :=
  h.clenchMismatch.right

/-- Given faith-shaped closure, delivery, and the receiver's live aversion
    context, the share-drop landing follows. -/
theorem waa_path_landing
    {g : G.Being} {before : Config Contrib} {deed reception : G.Weld}
    (hfaith : WaaEffectiveTerminus G g)
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
  WaaEffectiveTerminus G g →
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

end WAA
