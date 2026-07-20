/-
================================================================================
  WeldAndArrow.Doctrines.Ethics
  Ethics as the bundled production-fidelity conditional
================================================================================
-/

import WeldAndArrow.Doctrines.Faith

namespace WAA
namespace Grid
namespace DirectedConvention

variable {Contrib : Type} [PreorderBot Contrib]
variable (G : Grid Contrib)

/-- The stance carries factive faith and the model-side assertion that its
    fidelity predicate is instantiated by actual speech productions. -/
structure WaaEthicsStance
    (sr : SpeechReading G (waaPathClaimLanguage G))
    (Fidelity : RecordedUtterance G (waaPathClaimLanguage G) → Prop)
    (Faith : Prop → Prop) (b : G.Being) : Prop where
  factive : Factive Faith
  faith : Faith (WaaFullyEnlightened G sr b)
  fidelityProduces : ∀ record, Fidelity record →
    ProductionFidelity G sr record

/-- The ethical code remains an implication type. The prior untied act-time
    witness is gone: production fidelity fixes the record's own act-time. -/
def WaaEthicalCode
    (sr : SpeechReading G (waaPathClaimLanguage G))
    (Fidelity : RecordedUtterance G (waaPathClaimLanguage G) → Prop)
    (Faith : Prop → Prop) (b : G.Being) : Prop :=
  WaaEthicsStance G sr Fidelity Faith b →
    ∀ u : RecordedUtterance G (waaPathClaimLanguage G), Fidelity u →
      u.weld.agent = b →
        DeliveredTo G u.content.deed u.content.reception →
          WaaAversionContext G u.content.before u.content.reception →
            HasShareDropLanding G u.content.before u.content.deed

theorem waa_stance_says_true
    {sr : SpeechReading G (waaPathClaimLanguage G)}
    {Fidelity : RecordedUtterance G (waaPathClaimLanguage G) → Prop}
    {Faith : Prop → Prop} {b : G.Being}
    (hstance : WaaEthicsStance G sr Fidelity Faith b)
    (u : RecordedUtterance G (waaPathClaimLanguage G))
    (hagent : u.weld.agent = b) (hfid : Fidelity u) :
    u.FitsOfferedTier :=
  waa_says_true_of_faith G hstance.factive hstance.faith u hagent
    (hstance.fidelityProduces u hfid)

theorem waa_ethics_landing_of_stance
    {sr : SpeechReading G (waaPathClaimLanguage G)}
    {Fidelity : RecordedUtterance G (waaPathClaimLanguage G) → Prop}
    {Faith : Prop → Prop} {b : G.Being}
    (hstance : WaaEthicsStance G sr Fidelity Faith b)
    (u : RecordedUtterance G (waaPathClaimLanguage G))
    (hagent : u.weld.agent = b) (hfid : Fidelity u)
    (hdel : DeliveredTo G u.content.deed u.content.reception)
    (hctx : WaaAversionContext G u.content.before u.content.reception) :
    HasShareDropLanding G u.content.before u.content.deed :=
  waa_path_landing_of_stance G hstance.factive hstance.faith u hagent
    (hstance.fidelityProduces u hfid) hdel hctx

theorem waaEthicalCode_conditional
    (sr : SpeechReading G (waaPathClaimLanguage G))
    (Fidelity : RecordedUtterance G (waaPathClaimLanguage G) → Prop)
    (Faith : Prop → Prop) (b : G.Being) :
    WaaEthicalCode G sr Fidelity Faith b := by
  intro hstance u hfid hagent hdel hctx
  exact waa_ethics_landing_of_stance G hstance u hagent hfid hdel hctx

theorem waaFaithOught_of_ethicalCode
    {sr : SpeechReading G (waaPathClaimLanguage G)}
    {Fidelity : RecordedUtterance G (waaPathClaimLanguage G) → Prop}
    {Faith : Prop → Prop} {b : G.Being}
    (hcode : WaaEthicalCode G sr Fidelity Faith b)
    (u : RecordedUtterance G (waaPathClaimLanguage G)) :
    WaaFaithOught G sr Fidelity Faith b u := by
  intro hfact hfaith hfid hproduces hagent hdel hctx
  exact hcode ⟨hfact, hfaith, hproduces⟩ u hfid hagent hdel hctx

namespace BeingConvention
namespace GridConvention

def WaaEthicsConditionalVoice : ErrorGrade := ErrorGrade.verdict
def WaaEthicsDetachedVoice : ErrorGrade := ErrorGrade.shortfall

theorem waa_ethics_conditional_voice_assertable :
    ErrorGrade.voice WaaEthicsConditionalVoice = VerdictVoice.assertable := rfl

theorem waa_ethics_detached_voice_displayable :
    ErrorGrade.voice WaaEthicsDetachedVoice = VerdictVoice.displayable := rfl

end GridConvention
end BeingConvention

end DirectedConvention
end Grid
end WAA
