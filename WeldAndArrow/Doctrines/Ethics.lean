/-
================================================================================
  WeldAndArrow.Doctrines.Ethics
  Ethics as the bundled faith-conditional code
================================================================================

Ethics as the bundled faith-conditional code. The grid proves the conditional;
it discharges neither the principle nor the faith, and the detached injunction
appears nowhere in the assertable voice.

Reading and motivation: Identification/Commentary.lean, C.4.
-/

import WeldAndArrow.Doctrines.Faith

namespace WAA

namespace Grid

namespace DirectedConvention

variable {Contrib : Type} [PreorderBot Contrib]
variable (G : Grid Contrib)

/- ==============================================================================
   Ethics as faith-conditional code
============================================================================== -/

/-- The ethics stance: exactly what the agent brings and the grid never
    discharges. Principle plus faith in one being's full enlightenment. Reading
    and motivation: Identification/Commentary.lean, C.4. -/
structure WaaEthicsStance (Faith : Prop -> Prop) (b : G.Being) : Prop where
  principle : WaaFaithPrinciple G (waaPathClaimLanguage G) Faith
  faith : Faith (WaaFullyEnlightened G b)

/-- The ethical code as an implication type only. One stance yields, for every
    recorded utterance of the faith-object, delivered into a live aversion
    context, the share-drop landing. The detached consequent appears nowhere.
    Reading and motivation: Identification/Commentary.lean, C.4. -/
def WaaEthicalCode (Faith : Prop -> Prop) (b : G.Being) : Prop :=
  WaaEthicsStance G Faith b ->
    forall u : RecordedUtterance G (waaPathClaimLanguage G),
      u.weld.agent = b ->
        DeliveredTo G u.content.deed u.content.reception ->
          WaaAversionContext G u.content.before u.content.reception ->
            HasShareDropLanding G u.content.before u.content.deed

/-- Under a stance, the faith-object's testimony is true at its offered tier:
    the "what they say is true" half. Thin wrapper over
    `waa_says_true_of_faith`. Reading and motivation:
    Identification/Commentary.lean, C.4. -/
theorem waa_stance_says_true
    {Faith : Prop -> Prop} {b : G.Being}
    (hstance : WaaEthicsStance G Faith b)
    (u : RecordedUtterance G (waaPathClaimLanguage G))
    (hutter : u.weld.agent = b) :
    u.FitsOfferedTier :=
  waa_says_true_of_faith G hstance.principle hstance.faith u hutter

/-- Under a stance, one delivered utterance met with live aversion yields the
    landing: the per-utterance ought. Route through
    `waa_path_landing_of_faithPrinciple`. Reading and motivation:
    Identification/Commentary.lean, C.4. -/
theorem waa_ethics_landing_of_stance
    {Faith : Prop -> Prop} {b : G.Being}
    (hstance : WaaEthicsStance G Faith b)
    (u : RecordedUtterance G (waaPathClaimLanguage G))
    (hutter : u.weld.agent = b)
    (hdel : DeliveredTo G u.content.deed u.content.reception)
    (hctx : WaaAversionContext G u.content.before u.content.reception) :
    HasShareDropLanding G u.content.before u.content.deed :=
  waa_path_landing_of_faithPrinciple G
    hstance.principle hstance.faith u hutter hdel hctx

/-- The grid proves the whole code as one conditional, hypothesis-free.
    Reading and motivation: Identification/Commentary.lean, C.4. -/
theorem waaEthicalCode_conditional
    (Faith : Prop -> Prop) (b : G.Being) :
    WaaEthicalCode G Faith b := by
  intro hstance u hutter hdel hctx
  exact waa_ethics_landing_of_stance G hstance u hutter hdel hctx

/-- Bridge: each instance of the code is a `WaaFaithOught`, so the ethics
    layer adds bundling and naming, not new assertive content. Reading and
    motivation: Identification/Commentary.lean, C.4. -/
theorem waaFaithOught_of_ethicalCode
    {Faith : Prop -> Prop} {b : G.Being}
    (hcode : WaaEthicalCode G Faith b)
    (u : RecordedUtterance G (waaPathClaimLanguage G)) :
    WaaFaithOught G Faith b u := by
  intro hprinciple hfaith hutter hdel hctx
  exact hcode ⟨hprinciple, hfaith⟩ u hutter hdel hctx

namespace BeingConvention
namespace GridConvention

/-- The ethics conditional is a grammatical verdict item. Reading and
    motivation: Identification/Commentary.lean, C.4. -/
def WaaEthicsConditionalVoice : ErrorGrade :=
  ErrorGrade.verdict

/-- The detached ethics injunction is only displayable as shortfall-voiced.
    Reading and motivation: Identification/Commentary.lean, C.4. -/
def WaaEthicsDetachedVoice : ErrorGrade :=
  ErrorGrade.shortfall

/-- The conditional ethics voice is assertable. Reading and motivation:
    Identification/Commentary.lean, C.4. -/
theorem waa_ethics_conditional_voice_assertable :
    ErrorGrade.voice WaaEthicsConditionalVoice = VerdictVoice.assertable :=
  rfl

/-- The detached ethics voice is displayable. Reading and motivation:
    Identification/Commentary.lean, C.4. -/
theorem waa_ethics_detached_voice_displayable :
    ErrorGrade.voice WaaEthicsDetachedVoice = VerdictVoice.displayable :=
  rfl

end GridConvention
end BeingConvention

end DirectedConvention

end Grid

end WAA
