/-
================================================================================
  WeldAndArrow.Doctrines.Shusho
  Per-occurrence effectiveness face and standing-display fence
================================================================================

Reading and motivation: Identification/Commentary.lean, C.4.
-/

import WeldAndArrow.Doctrines.Sraddha
import WeldAndArrow.Doctrines.Doors

namespace WAA

namespace Grid

namespace DirectedConvention

variable {Contrib : Type} [PreorderBot Contrib]
variable (G : Grid Contrib)

/-- The sho face of a single occurrence: an actual weld whose share sits in
    the pole-class. No standing rank is implied; the fact is about this act
    and is spent with it. Reading and motivation: Identification/Commentary.lean,
    C.4. -/
def WaaPoleDeed (w : G.Weld) : Prop :=
  G.Actual w ∧ AtBot (G.share w)

/-- Shushō-ittō, grid-side: effective closure as a fact about one delivered
    occurrence -- a pole-typed actual deed landing with a share-drop against a
    live prior tendency. This, not the standing predicate, is what act-time
    verdicts may assert. Reading and motivation: Identification/Commentary.lean,
    C.4. -/
def WaaEffectiveOccurrence
    (before : Config Contrib) (deed reception : G.Weld) : Prop :=
  WaaPoleDeed G deed ∧
    ¬ AtBot before.tendency ∧
      LandsWithShareDrop G before deed reception

theorem waaEffectiveOccurrence_hasShareDropLanding
    {before : Config Contrib} {deed reception : G.Weld}
    (h : WaaEffectiveOccurrence G before deed reception) :
    HasShareDropLanding G before deed :=
  ⟨reception, h.right.right⟩

theorem waaPoleDeed_of_terminus_response
    {w : G.Weld} (hterm : G.Terminus w.agent) (hactual : G.Actual w) :
    WaaPoleDeed G w :=
  ⟨hactual, G.atBot_of_terminus_response hterm hactual⟩

/-- Any supplied production by a terminus producer has the per-occurrence
    shō face.  The statement is door-neutral; speech-door productions may then
    enter testimony, while mind-door productions remain character evidence. -/
theorem waaPoleDeed_of_produced_terminus
    {L : ClaimLanguage G} {sr : SpeechReading G L}
    (u : ProducedUtterance sr) (hterm : G.Terminus u.weld.agent) :
    WaaPoleDeed G u.weld :=
  waaPoleDeed_of_terminus_response G hterm u.actual

/-- The standing display entails an occurrence face only once the deed is an
    actual mounted response and the regime supplies a live delivered pair. The
    landing witness may be a different actual reception from the supplied
    delivery, because `ShortfallClosedAt` asserts existence of a share-drop
    landing for that deed. -/
theorem waaEffectiveOccurrence_of_waaEffectiveTerminus
    {b : G.Being} {before : Config Contrib} {deed reception : G.Weld}
    (h : WaaEffectiveTerminus G b)
    (hdeed : deed.agent = b)
    (hactual : G.Actual deed)
    (hdel : DeliveredTo G deed reception)
    (hlive : ¬ AtBot before.tendency) :
    ∃ reception',
      WaaEffectiveOccurrence G before deed reception' := by
  rcases shortfallClosedAt_of_waaEffectiveTerminus G h hdeed hlive hdel with
    ⟨reception', hland⟩
  refine ⟨reception', ?_⟩
  refine ⟨?_, hlive, hland⟩
  have htermDeed : G.Terminus deed.agent := by
    simpa [hdeed] using h.left.right
  exact waaPoleDeed_of_terminus_response G htermDeed hactual

/-- The old sraddha landing route factors through the per-occurrence face once
    the speaker's deed is known to be actual. -/
theorem waa_path_landing_factors
    {g : G.Being} {before : Config Contrib} {deed reception : G.Weld}
    (hfaith : WaaEffectiveTerminus G g)
    (hdeed : deed.agent = g)
    (hactual : G.Actual deed)
    (hdel : DeliveredTo G deed reception)
    (hctx : WaaAversionContext G before reception) :
    ∃ reception',
      WaaEffectiveOccurrence G before deed reception' :=
  waaEffectiveOccurrence_of_waaEffectiveTerminus
    G hfaith hdeed hactual hdel hctx.liveBefore

/-- Earned, non-vacuous effectiveness display: the standing pattern plus at
    least one actual effective occurrence witnessing it. The sealed-regime
    terminus satisfies the standing predicate vacuously and fails this enacted
    form. -/
def WaaEffectivenessEnacted (b : G.Being) : Prop :=
  WaaEffectiveTerminus G b ∧
    ∃ before deed reception,
      deed.agent = b ∧ WaaEffectiveOccurrence G before deed reception

theorem waaEffectiveTerminus_of_effectivenessEnacted
    {b : G.Being} (h : WaaEffectivenessEnacted G b) :
    WaaEffectiveTerminus G b :=
  h.left

theorem not_effectivenessEnacted_of_undelivered
    {b : G.Being}
    (hundelivered : ∀ (deed reception : G.Weld),
      deed.agent = b → ¬ DeliveredTo G deed reception) :
    ¬ WaaEffectivenessEnacted G b := by
  rintro ⟨_hstanding, before, deed, reception, hdeed, hocc⟩
  exact hundelivered deed reception hdeed
    (deliveredTo_of_landsWithShareDrop G hocc.right.right)

namespace BeingConvention
namespace GridConvention

/-- Per-occurrence effective landing is a grammatical verdict item. -/
def WaaEffectiveOccurrenceVoice : ErrorGrade :=
  ErrorGrade.verdict

/-- The standing universal is displayable as shortfall-voiced, not assertable
    as an act-time verdict. -/
def WaaStandingEffectivenessVoice : ErrorGrade :=
  ErrorGrade.shortfall

theorem waa_effective_occurrence_voice_assertable :
    ErrorGrade.voice WaaEffectiveOccurrenceVoice = VerdictVoice.assertable :=
  rfl

theorem waa_standing_effectiveness_voice_displayable :
    ErrorGrade.voice WaaStandingEffectivenessVoice = VerdictVoice.displayable :=
  rfl

end GridConvention
end BeingConvention

end DirectedConvention

end Grid

end WAA
