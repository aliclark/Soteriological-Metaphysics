/-
================================================================================
  WeldAndArrow.Doctrines.Faith
  Speech-only testimony and speech-or-mind no-nescience
================================================================================
-/

import WeldAndArrow.Doctrines.Shusho
import WeldAndArrow.Doctrines.Doors

namespace WAA

namespace Grid
namespace DirectedConvention

variable {Contrib : Type} [PreorderBot Contrib]
variable (G : Grid Contrib)

structure WaaPathClaim where
  before : Config Contrib
  deed : G.Weld
  reception : G.Weld

def waaPathClaimLanguage : ClaimLanguage G where
  Claim := WaaPathClaim G
  Holds
    | .floor, _ => False
    | .actTime _, claim =>
        ShortfallClosedAt G claim.before claim.deed claim.reception

def Factive (Faith : Prop → Prop) : Prop :=
  ∀ P : Prop, Faith P → P

/-- The former speech-side character conjunct, retained as the comparison
    target for the deliberate strengthening to `WaaNoNescience`. -/
def WaaNoDelusion
    (Fidelity : RecordedUtterance G (waaPathClaimLanguage G) → Prop)
    (b : G.Being) : Prop :=
  ∀ u : RecordedUtterance G (waaPathClaimLanguage G),
    u.weld.agent = b → Fidelity u →
      ∀ w : G.Weld, u.offeredAt = Tier.actTime w →
        (waaPathClaimLanguage G).TrueAt u.offeredAt u.content

/-- Production-instantiated fidelity: a record is faithful here exactly when
    it is the speech-door record of a supplied production. -/
def ProductionFidelity
    (sr : SpeechReading G (waaPathClaimLanguage G))
    (record : RecordedUtterance G (waaPathClaimLanguage G)) : Prop :=
  ∃ u : ProducedUtterance sr,
    ∃ hspeech : sr.door u.weld = .speech,
      u.toRecorded hspeech = record

/-- Positive truth at a production's own act-time for every speech-or-mind
    pole-share production. This is the cognitive-obscuration conjunct:
    thoughts are included, while testimony remains speech-only. -/
def WaaNoNescience
    (sr : SpeechReading G (waaPathClaimLanguage G)) (b : G.Being) : Prop :=
  ∀ u : ProducedUtterance sr,
    u.weld.agent = b →
      (sr.door u.weld = .speech ∨ sr.door u.weld = .mind) →
      AtBot (G.share u.weld) →
        (waaPathClaimLanguage G).TrueAt
          (Tier.actTime u.weld) u.content

/-- For a terminus producer, every production-instantiated speech record is at
    pole, so no-nescience supplies the old speech-side no-delusion theorem. -/
theorem noDelusion_of_noNescience_of_terminus
    (sr : SpeechReading G (waaPathClaimLanguage G)) {b : G.Being}
    (hnescience : WaaNoNescience G sr b) (hterm : G.Terminus b) :
    WaaNoDelusion G (ProductionFidelity G sr) b := by
  intro record hagent hfid w hoff
  rcases hfid with ⟨u, hspeech, rfl⟩
  have hagentU : u.weld.agent = b := by simpa using hagent
  have htermU : G.Terminus u.weld.agent := by
    rw [hagentU]
    exact hterm
  change (waaPathClaimLanguage G).TrueAt
    (Tier.actTime u.weld) u.content
  exact hnescience u hagentU (Or.inl hspeech)
    (G.atBot_of_terminus_response htermU u.actual)

theorem waaNoDelusion_not_misfits
    {Fidelity : RecordedUtterance G (waaPathClaimLanguage G) → Prop}
    {b : G.Being} (h : WaaNoDelusion G Fidelity b)
    (u : RecordedUtterance G (waaPathClaimLanguage G))
    (hutter : u.weld.agent = b) (hfid : Fidelity u) :
    ¬ u.MisfitsOfferedTier := by
  rintro ⟨w, hoff, hnot⟩
  exact hnot (h u hutter hfid w hoff)

/-- Full enlightenment combines effective termination with the strengthened
    speech-or-mind no-nescience conjunct. Including thought is the point: the
    jñeyāvaraṇa face is stronger than faithful speech alone. -/
structure WaaFullyEnlightened
    (sr : SpeechReading G (waaPathClaimLanguage G))
    (b : G.Being) : Prop where
  effective : WaaEffectiveTerminus G b
  noNescience : WaaNoNescience G sr b

/-- A non-vacuous faithful speech occurrence, tied to its production weld and
    therefore definitionally offered at that weld's act-time. -/
def WaaFaithfulSpeechOccurrence
    (sr : SpeechReading G (waaPathClaimLanguage G))
    (Fidelity : RecordedUtterance G (waaPathClaimLanguage G) → Prop)
    (b : G.Being) : Prop :=
  ∃ u : ProducedUtterance sr,
    u.weld.agent = b ∧
      ∃ hspeech : sr.door u.weld = .speech,
        Fidelity (u.toRecorded hspeech) ∧
          (u.toRecorded hspeech).FitsOfferedTier

/-- Enacted faithful speech is standing full enlightenment plus a tied speech
    occurrence. -/
def WaaFaithfulSpeechEnacted
    (sr : SpeechReading G (waaPathClaimLanguage G))
    (Fidelity : RecordedUtterance G (waaPathClaimLanguage G) → Prop)
    (b : G.Being) : Prop :=
  WaaFullyEnlightened G sr b ∧
    WaaFaithfulSpeechOccurrence G sr Fidelity b

structure WaaFullyEnlightenedEnacted
    (sr : SpeechReading G (waaPathClaimLanguage G))
    (Fidelity : RecordedUtterance G (waaPathClaimLanguage G) → Prop)
    (b : G.Being) : Prop where
  standing : WaaFullyEnlightened G sr b
  deedWitness : WaaEffectivenessEnacted G b
  speechOccurrence : WaaFaithfulSpeechOccurrence G sr Fidelity b

theorem waaEffectiveTerminus_of_fullyEnlightened
    {sr : SpeechReading G (waaPathClaimLanguage G)} {b : G.Being}
    (h : WaaFullyEnlightened G sr b) : WaaEffectiveTerminus G b :=
  h.effective

theorem waaFullyEnlightened_of_fullyEnlightenedEnacted
    {sr : SpeechReading G (waaPathClaimLanguage G)}
    {Fidelity : RecordedUtterance G (waaPathClaimLanguage G) → Prop}
    {b : G.Being} (h : WaaFullyEnlightenedEnacted G sr Fidelity b) :
    WaaFullyEnlightened G sr b :=
  h.standing

theorem waaEffectivenessEnacted_of_fullyEnlightenedEnacted
    {sr : SpeechReading G (waaPathClaimLanguage G)}
    {Fidelity : RecordedUtterance G (waaPathClaimLanguage G) → Prop}
    {b : G.Being} (h : WaaFullyEnlightenedEnacted G sr Fidelity b) :
    WaaEffectivenessEnacted G b :=
  h.deedWitness

theorem waaFaithfulSpeechEnacted_of_fullyEnlightenedEnacted
    {sr : SpeechReading G (waaPathClaimLanguage G)}
    {Fidelity : RecordedUtterance G (waaPathClaimLanguage G) → Prop}
    {b : G.Being} (h : WaaFullyEnlightenedEnacted G sr Fidelity b) :
    WaaFaithfulSpeechEnacted G sr Fidelity b :=
  ⟨h.standing, h.speechOccurrence⟩

theorem waaNoNescience_of_factive_faith
    {Faith : Prop → Prop}
    {sr : SpeechReading G (waaPathClaimLanguage G)} {b : G.Being}
    (hfact : Factive Faith) (hfaith : Faith (WaaFullyEnlightened G sr b)) :
    WaaNoNescience G sr b :=
  (hfact _ hfaith).noNescience

/-- Factive faith plus a production witness gives truth for a speech record.
    Mind productions cannot supply `ProductionFidelity` and never enter this
    testimonial route. -/
theorem waa_says_true_of_faith
    {Faith : Prop → Prop}
    {sr : SpeechReading G (waaPathClaimLanguage G)} {b : G.Being}
    (hfact : Factive Faith) (hfaith : Faith (WaaFullyEnlightened G sr b))
    (record : RecordedUtterance G (waaPathClaimLanguage G))
    (hagent : record.weld.agent = b)
    (hproduction : ProductionFidelity G sr record) :
    record.FitsOfferedTier := by
  rcases hproduction with ⟨u, hspeech, rfl⟩
  have hfull := hfact _ hfaith
  have hagentU : u.weld.agent = b := by simpa using hagent
  have htermU : G.Terminus u.weld.agent := by
    rw [hagentU]
    exact hfull.effective.left.right
  change (waaPathClaimLanguage G).TrueAt
    (Tier.actTime u.weld) u.content
  exact hfull.noNescience u hagentU (Or.inl hspeech)
    (G.atBot_of_terminus_response htermU u.actual)

theorem waa_no_misfit_of_stance
    {Faith : Prop → Prop}
    {sr : SpeechReading G (waaPathClaimLanguage G)} {b : G.Being}
    (hfact : Factive Faith) (hfaith : Faith (WaaFullyEnlightened G sr b))
    (record : RecordedUtterance G (waaPathClaimLanguage G))
    (hagent : record.weld.agent = b)
    (hproduction : ProductionFidelity G sr record) :
    ¬ record.MisfitsOfferedTier := by
  intro hmisfit
  exact hmisfit.elim (fun _ hw => hw.right
    (waa_says_true_of_faith G hfact hfaith record hagent hproduction))

theorem waaPath_not_misfits_of_floor_offer
    (u : RecordedUtterance G (waaPathClaimLanguage G))
    (hoff : u.offeredAt = Tier.floor) : ¬ u.MisfitsOfferedTier := by
  rintro ⟨w, hact, _hfalse⟩
  rw [hoff] at hact
  cases hact

theorem fitsOfferedTier_of_waaEffectiveTerminus_ownDeed
    {b : G.Being} (h : WaaEffectiveTerminus G b)
    (u : RecordedUtterance G (waaPathClaimLanguage G))
    (hdeed : u.content.deed.agent = b)
    (w : G.Weld) (hoff : u.offeredAt = Tier.actTime w) :
    u.FitsOfferedTier := by
  change (waaPathClaimLanguage G).TrueAt u.offeredAt u.content
  rw [hoff]
  exact h.right u.content.before u.content.deed u.content.reception hdeed

theorem waa_path_landing_of_stance
    {Faith : Prop → Prop}
    {sr : SpeechReading G (waaPathClaimLanguage G)} {b : G.Being}
    (hfact : Factive Faith) (hfaith : Faith (WaaFullyEnlightened G sr b))
    (u : RecordedUtterance G (waaPathClaimLanguage G))
    (hagent : u.weld.agent = b) (hproduction : ProductionFidelity G sr u)
    (hdel : DeliveredTo G u.content.deed u.content.reception)
    (hctx : WaaAversionContext G u.content.before u.content.reception) :
    HasShareDropLanding G u.content.before u.content.deed := by
  have hfit := waa_says_true_of_faith G hfact hfaith u hagent hproduction
  have hclosed :
      ShortfallClosedAt G u.content.before u.content.deed u.content.reception := by
    rcases hproduction with ⟨production, hspeech, hrecord⟩
    subst hrecord
    change (waaPathClaimLanguage G).TrueAt
      (Tier.actTime production.weld) production.content at hfit
    dsimp [waaPathClaimLanguage, ClaimLanguage.TrueAt] at hfit
    change ShortfallClosedAt G production.content.before
      production.content.deed production.content.reception
    exact hfit
  exact hclosed hctx.liveBefore hdel

def WaaFaithOught
    (sr : SpeechReading G (waaPathClaimLanguage G))
    (Fidelity : RecordedUtterance G (waaPathClaimLanguage G) → Prop)
    (Faith : Prop → Prop) (b : G.Being)
    (u : RecordedUtterance G (waaPathClaimLanguage G)) : Prop :=
  Factive Faith → Faith (WaaFullyEnlightened G sr b) → Fidelity u →
    (∀ record, Fidelity record → ProductionFidelity G sr record) →
      u.weld.agent = b →
        DeliveredTo G u.content.deed u.content.reception →
          WaaAversionContext G u.content.before u.content.reception →
            HasShareDropLanding G u.content.before u.content.deed

theorem waaFaithOught_conditional
    (sr : SpeechReading G (waaPathClaimLanguage G))
    (Fidelity : RecordedUtterance G (waaPathClaimLanguage G) → Prop)
    (Faith : Prop → Prop) (b : G.Being)
    (u : RecordedUtterance G (waaPathClaimLanguage G)) :
    WaaFaithOught G sr Fidelity Faith b u := by
  intro hfact hfaith hfid hproduces hagent hdel hctx
  exact waa_path_landing_of_stance G hfact hfaith u hagent
    (hproduces u hfid) hdel hctx

end DirectedConvention
end Grid
end WAA
