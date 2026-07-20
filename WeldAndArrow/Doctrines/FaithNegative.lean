/-
================================================================================
  WeldAndArrow.Doctrines.FaithNegative
  Speech/mind strictness, undefiled nescience, and silent buddhas
================================================================================
-/

import WeldAndArrow.Doctrines.Faith

namespace WAA
namespace FaithNegative

open Grid
open Grid.DirectedConvention

/-! ### A pole-share producer with true speech and a false thought -/

inductive Call
  | speech
  | mind
  | target
deriving DecidableEq

/-- Speech and thought occur at the pole.  The target is a merely possible
    reception used to make the thought-content false. -/
def grid : Grid Nat where
  Being := Unit
  Call := Call
  Response := Unit
  respondsTo _ c :=
    match c with
    | .speech | .mind => some ()
    | .target => none
  grade _ c _ :=
    match c with
    | .speech | .mind => 0
    | .target => 1
  conditions deed reception :=
    deed.call = .mind ∧ reception.call = .target

def speechWeld : grid.Weld := ⟨(), .speech, ()⟩
def mindWeld : grid.Weld := ⟨(), .mind, ()⟩
def targetWeld : grid.Weld := ⟨(), .target, ()⟩

def poleBefore : Config Nat := ⟨0⟩
def liveBefore : Config Nat := ⟨1⟩

def trueContent : WaaPathClaim grid :=
  ⟨poleBefore, speechWeld, targetWeld⟩

def falseContent : WaaPathClaim grid :=
  ⟨liveBefore, mindWeld, targetWeld⟩

def reading : SpeechReading grid (waaPathClaimLanguage grid) where
  door w :=
    match w.call with
    | .speech => .speech
    | .mind => .mind
    | .target => .body
  voices w :=
    match w.call with
    | .speech => some trueContent
    | .mind => some falseContent
    | .target => none

def speechProduction : ProducedUtterance reading where
  weld := speechWeld
  actual := rfl
  content := trueContent
  voiced := rfl

def mindProduction : ProducedUtterance reading where
  weld := mindWeld
  actual := rfl
  content := falseContent
  voiced := rfl

theorem trueContent_trueAt :
    (waaPathClaimLanguage grid).TrueAt
      (Tier.actTime speechWeld) trueContent := by
  intro hlive
  exact False.elim (hlive (Nat.le_refl 0))

theorem liveBefore_not_atBot : ¬ AtBot liveBefore.tendency := by
  intro h
  exact Nat.not_succ_le_zero 0 h

theorem mind_delivered_to_target :
    DeliveredTo grid mindWeld targetWeld :=
  ⟨rfl, rfl⟩

theorem mind_has_no_shareDropLanding :
    ¬ HasShareDropLanding grid liveBefore mindWeld := by
  rintro ⟨received, hland⟩
  have htarget : received.call = Call.target := hland.left.left.right
  have hactual : grid.Actual received := hland.left.right
  cases received with
  | mk agent call response =>
      simp only at htarget
      subst call
      change (none : Option Unit) = some response at hactual
      cases hactual

theorem falseContent_not_trueAt :
    ¬ (waaPathClaimLanguage grid).TrueAt
      (Tier.actTime mindWeld) falseContent := by
  intro htrue
  exact mind_has_no_shareDropLanding
    (htrue liveBefore_not_atBot mind_delivered_to_target)

theorem all_speech_productions_true :
    ∀ u : ProducedUtterance reading,
      reading.door u.weld = .speech →
        (waaPathClaimLanguage grid).TrueAt
          (Tier.actTime u.weld) u.content := by
  intro u hspeech
  cases hcall : u.weld.call with
  | speech =>
      have hweld : u.weld = speechWeld := by
        apply RawWeld.ext
        · change (u.weld.agent : Unit) = ()
          exact Unit.ext _ _
        · exact hcall
        · change (u.weld.response : Unit) = ()
          exact Unit.ext _ _
      have hvoiced := u.voiced
      rw [hweld] at hvoiced ⊢
      have hcontent : u.content = trueContent := by
        change some trueContent = some u.content at hvoiced
        exact (Option.some.inj hvoiced).symm
      rw [hcontent]
      exact trueContent_trueAt
  | mind => simp [reading, hcall] at hspeech
  | target => simp [reading, hcall] at hspeech

/-- Production-instantiated fidelity sees precisely speech-door productions,
    all of which are true in the strictness model. -/
theorem old_speech_side_holds :
    WaaNoDelusion grid (ProductionFidelity grid reading) () := by
  intro record _hagent hfid _w _hoff
  rcases hfid with ⟨u, hspeech, rfl⟩
  exact all_speech_productions_true u hspeech

theorem not_noNescience :
    ¬ WaaNoNescience grid reading () := by
  intro h
  exact falseContent_not_trueAt
    (h mindProduction rfl (Or.inr rfl) (Nat.le_refl 0))

/-- No-nescience is deliberately stronger than the former speech-only test. -/
theorem noNescience_strictly_stronger_witness :
    WaaNoDelusion grid (ProductionFidelity grid reading) () ∧
      (∀ u : ProducedUtterance reading,
        reading.door u.weld = .speech →
          (waaPathClaimLanguage grid).TrueAt
            (Tier.actTime u.weld) u.content) ∧
      ¬ WaaNoNescience grid reading () :=
  ⟨old_speech_side_holds, all_speech_productions_true, not_noNescience⟩

/-- The false thought is cognitive error but not defiled: its occurrence has
    no live self-pole.  This is the checked akliṣṭa-ajñāna separation. -/
theorem aklishta_ajnana_witness :
    grid.Actual mindProduction.weld ∧
      AtBot (grid.share mindProduction.weld) ∧
      ¬ (waaPathClaimLanguage grid).TrueAt
        (Tier.actTime mindProduction.weld) mindProduction.content ∧
      ¬ grid.HasSelfPoleIndex mindProduction.weld := by
  refine ⟨mindProduction.actual, Nat.le_refl 0,
    falseContent_not_trueAt, ?_⟩
  exact grid.no_self_pole_index_of_atBot mindProduction.weld
    (Nat.le_refl 0)

theorem quiet_everywhere : QuietOn grid () (fun _ => True) := by
  intro w hactual _hagent _
  cases hcall : w.call with
  | speech =>
      change AtBot (grid.grade w.agent w.call w.response)
      rw [hcall]
      change AtBot (0 : Nat)
      exact Nat.le_refl 0
  | mind =>
      change AtBot (grid.grade w.agent w.call w.response)
      rw [hcall]
      change AtBot (0 : Nat)
      exact Nat.le_refl 0
  | target =>
      unfold Grid.Actual at hactual
      rw [hcall] at hactual
      simp [grid] at hactual

/-- Three-door arhat quietness removes the afflictive self-pole but does not by
    itself make every speech-or-mind production true. -/
theorem arhat_retains_nescience_witness :
    QuietOn grid () (fun _ => True) ∧
      ¬ WaaNoNescience grid reading () :=
  ⟨quiet_everywhere, not_noNescience⟩

/-! ### Sealed silent and thinking buddhas -/

namespace Sealed

def grid : Grid Nat where
  Being := Unit
  Call := Unit
  Response := Unit
  respondsTo _ _ := some ()
  grade _ _ _ := 0
  conditions _ _ := False

def weld : grid.Weld := ⟨(), (), ()⟩
def poleBefore : Config Nat := ⟨0⟩
def content : WaaPathClaim grid := ⟨poleBefore, weld, weld⟩

def silentReading : SpeechReading grid (waaPathClaimLanguage grid) where
  door _ := .mind
  voices _ := none

def thinkingReading : SpeechReading grid (waaPathClaimLanguage grid) where
  door _ := .mind
  voices _ := some content

def thought : ProducedUtterance thinkingReading where
  weld := weld
  actual := rfl
  content := content
  voiced := rfl

theorem responsiveTerminus : grid.ResponsiveTerminus () := by
  constructor
  · intro _
    exact ⟨(), rfl⟩
  · intro _ _ _
    exact Nat.le_refl 0

theorem own_deeds_undelivered
    (deed reception : grid.Weld) (_hdeed : deed.agent = ()) :
    ¬ DeliveredTo grid deed reception := by
  simp [DeliveredTo, grid]

theorem effectiveTerminus : WaaEffectiveTerminus grid () :=
  waaEffectiveTerminus_of_responsiveTerminus_of_undelivered
    grid responsiveTerminus own_deeds_undelivered

theorem content_trueAt :
    (waaPathClaimLanguage grid).TrueAt (Tier.actTime weld) content := by
  intro hlive
  exact False.elim (hlive (Nat.le_refl 0))

theorem silent_noNescience : WaaNoNescience grid silentReading () := by
  intro u _ _ _
  have := u.voiced
  simp [silentReading] at this

theorem thinking_noNescience : WaaNoNescience grid thinkingReading () := by
  intro u _ _ _
  have hcontent : u.content = content := by
    simpa [thinkingReading] using u.voiced.symm
  rw [hcontent]
  rcases u.weld with ⟨⟨⟩, ⟨⟩, ⟨⟩⟩
  exact content_trueAt

theorem silent_fullyEnlightened :
    WaaFullyEnlightened grid silentReading () :=
  ⟨effectiveTerminus, silent_noNescience⟩

theorem thinking_fullyEnlightened :
    WaaFullyEnlightened grid thinkingReading () :=
  ⟨effectiveTerminus, thinking_noNescience⟩

def noFidelity
    (_ : RecordedUtterance grid (waaPathClaimLanguage grid)) : Prop := False

theorem silent_no_speech_occurrence :
    ¬ WaaFaithfulSpeechOccurrence grid silentReading noFidelity () := by
  rintro ⟨u, _hagent, hspeech, _⟩
  simp [silentReading] at hspeech

theorem thinking_no_speech_occurrence :
    ¬ WaaFaithfulSpeechOccurrence grid thinkingReading noFidelity () := by
  rintro ⟨u, _hagent, hspeech, _⟩
  simp [thinkingReading] at hspeech

theorem thinking_has_mind_production :
    ∃ u : ProducedUtterance thinkingReading,
      thinkingReading.door u.weld = .mind :=
  ⟨thought, rfl⟩

theorem no_effectiveness_enacted :
    ¬ WaaEffectivenessEnacted grid () :=
  not_effectivenessEnacted_of_undelivered grid own_deeds_undelivered

/-- Both sealed readings are fully enlightened.  One produces no thought and
    the other produces a true thought; neither silently acquires a testimonial
    or enacted deed witness. -/
theorem silent_buddha_models :
    WaaFullyEnlightened grid silentReading () ∧
      WaaFullyEnlightened grid thinkingReading () ∧
      (¬ WaaFaithfulSpeechOccurrence grid silentReading noFidelity ()) ∧
      (¬ WaaFaithfulSpeechOccurrence grid thinkingReading noFidelity ()) ∧
      (∃ u : ProducedUtterance thinkingReading,
        thinkingReading.door u.weld = .mind) ∧
      ¬ WaaEffectivenessEnacted grid () :=
  ⟨silent_fullyEnlightened, thinking_fullyEnlightened,
    silent_no_speech_occurrence, thinking_no_speech_occurrence,
    thinking_has_mind_production, no_effectiveness_enacted⟩

end Sealed

end FaithNegative
end WAA
