/-
================================================================================
  WeldAndArrow.Doctrines.FaithNegative
  The two-obscurations separator and non-vacuity witness
================================================================================

The countermodel is the undefiled-nescience witness: effective functioning and
universal shortfall closure do not remove cognitive obscuration. Under total
occurrence fidelity the buddha has `WaaEffectiveTerminus` but lacks
`WaaNoDelusion`, and therefore lacks the two-obscurations bundle
`WaaFullyEnlightened`. Further witnesses prove the strict standing/enacted
ladder, exhibit its sealed-and-silent pratyeka face, and inhabit its samyak top.
-/

import WeldAndArrow.Doctrines.Faith

namespace WAA

namespace FaithNegative

open Grid
open Grid.DirectedConvention

inductive Being
  | buddha
  | disciple
  | receiver

inductive Call
  | call

inductive Response
  | response

/-- A grid in which the buddha is an effective terminus for free: its own deeds are
    never delivered, so shortfall closure for its own deeds is vacuous. The
    disciple's deed is delivered to a receiver whose live share does not drop. -/
def grid : Grid Nat where
  Being      := Being
  Call       := Call
  Response   := Response
  respondsTo _ _ := some Response.response
  grade b _ _ :=
    match b with
    | .buddha   => 0
    | .disciple => 1
    | .receiver => 1
  conditions deed reception :=
    deed.agent = Being.disciple ∧ reception.agent = Being.receiver

def liveBefore : Config Nat :=
  { tendency := 1 }

def discipleDeed : grid.Weld :=
  ⟨Being.disciple, Call.call, Response.response⟩

def reception : grid.Weld :=
  ⟨Being.receiver, Call.call, Response.response⟩

def buddhaWeld : grid.Weld :=
  ⟨Being.buddha, Call.call, Response.response⟩

theorem liveBefore_not_atBot :
    ¬ AtBot liveBefore.tendency := by
  intro h
  exact Nat.not_succ_le_zero 0 h

theorem delivered :
    DeliveredTo grid discipleDeed reception :=
  ⟨rfl, rfl⟩

/-- The buddha side of the model is sealed even though disciple-side delivery
    remains live. This is the deed-vacuity half of the pratyekabuddha witness. -/
theorem buddha_own_deeds_undelivered
    (deed reception : grid.Weld) (hdeed : deed.agent = Being.buddha) :
    ¬ DeliveredTo grid deed reception := by
  rintro ⟨hdisciple, _hreceiver⟩
  rw [hdeed] at hdisciple
  exact Being.noConfusion hdisciple

theorem buddhaWeld_actual :
    grid.Actual buddhaWeld :=
  rfl

theorem buddha_responsiveTerminus :
    grid.ResponsiveTerminus Being.buddha := by
  constructor
  · intro _c
    exact ⟨Response.response, rfl⟩
  · intro _c _r _hresp
    exact Nat.le_refl 0

/-- The buddha's own deeds are never delivered in this grid, so the shortfall
    closure conjunct holds vacuously. -/
theorem buddha_waaEffectiveTerminus :
    WaaEffectiveTerminus grid Being.buddha := by
  refine ⟨buddha_responsiveTerminus, ?_⟩
  intro _before deed reception hdeed _hlive hdel
  exact False.elim (buddha_own_deeds_undelivered deed reception hdeed hdel)

theorem not_hasShareDropLanding :
    ¬ HasShareDropLanding grid liveBefore discipleDeed := by
  rintro ⟨received, hland⟩
  have hreceiver : received.agent = Being.receiver := hland.left.left.right
  have hdrop : Strict (grid.share received) liveBefore.tendency :=
    hland.right
  have hstrict : Strict (1 : Nat) 1 := by
    simpa [grid, Grid.share, liveBefore, hreceiver] using hdrop
  exact strict_irrefl (1 : Nat) hstrict

/-- The buddha's recorded path claim about the disciple's deed is false: the
    delivered deed does not land as a share-drop for the live receiver context. -/
def falseClaim : RecordedUtterance grid (waaPathClaimLanguage grid) where
  weld      := buddhaWeld
  actual    := buddhaWeld_actual
  offeredAt := Tier.actTime buddhaWeld
  content   := ⟨liveBefore, discipleDeed, reception⟩

theorem falseClaim_not_fitsOfferedTier :
    ¬ falseClaim.FitsOfferedTier := by
  intro hfit
  change (waaPathClaimLanguage grid).TrueAt falseClaim.offeredAt
    falseClaim.content at hfit
  dsimp [waaPathClaimLanguage, ClaimLanguage.TrueAt, falseClaim,
    ShortfallClosedAt] at hfit
  exact not_hasShareDropLanding (hfit liveBefore_not_atBot delivered)

/-- Every attributed occurrence is treated as faithful in the separating
    model, so the character conjunct cannot evade the counterexample by a
    sealed channel. -/
def totalFidelity :
    RecordedUtterance grid (waaPathClaimLanguage grid) → Prop :=
  fun _ => True

theorem falseClaim_misfitsOfferedTier :
    falseClaim.MisfitsOfferedTier :=
  ⟨buddhaWeld, rfl, falseClaim_not_fitsOfferedTier⟩

/-- Effective termination does not remove undefiled nescience: under total
    fidelity the attributed false claim refutes no-delusion. -/
theorem buddha_not_waaNoDelusion :
    ¬ WaaNoDelusion grid totalFidelity Being.buddha := by
  intro hno
  exact falseClaim_not_fitsOfferedTier
    (hno falseClaim rfl trivial buddhaWeld rfl)

/-- The two-obscurations separator. Removal of the afflictive obscuration,
    represented by `WaaEffectiveTerminus`, does not by itself remove the
    cognitive obscuration represented by `WaaNoDelusion`. -/
theorem effectiveTerminus_not_waaFullyEnlightened :
    WaaEffectiveTerminus grid Being.buddha ∧
      ¬ WaaFullyEnlightened grid totalFidelity Being.buddha := by
  refine ⟨buddha_waaEffectiveTerminus, ?_⟩
  intro hfull
  exact buddha_not_waaNoDelusion hfull.noDelusion

/-- The first strict ladder joint: full enlightenment always projects to
    effective termination, while total fidelity exposes this effective
    terminus as lacking the standing two-obscurations bundle. -/
theorem effectiveTerminus_strictly_weaker_than_fullyEnlightened :
    (WaaFullyEnlightened grid totalFidelity Being.buddha →
        WaaEffectiveTerminus grid Being.buddha) ∧
      WaaEffectiveTerminus grid Being.buddha ∧
        ¬ WaaFullyEnlightened grid totalFidelity Being.buddha :=
  ⟨fun h => waaEffectiveTerminus_of_fullyEnlightened grid h,
    effectiveTerminus_not_waaFullyEnlightened⟩

/-- Doctrinal name for the same undefiled-nescience witness. -/
theorem aklishta_ajnana_witness :
    WaaEffectiveTerminus grid Being.buddha ∧
      ¬ WaaNoDelusion grid totalFidelity Being.buddha :=
  ⟨buddha_waaEffectiveTerminus, buddha_not_waaNoDelusion⟩

/-- A faithful, fitting, act-time own-deed claim for the non-vacuity witness. -/
def faithfulClaim : RecordedUtterance grid (waaPathClaimLanguage grid) where
  weld := buddhaWeld
  actual := buddhaWeld_actual
  offeredAt := Tier.actTime buddhaWeld
  content := ⟨liveBefore, buddhaWeld, reception⟩

theorem faithfulClaim_fitsOfferedTier :
    faithfulClaim.FitsOfferedTier :=
  fitsOfferedTier_of_waaEffectiveTerminus_ownDeed grid
    buddha_waaEffectiveTerminus faithfulClaim rfl buddhaWeld rfl

/-- Concrete fidelity that records exactly fitting occurrences. -/
def fittingFidelity :
    RecordedUtterance grid (waaPathClaimLanguage grid) → Prop :=
  fun u => u.FitsOfferedTier

theorem buddha_waaNoDelusion_fittingFidelity :
    WaaNoDelusion grid fittingFidelity Being.buddha := by
  intro u _hagent hfit _w _hoff
  exact hfit

/-- The full bundle is non-vacuously inhabited: one faithful, fitting,
    act-time utterance accompanies the two conjuncts. -/
theorem waaFullyEnlightened_faithful_actTime_inhabited :
    WaaFullyEnlightened grid fittingFidelity Being.buddha ∧
      ∃ u : RecordedUtterance grid (waaPathClaimLanguage grid),
        fittingFidelity u ∧
          (∃ w : grid.Weld, u.offeredAt = Tier.actTime w) ∧
            u.FitsOfferedTier := by
  refine ⟨⟨buddha_waaEffectiveTerminus,
    buddha_waaNoDelusion_fittingFidelity⟩, faithfulClaim, ?_, ?_, ?_⟩
  · exact faithfulClaim_fitsOfferedTier
  · exact ⟨buddhaWeld, rfl⟩
  · exact faithfulClaim_fitsOfferedTier

/- ==============================================================================
   The sealed-and-silent pratyekabuddha strictness witness
============================================================================== -/

/-- No record is admitted as faithful in the silent reading. -/
def silentFidelity :
    RecordedUtterance grid (waaPathClaimLanguage grid) → Prop :=
  fun _ => False

theorem buddha_not_waaFaithfulSpeechEnacted_silent :
    ¬ WaaFaithfulSpeechEnacted grid silentFidelity Being.buddha :=
  not_faithfulSpeechEnacted_of_no_faithful_utterance
    grid (by
      intro _u _hagent hfaithful
      exact hfaithful)

theorem buddha_waaFullyEnlightened_silent :
    WaaFullyEnlightened grid silentFidelity Being.buddha :=
  waaFullyEnlightened_of_effectiveTerminus_of_no_faithful_utterance
    grid silentFidelity buddha_waaEffectiveTerminus (by
      intro _u _hagent hfaithful
      exact hfaithful)

theorem buddha_not_waaFullyEnlightenedEnacted_silent :
    ¬ WaaFullyEnlightenedEnacted grid silentFidelity Being.buddha := by
  intro htop
  exact (not_effectivenessEnacted_of_undelivered grid
    buddha_own_deeds_undelivered) htop.deedWitness

/-- Both existential additions at the enacted rung fail in the same standing
    witness: own deeds are sealed from delivery and faithful speech is silent. -/
theorem buddha_enacted_faces_absent_silent :
    (¬ WaaEffectivenessEnacted grid Being.buddha) ∧
      ¬ WaaFaithfulSpeechEnacted grid silentFidelity Being.buddha :=
  ⟨not_effectivenessEnacted_of_undelivered grid
      buddha_own_deeds_undelivered,
    buddha_not_waaFaithfulSpeechEnacted_silent⟩

/-- The second strict ladder joint: the sealed, silent buddha satisfies the
    standing bundle but not the enacted bundle. This is the checked
    pratyekabuddha face rather than a defect in standing enlightenment. -/
theorem fullyEnlightened_strictly_weaker_than_enacted :
    (WaaFullyEnlightenedEnacted grid silentFidelity Being.buddha →
        WaaFullyEnlightened grid silentFidelity Being.buddha) ∧
      WaaFullyEnlightened grid silentFidelity Being.buddha ∧
        ¬ WaaFullyEnlightenedEnacted grid silentFidelity Being.buddha :=
  ⟨fun h => waaFullyEnlightened_of_fullyEnlightenedEnacted grid h,
    buddha_waaFullyEnlightened_silent,
    buddha_not_waaFullyEnlightenedEnacted_silent⟩

/- ==============================================================================
   A non-vacuous samyaksambuddha inhabitant of the enacted top rung
============================================================================== -/

namespace EnactedWitness

/-- A one-being model in which the pole deed is delivered and lands with a
    share drop for every live prior tendency. -/
def grid : Grid Nat where
  Being := Unit
  Call := Unit
  Response := Unit
  respondsTo _ _ := some ()
  grade _ _ _ := 0
  conditions _ _ := True

def weld : grid.Weld := ⟨(), (), ()⟩

def liveBefore : Config Nat := ⟨1⟩

theorem weld_actual : grid.Actual weld :=
  rfl

theorem liveBefore_not_atBot : ¬ AtBot liveBefore.tendency := by
  intro hbot
  exact Nat.not_succ_le_zero 0 hbot

theorem responsiveTerminus : grid.ResponsiveTerminus () := by
  constructor
  · intro _call
    exact ⟨(), rfl⟩
  · intro _call _response _hresponds
    exact Nat.le_refl 0

theorem effectiveTerminus : WaaEffectiveTerminus grid () := by
  refine ⟨responsiveTerminus, ?_⟩
  intro before _deed reception _hdeed hlive hdel
  refine ⟨reception, ?_⟩
  refine ⟨⟨hdel, rfl⟩, ?_⟩
  exact ⟨Nat.zero_le before.tendency, hlive⟩

theorem effectivenessEnacted : WaaEffectivenessEnacted grid () := by
  refine ⟨effectiveTerminus, liveBefore, weld, weld, rfl, ?_⟩
  refine ⟨⟨weld_actual, Nat.le_refl 0⟩, liveBefore_not_atBot, ?_⟩
  exact ⟨⟨True.intro, weld_actual⟩,
    ⟨Nat.zero_le liveBefore.tendency, liveBefore_not_atBot⟩⟩

def claim : RecordedUtterance grid (waaPathClaimLanguage grid) where
  weld := weld
  actual := weld_actual
  offeredAt := Tier.actTime weld
  content := ⟨liveBefore, weld, weld⟩

theorem claim_fitsOfferedTier : claim.FitsOfferedTier :=
  fitsOfferedTier_of_waaEffectiveTerminus_ownDeed
    grid effectiveTerminus claim rfl weld rfl

def fittingFidelity :
    RecordedUtterance grid (waaPathClaimLanguage grid) → Prop :=
  fun u => u.FitsOfferedTier

theorem noDelusion : WaaNoDelusion grid fittingFidelity () := by
  intro _u _hagent hfit _w _hoff
  exact hfit

theorem fullyEnlightened : WaaFullyEnlightened grid fittingFidelity () :=
  ⟨effectiveTerminus, noDelusion⟩

theorem faithfulSpeechEnacted :
    WaaFaithfulSpeechEnacted grid fittingFidelity () :=
  ⟨claim, rfl, claim_fitsOfferedTier,
    weld, rfl, claim_fitsOfferedTier⟩

theorem fullyEnlightenedEnacted :
    WaaFullyEnlightenedEnacted grid fittingFidelity () :=
  ⟨fullyEnlightened, effectivenessEnacted, faithfulSpeechEnacted⟩

end EnactedWitness

end FaithNegative

end WAA
