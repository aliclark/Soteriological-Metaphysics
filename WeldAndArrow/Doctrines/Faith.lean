/-
================================================================================
  WeldAndArrow.Doctrines.Faith
  Testimonial abstraction of the sraddha conditional
================================================================================

Faith is modeled as an arbitrary attitude operator on propositions. The grid
derives neither its factivity nor occurrence fidelity. Testimony proceeds only
when the held faith-object is factive, the particular record is faithful, and
the offer is conventional. A floor-offered record is error-free only vacuously:
it transmits no content through this route because the act-time premise fails.
The standing two-obscurations bundle admits the sealed-and-silent pratyeka
face; the enacted bundle adds witnessed deed and speech for the samyak face.

Reading and motivation: Identification/Commentary.lean, C.4.
-/

import WeldAndArrow.Doctrines.Shusho

namespace WAA

namespace Grid

namespace DirectedConvention

variable {Contrib : Type} [PreorderBot Contrib]
variable (G : Grid Contrib)

/- ==============================================================================
   Faith as fidelity-guarded testimony
============================================================================== -/

/-- A path claim records the local physician sentence: for this prior
    configuration, this delivered deed closes shortfall at this reception. -/
structure WaaPathClaim where
  before   : Config Contrib
  deed     : G.Weld
  reception : G.Weld

/-- The object language for path claims. At the floor it is silent; at act-time
    its truth condition is exactly local shortfall closure. -/
def waaPathClaimLanguage : ClaimLanguage G where
  Claim := WaaPathClaim G
  Holds
    | .floor, _ => False
    | .actTime _, claim =>
        ShortfallClosedAt G claim.before claim.deed claim.reception

/-- Factivity is the undischarged identity component of faith: what the
    attitude holds must in fact obtain. The grid never proves this principle
    from field facts. -/
def Factive (Faith : Prop → Prop) : Prop :=
  ∀ P : Prop, Faith P → P

/-- Positive act-time truth in faithfully recorded speech. The quantifier is
    deliberately restricted to conventional offers: floor offers transmit no
    content, while `Fidelity` remains a separate per-utterance hypothesis with
    the same open status as delivery. -/
def WaaNoDelusion
    (Fidelity : RecordedUtterance G (waaPathClaimLanguage G) → Prop)
    (b : G.Being) : Prop :=
  ∀ u : RecordedUtterance G (waaPathClaimLanguage G),
    u.weld.agent = b → Fidelity u →
      ∀ w : G.Weld, u.offeredAt = Tier.actTime w →
        (waaPathClaimLanguage G).TrueAt u.offeredAt u.content

/-- Positive act-time no-delusion constructively entails the privative error
    verdict. No double-negation elimination is needed: the supplied truth
    directly contradicts the misfit witness's falsity component. -/
theorem waaNoDelusion_not_misfits
    {Fidelity : RecordedUtterance G (waaPathClaimLanguage G) → Prop}
    {b : G.Being} (h : WaaNoDelusion G Fidelity b)
    (u : RecordedUtterance G (waaPathClaimLanguage G))
    (hutter : u.weld.agent = b) (hfid : Fidelity u) :
    ¬ u.MisfitsOfferedTier := by
  rintro ⟨w, hoff, hnot⟩
  exact hnot (h u hutter hfid w hoff)

/-- Full enlightenment removes both obscurations. `effective` is the
    afflictive-obscuration face (`WaaEffectiveTerminus`); `noDelusion` is the
    cognitive-obscuration face governing faithful speech. `FaithNegative`
    separates the two conjuncts. -/
structure WaaFullyEnlightened
    (Fidelity : RecordedUtterance G (waaPathClaimLanguage G) → Prop)
    (b : G.Being) : Prop where
  effective : WaaEffectiveTerminus G b
  noDelusion : WaaNoDelusion G Fidelity b

/-- A witnessed faithful sentence: an attributed, faithful record offered at
    act-time and fitting there. This names the non-vacuous speech content that
    standing no-delusion leaves open when no faithful utterances occur. -/
def WaaFaithfulSpeechEnacted
    (Fidelity : RecordedUtterance G (waaPathClaimLanguage G) → Prop)
    (b : G.Being) : Prop :=
  ∃ u : RecordedUtterance G (waaPathClaimLanguage G),
    u.weld.agent = b ∧ Fidelity u ∧
      ∃ w : G.Weld, u.offeredAt = Tier.actTime w ∧ u.FitsOfferedTier

/-- If the standing speech conditional has an empty faithful domain, its
    enacted speech witness is impossible. This is the silent-face fence. -/
theorem not_faithfulSpeechEnacted_of_no_faithful_utterance
    {Fidelity : RecordedUtterance G (waaPathClaimLanguage G) → Prop}
    {b : G.Being}
    (hnone : ∀ u : RecordedUtterance G (waaPathClaimLanguage G),
      u.weld.agent = b → Fidelity u → False) :
    ¬ WaaFaithfulSpeechEnacted G Fidelity b := by
  rintro ⟨u, hagent, hfaithful, _witness⟩
  exact hnone u hagent hfaithful

/-- Enacted full enlightenment witnesses both conditionals of the standing
    bundle. `deedWitness` supplies an own effective occurrence; `speechWitness`
    supplies faithful, fitting act-time testimony. The standing bundle permits
    the sealed and silent pratyekabuddha face, while this enacted rung names the
    samyaksambuddha who touches and teaches. -/
structure WaaFullyEnlightenedEnacted
    (Fidelity : RecordedUtterance G (waaPathClaimLanguage G) → Prop)
    (b : G.Being) : Prop where
  standing : WaaFullyEnlightened G Fidelity b
  deedWitness : WaaEffectivenessEnacted G b
  speechWitness : WaaFaithfulSpeechEnacted G Fidelity b

/-- Standing full enlightenment always contains effective termination. -/
theorem waaEffectiveTerminus_of_fullyEnlightened
    {Fidelity : RecordedUtterance G (waaPathClaimLanguage G) → Prop}
    {b : G.Being} (h : WaaFullyEnlightened G Fidelity b) :
    WaaEffectiveTerminus G b :=
  h.effective

/-- The enacted top rung forgets to the standing two-obscurations bundle. -/
theorem waaFullyEnlightened_of_fullyEnlightenedEnacted
    {Fidelity : RecordedUtterance G (waaPathClaimLanguage G) → Prop}
    {b : G.Being} (h : WaaFullyEnlightenedEnacted G Fidelity b) :
    WaaFullyEnlightened G Fidelity b :=
  h.standing

/-- The enacted top rung exposes its delivered effective occurrence. -/
theorem waaEffectivenessEnacted_of_fullyEnlightenedEnacted
    {Fidelity : RecordedUtterance G (waaPathClaimLanguage G) → Prop}
    {b : G.Being} (h : WaaFullyEnlightenedEnacted G Fidelity b) :
    WaaEffectivenessEnacted G b :=
  h.deedWitness

/-- The enacted top rung exposes its faithful, fitting act-time sentence. -/
theorem waaFaithfulSpeechEnacted_of_fullyEnlightenedEnacted
    {Fidelity : RecordedUtterance G (waaPathClaimLanguage G) → Prop}
    {b : G.Being} (h : WaaFullyEnlightenedEnacted G Fidelity b) :
    WaaFaithfulSpeechEnacted G Fidelity b :=
  h.speechWitness

/-- Factive faith in the full bundle exposes its no-delusion conjunct. -/
theorem waaNoDelusion_of_factive_faith
    {Faith : Prop → Prop}
    {Fidelity : RecordedUtterance G (waaPathClaimLanguage G) → Prop}
    {b : G.Being}
    (hfact : Factive Faith)
    (hfaith : Faith (WaaFullyEnlightened G Fidelity b)) :
    WaaNoDelusion G Fidelity b :=
  (hfact _ hfaith).noDelusion

/-- The open vacuity face: without any faithful attributed utterance,
    no-delusion holds without producing testimonial content. -/
theorem waaNoDelusion_of_no_faithful_utterance
    (Fidelity : RecordedUtterance G (waaPathClaimLanguage G) → Prop)
    (b : G.Being)
    (hnone : ∀ u : RecordedUtterance G (waaPathClaimLanguage G),
      u.weld.agent = b → ¬ Fidelity u) :
    WaaNoDelusion G Fidelity b := by
  intro u hagent hfaithful
  exact False.elim (hnone u hagent hfaithful)

/-- The bundle's sealed-channel face: an effective terminus with no faithful
    attributed utterances satisfies full enlightenment vacuously on the speech
    conjunct. The concrete witness in `FaithNegative` fences this face from
    non-vacuous faithful testimony. -/
theorem waaFullyEnlightened_of_effectiveTerminus_of_no_faithful_utterance
    (Fidelity : RecordedUtterance G (waaPathClaimLanguage G) → Prop)
    {b : G.Being} (heffective : WaaEffectiveTerminus G b)
    (hnone : ∀ u : RecordedUtterance G (waaPathClaimLanguage G),
      u.weld.agent = b → ¬ Fidelity u) :
    WaaFullyEnlightened G Fidelity b :=
  ⟨heffective, waaNoDelusion_of_no_faithful_utterance G Fidelity b hnone⟩

/-- Buddha's-silence face for path testimony: a floor-offered record is outside
    the conventional error family, but carries no positive testimonial fit. -/
theorem waaPath_not_misfits_of_floor_offer
    (u : RecordedUtterance G (waaPathClaimLanguage G))
    (hoff : u.offeredAt = Tier.floor) :
    ¬ u.MisfitsOfferedTier := by
  rintro ⟨w, hact, _hfalse⟩
  rw [hoff] at hact
  cases hact

/-- Factive faith plus occurrence fidelity yields the character predicate's
    negative verdict for this record. -/
theorem waa_no_misfit_of_stance
    {Faith : Prop → Prop}
    {Fidelity : RecordedUtterance G (waaPathClaimLanguage G) → Prop}
    {b : G.Being}
    (hfact : Factive Faith)
    (hfaith : Faith (WaaFullyEnlightened G Fidelity b))
    (u : RecordedUtterance G (waaPathClaimLanguage G))
    (hutter : u.weld.agent = b) (hfid : Fidelity u) :
    ¬ u.MisfitsOfferedTier :=
  waaNoDelusion_not_misfits G
    (waaNoDelusion_of_factive_faith G hfact hfaith) u hutter hfid

/-- The positive character predicate yields truth directly at a conventional
    offer. Floor offers are outside its quantifier rather than made true. -/
theorem waa_says_true_at_actTime_of_stance
    {Faith : Prop → Prop}
    {Fidelity : RecordedUtterance G (waaPathClaimLanguage G) → Prop}
    {b : G.Being}
    (hfact : Factive Faith)
    (hfaith : Faith (WaaFullyEnlightened G Fidelity b))
    (u : RecordedUtterance G (waaPathClaimLanguage G))
    (hutter : u.weld.agent = b) (hfid : Fidelity u)
    (w : G.Weld) (hoff : u.offeredAt = Tier.actTime w) :
    u.FitsOfferedTier :=
  waaNoDelusion_of_factive_faith G hfact hfaith u hutter hfid w hoff

/-- The fidelity-guarded testimonial route to offered-tier fit. -/
theorem waa_says_true_of_faith
    {Faith : Prop → Prop}
    {Fidelity : RecordedUtterance G (waaPathClaimLanguage G) → Prop}
    {b : G.Being}
    (hfact : Factive Faith)
    (hfaith : Faith (WaaFullyEnlightened G Fidelity b))
    (u : RecordedUtterance G (waaPathClaimLanguage G))
    (hutter : u.weld.agent = b) (hfid : Fidelity u)
    (w : G.Weld) (hoff : u.offeredAt = Tier.actTime w) :
    u.FitsOfferedTier :=
  waa_says_true_at_actTime_of_stance
    G hfact hfaith u hutter hfid w hoff

/-- On own-deed path claims, the direct route already supplies truth:
    `WaaEffectiveTerminus` closes shortfall for the being's own delivered deeds,
    no matter who records the claim. -/
theorem fitsOfferedTier_of_waaEffectiveTerminus_ownDeed
    {b : G.Being} (h : WaaEffectiveTerminus G b)
    (u : RecordedUtterance G (waaPathClaimLanguage G))
    (hdeed : u.content.deed.agent = b)
    (w : G.Weld) (hoff : u.offeredAt = Tier.actTime w) :
    u.FitsOfferedTier := by
  change (waaPathClaimLanguage G).TrueAt u.offeredAt u.content
  rw [hoff]
  dsimp [waaPathClaimLanguage, ClaimLanguage.TrueAt]
  exact h.right u.content.before u.content.deed u.content.reception hdeed

/-- The testimonial route to the śraddhā landing. Unlike the direct route in
    `Sraddha`, the deed need not be the speaker's own deed; factive faith,
    faithful occurrence, and conventional offering jointly license the claim. -/
theorem waa_path_landing_of_stance
    {Faith : Prop → Prop}
    {Fidelity : RecordedUtterance G (waaPathClaimLanguage G) → Prop}
    {b : G.Being}
    (hfact : Factive Faith)
    (hfaith : Faith (WaaFullyEnlightened G Fidelity b))
    (u : RecordedUtterance G (waaPathClaimLanguage G))
    (hutter : u.weld.agent = b) (hfid : Fidelity u)
    (w : G.Weld) (hoff : u.offeredAt = Tier.actTime w)
    (hdel : DeliveredTo G u.content.deed u.content.reception)
    (hctx : WaaAversionContext G u.content.before u.content.reception) :
    HasShareDropLanding G u.content.before u.content.deed := by
  have hfit : u.FitsOfferedTier :=
    waa_says_true_of_faith G hfact hfaith u hutter hfid w hoff
  have hclosed :
      ShortfallClosedAt G u.content.before u.content.deed u.content.reception := by
    change (waaPathClaimLanguage G).TrueAt u.offeredAt u.content at hfit
    rw [hoff] at hfit
    simpa [waaPathClaimLanguage, ClaimLanguage.TrueAt] using hfit
  exact hclosed hctx.liveBefore hdel

/-- The faith-mediated fourth-truth ought as an implication type only. -/
def WaaFaithOught
    (Fidelity : RecordedUtterance G (waaPathClaimLanguage G) → Prop)
    (Faith : Prop → Prop) (b : G.Being)
    (u : RecordedUtterance G (waaPathClaimLanguage G)) (w : G.Weld) : Prop :=
  Factive Faith →
    Faith (WaaFullyEnlightened G Fidelity b) →
      Fidelity u →
        u.offeredAt = Tier.actTime w →
          u.weld.agent = b →
            DeliveredTo G u.content.deed u.content.reception →
              WaaAversionContext G u.content.before u.content.reception →
                HasShareDropLanding G u.content.before u.content.deed

/-- The grid proves only the conditional: principle, faith, testimony, delivery,
    and live aversion imply the landing. -/
theorem waaFaithOught_conditional
    (Fidelity : RecordedUtterance G (waaPathClaimLanguage G) → Prop)
    (Faith : Prop → Prop) (b : G.Being)
    (u : RecordedUtterance G (waaPathClaimLanguage G)) (w : G.Weld) :
    WaaFaithOught G Fidelity Faith b u w := by
  intro hfact hfaith hfid hoff hutter hdel hctx
  exact waa_path_landing_of_stance
    G hfact hfaith u hutter hfid w hoff hdel hctx

end DirectedConvention

end Grid

end WAA
