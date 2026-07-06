/-
================================================================================
  WeldAndArrow.Doctrines.Faith
  Testimonial abstraction of the sraddha conditional
================================================================================

Faith is modeled as an arbitrary attitude operator on propositions. The grid
never derives it and the principle below is held only as an antecedent: faith in
a fully enlightened being transmits truth to that being's recorded utterances.

Reading and motivation: Identification/Commentary.lean, C.4.
-/

import WeldAndArrow.Doctrines.Sraddha

namespace WAA

namespace Grid

namespace DirectedConvention

variable {Contrib : Type} [PreorderBot Contrib]
variable (G : Grid Contrib)

/- ==============================================================================
   Faith as testimonial truth-transmission
============================================================================== -/

/-- A path claim records the local physician sentence: for this prior
    configuration, this delivered deed closes shortfall at this reception. -/
structure WaaPathClaim where
  before   : Config Contrib
  deed     : G.Weld
  reception : G.Weld

/-- The object language for path claims. Its truth condition is exactly local
    shortfall closure; the tier is ignored because the claim is not a
    separate/fuse distinction. -/
def waaPathClaimLanguage : ClaimLanguage G where
  Claim := WaaPathClaim G
  Holds := fun _ claim =>
    ShortfallClosedAt G claim.before claim.deed claim.reception

/-- A lawless faith attitude supports testimony only when paired with this
    principle: faith in a fully enlightened being makes that being's recorded
    utterances true at their offered tier. -/
def WaaFaithPrinciple (L : ClaimLanguage G) (Faith : Prop → Prop) : Prop :=
  ∀ b : G.Being,
    Faith (WaaFullyEnlightened G b) →
      ∀ u : RecordedUtterance G L,
        u.weld.agent = b →
          u.FitsOfferedTier

/-- Direct use of the faith principle: what a trusted fully enlightened speaker
    says is true, in the existing offered-tier sense. -/
theorem waa_says_true_of_faith
    {L : ClaimLanguage G} {Faith : Prop → Prop}
    (hprinciple : WaaFaithPrinciple G L Faith)
    {b : G.Being} (hfaith : Faith (WaaFullyEnlightened G b))
    (u : RecordedUtterance G L) (hutter : u.weld.agent = b) :
    u.FitsOfferedTier :=
  hprinciple b hfaith u hutter

/-- On own-deed path claims, the old direct route already supplies truth:
    `WaaFullyEnlightened` closes shortfall for the being's own delivered deeds,
    no matter who records the claim. -/
theorem fitsOfferedTier_of_waaFullyEnlightened_ownDeed
    {b : G.Being} (h : WaaFullyEnlightened G b)
    (u : RecordedUtterance G (waaPathClaimLanguage G))
    (hdeed : u.content.deed.agent = b) :
    u.FitsOfferedTier := by
  change (waaPathClaimLanguage G).TrueAt u.offeredAt u.content
  dsimp [waaPathClaimLanguage, ClaimLanguage.TrueAt]
  exact h.right u.content.before u.content.deed u.content.reception hdeed

/-- The testimonial route to the sraddha landing. Unlike the direct route in
    `Sraddha`, the deed need not be the speaker's own deed; the principle covers
    what the faith-object says. -/
theorem waa_path_landing_of_faithPrinciple
    {Faith : Prop → Prop} {b : G.Being}
    (hprinciple : WaaFaithPrinciple G (waaPathClaimLanguage G) Faith)
    (hfaith : Faith (WaaFullyEnlightened G b))
    (u : RecordedUtterance G (waaPathClaimLanguage G))
    (hutter : u.weld.agent = b)
    (hdel : DeliveredTo G u.content.deed u.content.reception)
    (hctx : WaaAversionContext G u.content.before u.content.reception) :
    HasShareDropLanding G u.content.before u.content.deed := by
  have hfit : u.FitsOfferedTier :=
    hprinciple b hfaith u hutter
  have hclosed :
      ShortfallClosedAt G u.content.before u.content.deed u.content.reception := by
    change (waaPathClaimLanguage G).TrueAt u.offeredAt u.content at hfit
    simpa [waaPathClaimLanguage, ClaimLanguage.TrueAt] using hfit
  exact hclosed hctx.liveBefore hdel

/-- The faith-mediated fourth-truth ought as an implication type only. -/
def WaaFaithOught
    (Faith : Prop → Prop) (b : G.Being)
    (u : RecordedUtterance G (waaPathClaimLanguage G)) : Prop :=
  WaaFaithPrinciple G (waaPathClaimLanguage G) Faith →
    Faith (WaaFullyEnlightened G b) →
      u.weld.agent = b →
        DeliveredTo G u.content.deed u.content.reception →
          WaaAversionContext G u.content.before u.content.reception →
            HasShareDropLanding G u.content.before u.content.deed

/-- The grid proves only the conditional: principle, faith, testimony, delivery,
    and live aversion imply the landing. -/
theorem waaFaithOught_conditional
    (Faith : Prop → Prop) (b : G.Being)
    (u : RecordedUtterance G (waaPathClaimLanguage G)) :
    WaaFaithOught G Faith b u := by
  intro hprinciple hfaith hutter hdel hctx
  exact waa_path_landing_of_faithPrinciple
    G hprinciple hfaith u hutter hdel hctx

end DirectedConvention

end Grid

end WAA
