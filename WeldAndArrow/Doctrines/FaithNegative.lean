/-
================================================================================
  WeldAndArrow.Doctrines.FaithNegative
  Negative witnesses for the abstracted faith principle
================================================================================

Two facts keep `WaaFaithPrinciple` honest as a faith-shaped antecedent:

  1. `waaFaithPrinciple_id_fails`: even taking `WaaFullyEnlightened G b` as a
     premise does not yield the principle. A fully enlightened buddha can utter
     a path claim about another being's deed, and nothing in the enlightenment
     proposition makes that claim true.

  2. `waaFaithPrinciple_trivial_fails`: free faith (`Faith := fun _ => True`)
     does not supply truth-transmission either.

Together with `SraddhaNegative`, the abstraction adds no assertion the old
bundling avoided.
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

/-- A grid in which the buddha is fully enlightened for free: its own deeds are
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
theorem buddha_waaFullyEnlightened :
    WaaFullyEnlightened grid Being.buddha := by
  refine ⟨buddha_responsiveTerminus, ?_⟩
  intro before deed reception hdeed _hlive hdel
  obtain ⟨hdisciple, _hreceiver⟩ := hdel
  rw [hdeed] at hdisciple
  exact Being.noConfusion hdisciple

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
  offeredAt := Tier.floor
  content   := ⟨liveBefore, discipleDeed, reception⟩

theorem falseClaim_not_fitsOfferedTier :
    ¬ falseClaim.FitsOfferedTier := by
  intro hfit
  change (waaPathClaimLanguage grid).TrueAt falseClaim.offeredAt
    falseClaim.content at hfit
  dsimp [waaPathClaimLanguage, ClaimLanguage.TrueAt, falseClaim,
    ShortfallClosedAt] at hfit
  exact not_hasShareDropLanding (hfit liveBefore_not_atBot delivered)

/-- Taking-as-premise faith does not validate the unrestricted principle:
    the enlightenment proposition itself is in hand, but the uttered path claim
    about another being's deed is still false. -/
theorem waaFaithPrinciple_id_fails :
    ¬ WaaFaithPrinciple grid (waaPathClaimLanguage grid) (fun P => P) := by
  intro hFP
  exact falseClaim_not_fitsOfferedTier
    (hFP Being.buddha buddha_waaFullyEnlightened falseClaim rfl)

/-- Nor does free faith: an operator holding everywhere, without the
    truth-transmission principle, lands nothing. -/
theorem waaFaithPrinciple_trivial_fails :
    ¬ WaaFaithPrinciple grid (waaPathClaimLanguage grid) (fun _ => True) := by
  intro hFP
  exact falseClaim_not_fitsOfferedTier
    (hFP Being.buddha trivial falseClaim rfl)

end FaithNegative

end WAA
