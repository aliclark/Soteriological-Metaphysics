/-
================================================================================
  WeldAndArrow.Doctrines.SraddhaNegative
  Negative witnesses for the sraddha conditional
================================================================================

Reading and motivation: Identification/Commentary.lean, C.4.
-/

import WeldAndArrow.Doctrines.Sraddha

namespace WAA
/- ==============================================================================
   Negative witnesses: both antecedents matter
============================================================================== -/

namespace SraddhaNegative

open Grid.DirectedConvention

inductive Being
  | sraddha
  | receiver

inductive Call
  | call

inductive Response
  | response

/-- A responsive terminus whose delivered deed has no share-drop landing for
    the receiver's live prior tendency. -/
def zeroEffectGrid : Grid Nat where
  Being      := Being
  Call       := Call
  Response   := Response
  respondsTo _ _ := some Response.response
  grade b _ _ :=
    match b with
    | .sraddha => 0
    | .receiver => 1
  conditions deed reception :=
    deed.agent = Being.sraddha ∧ reception.agent = Being.receiver

def liveBefore : Config Nat :=
  { tendency := 1 }

def poleBefore : Config Nat :=
  { tendency := 0 }

def deed : zeroEffectGrid.Weld :=
  ⟨Being.sraddha, Call.call, Response.response⟩

def reception : zeroEffectGrid.Weld :=
  ⟨Being.receiver, Call.call, Response.response⟩

theorem liveBefore_not_atBot :
    ¬ AtBot liveBefore.tendency := by
  intro h
  exact Nat.not_succ_le_zero 0 h

theorem poleBefore_atBot :
    AtBot poleBefore.tendency :=
  Nat.le_refl 0

theorem reception_actual :
    zeroEffectGrid.Actual reception :=
  rfl

theorem delivered :
    DeliveredTo zeroEffectGrid deed reception :=
  ⟨rfl, rfl⟩

theorem reception_hasSelfPoleIndex :
    zeroEffectGrid.HasSelfPoleIndex reception := by
  intro hbot
  exact Nat.not_succ_le_zero 0 hbot

theorem aversionContext :
    WaaAversionContext zeroEffectGrid liveBefore reception :=
  { liveBefore := liveBefore_not_atBot
    clenchMismatch := ⟨reception_actual, reception_hasSelfPoleIndex⟩ }

theorem sraddha_responsiveTerminus :
    zeroEffectGrid.ResponsiveTerminus Being.sraddha := by
  constructor
  · intro _c
    exact ⟨Response.response, rfl⟩
  · intro _c _r _hresp
    exact Nat.le_refl 0

theorem not_hasShareDropLanding_liveBefore :
    ¬ HasShareDropLanding zeroEffectGrid liveBefore deed := by
  rintro ⟨received, hland⟩
  have hreceiver : received.agent = Being.receiver := hland.left.left.right
  have hdrop : Strict (zeroEffectGrid.share received) liveBefore.tendency :=
    hland.right
  have hstrict : Strict (1 : Nat) 1 := by
    simpa [zeroEffectGrid, Grid.share, liveBefore, hreceiver] using hdrop
  exact strict_irrefl (1 : Nat) hstrict

theorem not_waaEffectiveTerminus :
    ¬ WaaEffectiveTerminus zeroEffectGrid Being.sraddha := by
  intro hfaith
  exact not_hasShareDropLanding_liveBefore
    (hfaith.right liveBefore deed reception rfl liveBefore_not_atBot delivered)

/-- Dropping the faith conjunct leaves delivery and aversion insufficient. -/
theorem drop_faith_antecedent_fails :
    zeroEffectGrid.ResponsiveTerminus Being.sraddha ∧
      DeliveredTo zeroEffectGrid deed reception ∧
      WaaAversionContext zeroEffectGrid liveBefore reception ∧
      ¬ HasShareDropLanding zeroEffectGrid liveBefore deed :=
  ⟨sraddha_responsiveTerminus, delivered, aversionContext,
    not_hasShareDropLanding_liveBefore⟩

theorem not_hasShareDropLanding_poleBefore :
    ¬ HasShareDropLanding zeroEffectGrid poleBefore deed :=
  no_waa_path_at_pole zeroEffectGrid poleBefore_atBot deed

/-- Dropping the aversion conjunct leaves a pole-prior case where no
    share-drop landing is constructible. -/
theorem drop_aversion_antecedent_fails :
    AtBot poleBefore.tendency ∧
      DeliveredTo zeroEffectGrid deed reception ∧
      ¬ WaaAversionContext zeroEffectGrid poleBefore reception ∧
      ¬ HasShareDropLanding zeroEffectGrid poleBefore deed :=
  ⟨poleBefore_atBot, delivered,
    no_waa_aversion_context_at_pole zeroEffectGrid poleBefore_atBot reception,
    not_hasShareDropLanding_poleBefore⟩

end SraddhaNegative

/- ==============================================================================
   Sraddha orthogonality countermodel
============================================================================== -/

namespace OrthogonalityNegative

open Grid.DirectedConvention

/-- The same zero-effectiveness witness used by `SraddhaNegative`: a responsive
    terminus whose delivered deed does not land as a share-drop for the live
    receiver context. -/
abbrev zeroEffectGrid : Grid Nat :=
  SraddhaNegative.zeroEffectGrid

theorem responsiveTerminus_with_no_shareDropLanding :
    zeroEffectGrid.ResponsiveTerminus SraddhaNegative.Being.sraddha ∧
      ¬ HasShareDropLanding zeroEffectGrid SraddhaNegative.liveBefore SraddhaNegative.deed :=
  ⟨SraddhaNegative.sraddha_responsiveTerminus,
    SraddhaNegative.not_hasShareDropLanding_liveBefore⟩

theorem terminus_not_waaEffectiveTerminus :
    zeroEffectGrid.Terminus SraddhaNegative.Being.sraddha ∧
      ¬ WaaEffectiveTerminus zeroEffectGrid SraddhaNegative.Being.sraddha :=
  ⟨SraddhaNegative.sraddha_responsiveTerminus.right,
    SraddhaNegative.not_waaEffectiveTerminus⟩

/-- `WaaEffectiveTerminus` is strictly stronger than terminus typing: it
    implies terminus, and this concrete responsive terminus still fails the
    shortfall-closure conjunct. -/
theorem waaEffectiveTerminus_stronger_than_terminus :
    (WaaEffectiveTerminus zeroEffectGrid SraddhaNegative.Being.sraddha →
        zeroEffectGrid.Terminus SraddhaNegative.Being.sraddha) ∧
      zeroEffectGrid.Terminus SraddhaNegative.Being.sraddha ∧
      ¬ WaaEffectiveTerminus zeroEffectGrid SraddhaNegative.Being.sraddha := by
  constructor
  · intro h
    exact (responsiveTerminus_of_waaEffectiveTerminus zeroEffectGrid h).right
  · exact terminus_not_waaEffectiveTerminus

end OrthogonalityNegative

end WAA
