/-
================================================================================
  WeldAndArrow.Doctrines.OtherPower
  Other-power as delivery-regime, not a second act grammar
================================================================================

Reception is a deed either way. Tariki names a delivery-regime, not a second
act-grammar: Dogen's passive "being verified" reading is modeled by ordinary
reception-welds whose delivery line is supplied from elsewhere. No theorem in
this module ranks self-power and other-power against one another; that
no-polemic clause is part of the model design.

The checked surface uses only existing predicates: `Actual`, `share`,
`conditions`/`DeliveredTo`, `ResponseInvariant`, and `HasShareDropLanding`.
-/

import WeldAndArrow.Consequences.Basic

namespace WAA

namespace Grid
namespace DirectedConvention

variable {Contrib : Type} [PreorderBot Contrib]
variable (G : Grid Contrib)

/-- Changing only the delivery relation does not change the reception's grade,
    share, or actuality. The sower's identity is delivery data; reception
    typing reads the weld itself. -/
theorem reception_typing_ignores_sower
    (conditions₁ conditions₂ : G.Weld -> G.Weld -> Prop)
    (reception : G.Weld) :
    (G.withConditions conditions₁).grade
        reception.agent reception.call reception.response =
      (G.withConditions conditions₂).grade
        reception.agent reception.call reception.response ∧
    (G.withConditions conditions₁).share reception =
      (G.withConditions conditions₂).share reception ∧
    ((G.withConditions conditions₁).Actual reception ↔
      (G.withConditions conditions₂).Actual reception) :=
  ⟨G.grade_independent_of_conditions conditions₁ conditions₂
      reception.agent reception.call reception.response,
    G.share_independent_of_conditions conditions₁ conditions₂ reception,
    Iff.rfl⟩

/-- Same-agent lines and cross-agent lines both fill the ordinary reach-back
    relation once the model supplies the delivery line. The actuality
    hypothesis records that the reception is a deed; the conclusion is just the
    shared first conjunct of the two delivery-regime predicates. -/
theorem waaReachBack_filled_either_regime
    {deed reception : G.Weld} (_hactual : G.Actual reception) :
    (SameAgentDelivery G deed reception →
        WaaReachBackFull G deed reception) ∧
      (CrossAgentDelivery G deed reception →
        WaaReachBackFull G deed reception) :=
  ⟨fun h => h.left, fun h => h.left⟩

/-- Other-power line: a cross-agent delivery line read in WAA vocabulary. -/
abbrev WaaTarikiLine (deed reception : G.Weld) : Prop :=
  CrossAgentDelivery G deed reception

/-- Self-power line: a same-agent delivery line read in WAA vocabulary. -/
abbrev WaaJirikiLine (deed reception : G.Weld) : Prop :=
  SameAgentDelivery G deed reception

end DirectedConvention
end Grid

/- ==============================================================================
   Tariki perfected limit model
============================================================================== -/

namespace TarikiCase

open Grid
open Grid.DirectedConvention

inductive Being
  | invoker
  | name
deriving DecidableEq

inductive Call
  | heard
deriving DecidableEq

inductive Response
  | chime
  | receive
deriving DecidableEq

/-- A two-being model: the name chimes independent of the call, the invoker
    receives, and delivery sends the name's weld to every invoker reception.
    This checks grammar only; it asserts no Pure Land doctrine and no ranking
    of regimes. -/
def tarikiGrid : Grid Nat where
  Being      := Being
  Call       := Call
  Response   := Response
  respondsTo b _ :=
    match b with
    | .name    => some Response.chime
    | .invoker => some Response.receive
  grade b _ _ :=
    match b with
    | .name    => 0
    | .invoker => 1
  conditions deed reception :=
    deed.agent = Being.name ∧ reception.agent = Being.invoker

def liveBefore : Config Nat :=
  { tendency := 2 }

/-- The fixed call-source weld. Its call is still carried by the weld; a
    quotation severed from its call would be quotable, never gradeable. -/
def nameWeld : tarikiGrid.Weld :=
  ⟨Being.name, Call.heard, Response.chime⟩

def invokerReception : tarikiGrid.Weld :=
  ⟨Being.invoker, Call.heard, Response.receive⟩

theorem nameWeld_actual :
    tarikiGrid.Actual nameWeld :=
  rfl

theorem invokerReception_actual :
    tarikiGrid.Actual invokerReception :=
  rfl

theorem liveBefore_not_atBot :
    ¬ AtBot liveBefore.tendency := by
  intro h
  exact Nat.not_succ_le_zero 1 h

theorem name_responseInvariant :
    tarikiGrid.ResponseInvariant Being.name := by
  intro c₁ c₂ r₁ r₂ h₁ h₂
  cases c₁
  cases c₂
  cases r₁ <;> cases r₂ <;> simp [tarikiGrid] at h₁ h₂ ⊢

theorem name_actualAgentInhabited :
    tarikiGrid.ActualAgentInhabited Being.name :=
  ⟨⟨Being.name, Call.heard, Response.chime⟩, rfl, rfl⟩

theorem name_share_bot
    (w : tarikiGrid.Weld) (hagent : w.agent = Being.name) :
    tarikiGrid.share w = 0 := by
  cases w with
  | mk agent call response =>
      cases hagent
      rfl

theorem name_object_axis_entire
    (reception : tarikiGrid.Weld) (hagent : reception.agent = Being.invoker) :
    DeliveredTo tarikiGrid nameWeld reception :=
  ⟨rfl, hagent⟩

/-- The fixed-call source lands at every actual invoker reception as a
    share-drop from `liveBefore`. This is the effective corner opposite
    `OrthogonalityNegative`: non-adaptivity does not by itself decide
    effectiveness. -/
theorem universal_fixed_call_lands_without_reading
    (reception : tarikiGrid.Weld)
    (hagent : reception.agent = Being.invoker)
    (hactual : tarikiGrid.Actual reception) :
    HasShareDropLanding tarikiGrid liveBefore nameWeld := by
  refine ⟨reception,
    ⟨⟨name_object_axis_entire reception hagent, hactual⟩, ?_⟩⟩
  cases reception with
  | mk agent call response =>
      cases hagent
      dsimp [Grid.IsShareDrop, Grid.share, tarikiGrid, liveBefore]
      constructor
      · show (1 : Nat) ≤ 2
        decide
      · show ¬ (2 : Nat) ≤ 1
        decide

theorem name_to_invoker_tarikiLine :
    WaaTarikiLine tarikiGrid nameWeld invokerReception := by
  constructor
  · exact name_object_axis_entire invokerReception rfl
  · intro h
    cases h

theorem fixed_call_landing_witness :
    HasShareDropLanding tarikiGrid liveBefore nameWeld :=
  universal_fixed_call_lands_without_reading
    invokerReception rfl invokerReception_actual

/-- The invoker's reception is an ordinary actual deed with ordinary live
    share, even though the delivery-regime is cross-agent. -/
theorem invoker_reception_is_deed :
    tarikiGrid.Actual invokerReception ∧
      tarikiGrid.share invokerReception = 1 ∧
        tarikiGrid.HasSelfPoleIndex invokerReception := by
  constructor
  · exact invokerReception_actual
  · constructor
    · rfl
    · intro hbot
      exact Nat.not_succ_le_zero 0 hbot

end TarikiCase

end WAA
