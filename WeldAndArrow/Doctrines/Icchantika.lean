/-
================================================================================
  WeldAndArrow.Doctrines.Icchantika
  The icchantika as a declined foreclosure case
================================================================================

Reading and motivation: Identification/Commentary.lean, C.13.
-/

import WeldAndArrow.Doctrines.Sraddha

namespace WAA

open Grid.DirectedConvention

variable {Contrib : Type} [PreorderBot Contrib]

/- ==============================================================================
   Icchantika typing
============================================================================== -/

/-- The icchantika read literally as a run-shape, not as a stored nature:
    an actual occurrence is supplied, and every actual response remains live
    at the self-pole index. Reading and motivation:
    `Identification/Commentary.lean`, C.13. -/
def Icchantika (G : Grid Contrib) (b : G.Being) : Prop :=
  G.ActualAgentInhabited b ∧
    ∀ c r, G.respondsTo b c = some r → G.HasSelfPoleIndex ⟨b, c, r⟩

/-- An icchantika is the terminus's inverse on its mounted run: the mounted
    witness supplies a live self-pole index where terminus typing would force
    the pole-class. Reading and motivation:
    `Identification/Commentary.lean`, C.13. -/
theorem icchantika_not_terminus
    {G : Grid Contrib} {b : G.Being} (h : Icchantika G b) :
    ¬ G.Terminus b := by
  intro hterm
  rcases h.left with ⟨w, hactual, hagent⟩
  have hresp : G.respondsTo b w.call = some w.response := by
    rw [← hagent]
    exact hactual
  exact h.right w.call w.response hresp
    (G.atBot_of_terminus_response hterm hresp)

/-- The honest negative fact: an icchantika cannot be seated as a fully
    enlightened agent on this run, because `WaaEffectiveTerminus` includes
    terminus typing. This is not a verdict that the being cannot become buddha.
    Reading and motivation: `Identification/Commentary.lean`, C.13. -/
theorem not_waaEffectiveTerminus_of_icchantika
    {G : Grid Contrib} {b : G.Being} (h : Icchantika G b) :
    ¬ WaaEffectiveTerminus G b := by
  intro hfull
  exact icchantika_not_terminus (G := G) h hfull.left.right

/-- Receiver-side correction: whenever an actual reception is made by an
    icchantika and the prior tendency is live, the sraddha aversion antecedent
    is available. Reading and motivation:
    `Identification/Commentary.lean`, C.13. -/
theorem aversionContext_of_icchantika_reception
    {G : Grid Contrib} {before : Config Contrib} {b : G.Being}
    {reception : G.Weld}
    (hagent : reception.agent = b) (hic : Icchantika G b)
    (hactual : G.Actual reception) (hlive : ¬ AtBot before.tendency) :
    WaaAversionContext G before reception := by
  refine
    { liveBefore := hlive
      clenchMismatch := ?_ }
  refine ⟨hactual, ?_⟩
  subst b
  simpa using hic.right reception.call reception.response hactual

/-- If a fully enlightened deliverer reaches an icchantika reception, the
    existing sraddha theorem supplies the share-drop landing: the icchantika is
    reachable as receiver even though it cannot be seated as the enlightened
    agent on its run. Reading and motivation:
    `Identification/Commentary.lean`, C.13. -/
theorem icchantika_reachable
    {G : Grid Contrib} {g b : G.Being} {before : Config Contrib}
    {deed reception : G.Weld}
    (hfaith : WaaEffectiveTerminus G g)
    (hdeed : deed.agent = g)
    (hdel : DeliveredTo G deed reception)
    (hreceiver : reception.agent = b) (hic : Icchantika G b)
    (hactual : G.Actual reception) (hlive : ¬ AtBot before.tendency) :
    HasShareDropLanding G before deed :=
  waa_path_landing G hfaith hdeed hdel
    (aversionContext_of_icchantika_reception
      (G := G) hreceiver hic hactual hlive)

/- ==============================================================================
   Concrete non-foreclosure witness
============================================================================== -/

namespace IcchantikaCase

/-- The small carrier used only to witness the declined foreclosure reading. -/
inductive Being
  | buddha
  | icchantika

/-- The single call used by the icchantika witness. -/
inductive Call
  | call

/-- The single response used by the icchantika witness. -/
inductive Response
  | response

/-- A concrete grid where the icchantika mounts a live response and a buddha
    deed is delivered to that response. -/
def grid : Grid Nat where
  Being := Being
  Call := Call
  Response := Response
  respondsTo _ _ := some Response.response
  grade b _ _ :=
    match b with
    | .buddha => 0
    | .icchantika => 1
  conditions deed reception :=
    deed.agent = Being.buddha ∧ reception.agent = Being.icchantika

/-- A live prior tendency high enough for the icchantika reception itself to
    be a share-drop. -/
def liveBefore : Config Nat :=
  { tendency := 2 }

/-- The delivered buddha-side deed in the concrete witness. -/
def deed : grid.Weld :=
  ⟨Being.buddha, Call.call, Response.response⟩

/-- The icchantika-side reception in the concrete witness. -/
def reception : grid.Weld :=
  ⟨Being.icchantika, Call.call, Response.response⟩

/-- The prior tendency in the witness is live. -/
theorem liveBefore_not_atBot :
    ¬ AtBot liveBefore.tendency := by
  dsimp [liveBefore, AtBot, shareBot]
  show ¬ (2 : Nat) ≤ 0
  decide

/-- The icchantika response is actual in the witness grid. -/
theorem reception_actual :
    grid.Actual reception :=
  rfl

/-- The buddha deed is actual in the witness grid. -/
theorem deed_actual :
    grid.Actual deed :=
  rfl

/-- The witness receiver satisfies the icchantika run-shape. -/
theorem receiver_icchantika :
    Icchantika grid Being.icchantika := by
  constructor
  · exact ⟨reception, reception_actual, rfl⟩
  · intro c r _hresp
    cases c
    cases r
    dsimp [Grid.HasSelfPoleIndex, Grid.share, grid, AtBot, shareBot]
    show ¬ (1 : Nat) ≤ 0
    decide

/-- The buddha deed is delivered to the icchantika reception. -/
theorem delivered :
    DeliveredTo grid deed reception :=
  ⟨rfl, rfl⟩

/-- The icchantika reception is itself a share-drop from the live prior
    tendency. -/
theorem reception_shareDrop :
    grid.IsShareDrop liveBefore reception := by
  dsimp [Grid.IsShareDrop, Grid.share, liveBefore, reception, grid]
  constructor
  · show (1 : Nat) ≤ 2
    decide
  · show ¬ (2 : Nat) ≤ 1
    decide

/-- The concrete icchantika receiver is constructible. -/
theorem constructible :
    ∃ b : grid.Being, Icchantika grid b :=
  ⟨Being.icchantika, receiver_icchantika⟩

/-- The delivered icchantika reception lands as a share-drop in the concrete
    witness. -/
theorem landing :
    HasShareDropLanding grid liveBefore deed := by
  exact ⟨reception, ⟨⟨delivered, reception_actual⟩, reception_shareDrop⟩⟩

end IcchantikaCase

/-- Foreclosure is not recovered from the icchantika run: in a concrete grid an
    icchantika-typed receiver is actual, delivered to, and itself participates
    in a share-drop landing from a live prior tendency. Reading and motivation:
    `Identification/Commentary.lean`, C.13. -/
theorem icchantika_release_not_foreclosed :
    ∃ (before : Config Nat) (b : IcchantikaCase.grid.Being)
      (deed reception : IcchantikaCase.grid.Weld),
      Icchantika IcchantikaCase.grid b ∧
        reception.agent = b ∧
          IcchantikaCase.grid.Actual reception ∧
            ¬ AtBot before.tendency ∧
              DeliveredTo IcchantikaCase.grid deed reception ∧
                IcchantikaCase.grid.IsShareDrop before reception ∧
                  HasShareDropLanding IcchantikaCase.grid before deed := by
  refine ⟨IcchantikaCase.liveBefore, IcchantikaCase.Being.icchantika,
    IcchantikaCase.deed, IcchantikaCase.reception, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact IcchantikaCase.receiver_icchantika
  · rfl
  · exact IcchantikaCase.reception_actual
  · exact IcchantikaCase.liveBefore_not_atBot
  · exact IcchantikaCase.delivered
  · exact IcchantikaCase.reception_shareDrop
  · exact IcchantikaCase.landing

end WAA
