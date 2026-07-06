/-
================================================================================
  WeldAndArrow.Doctrines.SuddenGradual
  Sudden and gradual arrivals as thin readings over re-pitch machinery
================================================================================

The doctrine-facing vocabulary here names shapes already permitted by the
signature: one received weld can arrive at the pole, and a finite run can do so
in stages. No rate preference or stored altitude is added.
-/

import WeldAndArrow.Signature
import WeldAndArrow.Consequences.Basic
import WeldAndArrow.Consequences.Taxonomy
import WeldAndArrow.Doctrines.Correlations

namespace WAA

namespace Grid

variable {Contrib : Type} [PreorderBot Contrib]
variable (G : Grid Contrib)

/- ==============================================================================
   Sudden and gradual arrival shapes
============================================================================== -/

/-- Sudden arrival, as a one-step received weld: an actual share-drop moves a
    live prior tendency to the pole-class in one re-pitch. -/
def WaaSuddenArrival (before : Config Contrib) (received : G.Weld) : Prop :=
  G.Actual received ∧
    ¬ AtBot before.tendency ∧
      G.IsShareDrop before received ∧
        AtBot ((G.rePitch before received).tendency)

/-- Re-pitch a finite list of received welds from left to right. -/
def rePitchRun (before : Config Contrib) (run : List G.Weld) :
    Config Contrib :=
  run.foldl (fun cfg received => G.rePitch cfg received) before

@[simp]
theorem rePitchRun_nil (before : Config Contrib) :
    G.rePitchRun before [] = before :=
  rfl

@[simp]
theorem rePitchRun_cons
    (before : Config Contrib) (received : G.Weld) (rest : List G.Weld) :
    G.rePitchRun before (received :: rest) =
      G.rePitchRun (G.rePitch before received) rest :=
  rfl

/-- Gradual arrival, as a staged share-drop run that eventually reaches the
    pole-class. This is only the grid-legal face: a run can be staged; no
    stored attainment or rate preference is introduced. -/
def WaaGradualArrival (before : Config Contrib) (run : List G.Weld) : Prop :=
  G.ShareDropRun before run ∧
    run.length ≥ 2 ∧
      ¬ AtBot before.tendency ∧
        AtBot ((G.rePitchRun before run).tendency)

/- ==============================================================================
   Rate invisibility
============================================================================== -/

/-- The post-reception configuration is blind to the prior rate-history. A
    sudden arrival and a gradual arrival ending in the same received weld hand
    the field the same configuration; this is the precise sense in which the
    grid prefers no rate. -/
theorem rate_invisible_to_config
    (before₁ before₂ : Config Contrib) (received : G.Weld) :
    G.rePitch before₁ received = G.rePitch before₂ received :=
  G.rePitch_forgets before₁ before₂ received

theorem rePitchRun_append_singleton
    (before : Config Contrib) (run : List G.Weld) (last : G.Weld) :
    G.rePitchRun before (run ++ [last]) =
      G.rePitch (G.rePitchRun before run) last := by
  induction run generalizing before with
  | nil =>
      rfl
  | cons received rest ih =>
      change G.rePitchRun (G.rePitch before received) (rest ++ [last]) =
        G.rePitch (G.rePitchRun (G.rePitch before received) rest) last
      exact ih (G.rePitch before received)

/-- Run histories that share their final received weld have the same final
    configuration, however different their earlier rates or stages were. -/
theorem rePitchRun_forgets_same_final
    (before₁ before₂ : Config Contrib)
    (run₁ run₂ : List G.Weld) (last : G.Weld) :
    G.rePitchRun before₁ (run₁ ++ [last]) =
      G.rePitchRun before₂ (run₂ ++ [last]) := by
  rw [G.rePitchRun_append_singleton before₁ run₁ last,
    G.rePitchRun_append_singleton before₂ run₂ last]
  exact G.rePitch_forgets (G.rePitchRun before₁ run₁)
    (G.rePitchRun before₂ run₂) last

/-- Any score that factors through the final configuration agrees across run
    histories that share their final received weld. -/
theorem score_of_rePitchRun_constant_of_same_final
    {α : Type} (score : Config Contrib -> α)
    (before₁ before₂ : Config Contrib)
    (run₁ run₂ : List G.Weld) (last : G.Weld) :
    score (G.rePitchRun before₁ (run₁ ++ [last])) =
      score (G.rePitchRun before₂ (run₂ ++ [last])) := by
  rw [G.rePitchRun_append_singleton before₁ run₁ last,
    G.rePitchRun_append_singleton before₂ run₂ last]
  exact G.accumulated_attainment_constant_of_same_final score
    (G.rePitchRun before₁ run₁) (G.rePitchRun before₂ run₂) last

end Grid

/- ==============================================================================
   Concrete witnesses
============================================================================== -/

/-- The existing clock-grid subitism witness, named in its doctrine-facing
    one-step arrival form. -/
theorem waaSuddenArrival_witness :
    ∃ (before : Config Nat) (received : clockGrid.Weld),
      clockGrid.WaaSuddenArrival before received := by
  refine ⟨{ tendency := 5 },
    ⟨Clock.adaptive, Listener.present, Chime.chime⟩, ?_⟩
  constructor
  · rfl
  · constructor
    · dsimp [AtBot, shareBot]
      show ¬ (5 : Nat) ≤ 0
      decide
    · constructor
      · dsimp [Grid.IsShareDrop, Grid.share, clockGrid]
        constructor
        · show (0 : Nat) ≤ 5
          decide
        · show ¬ (5 : Nat) ≤ 0
          decide
      · exact clockGrid.rePitch_tendency_atBot_of_terminus_response
          { tendency := 5 } adaptive_is_terminus rfl

/-- In the register clock, a two-step run can drop from a live tendency to an
    intermediate live rung and then to the pole-class. -/
theorem waaGradualArrival_witness :
    ∃ (before : Config Nat) (run : List registerClockGrid.Weld),
      registerClockGrid.WaaGradualArrival before run := by
  let first : registerClockGrid.Weld := ⟨(2 : Nat), (), (3 : Nat)⟩
  let second : registerClockGrid.Weld := ⟨(0 : Nat), (), (1 : Nat)⟩
  refine ⟨{ tendency := 5 }, [first, second], ?_⟩
  constructor
  · refine Grid.ShareDropRun.cons ?_ ?_ ?_
    · rfl
    · dsimp [Grid.IsShareDrop, Grid.share, registerClockGrid, first]
      constructor
      · show (2 : Nat) ≤ 5
        decide
      · show ¬ (5 : Nat) ≤ 2
        decide
    · refine Grid.ShareDropRun.cons ?_ ?_ ?_
      · rfl
      · dsimp [Grid.IsShareDrop, Grid.share, Grid.rePitch,
          registerClockGrid, first, second]
        constructor
        · show (0 : Nat) ≤ 2
          decide
        · show ¬ (2 : Nat) ≤ 0
          decide
      · exact Grid.ShareDropRun.nil _
  · constructor
    · decide
    · constructor
      · dsimp [AtBot, shareBot]
        show ¬ (5 : Nat) ≤ 0
        decide
      · dsimp [Grid.rePitchRun, Grid.rePitch, Grid.share, registerClockGrid,
          first, second, AtBot, shareBot]
        show (0 : Nat) ≤ 0
        decide

end WAA
