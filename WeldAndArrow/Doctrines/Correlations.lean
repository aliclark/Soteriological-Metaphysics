/-
================================================================================
  WeldAndArrow.Doctrines.Correlations
  Ten Bulls, Five Ranks, and stage-schemes as checked correlations
================================================================================

The doctrine vocabulary here is deliberately thin: named readings over existing
grid machinery, with the correlations stated as corollaries rather than new
axioms.
-/

import WeldAndArrow.Doctrines.Deliberation

namespace WAA

namespace Grid

open DirectedConvention
open DirectedConvention.BeingConvention

variable {Contrib : Type} [PreorderBot Contrib]
variable (G : Grid Contrib)

/- ==============================================================================
   Stage-schemes as coarsenings
============================================================================== -/

/-- A stage-scheme is a diagnosis-time coarsening of fine being tags. -/
abbrev StageScheme (Stage : Type) : Type :=
  BeingCoarsening G Stage

/-- The fifty-two-stage scheme, with no extra signature field. -/
abbrev FiftyTwoStageScheme : Type :=
  G.StageScheme (Fin 52)

/-- The boundary relation read from a supplied coarsening. -/
abbrev CoarseningBoundary {Macro : Type} (κ : BeingCoarsening G Macro) :
    G.Being → G.Being → Prop :=
  κ.SameFiber

/- ==============================================================================
   Ten Bulls
============================================================================== -/

-- TODO(prose): verify Kuòān verse locus.

/-- The ten pictures, as data. The interpretation lives in the predicates
    below and the commentary. -/
inductive BullStage
  | seeking
  | footprints
  | glimpse
  | catching
  | taming
  | ridingHome
  | bullForgotten
  | bothForgotten
  | returningSource
  | marketplace

namespace BullStage

/-- Bulls 1-6 are the share-drop ascent portion of the sequence. -/
def ascentIndex : BullStage → Option Nat
  | .seeking => some 0
  | .footprints => some 1
  | .glimpse => some 2
  | .catching => some 3
  | .taming => some 4
  | .ridingHome => some 5
  | .bullForgotten
  | .bothForgotten
  | .returningSource
  | .marketplace => none

theorem seeking_ascentIndex : ascentIndex seeking = some 0 := rfl
theorem footprints_ascentIndex : ascentIndex footprints = some 1 := rfl
theorem glimpse_ascentIndex : ascentIndex glimpse = some 2 := rfl
theorem catching_ascentIndex : ascentIndex catching = some 3 := rfl
theorem taming_ascentIndex : ascentIndex taming = some 4 := rfl
theorem ridingHome_ascentIndex : ascentIndex ridingHome = some 5 := rfl

end BullStage

/-- A finite run in which every received weld is actual and drops the current
    carried share, after which the configuration is re-pitched to that weld. -/
inductive ShareDropRun : Config Contrib → List G.Weld → Prop
  | nil (before : Config Contrib) : ShareDropRun before []
  | cons {before : Config Contrib} {received : G.Weld} {rest : List G.Weld} :
      G.Actual received →
      G.IsShareDrop before received →
      ShareDropRun (G.rePitch before received) rest →
        ShareDropRun before (received :: rest)

/-- Bulls 1-6 as a run-fact: the climb is per-call and stores no altitude. -/
structure BullAscent where
  before : Config Contrib
  run    : List G.Weld
  drops  : ShareDropRun G before run

/-- Bull 7: probe-constancy with a live self-pole index still present. -/
def WaaBullSeven (b : G.Being) : Prop :=
  G.ProbeConstant b (fun _ => True) ∧
    ∃ w : G.Weld, G.Actual w ∧ w.agent = b ∧ G.HasSelfPoleIndex w

/-- Bull 8: the empty circle as the pole-class, covering stone and terminus
    arrivals without collapsing them. -/
abbrev WaaBullEight (b : G.Being) : Prop :=
  G.AtPoleClass b

/-- Bull 9: return to source as call-entire terminus response. -/
abbrev WaaBullNine (b : G.Being) : Prop :=
  G.ResponsiveTerminus b

/-- Bull 10: marketplace functioning through at least one delivery line into
    another sentient fiber. The existential reading is the modest picture-level
    claim; stronger universal delivery is a separate asymptote. -/
def WaaBullTen {Macro : Type} (κ : BeingCoarsening G Macro)
    (b : G.Being) : Prop :=
  G.ResponsiveTerminus b ∧
    ∃ deed reception : G.Weld,
      κ.InFiber (κ.proj b) deed ∧
      G.Actual reception ∧
      ¬ κ.SameFiber deed.agent reception.agent ∧
      κ.SentientTag (κ.proj reception.agent) ∧
      DeliveredTo G deed reception

/-- The shelved stronger bodhisattva reading: delivery reaches every other
    sentient fiber. The source picture does not require this strength. -/
def StrongWaaBullTen {Macro : Type} (κ : BeingCoarsening G Macro)
    (b : G.Being) : Prop :=
  G.ResponsiveTerminus b ∧
    ∀ m : Macro,
      κ.SentientTag m →
        m ≠ κ.proj b →
          ∃ deed reception : G.Weld,
            κ.InFiber (κ.proj b) deed ∧
            κ.InFiber m reception ∧
            G.Actual reception ∧
            DeliveredTo G deed reception

theorem bullSeven_not_terminus {b : G.Being}
    (h : G.WaaBullSeven b) :
    ¬ G.Terminus b := by
  intro hterm
  rcases h.right with ⟨w, hactual, hagent, hidx⟩
  rw [← hagent] at hterm
  exact hidx (G.atBot_of_terminus_response hterm hactual)

theorem bullSeven_not_bullEight {b : G.Being}
    (h : G.WaaBullSeven b) :
    ¬ G.WaaBullEight b := by
  intro height
  rcases h.right with ⟨w, hactual, hagent, _hidx⟩
  cases height with
  | inl hstone =>
      have hstoneW : G.Stone w.agent := by
        simpa [hagent] using hstone
      exact G.not_actual_of_stone w.agent hstoneW hactual
  | inr hterm =>
      exact G.bullSeven_not_terminus h hterm

theorem bullTen_to_bullNine {Macro : Type}
    {κ : BeingCoarsening G Macro} {b : G.Being}
    (h : G.WaaBullTen κ b) :
    G.WaaBullNine b :=
  h.left

theorem bullNine_to_terminus {b : G.Being}
    (h : G.WaaBullNine b) :
    G.Terminus b :=
  h.right

theorem terminus_to_bullEight {b : G.Being}
    (h : G.Terminus b) :
    G.WaaBullEight b :=
  Or.inr h

theorem bullNine_to_bullEight {b : G.Being}
    (h : G.WaaBullNine b) :
    G.WaaBullEight b :=
  G.terminus_to_bullEight h.right

theorem bullTen_to_bullEight {Macro : Type}
    {κ : BeingCoarsening G Macro} {b : G.Being}
    (h : G.WaaBullTen κ b) :
    G.WaaBullEight b :=
  G.bullNine_to_bullEight h.left

end Grid

/- ==============================================================================
   Five Ranks
============================================================================== -/

/-- Dongshan's Five Ranks as data. -/
inductive FiveRank
  | shoChuHen
  | henChuSho
  | shoChuRai
  | henChuShi
  | kenChuTo

/-- Thin reading labels for the ranks. -/
inductive RankReading
  | hostWithinGuest
  | guestWithinHost
  | comingFromHost
  | arrivingWithinGuest
  | marketplaceArrival

namespace FiveRank

def reading : FiveRank → RankReading
  | .shoChuHen => .hostWithinGuest
  | .henChuSho => .guestWithinHost
  | .shoChuRai => .comingFromHost
  | .henChuShi => .arrivingWithinGuest
  | .kenChuTo => .marketplaceArrival

theorem kenChuTo_reading :
    reading kenChuTo = RankReading.marketplaceArrival :=
  rfl

end FiveRank

namespace Grid

open DirectedConvention.BeingConvention

variable {Contrib : Type} [PreorderBot Contrib]
variable (G : Grid Contrib)

/-- A minimal object-language for rank-diagnosis utterances. It records the
    rank named by an utterance without adding a new semantic row. -/
inductive RankClaim
  | says (r : FiveRank)

def rankLanguage : ClaimLanguage G where
  Claim := RankClaim
  Holds := fun _ _ => True

abbrev RecordedRankUtterance : Type :=
  RecordedUtterance G (G.rankLanguage)

/-- The 到 rank's checked shape: marketplace arrival is exactly the Bull 10
    delivery pattern under the supplied coarsening. -/
abbrev KenChuToShape {Macro : Type} (κ : BeingCoarsening G Macro)
    (b : G.Being) : Prop :=
  G.WaaBullTen κ b

theorem kenChuTo_implies_waaBullTen {Macro : Type}
    {κ : BeingCoarsening G Macro} {b : G.Being}
    (h : G.KenChuToShape κ b) :
    G.WaaBullTen κ b :=
  h

end Grid

end WAA
