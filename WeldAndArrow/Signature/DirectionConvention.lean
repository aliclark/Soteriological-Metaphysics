/-
================================================================================
  WeldAndArrow.Signature.DirectionConvention
  Direction-coarsening vocabulary over the delivery axis
================================================================================

Reading and motivation: Identification/Commentary.lean, C.1.
-/

import WeldAndArrow.Signature.Grid

namespace WAA

namespace Grid
namespace DirectedConvention

variable {Contrib : Type} [PreorderBot Contrib]

/- Reading and motivation: Identification/Commentary.lean, C.1. -/
/-- A diagnosis-time projection on the delivery axis. Finite clock speed is
    represented by the supplied tick carrier; the projection is not a field of
    `Grid`. -/
structure DirectionCoarsening (G : Grid Contrib) (Tick : Type) where
  tick : G.Weld -> Tick

namespace DirectionCoarsening

variable {G : Grid Contrib} {Tick : Type} (ρ : DirectionCoarsening G Tick)

/- Reading and motivation: Identification/Commentary.lean, C.1. -/
/-- Two welds lie inside the same clock tick. This is direction-neutral. -/
def SameTick (w₁ w₂ : G.Weld) : Prop := ρ.tick w₁ = ρ.tick w₂

theorem sameTick_symm {w₁ w₂ : G.Weld} (h : ρ.SameTick w₁ w₂) :
    ρ.SameTick w₂ w₁ :=
  h.symm

/- Reading and motivation: Identification/Commentary.lean, C.1. -/
/-- Delivery the clock can resolve. -/
def ResolvedDelivery (deed reception : G.Weld) : Prop :=
  DeliveredTo G deed reception ∧ ρ.tick deed ≠ ρ.tick reception

/- Reading and motivation: Identification/Commentary.lean, C.1. -/
/-- Delivery below resolution: the coarse-direction residue. -/
def SubTickDelivery (deed reception : G.Weld) : Prop :=
  DeliveredTo G deed reception ∧ ρ.SameTick deed reception

/- Reading and motivation: Identification/Commentary.lean, C.1. -/
/-- A model-supplied coherence condition for the display. It is not a
    legitimacy, pole, or typing condition. -/
def ResolutionBounded : Prop :=
  ∀ w₁ w₂ : G.Weld, ρ.SameTick w₁ w₂ -> OrderEq (G.share w₁) (G.share w₂)

/-- Sub-tick delivery carries no strict share-direction. -/
theorem no_timeDirection_within_tick
    (h : ρ.ResolutionBounded) {deed reception : G.Weld}
    (hsub : ρ.SubTickDelivery deed reception) :
    ¬ TimeDirection (G.share deed) (G.share reception) :=
  not_strict_of_orderEq (h deed reception hsub.right)

/-- Weld-restricted fully coarse limit: one tick gives no directed share-pair
    among welds. -/
theorem no_timeDirection_of_resolutionBounded_subsingleton
    (h : ρ.ResolutionBounded) (hone : ∀ w₁ w₂ : G.Weld, ρ.SameTick w₁ w₂)
    (w₁ w₂ : G.Weld) :
    ¬ TimeDirection (G.share w₁) (G.share w₂) :=
  not_strict_of_orderEq (h w₁ w₂ (hone w₁ w₂))

/-- Transpose a direction-coarsening across the condition-transpose operation.
    Ticks are unchanged; only delivery order reverses. -/
def transpose (ρ : DirectionCoarsening G Tick) :
    DirectionCoarsening G.transpose Tick where
  tick := ρ.tick

theorem transpose_sameTick_iff (b₁ b₂ : G.Weld) :
    ρ.transpose.SameTick b₁ b₂ ↔ ρ.SameTick b₁ b₂ :=
  Iff.rfl

theorem transpose_resolutionBounded_iff :
    ρ.transpose.ResolutionBounded ↔ ρ.ResolutionBounded :=
  Iff.rfl

/-- Direction-smuggling detector for sub-tick delivery: transposition reverses
    the delivery line while leaving tick equality untouched. -/
theorem transpose_subTickDelivery (deed reception : G.Weld) :
    ρ.transpose.SubTickDelivery deed reception ↔
      DeliveredTo G reception deed ∧ ρ.SameTick deed reception := by
  constructor
  · intro h
    exact ⟨(transpose_deliveredTo_iff G deed reception).mp h.left, h.right⟩
  · intro h
    exact ⟨(transpose_deliveredTo_iff G deed reception).mpr h.left, h.right⟩

end DirectionCoarsening

end DirectedConvention
end Grid

end WAA
