/-
================================================================================
  WeldAndArrow.Signature.Models
  Concrete signature-level grids used as witnesses
================================================================================

Reading and motivation: Identification/Commentary.lean, C.1.
-/

import WeldAndArrow.Signature.BeingConvention

namespace WAA

section Preview
/- Reading and motivation: Identification/Commentary.lean, C.1. -/

/-- Two devices, differing only in whether their chime is a function of
    who is listening. -/
inductive Clock
  | rigid
  | adaptive

/-- The one call in play: whether a listener is actually present to hear
    the chime. -/
inductive Listener
  | present
  | absent

/-- The chime itself; its content is immaterial, only whether it occurs
    and what drove it matters. -/
inductive Chime
  | chime

instance : PreorderBot Nat where
  le       := Nat.le
  le_refl  := Nat.le_refl
  le_trans := fun h1 h2 => Nat.le_trans h1 h2
  bot      := 0
  bot_le   := Nat.zero_le

/- Reading and motivation: Identification/Commentary.lean, C.1. -/
def clockGrid : Grid Nat where
  Being      := Clock
  Call       := Listener
  Response   := Chime
  respondsTo b c :=
    match b, c with
    | .rigid,    _        => none
    | .adaptive, .present => some .chime
    | .adaptive, .absent  => none
  grade _ _ _ := 0
  conditions _ _ := False

theorem rigid_is_stone : clockGrid.Stone Clock.rigid :=
  fun _c ⟨_r, hr⟩ => by cases hr

theorem adaptive_is_terminus : clockGrid.Terminus Clock.adaptive :=
  fun _c _r _h => Nat.le_refl 0

theorem adaptive_not_stone : ¬ clockGrid.Stone Clock.adaptive :=
  fun h => h Listener.present ⟨Chime.chime, rfl⟩

/- Reading and motivation: Identification/Commentary.lean, C.1. -/
theorem clockGrid_function_share_split_witness :
    clockGrid.Stone Clock.rigid ∧
    clockGrid.Terminus Clock.adaptive ∧
    ¬ clockGrid.Stone Clock.adaptive :=
  ⟨rigid_is_stone, adaptive_is_terminus, adaptive_not_stone⟩

/- --------------------------------------------------------------------------
   Second concrete display — integer registers with diagnosis-time κ

   The adaptive register clock builds its fine tags as integer-like registers.
   The macro designation is still supplied outside the signature, by a
   `BeingCoarsening`: the model may implement stable internal registers, but
   the standing partition is not stored as "the" being-boundary.
-------------------------------------------------------------------------- -/

/-- A register clock whose fine tags are natural-numbered registers. Each
    register answers the tick by handing off to the next register, and
    delivery follows that hand-off. -/
def registerClockGrid : Grid Nat where
  Being      := Nat
  Call       := Unit
  Response   := Nat
  respondsTo n _ := some (n + 1)
  grade n _ _ := n
  conditions deed reception := reception.agent = deed.response

/-- A macro coarsening that sends all fine registers to one macro tag. -/
def registerClockCoarsening :
    Grid.DirectedConvention.BeingConvention.BeingCoarsening registerClockGrid Unit where
  proj _ := ()

theorem registerClock_macro_sentient :
    registerClockCoarsening.SentientTag () :=
  ⟨(0 : Nat), rfl, ⟨(), ⟨(1 : Nat), rfl⟩⟩⟩

theorem registerClock_macro_selfConditioning :
    registerClockCoarsening.SelfConditioningTag () := by
  refine ⟨⟨(0 : Nat), (), (1 : Nat)⟩, ⟨(1 : Nat), (), (2 : Nat)⟩,
    rfl, rfl, rfl, ?_⟩
  rfl

/- `clockGrid` is a genuine, finite, computable term of type `Grid Nat` —
    direct evidence that "a model of the theory" is a buildable Lean
    object, and that facts about a concrete instance are provable at
    `rfl`-level once the instance is fixed. The prudential-privilege
    construction this scaffolding anticipated is carried out in
    `Identification/Ownership.lean`, under
    `Grid.DirectedConvention.PrudentialPrivilegeNegative`: an actual
    `ReceptionPair`, the relevant `Config`/`rePitch` steps, and a named
    `PrudentialPrivilege` recovery proposition are fixed there and the
    proposition is shown to fail. This section checks only that the model
    scaffolding does not get in the way. -/

end Preview

end WAA
