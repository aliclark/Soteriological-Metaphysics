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

theorem adaptive_is_terminus : clockGrid.Terminus Clock.adaptive :=
  fun _c _r _h => Nat.le_refl 0

/-- A supplied reading for examples involving the adaptive clock.  This does
    not follow from the clock's response table. -/
def clockSentienceReading : clockGrid.SentienceReading where
  sentient w := w.agent = Clock.adaptive

/- --------------------------------------------------------------------------
   The inhabited sentience/share square
-------------------------------------------------------------------------- -/

inductive SquareCall
  | ordinary
  | terminus
  | insentientAppropriation
  | stone

def sentienceSquareGrid : Grid Nat where
  Being := Unit
  Call := SquareCall
  Response := Unit
  respondsTo _ _ := some ()
  grade _ c _ :=
    match c with
    | .ordinary | .insentientAppropriation => 1
    | .terminus | .stone => 0
  conditions _ _ := True

def sentienceSquareReading : sentienceSquareGrid.SentienceReading where
  sentient w :=
    match w.call with
    | .ordinary | .terminus => True
    | .insentientAppropriation | .stone => False

def squareWeld (c : SquareCall) : sentienceSquareGrid.Weld :=
  ⟨(), c, ()⟩

theorem square_ordinary :
    sentienceSquareGrid.OrdinaryAct sentienceSquareReading
      (squareWeld .ordinary) := by
  refine ⟨⟨rfl, True.intro⟩, ?_⟩
  dsimp [Grid.HasSelfPoleIndex, Grid.share, sentienceSquareGrid, squareWeld,
    AtBot, shareBot]
  exact Nat.not_succ_le_zero 0

theorem square_terminus :
    sentienceSquareGrid.TerminusAct sentienceSquareReading
      (squareWeld .terminus) :=
  ⟨⟨rfl, True.intro⟩, Nat.le_refl 0⟩

theorem square_insentientAppropriation :
    sentienceSquareGrid.InsentientAppropriation sentienceSquareReading
      (squareWeld .insentientAppropriation) := by
  refine ⟨⟨rfl, fun h => h⟩, ?_⟩
  dsimp [Grid.HasSelfPoleIndex, Grid.share, sentienceSquareGrid, squareWeld,
    AtBot, shareBot]
  exact Nat.not_succ_le_zero 0

theorem square_stone :
    sentienceSquareGrid.StoneAct sentienceSquareReading
      (squareWeld .stone) :=
  ⟨⟨rfl, fun h => h⟩, Nat.le_refl 0⟩

/-- No signature law excludes any of the four actual act kinds. -/
theorem sentience_share_square_inhabited :
    (∃ w, sentienceSquareGrid.OrdinaryAct sentienceSquareReading w) ∧
      (∃ w, sentienceSquareGrid.TerminusAct sentienceSquareReading w) ∧
      (∃ w, sentienceSquareGrid.InsentientAppropriation
        sentienceSquareReading w) ∧
      (∃ w, sentienceSquareGrid.StoneAct sentienceSquareReading w) :=
  ⟨⟨squareWeld .ordinary, square_ordinary⟩,
   ⟨squareWeld .terminus, square_terminus⟩,
   ⟨squareWeld .insentientAppropriation, square_insentientAppropriation⟩,
   ⟨squareWeld .stone, square_stone⟩⟩

/- --------------------------------------------------------------------------
   Second concrete display — integer registers with diagnosis-time κ

   The adaptive register clock builds its fine tags as integer-like registers.
   The macro designation is still supplied outside the signature, by a
   `BeingCoarsening`: the model may implement stable internal registers, but
   the standing partition is not stored as "the" being-boundary.
-------------------------------------------------------------------------- -/

/-- A register clock whose fine tags are natural-numbered registers. Each
    register answers the tick by handing off to the next register, and
    delivery follows that hand-off.

    The grade equation `grade n _ _ := n` makes a re-pitched tendency
    extensionally equal to the acting register's tag. This coincidence is kept
    deliberately: it is the recorded countermodel to the information-flow
    reading of non-storage (`ConfigLeakWitness.registerClock_config_recovers_agent`),
    and the ladder witnesses depend on these grades. -/
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

def registerClockSentienceReading : registerClockGrid.SentienceReading :=
  Grid.SentienceReading.allSentient registerClockGrid

theorem registerClock_macro_sentient :
    registerClockCoarsening.SentientTag registerClockSentienceReading () :=
  ⟨⟨(0 : Nat), (), (1 : Nat)⟩, ⟨rfl, by
    change True
    exact True.intro⟩, rfl⟩

theorem registerClock_macro_selfConditioning :
    registerClockCoarsening.SelfConditioningTag () := by
  refine ⟨⟨(0 : Nat), (), (1 : Nat)⟩, ⟨(1 : Nat), (), (2 : Nat)⟩,
    rfl, rfl, rfl, ?_⟩
  rfl

/- --------------------------------------------------------------------------
   Third concrete display — backsliding in one grid

   A single being answers both calls. The gentle call drops to the pole-class;
   the harsh call later carries live share again. Nothing in the grid stores
   the prior drop as an attainment.
-------------------------------------------------------------------------- -/

inductive Cue
  | gentle
  | harsh

def backslideGrid : Grid Nat where
  Being      := Unit
  Call       := Cue
  Response   := Unit
  respondsTo _ _ := some ()
  grade _ c _ :=
    match c with
    | .gentle => 0
    | .harsh => 5
  conditions _ _ := True

/- --------------------------------------------------------------------------
   Fourth concrete display — grading is weld-side, not field-residue side

   The two actual welds share the same call-response residue while receiving
   different shares. The event residue alone therefore cannot carry the grade.
-------------------------------------------------------------------------- -/

inductive GradingCollisionBeing
  | left
  | right

def gradingCollisionGrid : Grid Nat where
  Being      := GradingCollisionBeing
  Call       := Unit
  Response   := Unit
  respondsTo _ _ := some ()
  grade b _ _ :=
    match b with
    | .left => 5
    | .right => 0
  conditions _ _ := True

def gradingCollisionLeft : gradingCollisionGrid.Weld :=
  ⟨GradingCollisionBeing.left, (), ()⟩

def gradingCollisionRight : gradingCollisionGrid.Weld :=
  ⟨GradingCollisionBeing.right, (), ()⟩

/- --------------------------------------------------------------------------
   Fifth concrete display — share collision across agents

   Two distinct agents receive the same live share, so their re-pitched
   configurations coincide and under-determine who acted.
-------------------------------------------------------------------------- -/

inductive ShareCollisionBeing
  | left
  | right

def shareCollisionGrid : Grid Nat where
  Being      := ShareCollisionBeing
  Call       := Unit
  Response   := Unit
  respondsTo _ _ := some ()
  grade _ _ _ := 3
  conditions _ _ := True

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
