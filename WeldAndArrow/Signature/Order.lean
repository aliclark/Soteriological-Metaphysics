/-
================================================================================
  WeldAndArrow.Signature.Order
  Dependency-free preorder infrastructure
================================================================================

Reading and motivation: Identification/Commentary.lean, C.1.
-/

namespace WAA

/- ==============================================================================
   §0  Dependency-free preorder infrastructure
============================================================================== -/

/-- A bare preorder, rolled by hand and not assumed total or antisymmetric. -/
class Preorder (α : Type) where
  /-- The display-order relation: `a ≼ b` means `a` is no more self-driven
      than `b` in the ordinal Row-2 sense. -/
  le       : α → α → Prop
  le_refl  : ∀ a, le a a
  le_trans : ∀ {a b c : α}, le a b → le b c → le a c

@[inherit_doc] infix:50 " ≼ " => Preorder.le

instance instTransPreorderLe [Preorder α] :
    Trans (fun a b : α => a ≼ b) (fun a b : α => a ≼ b) (fun a b : α => a ≼ b) where
  trans := fun h₁ h₂ => Preorder.le_trans h₁ h₂

/- Reading and motivation: Identification/Commentary.lean, C.1. -/
def Incomparable [Preorder α] (a b : α) : Prop := ¬ a ≼ b ∧ ¬ b ≼ a

/-- Order-equivalence: neither more nor less self-driven. -/
def OrderEq [Preorder α] (a b : α) : Prop := a ≼ b ∧ b ≼ a

/-- Strict comparability in a preorder: `a` is below `b`, with no return comparison. -/
def Strict [Preorder α] (a b : α) : Prop := a ≼ b ∧ ¬ b ≼ a

theorem orderEq_refl [Preorder α] (a : α) : OrderEq a a :=
  ⟨Preorder.le_refl a, Preorder.le_refl a⟩

theorem orderEq_symm [Preorder α] {a b : α} (h : OrderEq a b) :
    OrderEq b a :=
  ⟨h.right, h.left⟩

theorem orderEq_trans [Preorder α] {a b c : α}
    (hab : OrderEq a b) (hbc : OrderEq b c) :
    OrderEq a c :=
  ⟨Preorder.le_trans hab.left hbc.left,
    Preorder.le_trans hbc.right hab.right⟩

theorem strict_irrefl [Preorder α] (a : α) : ¬ Strict a a :=
  fun h => h.right h.left

theorem strict_asymm [Preorder α] {a b : α} (h : Strict a b) :
    ¬ Strict b a :=
  fun hba => h.right hba.left

theorem strict_trans [Preorder α] {a b c : α}
    (hab : Strict a b) (hbc : Strict b c) :
    Strict a c :=
  ⟨Preorder.le_trans hab.left hbc.left,
    fun hca => hab.right (Preorder.le_trans hbc.left hca)⟩

theorem strict_of_le_of_strict [Preorder α] {a b c : α}
    (hab : a ≼ b) (hbc : Strict b c) :
    Strict a c :=
  ⟨Preorder.le_trans hab hbc.left,
    fun hca => hbc.right (Preorder.le_trans hca hab)⟩

theorem strict_of_strict_of_le [Preorder α] {a b c : α}
    (hab : Strict a b) (hbc : b ≼ c) :
    Strict a c :=
  ⟨Preorder.le_trans hab.left hbc,
    fun hca => hab.right (Preorder.le_trans hbc hca)⟩

theorem not_strict_of_orderEq [Preorder α] {a b : α} (h : OrderEq a b) :
    ¬ Strict a b :=
  fun hs => hs.right h.right

theorem no_strict_of_all_orderEq [Preorder α]
    (h : ∀ a b : α, OrderEq a b) (a b : α) :
    ¬ Strict a b :=
  not_strict_of_orderEq (h a b)

/- Reading and motivation: Identification/Commentary.lean, C.1. -/
def DirectionVoid (α : Type) [Preorder α] : Prop := ∀ a b : α, ¬ Strict a b

/- Reading and motivation: Identification/Commentary.lean, C.1. -/
class PreorderBot (α : Type) extends Preorder α where
  bot    : α
  bot_le : ∀ a, le bot a

/-- Shorthand for the bottom of whatever `Contrib` is in scope. -/
def shareBot [PreorderBot α] : α := PreorderBot.bot

/-- The designated bottom is below every display value. -/
theorem shareBot_le [PreorderBot α] (a : α) :
    (shareBot : α) ≼ a :=
  PreorderBot.bot_le a

/- Reading and motivation: Identification/Commentary.lean, C.1. -/
def AtBot [PreorderBot α] (a : α) : Prop := a ≼ shareBot

theorem atBot_shareBot [PreorderBot α] : AtBot (shareBot : α) :=
  Preorder.le_refl shareBot

theorem atBot_of_eq_shareBot [PreorderBot α] {a : α}
    (h : a = shareBot) :
    AtBot a :=
  h ▸ atBot_shareBot

theorem orderEq_shareBot_of_atBot [PreorderBot α] {a : α}
    (h : AtBot a) :
    OrderEq a shareBot :=
  ⟨h, shareBot_le a⟩

theorem atBot_of_orderEq_shareBot [PreorderBot α] {a : α}
    (h : OrderEq a shareBot) :
    AtBot a :=
  h.left

theorem orderEq_shareBot_iff_atBot [PreorderBot α] (a : α) :
    OrderEq a shareBot ↔ AtBot a :=
  ⟨atBot_of_orderEq_shareBot, orderEq_shareBot_of_atBot⟩

theorem strict_shareBot_iff_not_atBot [PreorderBot α] (a : α) :
    Strict (shareBot : α) a ↔ ¬ AtBot a := by
  constructor
  · intro h
    exact h.right
  · intro h
    exact ⟨shareBot_le a, h⟩


end WAA
