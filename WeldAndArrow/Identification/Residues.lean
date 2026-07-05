/-
================================================================================
  WeldAndArrow.Identification.Residues
  Field residues and index recovery
================================================================================

Reading and motivation: Identification/Commentary.lean, C.0-C.1.
-/

import WeldAndArrow.Consequences.Basic

namespace WAA

/- ==============================================================================
   §0  Field residues and index recovery
============================================================================== -/

namespace Grid

variable {Contrib : Type} [PreorderBot Contrib]
variable (G : Grid Contrib)

/-- A field residue: the call and response left when the agent-index is not part
    of the data. -/
abbrev FieldFact : Type := G.Call × G.Response

/-- A field-only recovery candidate tries to recover an agent-index from field
    residues alone. -/
abbrev FieldRecovery : Type := G.FieldFact → G.Being

/-- Correctness for a field-only recovery candidate: for every actual weld, it
    must recover the very index projected from that weld. -/
def CorrectFieldRecovery (recover : G.FieldRecovery) : Prop :=
  ∀ w : G.Weld, G.Actual w → recover (G.fieldOf w) = G.index w

/-- A correct field-only recovery cannot distinguish two actual welds with the
    same field residue; it must assign them the same index. -/
theorem correctFieldRecovery_forces_same_index_of_same_field
    {recover : G.FieldRecovery} (hrec : G.CorrectFieldRecovery recover)
    {w₁ w₂ : G.Weld} (h₁ : G.Actual w₁) (h₂ : G.Actual w₂)
    (hfield : G.fieldOf w₁ = G.fieldOf w₂) :
    G.index w₁ = G.index w₂ :=
  calc
    G.index w₁ = recover (G.fieldOf w₁) := (hrec w₁ h₁).symm
    _ = recover (G.fieldOf w₂) := congrArg recover hfield
    _ = G.index w₂ := hrec w₂ h₂

/-- If two actual welds share the field residue but differ in index, no
    field-only recovery can be correct. This is the modest internal fact that
    field residues under-determine the agent-index. -/
theorem no_agent_recovery_from_same_field_distinct_index
    {w₁ w₂ : G.Weld} (h₁ : G.Actual w₁) (h₂ : G.Actual w₂)
    (hfield : G.fieldOf w₁ = G.fieldOf w₂)
    (hne : G.index w₁ ≠ G.index w₂) :
    ¬ ∃ recover : G.FieldRecovery, G.CorrectFieldRecovery recover :=
  fun ⟨_recover, hrec⟩ =>
    hne (G.correctFieldRecovery_forces_same_index_of_same_field
      hrec h₁ h₂ hfield)

/-- The concrete same-call/same-response witness used in the prose: two
    different beings can actually answer the same call with the same response,
    and the field residue cannot say which one acted. -/
theorem no_agent_recovery_from_same_call_response
    (a₁ a₂ : G.Being) (c : G.Call) (r : G.Response)
    (h₁ : G.Actual ⟨a₁, c, r⟩) (h₂ : G.Actual ⟨a₂, c, r⟩)
    (hne : a₁ ≠ a₂) :
    ¬ ∃ recover : G.FieldRecovery, G.CorrectFieldRecovery recover :=
  G.no_agent_recovery_from_same_field_distinct_index h₁ h₂ rfl hne


end Grid


/- ==============================================================================
   Mis-feed negative: the avyākata fence and delivery gate
============================================================================== -/

namespace MisFeedNegative

variable {Contrib : Type} [PreorderBot Contrib]

/-- The index-seeking question-form, modeled as its universe of candidate
    answers: one purported self-pole index for each field residue. -/
abbrev IndexSeekingForm (G : Grid Contrib) : Type :=
  G.FieldFact → G.Being

/-- Success for the form: correctness at every actual weld. -/
def AnswersCorrectly (G : Grid Contrib) (ans : IndexSeekingForm G) : Prop :=
  ∀ w : G.Weld, G.Actual w → ans (G.fieldOf w) = G.index w

/-- A field collision: two actual welds with the same residue and distinct
    agents. -/
structure FieldCollision (G : Grid Contrib) where
  w1 : G.Weld
  w2 : G.Weld
  actual1 : G.Actual w1
  actual2 : G.Actual w2
  same_field : G.fieldOf w1 = G.fieldOf w2
  distinct_agent : w1.agent ≠ w2.agent

/-- No answer-function for the index-seeking form is correct under a field
    collision. The negation encloses the whole universe of candidate answers,
    so the obstruction belongs to the question-shape, not to one bad answer. -/
theorem no_indexSeeking_success_of_collision
    {G : Grid Contrib} (c : FieldCollision G) :
    ¬ ∃ ans : IndexSeekingForm G, AnswersCorrectly G ans := by
  rintro ⟨ans, hans⟩
  have hsame : G.index c.w1 = G.index c.w2 := by
    calc
      G.index c.w1 = ans (G.fieldOf c.w1) := (hans c.w1 c.actual1).symm
      _ = ans (G.fieldOf c.w2) := congrArg ans c.same_field
      _ = G.index c.w2 := hans c.w2 c.actual2
  exact c.distinct_agent (by simpa [Grid.index] using hsame)

/-- Claim-level face of the same obstruction: one field residue has two
    actual-backed, distinct index claims. -/
theorem indexClaim_not_functional_of_collision
    {G : Grid Contrib} (c : FieldCollision G) :
    ∃ f : G.FieldFact, ∃ b1 b2 : G.Being, b1 ≠ b2 ∧
      (∃ w : G.Weld, G.Actual w ∧ G.fieldOf w = f ∧ w.agent = b1) ∧
      (∃ w : G.Weld, G.Actual w ∧ G.fieldOf w = f ∧ w.agent = b2) :=
  ⟨G.fieldOf c.w1, c.w1.agent, c.w2.agent, c.distinct_agent,
    ⟨c.w1, c.actual1, rfl, rfl⟩,
    ⟨c.w2, c.actual2, c.same_field.symm, rfl⟩⟩

/-- Two beings, one call, one response: both actual welds have the same field
    residue. -/
inductive CollisionBeing
  | left
  | right
deriving DecidableEq

/-- A concrete grid witnessing a field collision while keeping delivery
    answerable in the same model. -/
def collisionGrid : Grid Nat where
  Being      := CollisionBeing
  Call       := Unit
  Response   := Unit
  respondsTo _ _ := some ()
  grade _ _ _ := 0
  conditions _ _ := True

def wLeft : collisionGrid.Weld :=
  ⟨CollisionBeing.left, (), ()⟩

def wRight : collisionGrid.Weld :=
  ⟨CollisionBeing.right, (), ()⟩

/-- The fence's hypothesis, witnessed concretely. -/
def collisionGrid_fieldCollision : FieldCollision collisionGrid where
  w1 := wLeft
  w2 := wRight
  actual1 := rfl
  actual2 := rfl
  same_field := rfl
  distinct_agent := by
    intro h
    cases h

/-- The fence fired at the concrete witness. -/
theorem collisionGrid_no_indexSeeking_success :
    ¬ ∃ ans : IndexSeekingForm collisionGrid,
        AnswersCorrectly collisionGrid ans :=
  no_indexSeeking_success_of_collision collisionGrid_fieldCollision

/-- The delivery-typed twin question-form in the concrete model. -/
abbrev DeliveryForm : Type :=
  collisionGrid.Weld → collisionGrid.Weld → Bool

/-- Success for the delivery twin: agreement with `conditions` in the witness
    grid. -/
def DeliveryAnswersCorrectly (ans : DeliveryForm) : Prop :=
  ∀ deed reception,
    ans deed reception = true ↔ collisionGrid.conditions deed reception

/-- A checked delivery answer for the concrete model. -/
def deliveryTwinAnswer : DeliveryForm :=
  fun _ _ => true

/-- The delivery twin is answered in the same model. This is model-local: it
    shows the index fence does not enclose delivery-typed questions. -/
theorem deliveryTwinAnswers :
    DeliveryAnswersCorrectly deliveryTwinAnswer := by
  intro deed reception
  dsimp [DeliveryAnswersCorrectly, deliveryTwinAnswer, collisionGrid]
  exact ⟨fun _ => True.intro, fun _ => rfl⟩

/-- Fence and gate together in the same concrete model. -/
theorem fence_and_gate :
    (¬ ∃ ans : IndexSeekingForm collisionGrid,
        AnswersCorrectly collisionGrid ans) ∧
      (∃ ans : DeliveryForm, DeliveryAnswersCorrectly ans) :=
  ⟨collisionGrid_no_indexSeeking_success,
    ⟨deliveryTwinAnswer, deliveryTwinAnswers⟩⟩

end MisFeedNegative


end WAA