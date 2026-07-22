/-
================================================================================
  WeldAndArrow.Signature.SentienceConvention
  Supplied per-weld sentience readings
================================================================================

Sentience is diagnosis-time data over welds.  It is not a field of `Grid` and
no response, share, or delivery fact constrains it.
-/

import WeldAndArrow.Signature.Grid

namespace WAA

namespace Grid

variable {Contrib : Type} [PreorderBot Contrib]
variable (G : Grid Contrib)

/-- A supplied sentience marking on welds.  The marking is per occurrence,
    stores no standing nature on a being, and is unconstrained by grid data. -/
structure SentienceReading (G : Grid Contrib) where
  sentient : G.Weld → Prop

namespace SentienceReading

variable {G : Grid Contrib}

/-- The reading that marks every weld.  It is useful as one face of the
    non-recovery witness, not as a privileged interpretation. -/
def allSentient (G : Grid Contrib) : SentienceReading G where
  sentient _ := True

/-- The reading that marks no weld.  It is useful as one face of the
    non-recovery witness, not as a privileged interpretation. -/
def allInsentient (G : Grid Contrib) : SentienceReading G where
  sentient _ := False

/-- Transport a reading across reversal of the delivery relation.  Sentience
    is unchanged because transposition changes only `conditions`. -/
def transpose (S : SentienceReading G) : SentienceReading G.transpose where
  sentient := S.sentient

@[simp]
theorem transpose_sentient (S : SentienceReading G) (w : G.Weld) :
    S.transpose.sentient w ↔ S.sentient w :=
  Iff.rfl

end SentienceReading

/-- An actual occurrence marked sentient by the supplied reading. -/
def SentientAct (S : SentienceReading G) (w : G.Weld) : Prop :=
  G.Actual w ∧ S.sentient w

/-- An actual occurrence not marked sentient by the supplied reading. -/
def InsentientAct (S : SentienceReading G) (w : G.Weld) : Prop :=
  G.Actual w ∧ ¬ S.sentient w

/-- The sentient, live-self-share cell of the act square. -/
def OrdinaryAct (S : SentienceReading G) (w : G.Weld) : Prop :=
  G.SentientAct S w ∧ G.HasSelfPoleIndex w

/-- The sentient, pole-share cell of the act square. -/
def TerminusAct (S : SentienceReading G) (w : G.Weld) : Prop :=
  G.SentientAct S w ∧ AtBot (G.share w)

/-- The insentient, live-self-share cell of the act square. -/
def InsentientAppropriation (S : SentienceReading G) (w : G.Weld) : Prop :=
  G.InsentientAct S w ∧ G.HasSelfPoleIndex w

/-- The insentient, pole-share cell of the act square.  This is the current
    act-level meaning of "stone"; it is not a function-zero being type. -/
def StoneAct (S : SentienceReading G) (w : G.Weld) : Prop :=
  G.InsentientAct S w ∧ AtBot (G.share w)

theorem actual_of_sentientAct {S : SentienceReading G} {w : G.Weld}
    (h : G.SentientAct S w) :
    G.Actual w :=
  h.left

theorem actual_of_insentientAct {S : SentienceReading G} {w : G.Weld}
    (h : G.InsentientAct S w) :
    G.Actual w :=
  h.left

theorem not_insentientAct_of_sentientAct
    {S : SentienceReading G} {w : G.Weld}
    (h : G.SentientAct S w) :
    ¬ G.InsentientAct S w :=
  fun hi => hi.right h.right

theorem not_sentientAct_of_insentientAct
    {S : SentienceReading G} {w : G.Weld}
    (h : G.InsentientAct S w) :
    ¬ G.SentientAct S w :=
  fun hs => h.right hs.right

/-- With decisions for the two supplied propositions, every actual weld lies
    in one of the four cells.  The explicit decision hypotheses keep this
    signature theorem constructive. -/
theorem actual_act_fourfold (S : SentienceReading G) (w : G.Weld)
    [Decidable (S.sentient w)] [Decidable (AtBot (G.share w))]
    (hactual : G.Actual w) :
    G.OrdinaryAct S w ∨ G.TerminusAct S w ∨
      G.InsentientAppropriation S w ∨ G.StoneAct S w := by
  by_cases hsentient : S.sentient w
  · by_cases hpole : AtBot (G.share w)
    · exact Or.inr (Or.inl ⟨⟨hactual, hsentient⟩, hpole⟩)
    · exact Or.inl ⟨⟨hactual, hsentient⟩, hpole⟩
  · by_cases hpole : AtBot (G.share w)
    · exact Or.inr (Or.inr (Or.inr ⟨⟨hactual, hsentient⟩, hpole⟩))
    · exact Or.inr (Or.inr (Or.inl ⟨⟨hactual, hsentient⟩, hpole⟩))

/-- The grid fields visible to a would-be sentience recovery function. -/
abbrev SentienceGridData (G : Grid Contrib) : Type :=
  (G.Being → G.Call → Option G.Response) ×
    (G.Being → G.Call → G.Response → Contrib) ×
      (G.Weld → G.Weld → Prop)

def sentienceGridData : SentienceGridData G :=
  (G.respondsTo, G.grade, G.conditions)

/-- The two extremal readings classify the same actual weld on opposite sides
    of the sentient/insentient act distinction. -/
theorem actual_weld_readings_split (w : G.Weld) (hactual : G.Actual w) :
    G.SentientAct (SentienceReading.allSentient G) w ∧
      G.InsentientAct (SentienceReading.allInsentient G) w :=
  ⟨⟨hactual, True.intro⟩, ⟨hactual, fun h => h⟩⟩

/-- Sentience is maximally unrecovered on the actual domain: if an actual weld
    exists, the same complete grid data cannot recover its `SentientAct`
    classification under both the all-sentient and all-insentient readings. -/
theorem no_sentience_recovery (w : G.Weld) (hactual : G.Actual w) :
    ¬ ∃ recover : SentienceGridData G → G.Weld → Prop,
      recover G.sentienceGridData =
          G.SentientAct (SentienceReading.allSentient G) ∧
        recover G.sentienceGridData =
          G.SentientAct (SentienceReading.allInsentient G) := by
  rintro ⟨recover, hall, hnone⟩
  have hsplit := G.actual_weld_readings_split w hactual
  have htrue : recover G.sentienceGridData w := by
    rw [hall]
    exact hsplit.left
  have hfalse : ¬ recover G.sentienceGridData w := by
    rw [hnone]
    exact G.not_sentientAct_of_insentientAct hsplit.right
  exact hfalse htrue

end Grid

end WAA
