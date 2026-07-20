/-
================================================================================
  WeldAndArrow.Doctrines.FactorsNegative
  Supplied factor boundaries and order underdetermination
================================================================================
-/

import WeldAndArrow.Doctrines.Factors

namespace WAA

namespace FactorsNegative

open Grid

inductive Call
  | first
  | second

def grid : Grid Nat where
  Being := Unit
  Call := Call
  Response := Unit
  respondsTo _ _ := some ()
  grade _ c _ := match c with | .first => 1 | .second => 0
  conditions _ _ := True

def reading : grid.DoorReading where
  door w := match w.call with | .first => .speech | .second => .body

def firstWeld : grid.Weld := ⟨(), .first, ()⟩
def secondWeld : grid.Weld := ⟨(), .second, ()⟩

def firstViewReading : grid.FetterReading where
  provocationClass f w :=
    match f with
    | .identityView => w.call = .first
    | .ritesGrasp => w.call = .second
    | _ => False

def secondViewReading : grid.FetterReading where
  provocationClass f w :=
    match f with
    | .identityView => w.call = .second
    | .ritesGrasp => w.call = .first
    | _ => False

theorem speech_class_activated :
    PathFactor.blockerClass reading firstViewReading .speech firstWeld :=
  rfl

theorem conduct_class_inert (w : grid.Weld) :
    ¬ PathFactor.blockerClass reading firstViewReading .conduct w :=
  fun h => h

theorem first_view_held :
    grid.FactorHeld reading () firstViewReading .view [firstWeld] := by
  refine ⟨firstWeld, by simp, rfl, rfl, Or.inl rfl, ?_⟩
  dsimp [Grid.HasSelfPoleIndex, Grid.share, grid, firstWeld, AtBot, shareBot]
  show ¬ (1 : Nat) ≤ 0
  decide

theorem second_view_released :
    grid.FactorReleased reading () secondViewReading .view := by
  intro w _hactual _hagent hclass
  rcases hclass with hclass | hclass
  · cases w with
    | mk agent call response =>
      cases call <;> try { cases hclass }
      dsimp [Grid.share, grid, AtBot, shareBot]
      exact Nat.le_refl 0
  · cases hclass

abbrev GridData : Type :=
  (Unit → Call → Option Unit) × (Unit → Call → Unit → Nat)

def gridData : GridData := (grid.respondsTo, grid.grade)

def firstViewBoundary (w : grid.Weld) : Prop := w.call = .first
def secondViewBoundary (w : grid.Weld) : Prop := w.call = .second

/-- The same grid data supports incompatible factor boundaries, so a seen
    hold/release classification remains reading-relative. -/
theorem no_hold_conceit_boundary_recovery :
    ¬ ∃ recover : GridData → grid.Weld → Prop,
      recover gridData = firstViewBoundary ∧
        recover gridData = secondViewBoundary := by
  rintro ⟨recover, hfirst, hsecond⟩
  have hyes : recover gridData firstWeld := by rw [hfirst]; rfl
  have hno : ¬ recover gridData firstWeld := by
    rw [hsecond]
    intro h
    cases h
  exact hno hyes

/-- Swapping the supplied view and rites classes reverses their displayed
    factor order without changing the underlying grid. -/
theorem factor_order_underdetermined :
    firstViewReading.provocationClass Fetter.identityView firstWeld ∧
      secondViewReading.provocationClass Fetter.ritesGrasp firstWeld ∧
      firstViewReading.provocationClass Fetter.ritesGrasp secondWeld ∧
      secondViewReading.provocationClass Fetter.identityView secondWeld :=
  ⟨rfl, rfl, rfl, rfl⟩

end FactorsNegative

end WAA
