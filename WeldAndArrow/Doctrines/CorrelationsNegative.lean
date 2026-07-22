/-
================================================================================
  WeldAndArrow.Doctrines.CorrelationsNegative
  Negative witnesses for Bulls, ranks, and stage-coarsenings
================================================================================
-/

import WeldAndArrow.Doctrines.Correlations

namespace WAA

namespace CorrelationsNegative

open Grid.DirectedConvention
open Grid.DirectedConvention.BeingConvention

/- ==============================================================================
   Bull 9 without Bull 10
============================================================================== -/

inductive Being
  | solo
  | other
deriving DecidableEq

inductive Call
  | call

inductive Response
  | response

/-- A pole responder in a world where delivery never crosses fibers. -/
def solitaryGrid : Grid Nat where
  Being      := Being
  Call       := Call
  Response   := Response
  respondsTo _ _ := some Response.response
  grade _ _ _ := 0
  conditions deed reception := deed.agent = reception.agent

def identityCoarsening : BeingCoarsening solitaryGrid Being where
  proj := id

def solitarySentience : solitaryGrid.SentienceReading :=
  Grid.SentienceReading.allSentient solitaryGrid

theorem solo_bullNine :
    solitaryGrid.WaaBullNine Being.solo := by
  constructor
  · intro _c
    exact ⟨Response.response, rfl⟩
  · intro _c _r _hresp
    exact Nat.le_refl 0

theorem solo_not_bullTen :
    ¬ solitaryGrid.WaaBullTen solitarySentience identityCoarsening
      Being.solo := by
  intro h
  rcases h.right with
    ⟨deed, reception, _hdeed, _hactual, hnotSame, _hsentient, hdel⟩
  exact hnotSame hdel

/-- A pratyekabuddha-shaped witness: Bull 9 can hold while Bull 10 fails. -/
theorem pratyekabuddha_countermodel :
    solitaryGrid.WaaBullNine Being.solo ∧
      ¬ solitaryGrid.WaaBullTen solitarySentience identityCoarsening
        Being.solo :=
  ⟨solo_bullNine, solo_not_bullTen⟩

/- ==============================================================================
   No grid-carried recovery of a unique stage boundary
============================================================================== -/

/-- Two fine tags with identical grid data, as in the being-boundary witness. -/
def stageGrid : Grid Nat where
  Being      := Bool
  Call       := Unit
  Response   := Unit
  respondsTo _ _ := some ()
  grade _ _ _ := 0
  conditions _ _ := True

def stageMerge : stageGrid.StageScheme Unit where
  proj _ := ()

def stageSplit : stageGrid.StageScheme Bool where
  proj := id

theorem stageMerge_same_fiber :
    stageMerge.SameFiber false true :=
  rfl

theorem stageSplit_not_same_fiber :
    ¬ stageSplit.SameFiber false true := by
  intro h
  cases h

abbrev W := RawWeld Bool Unit Unit

abbrev GridData : Type :=
  (Bool → Unit → Option Unit) × (Bool → Unit → Unit → Nat) × (W → W → Prop)

def gridData : GridData :=
  (stageGrid.respondsTo, stageGrid.grade, stageGrid.conditions)

def mergedBoundary (_p _q : Bool) : Prop := True

def splitBoundary (p q : Bool) : Prop := p = q

/-- The same grid data supports a merge and a split stage-coarsening. Holding
    either boundary as recovered from the grid is the uniform freeze. -/
theorem no_stage_boundary_recovery :
    ¬ ∃ recover : GridData → Bool → Bool → Prop,
        recover gridData = mergedBoundary ∧
        recover gridData = splitBoundary := by
  rintro ⟨recover, hmerge, hsplit⟩
  have hmerged : recover gridData false true := by
    rw [hmerge]
    exact True.intro
  have hsplitNot : ¬ recover gridData false true := by
    rw [hsplit]
    intro h
    cases h
  exact hsplitNot hmerged

end CorrelationsNegative

end WAA
