/-
================================================================================
  WeldAndArrow.Identification.Registers
  Disclaimer 5 register sorting
================================================================================

Reading and motivation: Identification/Commentary.lean, C.1.
-/

import WeldAndArrow.Identification.Placements

namespace WAA

/- ==============================================================================
   §5  Register sorting
============================================================================== -/

/-- The three registers of disclaimer 5's fact-sorting: a sorting of registers,
    not of kinds of fact. -/
inductive Register
  | field
  | weld
  | stated

/-- The paper's table instances, as inspectable data. -/
inductive SortedFact
  | causalSeries
  | delivery
  | seed
  | arrogationTendency
  | agentIndex
  | forMeNess
  | receptionReachBack
  | rowTwoPlacement

namespace SortedFact

/-- The register assigned to each sorted fact in disclaimer 5. -/
def register : SortedFact → Register
  | .causalSeries => .field
  | .delivery => .field
  | .seed => .field
  | .arrogationTendency => .field
  | .agentIndex => .weld
  | .forMeNess => .weld
  | .receptionReachBack => .weld
  | .rowTwoPlacement => .stated

theorem causalSeries_register :
    register SortedFact.causalSeries = Register.field := rfl

theorem delivery_register :
    register SortedFact.delivery = Register.field := rfl

theorem seed_register :
    register SortedFact.seed = Register.field := rfl

theorem arrogationTendency_register :
    register SortedFact.arrogationTendency = Register.field := rfl

theorem agentIndex_register :
    register SortedFact.agentIndex = Register.weld := rfl

theorem forMeNess_register :
    register SortedFact.forMeNess = Register.weld := rfl

theorem receptionReachBack_register :
    register SortedFact.receptionReachBack = Register.weld := rfl

theorem rowTwoPlacement_register :
    register SortedFact.rowTwoPlacement = Register.stated := rfl

/-- Which sorted facts carry a self-index. -/
def selfIndexed : SortedFact → Bool
  | .agentIndex | .forMeNess | .receptionReachBack => true
  | _ => false

/-- Only the field register is carried between deeds. -/
def carried : Register → Bool
  | .field => true
  | _ => false

/-- Disclaimer 5's refined premise: nothing self-indexed is stored. The type-level
    enforcement is architectural (`Config` has no owner field); this is the
    paper-facing enumeration of the same claim. -/
theorem nothing_selfIndexed_carried :
    ∀ f : SortedFact, selfIndexed f = true → carried f.register = false := by
  intro f h
  cases f <;> simp [selfIndexed, carried, register] at h ⊢

end SortedFact

end WAA
