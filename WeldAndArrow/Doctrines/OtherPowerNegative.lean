/-
================================================================================
  WeldAndArrow.Doctrines.OtherPowerNegative
  Negative witnesses for regime/share polemics
================================================================================

The positive module types same-agent and cross-agent delivery as regimes over
the same act grammar. This sibling keeps the no-polemic clause honest: neither
regime determines reception share, and reception share does not recover the
regime.
-/

import WeldAndArrow.Doctrines.OtherPower

namespace WAA

namespace OtherPowerNegative

open Grid.DirectedConvention

inductive Being
  | source
  | receiver
deriving DecidableEq

inductive Call
  | live
  | pole
deriving DecidableEq

inductive Response
  | response
deriving DecidableEq

/-- Delivery is total; reception share is controlled only by the call. -/
def regimeShareGrid : Grid Nat where
  Being      := Being
  Call       := Call
  Response   := Response
  respondsTo _ _ := some Response.response
  grade _ c _ :=
    match c with
    | .live => 1
    | .pole => 0
  conditions _ _ := True

def sameLiveDeed : regimeShareGrid.Weld :=
  ⟨Being.source, Call.live, Response.response⟩

def sameLiveReception : regimeShareGrid.Weld :=
  ⟨Being.source, Call.live, Response.response⟩

def samePoleReception : regimeShareGrid.Weld :=
  ⟨Being.source, Call.pole, Response.response⟩

def crossLiveDeed : regimeShareGrid.Weld :=
  ⟨Being.source, Call.live, Response.response⟩

def crossLiveReception : regimeShareGrid.Weld :=
  ⟨Being.receiver, Call.live, Response.response⟩

def crossPoleReception : regimeShareGrid.Weld :=
  ⟨Being.receiver, Call.pole, Response.response⟩

theorem sameLiveLine :
    SameAgentDelivery regimeShareGrid sameLiveDeed sameLiveReception :=
  ⟨True.intro, rfl⟩

theorem samePoleLine :
    SameAgentDelivery regimeShareGrid sameLiveDeed samePoleReception :=
  ⟨True.intro, rfl⟩

theorem crossLiveLine :
    CrossAgentDelivery regimeShareGrid crossLiveDeed crossLiveReception := by
  constructor
  · exact True.intro
  · intro h
    cases h

theorem crossPoleLine :
    CrossAgentDelivery regimeShareGrid crossLiveDeed crossPoleReception := by
  constructor
  · exact True.intro
  · intro h
    cases h

/-- Cross-agent delivery and same-agent delivery each allow a live-share
    reception and a pole-class reception. The regime by itself therefore does
    not type the reception's share. -/
theorem regime_does_not_determine_share :
    (∃ deed reception,
      SameAgentDelivery regimeShareGrid deed reception ∧
        regimeShareGrid.Actual reception ∧
        ¬ AtBot (regimeShareGrid.share reception)) ∧
    (∃ deed reception,
      SameAgentDelivery regimeShareGrid deed reception ∧
        regimeShareGrid.Actual reception ∧
        AtBot (regimeShareGrid.share reception)) ∧
    (∃ deed reception,
      CrossAgentDelivery regimeShareGrid deed reception ∧
        regimeShareGrid.Actual reception ∧
        ¬ AtBot (regimeShareGrid.share reception)) ∧
    (∃ deed reception,
      CrossAgentDelivery regimeShareGrid deed reception ∧
        regimeShareGrid.Actual reception ∧
        AtBot (regimeShareGrid.share reception)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine ⟨sameLiveDeed, sameLiveReception, sameLiveLine, rfl, ?_⟩
    intro hbot
    exact Nat.not_succ_le_zero 0 hbot
  · refine ⟨sameLiveDeed, samePoleReception, samePoleLine, rfl, ?_⟩
    exact Nat.le_refl 0
  · refine ⟨crossLiveDeed, crossLiveReception, crossLiveLine, rfl, ?_⟩
    intro hbot
    exact Nat.not_succ_le_zero 0 hbot
  · refine ⟨crossLiveDeed, crossPoleReception, crossPoleLine, rfl, ?_⟩
    exact Nat.le_refl 0

/-- Equal reception share is compatible with both regimes, so the share value
    cannot recover whether the line was same-agent or cross-agent. -/
theorem share_does_not_determine_regime :
    ∃ sameDeed sameReception crossDeed crossReception,
      SameAgentDelivery regimeShareGrid sameDeed sameReception ∧
        CrossAgentDelivery regimeShareGrid crossDeed crossReception ∧
        regimeShareGrid.Actual sameReception ∧
        regimeShareGrid.Actual crossReception ∧
        regimeShareGrid.share sameReception =
          regimeShareGrid.share crossReception := by
  refine ⟨sameLiveDeed, sameLiveReception,
    crossLiveDeed, crossLiveReception, ?_⟩
  exact ⟨sameLiveLine, crossLiveLine, rfl, rfl, rfl⟩

end OtherPowerNegative

end WAA
