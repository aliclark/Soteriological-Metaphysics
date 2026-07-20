/-
================================================================================
  WeldAndArrow.Doctrines.DoorsNegative
  Recovery limits and inhabitation witnesses for doors and production
================================================================================
-/

import WeldAndArrow.Doctrines.Doors

namespace WAA

namespace DoorsNegative

open Grid

/-- A two-weld grid whose visible response, grade, and delivery data do not
    choose a door or a voicing interpretation. -/
def grid : Grid Nat where
  Being := Unit
  Call := Bool
  Response := Unit
  respondsTo _ _ := some ()
  grade _ _ _ := 1
  conditions _ _ := True

def wFalse : grid.Weld := ⟨(), false, ()⟩

def wTrue : grid.Weld := ⟨(), true, ()⟩

theorem wFalse_actual : grid.Actual wFalse := rfl

theorem wTrue_actual : grid.Actual wTrue := rfl

theorem wFalse_ne_wTrue : wFalse ≠ wTrue := by
  intro h
  have hcall : false = true := congrArg RawWeld.call h
  cases hcall

abbrev W := RawWeld Unit Bool Unit

abbrev GridData : Type :=
  (Unit → Bool → Option Unit) ×
    (Unit → Bool → Unit → Nat) ×
      (W → W → Prop)

def gridData : GridData :=
  (grid.respondsTo, grid.grade, grid.conditions)

/-- A merged door reading diagnoses every weld as bodily. -/
def mergedDoorReading : grid.DoorReading where
  door _ := .body

/-- A split reading diagnoses the second weld as mind-door. -/
def splitDoorReading : grid.DoorReading where
  door w :=
    match w.call with
    | false => .body
    | true => .mind

theorem door_readings_disagree :
    mergedDoorReading.door wTrue = .body ∧
      splitDoorReading.door wTrue = .mind := by
  constructor <;> rfl

/-- No function of the identical visible grid data recovers a unique total
    door classification. This replaces the old soma-region boundary witness. -/
theorem no_door_boundary_recovery :
    ¬ ∃ recover : GridData → W → Door,
      recover gridData = mergedDoorReading.door ∧
        recover gridData = splitDoorReading.door := by
  rintro ⟨recover, hmerged, hsplit⟩
  have hbody : recover gridData wTrue = .body := by
    rw [hmerged]
    rfl
  have hmind : recover gridData wTrue = .mind := by
    rw [hsplit]
    rfl
  rw [hbody] at hmind
  cases hmind

/-- A one-claim language used to isolate production identity from content. -/
def language : ClaimLanguage grid where
  Claim := Unit
  Holds _ _ := False

def speechReading : grid.SpeechReading language where
  door _ := .speech
  voices _ := some ()

def productionFalse : grid.ProducedUtterance speechReading where
  weld := wFalse
  actual := wFalse_actual
  content := ()
  voiced := rfl

def productionTrue : grid.ProducedUtterance speechReading where
  weld := wTrue
  actual := wTrue_actual
  content := ()
  voiced := rfl

/-- Equal record content cannot recover which of two distinct welds produced
    it; occurrence fidelity therefore remains an independent hypothesis. -/
theorem no_production_recovery :
    ¬ ∃ recover : language.Claim → grid.Weld,
      recover productionFalse.content = productionFalse.weld ∧
        recover productionTrue.content = productionTrue.weld := by
  rintro ⟨recover, hfalse, htrue⟩
  apply wFalse_ne_wTrue
  calc
    wFalse = recover () := hfalse.symm
    _ = wTrue := htrue

def mindDoorReading : grid.DoorReading where
  door _ := .mind

def voicedReading : grid.SpeechReading language where
  toDoorReading := mindDoorReading
  voices _ := some ()

def silentReading : grid.SpeechReading language where
  toDoorReading := mindDoorReading
  voices _ := none

/-- Voicing, including thought as mind-door voicing, is not recoverable from
    response/grade/delivery data. It is supplied diagnosis-time data. -/
theorem no_voicing_recovery :
    ¬ ∃ recover : GridData → W → Option language.Claim,
      recover gridData = voicedReading.voices ∧
        recover gridData = silentReading.voices := by
  rintro ⟨recover, hvis, hsil⟩
  have hsome : recover gridData wFalse = some () := by
    rw [hvis]
    rfl
  have hnone : recover gridData wFalse = none := by
    rw [hsil]
    rfl
  rw [hsome] at hnone
  cases hnone

theorem wFalse_hasSelfPoleIndex : grid.HasSelfPoleIndex wFalse := by
  dsimp [Grid.HasSelfPoleIndex, Grid.share, grid, wFalse, AtBot, shareBot]
  show ¬ (1 : Nat) ≤ 0
  decide

/-- The defiled-falsehood schema is inhabited independently of the fox model. -/
theorem defiledFalsehood_inhabited :
    grid.WaaDefiledFalsehood speechReading productionFalse :=
  ⟨rfl, by
    dsimp [language, ClaimLanguage.TrueAt]
    exact ⟨fun h => h, wFalse_hasSelfPoleIndex⟩⟩

end DoorsNegative

end WAA
