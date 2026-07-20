/-
================================================================================
  WeldAndArrow.Doctrines.FettersNegative
  Fresh-weld, view-content, and factor-split countermodels
================================================================================
-/

import WeldAndArrow.Doctrines.Fetters
import WeldAndArrow.Doctrines.SraddhaNegative

namespace WAA

namespace FettersNegative

open Grid
open Grid.DirectedConvention

/- The total quiet class still carries no function conjunct. -/

def stoneGrid : Grid Nat where
  Being := Unit
  Call := Unit
  Response := Unit
  respondsTo _ _ := none
  grade _ _ _ := 0
  conditions _ _ := False

theorem stone_quiet : QuietOn stoneGrid () (fun _ => True) := by
  intro w hactual
  cases w with
  | mk agent c r =>
    cases agent
    cases c
    cases r
    change (none : Option Unit) = some () at hactual
    cases hactual

theorem stone_not_functioning : ¬ stoneGrid.MountsSomewhere () := by
  rintro ⟨c, r, hresp⟩
  cases c
  cases r
  change (none : Option Unit) = some () at hresp
  cases hresp

/-- Total QuietOn alone is compatible with an all-stone model. -/
theorem total_cut_carries_no_function :
    QuietOn stoneGrid () (fun _ => True) ∧
      ¬ stoneGrid.MountsSomewhere () :=
  ⟨stone_quiet, stone_not_functioning⟩

theorem sraddha_total_quiet :
    QuietOn SraddhaNegative.zeroEffectGrid
      SraddhaNegative.Being.sraddha (fun _ => True) := by
  intro w _hactual hagent _
  cases w with
  | mk agent _c _r =>
    cases agent with
    | sraddha =>
        dsimp [Grid.share, SraddhaNegative.zeroEffectGrid, AtBot, shareBot]
        exact Nat.le_refl 0
    | receiver => cases hagent

theorem sraddha_functions :
    SraddhaNegative.zeroEffectGrid.MountsSomewhere
      SraddhaNegative.Being.sraddha :=
  ⟨SraddhaNegative.Call.call,
    SraddhaNegative.Response.response, rfl⟩

/-- Quietness plus response-function still does not entail regime-relative
    effectiveness. -/
theorem total_cut_with_function_not_waaEffectiveTerminus :
    QuietOn SraddhaNegative.zeroEffectGrid
      SraddhaNegative.Being.sraddha (fun _ => True) ∧
      SraddhaNegative.zeroEffectGrid.MountsSomewhere
        SraddhaNegative.Being.sraddha ∧
        ¬ WaaEffectiveTerminus SraddhaNegative.zeroEffectGrid
          SraddhaNegative.Being.sraddha :=
  ⟨sraddha_total_quiet, sraddha_functions,
    SraddhaNegative.not_waaEffectiveTerminus⟩

/- A quiet seen weld does not settle a fresh weld in the same fetter class. -/

inductive Call
  | seen
  | fresh

def quietGrid : Grid Nat where
  Being := Unit
  Call := Call
  Response := Unit
  respondsTo _ _ := some ()
  grade _ _ _ := 0
  conditions _ _ := True

def freshClenchGrid : Grid Nat where
  Being := Unit
  Call := Call
  Response := Unit
  respondsTo _ _ := some ()
  grade _ c _ := match c with | .seen => 0 | .fresh => 1
  conditions _ _ := True

def quietSeen : quietGrid.Weld := ⟨(), .seen, ()⟩
def freshSeen : freshClenchGrid.Weld := ⟨(), .seen, ()⟩
def freshWeld : freshClenchGrid.Weld := ⟨(), .fresh, ()⟩

def quietReading : quietGrid.FetterReading where
  provocationClass _ _ := True

def freshReading : freshClenchGrid.FetterReading where
  provocationClass _ _ := True

theorem quiet_seen_run :
    quietGrid.RunQuietOn ()
      (quietReading.provocationClass Fetter.identityView) [quietSeen] := by
  intro w _hmem _hactual _hagent _hclass
  cases w
  dsimp [Grid.share, quietGrid, AtBot, shareBot]
  exact Nat.le_refl 0

theorem fresh_seen_run :
    freshClenchGrid.RunQuietOn ()
      (freshReading.provocationClass Fetter.identityView) [freshSeen] := by
  intro w hmem _hactual _hagent _hclass
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  subst hmem
  dsimp [Grid.share, freshClenchGrid, freshSeen, AtBot, shareBot]
  exact Nat.le_refl 0

theorem quiet_fetterCut :
    quietGrid.FetterCut () quietReading Fetter.identityView := by
  intro w _hactual _hagent _hclass
  cases w
  dsimp [Grid.share, quietGrid, AtBot, shareBot]
  exact Nat.le_refl 0

theorem fresh_not_fetterCut :
    ¬ freshClenchGrid.FetterCut () freshReading Fetter.identityView := by
  intro hcut
  have hbot := hcut freshWeld rfl rfl True.intro
  dsimp [Grid.share, freshClenchGrid, freshWeld, AtBot, shareBot] at hbot
  exact Nat.not_succ_le_zero 0 hbot

/-- Identical one-weld quiet transcripts admit opposite whole-class verdicts
    because the fresh weld is outside the run. -/
theorem seen_run_underdetermines_fetterCut :
    quietGrid.RunQuietOn ()
        (quietReading.provocationClass Fetter.identityView) [quietSeen] ∧
      freshClenchGrid.RunQuietOn ()
        (freshReading.provocationClass Fetter.identityView) [freshSeen] ∧
      quietGrid.FetterCut () quietReading Fetter.identityView ∧
        ¬ freshClenchGrid.FetterCut () freshReading Fetter.identityView :=
  ⟨quiet_seen_run, fresh_seen_run, quiet_fetterCut, fresh_not_fetterCut⟩

/- View content is also supplied rather than recovered. -/

def viewLanguage : ClaimLanguage quietGrid where
  Claim := Bool
  Holds _ _ := True

def ownerAll : quietGrid.ViewReading viewLanguage where
  ownerClaim _ := True

def ownerNone : quietGrid.ViewReading viewLanguage where
  ownerClaim _ := False

abbrev ViewGridData : Type :=
  (Unit → Call → Option Unit) ×
    (Unit → Call → Unit → Nat)

def viewGridData : ViewGridData := (quietGrid.respondsTo, quietGrid.grade)

theorem no_view_content_recovery :
    ¬ ∃ recover : ViewGridData → Bool → Prop,
      recover viewGridData = ownerAll.ownerClaim ∧
        recover viewGridData = ownerNone.ownerClaim := by
  rintro ⟨recover, hall, hnone⟩
  have ht : recover viewGridData true := by rw [hall]; exact True.intro
  have hf : ¬ recover viewGridData true := by rw [hnone]; exact fun h => h
  exact hf ht

/- One checked coarsening-freeze correlation: the owner classifier names the
   stored-owner claim about a supplied merge, but does not derive it. -/

inductive MergeClaim
  | freezeOwner (left right : Bool)
  | other
deriving DecidableEq

def mergeGrid : Grid Nat where
  Being := Bool
  Call := Unit
  Response := Unit
  respondsTo _ _ := some ()
  grade _ _ _ := 0
  conditions _ _ := True

def mergeLanguage : ClaimLanguage mergeGrid where
  Claim := MergeClaim
  Holds _ _ := True

def mergeViewReading : mergeGrid.ViewReading mergeLanguage where
  ownerClaim claim := claim = .freezeOwner false true

def suppliedMerge :
    Grid.DirectedConvention.BeingConvention.BeingCoarsening mergeGrid Unit where
  proj _ := ()

theorem ownerClaim_coarsening_freeze_correlation :
    mergeViewReading.ownerClaim (.freezeOwner false true) ∧
      suppliedMerge.SameFiber false true :=
  ⟨rfl, rfl⟩

/- The new typing keeps view and rites distinct in one concrete model. -/

def factorLanguage : ClaimLanguage Grid.doorWitnessGrid where
  Claim := Bool
  Holds _ _ := True

def factorSpeechReading :
    Grid.doorWitnessGrid.SpeechReading factorLanguage where
  toDoorReading := Grid.doorWitnessReading
  voices w := match w.call with | .mind => some true | _ => none

def factorViewReading :
    Grid.doorWitnessGrid.ViewReading factorLanguage where
  ownerClaim claim := claim = true

def factorFetterReading : Grid.doorWitnessGrid.FetterReading where
  provocationClass f w :=
    match f with
    | .identityView => w.call = .mind
    | .ritesGrasp => w.call = .body
    | _ => False

theorem factor_view_cut :
    Grid.doorWitnessGrid.FetterCut () factorFetterReading
      Fetter.identityView := by
  intro w _hactual _hagent hclass
  cases w with
  | mk agent call response =>
    cases call <;> try { cases hclass }
    dsimp [Grid.share, Grid.doorWitnessGrid, AtBot, shareBot]
    exact Nat.le_refl 0

theorem factor_rites_not_cut :
    ¬ Grid.doorWitnessGrid.FetterCut () factorFetterReading
      Fetter.ritesGrasp := by
  intro hcut
  have hbot := hcut Grid.doorWitnessBodyWeld rfl rfl rfl
  exact Grid.doorWitnessBodyWeld_live hbot

theorem view_cut_rites_cut_split :
    Grid.doorWitnessGrid.FetterCut () factorFetterReading
        Fetter.identityView ∧
      ¬ Grid.doorWitnessGrid.FetterCut () factorFetterReading
        Fetter.ritesGrasp :=
  ⟨factor_view_cut, factor_rites_not_cut⟩

end FettersNegative

end WAA
