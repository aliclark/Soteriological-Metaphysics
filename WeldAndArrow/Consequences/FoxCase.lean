/-
================================================================================
  WeldAndArrow.Consequences.FoxCase
  The fox koan as a concrete grid run-through
================================================================================

This module gives the fox sentence a checked model: call, act, weld, arrow,
returns, clenched receptions, release-as-rung, nothing-kept, and the deliberately
built-in absence of any pole-class act in the case.

Reading and motivation: Identification/Commentary.lean, C.7a.
-/

import WeldAndArrow.Consequences.Taxonomy

namespace WAA

namespace FoxCase

open Grid
open Grid.DirectedConvention
open Grid.DirectedConvention.BeingConvention
open Grid.DirectedConvention.BeingConvention.GridConvention

inductive FoxCall
  | question
  | fruit
  | turningWord
deriving DecidableEq

inductive FoxResponse
  | notFall
  | clench
  | release
deriving DecidableEq

/-- The concrete fox grid: life 0 answers the question; later lives receive
    fruit; the turning word releases without reaching the pole. -/
def foxGrid : Grid Nat where
  Being      := Nat
  Call       := FoxCall
  Response   := FoxResponse
  respondsTo b c :=
    match b, c with
    | 0, .question    => some .notFall
    | _, .fruit       => some .clench
    | _, .turningWord => some .release
    | _, _            => none
  grade _ _ r :=
    match r with
    | .notFall => 5
    | .clench  => 5
    | .release => 1
  conditions deed reception :=
    reception.agent = deed.agent + 1 ∨ deed.agent = 0

def sentenceWeld : foxGrid.Weld :=
  ⟨(show foxGrid.Being from (0 : Nat)), FoxCall.question, FoxResponse.notFall⟩

def lifeReception (n : Nat) : foxGrid.Weld :=
  ⟨n, FoxCall.fruit, FoxResponse.clench⟩

def releaseWeld : foxGrid.Weld :=
  ⟨(show foxGrid.Being from (1 : Nat)), FoxCall.turningWord,
    FoxResponse.release⟩

def beforeRelease : Config Nat :=
  { tendency := 5 }

theorem sentenceWeld_actual :
    foxGrid.Actual sentenceWeld := by
  dsimp [Grid.Actual, foxGrid, sentenceWeld]
  rfl

theorem sentenceWeld_hasSelfPoleIndex :
    foxGrid.HasSelfPoleIndex sentenceWeld := by
  dsimp [Grid.HasSelfPoleIndex, Grid.share, foxGrid, sentenceWeld, AtBot,
    shareBot]
  show ¬ (5 : Nat) ≤ 0
  decide

/-- "He says not fall": the answer is actual and pitched hard to the self-pole. -/
theorem fox_sentence_live_selfPole :
    foxGrid.Actual sentenceWeld ∧ foxGrid.HasSelfPoleIndex sentenceWeld :=
  ⟨sentenceWeld_actual, sentenceWeld_hasSelfPoleIndex⟩

/-- "The arrow carries delivery, not desert": changing delivery leaves grade
    and share data untouched. -/
theorem fox_arrow_index_free
    (conditions₁ conditions₂ : foxGrid.Weld -> foxGrid.Weld -> Prop) :
    (∀ b c r,
      (foxGrid.withConditions conditions₁).grade b c r =
        (foxGrid.withConditions conditions₂).grade b c r) ∧
      ∀ w,
        (foxGrid.withConditions conditions₁).share w =
          (foxGrid.withConditions conditions₂).share w :=
  ⟨foxGrid.grade_independent_of_conditions conditions₁ conditions₂,
    foxGrid.share_independent_of_conditions conditions₁ conditions₂⟩

/-- "Five hundred fox lives arrive": the sentence's fruit is delivered
    life by life. -/
theorem fox_returns_delivered (n : Nat) :
    DeliveredTo foxGrid sentenceWeld (lifeReception (n + 1)) := by
  dsimp [DeliveredTo, foxGrid, sentenceWeld, lifeReception]
  exact Or.inr rfl

/-- "Each life's receiving is itself a deed": every fruit reception is actual
    and clenched at live share. -/
theorem fox_reception_clenched (n : Nat) :
    foxGrid.Actual (lifeReception (n + 1)) ∧
      foxGrid.HasSelfPoleIndex (lifeReception (n + 1)) := by
  constructor
  · rfl
  · dsimp [Grid.HasSelfPoleIndex, Grid.share, foxGrid, lifeReception, AtBot,
      shareBot]
    show ¬ (5 : Nat) ≤ 0
    decide

/-- "The configuration carries only tendency": no self-index field is stored
    between deeds. -/
theorem fox_config_carries_only_tendency (cfg : Config Nat) :
    cfg = { tendency := cfg.tendency } := by
  cases cfg
  rfl

/-- "The saying-mode is enacted anew": re-pitching forgets the prior
    configuration once the received weld is fixed. -/
theorem fox_rePitch_forgets
    (before₁ before₂ : Config Nat) (received : foxGrid.Weld) :
    foxGrid.rePitch before₁ received = foxGrid.rePitch before₂ received :=
  foxGrid.rePitch_forgets before₁ before₂ received

theorem releaseWeld_actual :
    foxGrid.Actual releaseWeld := by
  dsimp [Grid.Actual, foxGrid, releaseWeld]
  rfl

/-- "A kensho, a rung and not a pole": the turning-word reception drops share
    from the prior tendency while remaining live. -/
theorem fox_release_rung_not_pole :
    foxGrid.Actual releaseWeld ∧
      foxGrid.IsShareDrop beforeRelease releaseWeld ∧
        ¬ AtBot (foxGrid.share releaseWeld) := by
  refine ⟨releaseWeld_actual, ?_, ?_⟩
  · dsimp [Grid.IsShareDrop, Grid.share, foxGrid, beforeRelease, releaseWeld]
    constructor
    · show (1 : Nat) ≤ 5
      decide
    · show ¬ (5 : Nat) ≤ 1
      decide
  · dsimp [Grid.share, foxGrid, releaseWeld, AtBot, shareBot]
    show ¬ (1 : Nat) ≤ 0
    decide

/-- "The whole return appropriated": the release reaches back to the original
    sentence's delivered fruit. -/
theorem fox_reachBack_full_at_release :
    WaaReachBackFull foxGrid sentenceWeld releaseWeld := by
  dsimp [WaaReachBackFull, foxGrid, sentenceWeld, releaseWeld]
  exact Or.inr rfl

/-- "And nothing is kept": any score that reads the post-release configuration
    sees only the release reception, not a stored attainment. -/
theorem fox_nothing_kept
    {α : Type} (score : Config Nat -> α)
    (before₁ before₂ : Config Nat) :
    score (foxGrid.rePitch before₁ releaseWeld) =
      score (foxGrid.rePitch before₂ releaseWeld) :=
  foxGrid.accumulated_attainment_constant_of_same_final score before₁ before₂
    releaseWeld

/-- "The koan never tests share-zero": this is true by construction of the
    model's grades, so the absence is part of the display. -/
theorem fox_never_tests_pole :
    ∀ w : foxGrid.Weld, foxGrid.Actual w -> ¬ AtBot (foxGrid.share w) := by
  intro w _hactual
  cases w with
  | mk agent call response =>
      cases response <;> dsimp [Grid.share, foxGrid, AtBot, shareBot]
      · show ¬ (5 : Nat) ≤ 0
        decide
      · show ¬ (5 : Nat) ≤ 0
        decide
      · show ¬ (1 : Nat) ≤ 0
        decide

/-- The display convention merging all lives into "the fox"; the fine tags
    remain natural-numbered lives. -/
def foxSeriesCoarsening : BeingCoarsening foxGrid Unit where
  proj _ := ()

theorem foxSeries_macro_sentient :
    foxSeriesCoarsening.SentientTag () :=
  ⟨(show foxGrid.Being from (0 : Nat)), rfl,
    ⟨FoxCall.question, ⟨FoxResponse.notFall, rfl⟩⟩⟩

theorem foxSeries_macro_selfConditioning :
    foxSeriesCoarsening.SelfConditioningTag () := by
  refine ⟨sentenceWeld, lifeReception 1, rfl, rfl, ?_, ?_⟩
  · rfl
  · dsimp [DeliveredTo, foxGrid, sentenceWeld, lifeReception]
    exact Or.inr rfl

/-- Fine lives remain distinct even where the display coarsens them into
    "the fox". -/
theorem fox_consecutive_lives_distinct (n : Nat) :
    n ≠ n + 1 :=
  Nat.ne_of_lt (Nat.lt_succ_self n)

def oldManUtterance :
    Grid.RecordedUtterance foxGrid (rowLanguage foxGrid) where
  weld      := sentenceWeld
  actual    := sentenceWeld_actual
  offeredAt := Tier.actTime sentenceWeld
  content   := .denied .foxWeld

/-- "Not-fall", voiced to a live audience, repeats the fox's tier-error. -/
theorem oldMan_utterance_misfits :
    ¬ oldManUtterance.FitsOfferedTier :=
  fox_utterance_misfits_live_offer foxGrid oldManUtterance rfl
    sentenceWeld_hasSelfPoleIndex

def daishugyoFloorUtterance :
    Grid.RecordedUtterance foxGrid (rowLanguage foxGrid) where
  weld      := sentenceWeld
  actual    := sentenceWeld_actual
  offeredAt := Tier.floor
  content   := .denied .foxWeld

def daishugyoConventionalUtterance :
    Grid.RecordedUtterance foxGrid (rowLanguage foxGrid) where
  weld      := releaseWeld
  actual    := releaseWeld_actual
  offeredAt := Tier.actTime releaseWeld
  content   := .inForce .foxWeld

/-- "Daishugyo diagnoses": the two fox faces fit when each is held at its
    proper tier. -/
theorem daishugyo_diagnosis_fits :
    daishugyoFloorUtterance.FitsOfferedTier ∧
      daishugyoConventionalUtterance.FitsOfferedTier :=
  ⟨True.intro, True.intro⟩

def jinshinIngaInstruction :
    Grid.RecordedUtterance foxGrid (rowLanguage foxGrid) where
  weld      := releaseWeld
  actual    := releaseWeld_actual
  offeredAt := Tier.actTime releaseWeld
  content   := .inForce .foxWeld

/-- "Jinshin inga instructs": not-obscure, offered at a live tier, fits. -/
theorem jinshinInga_instruction_fits :
    jinshinIngaInstruction.FitsOfferedTier :=
  True.intro

def jinshinIngaFloorVoicing :
    Grid.RecordedUtterance foxGrid (rowLanguage foxGrid) where
  weld      := releaseWeld
  actual    := releaseWeld_actual
  offeredAt := Tier.actTime releaseWeld
  content   := .denied .foxWeld

theorem releaseWeld_hasSelfPoleIndex :
    foxGrid.HasSelfPoleIndex releaseWeld := by
  dsimp [Grid.HasSelfPoleIndex, Grid.share, foxGrid, releaseWeld, AtBot,
    shareBot]
  show ¬ (1 : Nat) ≤ 0
  decide

/-- "Voicing the floor would repeat the fox's error to a live audience." -/
theorem jinshinInga_floor_voicing_would_misfit :
    ¬ jinshinIngaFloorVoicing.FitsOfferedTier :=
  denied_misfits_live_offer foxGrid .foxWeld jinshinIngaFloorVoicing rfl
    releaseWeld_hasSelfPoleIndex

/-- The Dogen doubling gloss, grid-internally only: Daishugyo and Jinshin inga
    both fit at their act-times, while the floor-voicing counterfactual misfits. -/
theorem dogen_doubling_both_fit :
    (daishugyoFloorUtterance.FitsOfferedTier ∧
        daishugyoConventionalUtterance.FitsOfferedTier) ∧
      jinshinIngaInstruction.FitsOfferedTier ∧
        ¬ jinshinIngaFloorVoicing.FitsOfferedTier :=
  ⟨daishugyo_diagnosis_fits, jinshinInga_instruction_fits,
    jinshinInga_floor_voicing_would_misfit⟩

end FoxCase

end WAA
