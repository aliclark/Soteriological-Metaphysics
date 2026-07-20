/-
================================================================================
  WeldAndArrow.Doctrines.EthicsNegative
  Production-tied testimony and conditional ethics witnesses
================================================================================
-/

import WeldAndArrow.Doctrines.Ethics
import WeldAndArrow.Doctrines.FaithNegative

namespace WAA
namespace EthicsNegative

open Grid
open Grid.DirectedConvention
open FaithNegative

/-- The false thought from the strictness model cannot cross the testimonial
    boundary: its supplied door is mind, not speech. -/
theorem mind_production_not_testimony :
    ¬ reading.door mindProduction.weld = .speech := by
  intro h
  cases h

/-- Re-read the same false production as speech to test the ethics boundary
    itself.  This separate reading is deliberate: door typing is model-supplied
    diagnostic structure, not recoverable from the grid. -/
def falseSpeechReading :
    SpeechReading grid (waaPathClaimLanguage grid) where
  door _ := .speech
  voices w :=
    match w.call with
    | .mind => some falseContent
    | _ => none

def falseSpeechProduction : ProducedUtterance falseSpeechReading where
  weld := mindWeld
  actual := rfl
  content := falseContent
  voiced := rfl

def falseRecord : RecordedUtterance grid (waaPathClaimLanguage grid) :=
  falseSpeechProduction.toRecorded rfl

def onlyFalseFidelity
    (record : RecordedUtterance grid (waaPathClaimLanguage grid)) : Prop :=
  record = falseRecord

/-- No factive ethics stance can license an admitted false speech production.
    The contradiction is tied to that production's own act-time; there is no
    free-standing tier witness. -/
theorem no_stance_over_false_speech
    (Faith : Prop → Prop) :
    ¬ WaaEthicsStance grid falseSpeechReading onlyFalseFidelity Faith () := by
  intro hstance
  have hfit := waa_stance_says_true grid hstance falseRecord rfl rfl
  exact falseContent_not_trueAt hfit

/-- At a pole prior there is no live aversion antecedent and hence no detached
    practical conclusion, regardless of what production-tied stance is
    hypothesized. -/
theorem no_ethics_bearing_at_pole
    (Fidelity : RecordedUtterance grid (waaPathClaimLanguage grid) → Prop)
    (Faith : Prop → Prop)
    (_hstance : WaaEthicsStance grid reading Fidelity Faith ()) :
    ¬ WaaAversionContext grid poleBefore targetWeld ∧
      ¬ HasShareDropLanding grid poleBefore mindWeld :=
  ⟨no_waa_aversion_context_at_pole grid (Nat.le_refl 0) targetWeld,
    no_waa_path_at_pole grid (Nat.le_refl 0) mindWeld⟩

end EthicsNegative
end WAA
