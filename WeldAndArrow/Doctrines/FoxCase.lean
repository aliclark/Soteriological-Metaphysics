/-
================================================================================
  WeldAndArrow.Doctrines.FoxCase
  Dukkha-facing fox case checks
================================================================================

The concrete fox grid lives in `Consequences/FoxCase.lean`. This adjacent
doctrine module adds only the Four Truths vocabulary needed to say that a
clenched fox-life reception is the worked dukkha example.

Reading and motivation: Identification/Commentary.lean, C.7a.
-/

import WeldAndArrow.Consequences.FoxCase
import WeldAndArrow.Doctrines.Doors
import WeldAndArrow.Doctrines.FourTruths

namespace WAA

namespace FoxCase

open Grid
open Grid.DirectedConvention
open Grid.DirectedConvention.BeingConvention
open Grid.DirectedConvention.BeingConvention.GridConvention

/-- The worked fox production reading. The old man's sentence and the
    release instruction are speech-door productions; other welds are silent. -/
def foxSpeechReading : foxGrid.SpeechReading (rowLanguage foxGrid) where
  door _ := .speech
  voices w :=
    match w.response with
    | .notFall => some (.denied .foxWeld)
    | .release => some (.inForce .foxWeld)
    | .clench => none

def oldManProduction : foxGrid.ProducedUtterance foxSpeechReading where
  weld := sentenceWeld
  actual := sentenceWeld_actual
  content := .denied .foxWeld
  voiced := rfl

def jinshinIngaInstructionProduction :
    foxGrid.ProducedUtterance foxSpeechReading where
  weld := releaseWeld
  actual := releaseWeld_actual
  content := .inForce .foxWeld
  voiced := rfl

theorem oldManProduction_toRecorded :
    oldManProduction.toRecorded rfl = oldManUtterance :=
  rfl

/-- The old man's "not fall" is assertably wrong and defiled: its act-time
    content misfits and the sentence weld carries a live self-pole. -/
theorem oldMan_defiledFalsehood :
    foxGrid.WaaDefiledFalsehood foxSpeechReading oldManProduction := by
  refine ⟨rfl, ?_, sentenceWeld_hasSelfPoleIndex⟩
  rcases oldMan_utterance_misfits with ⟨w, _hoff, hfalse⟩
  exact hfalse

/-- The daishugyō floor face is structurally unproduced. Every testimonial
    production is offered at its own act-time, whereas this face is at floor.
    This sits beside, and does not replace, its existing error-free theorem. -/
theorem daishugyo_floor_face_unproduced :
    ¬ ∃ u : foxGrid.ProducedUtterance foxSpeechReading,
      ∃ hspeech : foxSpeechReading.door u.weld = .speech,
        u.toRecorded hspeech = daishugyoFloorUtterance := by
  rintro ⟨u, hspeech, hrecord⟩
  have hoff := congrArg
    (fun record : Grid.RecordedUtterance foxGrid (rowLanguage foxGrid) =>
      record.offeredAt) hrecord
  cases hoff

/-- Counterfactual reading in which the release weld voices the denied floor
    claim instead of the fitting instruction. -/
def foxFloorSpeechReading : foxGrid.SpeechReading (rowLanguage foxGrid) where
  door _ := .speech
  voices w :=
    match w.response with
    | .notFall => some (.denied .foxWeld)
    | .release => some (.denied .foxWeld)
    | .clench => none

def jinshinIngaFloorProduction :
    foxGrid.ProducedUtterance foxFloorSpeechReading where
  weld := releaseWeld
  actual := releaseWeld_actual
  content := .denied .foxWeld
  voiced := rfl

theorem jinshinIngaFloorProduction_toRecorded :
    jinshinIngaFloorProduction.toRecorded rfl = jinshinIngaFloorVoicing :=
  rfl

/-- The counterfactual floor voicing is defiled by the same predicate as the
    old man's sentence: both converge on act-time misfit plus a live self-pole. -/
theorem jinshinInga_floor_voicing_defiled :
    foxGrid.WaaDefiledFalsehood
      foxFloorSpeechReading jinshinIngaFloorProduction := by
  refine ⟨rfl, ?_, releaseWeld_hasSelfPoleIndex⟩
  rcases jinshinInga_floor_voicing_would_misfit with ⟨w, _hoff, hfalse⟩
  exact hfalse

/- A terminus producer of `jinshinIngaInstructionProduction` would place its
   weld at the pole, making the fitting instruction teaching without
   arrogation. The occurrence theorem is supplied with the Faith migration. -/

/-- Each clenched reception carries the structural mismatch, and its grade is
    definitionally the reception's share. -/
theorem fox_clenchMismatch_per_life (n : Nat) :
    foxGrid.ClenchMismatch (lifeReception (n + 1)) ∧
      foxGrid.WaaMismatchGrade (lifeReception (n + 1)) =
        foxGrid.share (lifeReception (n + 1)) :=
  ⟨fox_reception_clenched n, rfl⟩

/-- Under a reading that marks the reception, the same structural witness has
    the dukkha reading.  The mark is an explicit hypothesis, not grid output. -/
theorem fox_dukkha_per_life
    (S : foxGrid.SentienceReading) (n : Nat)
    (hsentient : S.sentient (lifeReception (n + 1))) :
    foxGrid.WaaDukkha S (lifeReception (n + 1)) :=
  ⟨hsentient, (fox_clenchMismatch_per_life n).1⟩

end FoxCase

end WAA
