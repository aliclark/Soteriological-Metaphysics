/-
================================================================================
  WeldAndArrow.Doctrines.Gradeability
  Gradeability for call-carrying records
================================================================================

The theorem-file gradeability rule says that the taxonomy may grade a recorded
utterance only where the record carries its call. This module checks the
formal part of that rule: severing a response from its call underdetermines the
grade, while a `RecordedUtterance` carries the call through its `weld`. The
normative discipline, the koan-form genre claim, and the Hakuin-epigram
pedigree note remain prose.

Reading and motivation: Identification/Commentary.lean, C.10.
-/

import WeldAndArrow.Signature.Claims
import WeldAndArrow.Signature.Models

namespace WAA

namespace Grid

variable {Contrib : Type} [PreorderBot Contrib]

/-- A quotation in its strongest severed form: the response is attributed to
    an agent, but the call that made it an occurrence has been forgotten. There
    is deliberately no `call`, no `offeredAt`, and no `actual` field here. With
    no `offeredAt`, this record cannot even be supplied to `FitsOfferedTier`:
    nothing is positioned for the taxonomy to classify. The generator-side
    standing verdict is therefore `severedVerdict`, a decline rather than a
    grade. -/
structure SeveredTranscript (G : Grid Contrib) where
  agent    : G.Being
  response : G.Response

namespace Weld

/-- Forget the call carried by a weld. -/
def sever {G : Grid Contrib} (w : G.Weld) : SeveredTranscript G :=
  { agent := w.agent, response := w.response }

@[simp]
theorem sever_agent {G : Grid Contrib} (w : G.Weld) :
    (w.sever).agent = w.agent :=
  rfl

@[simp]
theorem sever_response {G : Grid Contrib} (w : G.Weld) :
    (w.sever).response = w.response :=
  rfl

/-- Two welds with the same attributed agent and response have the same
    severed transcript, regardless of the calls they answered. -/
theorem sever_eq_of_agent_response {G : Grid Contrib} {w₁ w₂ : G.Weld}
    (hagent : w₁.agent = w₂.agent)
    (hresponse : w₁.response = w₂.response) :
    w₁.sever = w₂.sever := by
  cases w₁
  cases w₂
  dsimp [sever] at hagent hresponse ⊢
  cases hagent
  cases hresponse
  rfl

end Weld

namespace RecordedUtterance

/-- A recorded utterance is severed by forgetting the call already carried in
    its weld. -/
def sever {G : Grid Contrib} {L : ClaimLanguage G}
    (u : RecordedUtterance G L) : SeveredTranscript G :=
  u.weld.sever

@[simp]
theorem sever_eq_weld_sever {G : Grid Contrib} {L : ClaimLanguage G}
    (u : RecordedUtterance G L) :
    u.sever = u.weld.sever :=
  rfl

end RecordedUtterance

/-- The generator's public standing for a severed transcript: no call-carried
    utterance is present, so the taxonomy declines rather than grading. -/
def severedVerdict (G : Grid Contrib) : GeneratorOutcome G :=
  .declined

end Grid

/-- The compliant record carries the whole weld, so its grade is definitionally
    the grade of the agent-call-response occurrence stored in that record. The
    identification of this call-carrying form with the koan genre remains a
    prose claim; the checked point is the carried call. -/
theorem recordedUtterance_grade_determined
    {Contrib : Type} [PreorderBot Contrib]
    {G : Grid Contrib} {L : Grid.ClaimLanguage G}
    (u : Grid.RecordedUtterance G L) :
    G.share u.weld = G.grade u.weld.agent u.weld.call u.weld.response :=
  rfl

namespace GradeabilityNegative

variable {Contrib : Type} [PreorderBot Contrib]

/-- If two same-agent/same-response welds differ in grade, the missing field is
    necessarily the call. -/
theorem call_ne_of_severed_grade_collision
    {G : Grid Contrib} {w₁ w₂ : G.Weld}
    (hagent : w₁.agent = w₂.agent)
    (hresponse : w₁.response = w₂.response)
    (hshare : G.share w₁ ≠ G.share w₂) :
    w₁.call ≠ w₂.call := by
  intro hcall
  have hw : w₁ = w₂ := by
    cases w₁
    cases w₂
    dsimp at hagent hresponse hcall
    cases hagent
    cases hcall
    cases hresponse
    rfl
  exact hshare (by rw [hw])

/-- Under a same-agent/same-response collision with different shares, no
    function from severed transcripts can correctly recover the grade of every
    actual weld. Because the collision already fixes the agent, the still
    barer response-only quotation is covered a fortiori. -/
theorem no_grade_recovery_from_severed
    {G : Grid Contrib} {w₁ w₂ : G.Weld}
    (hactual₁ : G.Actual w₁) (hactual₂ : G.Actual w₂)
    (hagent : w₁.agent = w₂.agent)
    (hresponse : w₁.response = w₂.response)
    (hshare : G.share w₁ ≠ G.share w₂) :
    ¬ ∃ estimate : Grid.SeveredTranscript G -> Contrib,
        ∀ w : G.Weld, G.Actual w -> estimate w.sever = G.share w := by
  rintro ⟨estimate, hestimate⟩
  have hsever : w₁.sever = w₂.sever :=
    Grid.Weld.sever_eq_of_agent_response hagent hresponse
  have hsame : estimate w₁.sever = estimate w₂.sever :=
    congrArg estimate hsever
  have hshares : G.share w₁ = G.share w₂ := by
    calc
      G.share w₁ = estimate w₁.sever := (hestimate w₁ hactual₁).symm
      _ = estimate w₂.sever := hsame
      _ = G.share w₂ := hestimate w₂ hactual₂
  exact hshare hshares

/-- The gentle call in `backslideGrid`: same agent and response as the harsh
    call, but pole-class share. -/
def severedGentle : backslideGrid.Weld :=
  ⟨(), Cue.gentle, ()⟩

/-- The harsh call in `backslideGrid`: same agent and response as the gentle
    call, but live share. -/
def severedHarsh : backslideGrid.Weld :=
  ⟨(), Cue.harsh, ()⟩

/-- Concrete carrier for the gradeability rule's underdetermination face:
    same attributed quotation, different calls, different grades. -/
theorem gradeability_severed_underdetermination_witness :
    backslideGrid.Actual severedGentle ∧
      backslideGrid.Actual severedHarsh ∧
        severedGentle.agent = severedHarsh.agent ∧
          severedGentle.response = severedHarsh.response ∧
            severedGentle.call ≠ severedHarsh.call ∧
              backslideGrid.share severedGentle ≠
                backslideGrid.share severedHarsh := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_⟩
  · intro h
    cases h
  · dsimp [Grid.share, backslideGrid, severedGentle, severedHarsh]
    decide

/-- In the concrete backsliding grid, a severed transcript cannot be graded
    correctly for every actual weld. -/
theorem severed_transcript_ungradeable :
    ¬ ∃ estimate : Grid.SeveredTranscript backslideGrid -> Nat,
        ∀ w : backslideGrid.Weld, backslideGrid.Actual w ->
          estimate w.sever = backslideGrid.share w :=
  no_grade_recovery_from_severed
    (G := backslideGrid)
    (w₁ := severedGentle)
    (w₂ := severedHarsh)
    rfl
    rfl
    rfl
    rfl
    (by
      dsimp [Grid.share, backslideGrid, severedGentle, severedHarsh]
      decide)

end GradeabilityNegative

end WAA
