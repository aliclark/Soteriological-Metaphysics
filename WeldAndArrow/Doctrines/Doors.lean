/-
================================================================================
  WeldAndArrow.Doctrines.Doors
  Three-door diagnosis, production, and fine-being quiet
================================================================================
-/

import WeldAndArrow.Consequences.Taxonomy

namespace WAA

/-- The canonical three doors through which an occurrence may be diagnosed. -/
inductive Door
  | body
  | speech
  | mind
deriving DecidableEq

namespace Grid

open DirectedConvention
open DirectedConvention.BeingConvention

variable {Contrib : Type} [PreorderBot Contrib]
variable {G : Grid Contrib}

/-- A total, model-supplied diagnosis of every fine weld by door. -/
structure DoorReading (G : Grid Contrib) where
  door : G.Weld → Door

/-- A supplied voicing layer. Voicing is deliberately not restricted by door:
    thoughts and expressive bodily deeds may be represented by the same
    primitive, while testimonial predicates impose their own speech boundary. -/
structure SpeechReading (G : Grid Contrib) (L : ClaimLanguage G)
    extends DoorReading G where
  voices : G.Weld → Option L.Claim

/-- An actual weld together with the claim that the supplied reading says it
    produces. Production itself is door-neutral. -/
structure ProducedUtterance {G : Grid Contrib} {L : ClaimLanguage G}
    (sr : SpeechReading G L) where
  weld : G.Weld
  actual : G.Actual weld
  content : L.Claim
  voiced : sr.voices weld = some content

namespace ProducedUtterance

/-- Speech production enters the testimonial layer at its own act-time. The
    door proof is the structural fence excluding mind-door productions from
    `RecordedUtterance`, `Fidelity`, `Faith`, and `Ethics`. -/
def toRecorded {L : ClaimLanguage G} {sr : SpeechReading G L}
    (u : ProducedUtterance sr) (_hspeech : sr.door u.weld = .speech) :
    RecordedUtterance G L where
  weld := u.weld
  actual := u.actual
  offeredAt := Tier.actTime u.weld
  content := u.content

@[simp]
theorem toRecorded_weld {L : ClaimLanguage G} {sr : SpeechReading G L}
    (u : ProducedUtterance sr) (hspeech : sr.door u.weld = .speech) :
    (u.toRecorded hspeech).weld = u.weld :=
  rfl

@[simp]
theorem toRecorded_offeredAt {L : ClaimLanguage G} {sr : SpeechReading G L}
    (u : ProducedUtterance sr) (hspeech : sr.door u.weld = .speech) :
    (u.toRecorded hspeech).offeredAt = Tier.actTime u.weld :=
  rfl

end ProducedUtterance

/-- Speech-door production that misfits its token-reflexive act-time tier and
    carries a live self-pole. Identifying this derivable schema with canonical
    deliberate lying is a separate modelling claim. -/
def WaaDefiledFalsehood {L : ClaimLanguage G} (sr : SpeechReading G L)
    (u : ProducedUtterance sr) : Prop :=
  sr.door u.weld = .speech ∧
    ¬ L.TrueAt (Tier.actTime u.weld) u.content ∧
      G.HasSelfPoleIndex u.weld

/-- Fine-being quiet on a supplied class of welds. -/
def QuietOn (G : Grid Contrib) (b : G.Being) (ws : G.Weld → Prop) : Prop :=
  ∀ w, G.Actual w → w.agent = b → ws w → AtBot (G.share w)

/-- Quietness restricted to one supplied door. -/
def DoorQuiet (dr : DoorReading G) (b : G.Being) (d : Door) : Prop :=
  QuietOn G b (fun w => dr.door w = d)

/-- Every bad-content production by `b` at door `d` is at the pole. Full
    `QuietOn G b ⊤` therefore covers every door, including deceptive gesture;
    a merely speech-and-mind-quiet regional figure does not cover the body door. -/
def NoDefiledVoicing {L : ClaimLanguage G} (sr : SpeechReading G L)
    (b : G.Being) (bad : L.Claim → Prop) (d : Door) : Prop :=
  ∀ u : ProducedUtterance sr,
    u.weld.agent = b → sr.door u.weld = d → bad u.content →
      AtBot (G.share u.weld)

/-- Quietness is antitone in the selected weld-class. -/
theorem quietOn_mono {b : G.Being} {ws vs : G.Weld → Prop}
    (hsub : ∀ w, ws w → vs w) (hquiet : QuietOn G b vs) :
    QuietOn G b ws := by
  intro w hactual hagent hws
  exact hquiet w hactual hagent (hsub w hws)

/-- Total quietness supplies quietness on every weld-class. -/
theorem quietOn_univ {b : G.Being} {ws : G.Weld → Prop}
    (hquiet : QuietOn G b (fun _ => True)) : QuietOn G b ws :=
  quietOn_mono (fun _ _ => True.intro) hquiet

/-- Total quietness is exactly quietness through all three doors. -/
theorem arhat_iff_three_doors_quiet (dr : DoorReading G) (b : G.Being) :
    QuietOn G b (fun _ => True) ↔
      DoorQuiet dr b .body ∧ DoorQuiet dr b .speech ∧ DoorQuiet dr b .mind := by
  constructor
  · intro h
    exact ⟨quietOn_univ h, quietOn_univ h, quietOn_univ h⟩
  · rintro ⟨hbody, hspeech, hmind⟩ w hactual hagent _
    cases hdoor : dr.door w with
    | body => exact hbody w hactual hagent hdoor
    | speech => exact hspeech w hactual hagent hdoor
    | mind => exact hmind w hactual hagent hdoor

/-- A terminus is quiet on every actual weld it produces. -/
theorem arhat_of_terminus (_dr : DoorReading G) {b : G.Being}
    (hterm : G.Terminus b) : QuietOn G b (fun _ => True) := by
  intro w hactual hagent _
  subst hagent
  exact G.atBot_of_terminus_response hterm hactual

/-- Fine total quiet excludes a live self-pole on every actual weld of `b`. -/
theorem conceit_excluded_of_quietOn {b : G.Being}
    (hquiet : QuietOn G b (fun _ => True)) {w : G.Weld}
    (hactual : G.Actual w) (hagent : w.agent = b) :
    ¬ G.HasSelfPoleIndex w :=
  G.no_self_pole_index_of_atBot w
    (hquiet w hactual hagent True.intro)

/-- A pole production cannot instantiate defiled falsehood. -/
theorem not_defiledFalsehood_of_atBot {L : ClaimLanguage G}
    {sr : SpeechReading G L} {u : ProducedUtterance sr}
    (hbot : AtBot (G.share u.weld)) : ¬ WaaDefiledFalsehood sr u := by
  intro hfalse
  exact hfalse.right.right hbot

/-- Speech-door quiet excludes defiled falsehood by that fine being. -/
theorem no_defiledFalsehood_of_speechDoorQuiet {L : ClaimLanguage G}
    {sr : SpeechReading G L} {b : G.Being}
    (hquiet : DoorQuiet sr.toDoorReading b .speech) :
    ∀ u : ProducedUtterance sr, u.weld.agent = b →
      ¬ WaaDefiledFalsehood sr u := by
  intro u hagent hfalse
  exact hfalse.right.right
    (hquiet u.weld u.actual hagent hfalse.left)

/-- A terminus producer makes no defiled falsehood. -/
theorem no_defiledFalsehood_of_terminus {L : ClaimLanguage G}
    (sr : SpeechReading G L) {b : G.Being} (hterm : G.Terminus b) :
    ∀ u : ProducedUtterance sr, u.weld.agent = b →
      ¬ WaaDefiledFalsehood sr u :=
  no_defiledFalsehood_of_speechDoorQuiet
    (quietOn_univ (arhat_of_terminus sr.toDoorReading hterm))

/-- Three-door quietness, in its canonical arhat form, excludes falsehood. -/
theorem no_defiledFalsehood_of_arhat {L : ClaimLanguage G}
    (sr : SpeechReading G L) {b : G.Being}
    (harhat : DoorQuiet sr.toDoorReading b .body ∧
      DoorQuiet sr.toDoorReading b .speech ∧
        DoorQuiet sr.toDoorReading b .mind) :
    ∀ u : ProducedUtterance sr, u.weld.agent = b →
      ¬ WaaDefiledFalsehood sr u :=
  no_defiledFalsehood_of_speechDoorQuiet harhat.right.left

/-- Door quiet supplies the content-parametric no-defiled-voicing schema. -/
theorem noDefiledVoicing_of_doorQuiet {L : ClaimLanguage G}
    {sr : SpeechReading G L} {b : G.Being} {d : Door}
    (hquiet : DoorQuiet sr.toDoorReading b d) (bad : L.Claim → Prop) :
    NoDefiledVoicing sr b bad d := by
  intro u hagent hdoor _
  exact hquiet u.weld u.actual hagent hdoor

/-- Mind-door quiet excludes a live self-pole in any thought-production.
    This is freedom from defiled thought (the kleśāvaraṇa side), not the
    truth of the thought. Thought-truth is the later no-nescience conjunct on
    the jñeyāvaraṇa side. -/
theorem no_defiled_thought_of_mindDoorQuiet {L : ClaimLanguage G}
    {sr : SpeechReading G L} {b : G.Being}
    (hquiet : DoorQuiet sr.toDoorReading b .mind) :
    ∀ u : ProducedUtterance sr,
      u.weld.agent = b → sr.door u.weld = .mind →
        ¬ G.HasSelfPoleIndex u.weld := by
  intro u hagent hmind hidx
  exact hidx (hquiet u.weld u.actual hagent hmind)

/-- At the identity coarsening, old fiber-at-pole and fine total quiet are the
    same predicate. This is the retirement bridge for the old arhat display. -/
theorem quietOn_univ_iff_fiberAtPole_id (b : G.Being) :
    QuietOn G b (fun _ => True) ↔
      (BeingCoarsening.id G).FiberAtPole b := by
  constructor
  · intro h w hactual hfiber
    exact h w hactual hfiber True.intro
  · intro h w hactual hagent _
    exact h w hactual hagent

/-- Series-level quiet is derived display: precisely all fine tags in the
    coarsening fiber are quiet on the selected weld-class. -/
theorem seriesQuiet_iff_forall_fine {Macro : Type}
    (kappa : BeingCoarsening G Macro) (b : Macro) (ws : G.Weld → Prop) :
    (∀ p : G.Being, kappa.proj p = b → QuietOn G p ws) ↔
      ∀ w : G.Weld, G.Actual w → kappa.InFiber b w → ws w →
        AtBot (G.share w) := by
  constructor
  · intro hfine w hactual hfiber hws
    exact hfine w.agent hfiber w hactual rfl hws
  · intro hseries p hp w hactual hagent hws
    apply hseries w hactual
    · simpa [BeingCoarsening.InFiber, hagent] using hp
    · exact hws

end Grid

end WAA
