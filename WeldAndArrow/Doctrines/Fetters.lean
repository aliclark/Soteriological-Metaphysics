/-
================================================================================
  WeldAndArrow.Doctrines.Fetters
  The ten fetters and path-scheme readings
================================================================================
-/

import WeldAndArrow.Doctrines.Correlations
import WeldAndArrow.Doctrines.Doors

namespace WAA

/- ==============================================================================
   Data
============================================================================== -/

inductive Fetter
  | identityView
  | doubt
  | ritesGrasp
  | sensualDesire
  | illWill
  | formDesire
  | formlessDesire
  | conceit
  | restlessness
  | ignorance

inductive FetterClass
  | lower
  | higher

inductive Path
  | streamEntry
  | onceReturn
  | nonReturn
  | arhatship

inductive FetterRegister
  | field

namespace Fetter

def kind : Fetter → FetterClass
  | .identityView
  | .doubt
  | .ritesGrasp
  | .sensualDesire
  | .illWill => .lower
  | .formDesire
  | .formlessDesire
  | .conceit
  | .restlessness
  | .ignorance => .higher

def abandonedAt : Fetter → Path
  | .identityView => .streamEntry
  | .doubt => .streamEntry
  | .ritesGrasp => .streamEntry
  | .sensualDesire => .nonReturn
  | .illWill => .nonReturn
  | .formDesire => .arhatship
  | .formlessDesire => .arhatship
  | .conceit => .arhatship
  | .restlessness => .arhatship
  | .ignorance => .arhatship

/-- Fetters are standing field-register tendencies in this reading. -/
def register (_f : Fetter) : FetterRegister :=
  .field

theorem identityView_class :
    kind identityView = FetterClass.lower := rfl

theorem ignorance_class :
    kind ignorance = FetterClass.higher := rfl

theorem identityView_abandonedAt :
    abandonedAt identityView = Path.streamEntry := rfl

theorem doubt_abandonedAt :
    abandonedAt doubt = Path.streamEntry := rfl

theorem ritesGrasp_abandonedAt :
    abandonedAt ritesGrasp = Path.streamEntry := rfl

theorem sensualDesire_abandonedAt :
    abandonedAt sensualDesire = Path.nonReturn := rfl

theorem illWill_abandonedAt :
    abandonedAt illWill = Path.nonReturn := rfl

theorem formDesire_abandonedAt :
    abandonedAt formDesire = Path.arhatship := rfl

theorem formlessDesire_abandonedAt :
    abandonedAt formlessDesire = Path.arhatship := rfl

theorem conceit_abandonedAt :
    abandonedAt conceit = Path.arhatship := rfl

theorem restlessness_abandonedAt :
    abandonedAt restlessness = Path.arhatship := rfl

theorem ignorance_abandonedAt :
    abandonedAt ignorance = Path.arhatship := rfl

theorem identityView_register :
    register identityView = FetterRegister.field := rfl

theorem conceit_register :
    register conceit = FetterRegister.field := rfl

end Fetter

/- ==============================================================================
   Checked path-scheme readings
============================================================================== -/

namespace Grid

open DirectedConvention
open DirectedConvention.BeingConvention

variable {Contrib : Type} [PreorderBot Contrib]
variable (G : Grid Contrib)

/-- The four paths are another diagnosis-time coarsening. -/
abbrev PathScheme : Type :=
  G.StageScheme Path

/-- The model-supplied assignment of each fetter to a class of provocations.
    Classes are weld predicates: door, production, and content may all matter,
    while doubt and the upper fetters remain door-neutral when a model chooses. -/
structure FetterReading where
  provocationClass : Fetter → G.Weld → Prop

/-- Upgrade a legacy family of call-classes to weld-classes in one line. -/
def FetterReading.ofCallClasses
    (classes : Fetter → G.Call → Prop) : G.FetterReading where
  provocationClass f w := classes f w.call

/-- Identity-view content is supplied by a claim classifier; the grid does not
    infer stored ownership from share, door, or coarsening data. -/
structure ViewReading (G : Grid Contrib) (L : ClaimLanguage G) where
  ownerClaim : L.Claim → Prop

/-- A fetter is cut when the fine being is quiet on its supplied weld-class. -/
def FetterCut (b : G.Being) (fr : G.FetterReading) (f : Fetter) : Prop :=
  QuietOn G b (fr.provocationClass f)

/-- Retirement bridge for the old two-axis rectangle: a series rectangle is
    exactly fine quietness for every being in that coarsening fiber. -/
theorem fiberAtPoleOnWithin_iff_quietOn_rectangle {Macro : Type}
    (κ : BeingCoarsening G Macro) (b : Macro)
    (cs : G.Call → Prop) (ts : G.Being → Prop) :
    κ.FiberAtPoleOnWithin b cs ts ↔
      ∀ p : G.Being, κ.proj p = b →
        QuietOn G p (fun w => cs w.call ∧ ts w.agent) := by
  constructor
  · intro h p hp w hactual hagent hw
    exact h w hactual (by simpa [BeingCoarsening.InFiber, hagent] using hp)
      hw.left hw.right
  · intro h w hactual hfiber hcall htag
    exact h w.agent hfiber w hactual rfl ⟨hcall, htag⟩

/-- A seen run is quiet on a weld-class. This is finite display, not a claim
    about fresh welds. -/
def RunQuietOn (b : G.Being) (ws : G.Weld → Prop)
    (run : List G.Weld) : Prop :=
  ∀ w : G.Weld,
    w ∈ run → G.Actual w → w.agent = b → ws w →
      AtBot (G.share w)

theorem runQuietOn_of_fetterCut {b : G.Being}
    {fr : G.FetterReading} {f : Fetter} {run : List G.Weld}
    (h : G.FetterCut b fr f) :
    G.RunQuietOn b (fr.provocationClass f) run :=
  fun w _hmem hactual hagent hclass => h w hactual hagent hclass

/-- The forward-looking guarantee as a conditional: a regime may promote a
    finite class-quiet track record to a whole-class cut, but the grid does not
    discharge that antecedent. -/
def WaaIrreversibleRegime (b : G.Being)
    (fr : G.FetterReading) (run : List G.Weld) : Prop :=
  ∀ f : Fetter,
    G.RunQuietOn b (fr.provocationClass f) run →
      G.FetterCut b fr f

theorem waaIrreversibleRegime_conditional {b : G.Being}
    {fr : G.FetterReading} {run : List G.Weld} {f : Fetter}
    (hregime : G.WaaIrreversibleRegime b fr run)
    (hseen : G.RunQuietOn b (fr.provocationClass f) run) :
    G.FetterCut b fr f :=
  hregime f hseen

end Grid

namespace Path

/-- Which named fetters have been abandoned at a path. Once-return adds no new
    cut classes; it is retained as a path tag for the prose weakening clause.
    `Doctrines/Factors.lean` gives that weakening checked content as
    `WaaResolveAttenuation`. -/
def cutsFetter : Path → Fetter → Prop
  | .streamEntry, f => Fetter.abandonedAt f = .streamEntry
  | .onceReturn, f => Fetter.abandonedAt f = .streamEntry
  | .nonReturn, f =>
      Fetter.abandonedAt f = .streamEntry ∨
        Fetter.abandonedAt f = .nonReturn
  | .arhatship, _ => True

/-- The weld-class quieted by a path under a supplied fetter reading. -/
def cutClasses {Contrib : Type} [PreorderBot Contrib] {G : Grid Contrib}
    (fr : G.FetterReading) : Path → G.Weld → Prop
  | .streamEntry, w =>
      ∃ f : Fetter, cutsFetter .streamEntry f ∧ fr.provocationClass f w
  | .onceReturn, w =>
      ∃ f : Fetter, cutsFetter .onceReturn f ∧ fr.provocationClass f w
  | .nonReturn, w =>
      ∃ f : Fetter, cutsFetter .nonReturn f ∧ fr.provocationClass f w
  | .arhatship, _ => True

theorem streamEntry_cuts_identityView :
    cutsFetter streamEntry Fetter.identityView :=
  rfl

theorem streamEntry_cuts_doubt :
    cutsFetter streamEntry Fetter.doubt :=
  rfl

theorem nonReturn_cuts_sensualDesire :
    cutsFetter nonReturn Fetter.sensualDesire :=
  Or.inr rfl

theorem nonReturn_cuts_illWill :
    cutsFetter nonReturn Fetter.illWill :=
  Or.inr rfl

theorem arhatship_cuts_ignorance :
    cutsFetter arhatship Fetter.ignorance :=
  True.intro

theorem streamEntry_cutClasses_subset_onceReturn
    {Contrib : Type} [PreorderBot Contrib] {G : Grid Contrib}
    (fr : G.FetterReading) :
    ∀ w : G.Weld, cutClasses fr streamEntry w → cutClasses fr onceReturn w := by
  intro w h
  rcases h with ⟨f, hf, hc⟩
  exact ⟨f, hf, hc⟩

theorem onceReturn_cutClasses_subset_nonReturn
    {Contrib : Type} [PreorderBot Contrib] {G : Grid Contrib}
    (fr : G.FetterReading) :
    ∀ w : G.Weld, cutClasses fr onceReturn w → cutClasses fr nonReturn w := by
  intro w h
  rcases h with ⟨f, hf, hc⟩
  exact ⟨f, Or.inl hf, hc⟩

theorem nonReturn_cutClasses_subset_arhatship
    {Contrib : Type} [PreorderBot Contrib] {G : Grid Contrib}
    (fr : G.FetterReading) :
    ∀ w : G.Weld, cutClasses fr nonReturn w → cutClasses fr arhatship w :=
  fun _w _h => True.intro

end Path

namespace Fetter

theorem kind_lower_iff_cut_by_nonReturn (f : Fetter) :
    kind f = FetterClass.lower ↔ Path.cutsFetter Path.nonReturn f := by
  cases f <;> constructor <;> intro h
  · exact Or.inl rfl
  · rfl
  · exact Or.inl rfl
  · rfl
  · exact Or.inl rfl
  · rfl
  · exact Or.inr rfl
  · rfl
  · exact Or.inr rfl
  · rfl
  · cases h
  · rcases h with h | h <;> cases h
  · cases h
  · rcases h with h | h <;> cases h
  · cases h
  · rcases h with h | h <;> cases h
  · cases h
  · rcases h with h | h <;> cases h
  · cases h
  · rcases h with h | h <;> cases h

end Fetter

namespace Grid

open DirectedConvention
open DirectedConvention.BeingConvention

variable {Contrib : Type} [PreorderBot Contrib]
variable (G : Grid Contrib)

/-- Class quietness is monotone under weld-subclass restriction. -/
theorem classQuiet_mono {b : G.Being} {ws vs : G.Weld → Prop}
    (h : QuietOn G b ws) (hsub : ∀ w, vs w → ws w) :
    QuietOn G b vs :=
  quietOn_mono hsub h

/-- Fine-being quietness on the class cut by a path. -/
def PathQuiet (b : G.Being) (fr : G.FetterReading) (p : Path) : Prop :=
  QuietOn G b (Path.cutClasses fr p)

/-- The arhat path weld-class is total. -/
theorem arhatPathQuiet_iff_quietOn_univ (b : G.Being)
    (fr : G.FetterReading) :
    G.PathQuiet b fr Path.arhatship ↔ QuietOn G b (fun _ => True) :=
  Iff.rfl

theorem all_fetters_cut_at_arhat (b : G.Being) (fr : G.FetterReading)
    (h : QuietOn G b (fun _ => True)) :
    ∀ f : Fetter, G.FetterCut b fr f :=
  fun _f => quietOn_univ h

/-- If a class-restricted cut holds, no actual weld in that fiber and class
    carries a live self-pole index. -/
theorem classQuiet_no_clench_in_class {b : G.Being}
    {fr : G.FetterReading} {f : Fetter} {w : G.Weld}
    (h : G.FetterCut b fr f)
    (hactual : G.Actual w) (hagent : w.agent = b)
    (hclass : fr.provocationClass f w) :
    ¬ G.HasSelfPoleIndex w :=
  G.no_self_pole_index_of_atBot w (h w hactual hagent hclass)

/-- The view fetter factors through supplied mind-door owner-claim voicing
    exactly when the model identifies its provocation class that way. -/
theorem identityView_cut_iff_noDefiledVoicing
    {L : ClaimLanguage G} (sr : SpeechReading G L) (vr : ViewReading G L)
    (b : G.Being) (fr : G.FetterReading)
    (hfactor : ∀ w : G.Weld,
      fr.provocationClass Fetter.identityView w ↔
        sr.door w = .mind ∧
          ∃ content : L.Claim,
            sr.voices w = some content ∧ vr.ownerClaim content) :
    G.FetterCut b fr Fetter.identityView ↔
      NoDefiledVoicing sr b vr.ownerClaim .mind := by
  constructor
  · intro hcut u hagent hmind howner
    exact hcut u.weld u.actual hagent
      ((hfactor u.weld).mpr ⟨hmind, u.content, u.voiced, howner⟩)
  · intro hvoice w hactual hagent hclass
    rcases (hfactor w).mp hclass with ⟨hmind, content, hvoiced, howner⟩
    exact hvoice ⟨w, hactual, content, hvoiced⟩ hagent hmind howner

/-- Rites-grasp factors through a supplied body-door weld-class when the model
    gives that exact identification. -/
theorem ritesGrasp_cut_iff_bodyDoorQuietOn
    (dr : DoorReading G) (b : G.Being) (fr : G.FetterReading)
    (rites : G.Weld → Prop)
    (hfactor : ∀ w : G.Weld,
      fr.provocationClass Fetter.ritesGrasp w ↔
        dr.door w = .body ∧ rites w) :
    G.FetterCut b fr Fetter.ritesGrasp ↔
      QuietOn G b (fun w => dr.door w = .body ∧ rites w) := by
  constructor
  · exact fun h => quietOn_mono (fun w hw => (hfactor w).mpr hw) h
  · exact fun h => quietOn_mono (fun w hw => (hfactor w).mp hw) h

/-- The speech instance is the already-derived falsehood theorem; no new
    falsehood content is introduced in the fetter layer. -/
theorem falsehood_speech_instance {L : ClaimLanguage G}
    (sr : SpeechReading G L) {b : G.Being}
    (hquiet : DoorQuiet sr.toDoorReading b .speech) :
    ∀ u : ProducedUtterance sr, u.weld.agent = b →
      ¬ WaaDefiledFalsehood sr u :=
  no_defiledFalsehood_of_speechDoorQuiet hquiet

/-- The regional sravaka-arhat figure: speech and mind are quiet, while body
    may retain live share. It is not the canonical three-door arhat. -/
def WaaSravakaArhat (dr : DoorReading G) (b : G.Being) : Prop :=
  DoorQuiet dr b .speech ∧ DoorQuiet dr b .mind

/-- Share-vāsanā is residual live share in an actual body-door weld. -/
def WaaVasana (dr : DoorReading G) (b : G.Being) : Prop :=
  ∃ w : G.Weld, G.Actual w ∧ w.agent = b ∧
    dr.door w = .body ∧ G.HasSelfPoleIndex w

theorem sravakaArhat_no_defiledFalsehood {L : ClaimLanguage G}
    (sr : SpeechReading G L) {b : G.Being}
    (h : G.WaaSravakaArhat sr.toDoorReading b) :
    ∀ u : ProducedUtterance sr, u.weld.agent = b →
      ¬ WaaDefiledFalsehood sr u :=
  no_defiledFalsehood_of_speechDoorQuiet h.left

/- A compact Hakuin-shaped witness: speech and mind sit at bottom, body keeps
   live share, and all three doors still mount responses. -/
def doorWitnessGrid : Grid Nat where
  Being := Unit
  Call := Door
  Response := Unit
  respondsTo _ _ := some ()
  grade _ d _ := match d with | .body => 1 | .speech | .mind => 0
  conditions _ _ := True

def doorWitnessReading : doorWitnessGrid.DoorReading where
  door w := w.call

def doorWitnessBodyWeld : doorWitnessGrid.Weld := ⟨(), .body, ()⟩

theorem doorWitness_sravakaArhat :
    doorWitnessGrid.WaaSravakaArhat doorWitnessReading () := by
  constructor
  · intro w _hactual _hagent hdoor
    cases w with
    | mk agent call response =>
      cases call <;> try { cases hdoor }
      dsimp [Grid.share, doorWitnessGrid, AtBot, shareBot]
      show (0 : Nat) ≤ 0
      decide
  · intro w _hactual _hagent hdoor
    cases w with
    | mk agent call response =>
      cases call <;> try { cases hdoor }
      dsimp [Grid.share, doorWitnessGrid, AtBot, shareBot]
      show (0 : Nat) ≤ 0
      decide

theorem doorWitnessBodyWeld_live :
    doorWitnessGrid.HasSelfPoleIndex doorWitnessBodyWeld := by
  dsimp [Grid.HasSelfPoleIndex, Grid.share, doorWitnessGrid,
    doorWitnessBodyWeld, AtBot, shareBot]
  show ¬ (1 : Nat) ≤ 0
  decide

theorem doorWitness_vasana :
    doorWitnessGrid.WaaVasana doorWitnessReading () := by
  exact ⟨doorWitnessBodyWeld, rfl, rfl, rfl, doorWitnessBodyWeld_live⟩

/-- Speech/mind quiet does not imply canonical total quiet when the body door
    retains a live self-pole. -/
theorem sravakaArhat_not_arhat_witness :
    doorWitnessGrid.WaaSravakaArhat doorWitnessReading () ∧
      doorWitnessGrid.WaaVasana doorWitnessReading () ∧
        ¬ QuietOn doorWitnessGrid () (fun _ => True) := by
  refine ⟨doorWitness_sravakaArhat, doorWitness_vasana, ?_⟩
  intro hquiet
  exact doorWitness_vasana.elim (fun w hw =>
    hw.right.right.right (hquiet w hw.left hw.right.left True.intro))

/-- The unquiet body door still functions while speech and mind are quiet. -/
theorem unquiet_door_still_functions_witness :
    doorWitnessGrid.WaaSravakaArhat doorWitnessReading () ∧
      doorWitnessGrid.MountsAt () .body ∧
        ∃ w : doorWitnessGrid.Weld,
          doorWitnessGrid.Actual w ∧
            doorWitnessReading.door w = .body ∧
              doorWitnessGrid.HasSelfPoleIndex w :=
  ⟨doorWitness_sravakaArhat, ⟨(), rfl⟩,
    doorWitnessBodyWeld, rfl, rfl, doorWitnessBodyWeld_live⟩

end Grid

end WAA
