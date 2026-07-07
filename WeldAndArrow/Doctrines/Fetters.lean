/-
================================================================================
  WeldAndArrow.Doctrines.Fetters
  The ten fetters and path-scheme readings
================================================================================
-/

import WeldAndArrow.Doctrines.Correlations

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
    The grid cannot recover "sensual call" or "identity-view call" unaided. -/
structure FetterReading where
  provocationClass : Fetter → G.Call → Prop

/-- The model-supplied assignment of fine tags to the speech/thought region.
    The grid cannot recover "speech/thought tag" or "instinctual tag"
    unaided; the boundary is diagnosis-time data, never grid-carried
    anatomy. -/
structure SomaReading where
  speechThoughtTag : G.Being → Prop

/-- A fetter is cut in a fiber when that fiber reads at pole on the fetter's
    supplied provocation class. -/
def FetterCut {Macro : Type} (κ : BeingCoarsening G Macro) (b : Macro)
    (fr : G.FetterReading) (f : Fetter) : Prop :=
  κ.FiberAtPoleOn b (fr.provocationClass f)

/-- A fetter is cut within a tag-region when the fiber reads at pole on the
    fetter's provocation class restricted to that region. Cessation of
    enactment in the rectangle; no anti-fetter is possessed. -/
def FetterCutWithin {Macro : Type} (κ : BeingCoarsening G Macro) (b : Macro)
    (fr : G.FetterReading) (f : Fetter) (ts : G.Being → Prop) : Prop :=
  κ.FiberAtPoleOnWithin b (fr.provocationClass f) ts

theorem fetterCutWithin_univ_iff_fetterCut {Macro : Type}
    (κ : BeingCoarsening G Macro) (b : Macro)
    (fr : G.FetterReading) (f : Fetter) :
    G.FetterCutWithin κ b fr f (fun _ => True) ↔
      G.FetterCut κ b fr f :=
  κ.fiberAtPoleOnWithin_univTags_iff b (fr.provocationClass f)

/-- A seen run is quiet on a class. This is display over a finite track record,
    not a claim about fresh calls. -/
def RunQuiet {Macro : Type} (κ : BeingCoarsening G Macro) (b : Macro)
    (cs : G.Call → Prop) (run : List G.Weld) : Prop :=
  ∀ w : G.Weld,
    w ∈ run →
      G.Actual w →
        κ.InFiber b w →
          cs w.call →
            AtBot (G.share w)

/-- A seen run is quiet on a call-class within a tag-region. This remains
    finite display, not a claim about fresh calls or fresh tags. -/
def RunQuietWithin {Macro : Type} (κ : BeingCoarsening G Macro) (b : Macro)
    (cs : G.Call → Prop) (ts : G.Being → Prop) (run : List G.Weld) : Prop :=
  ∀ w : G.Weld,
    w ∈ run →
      G.Actual w →
        κ.InFiber b w →
          cs w.call →
            ts w.agent →
              AtBot (G.share w)

theorem runQuiet_of_fetterCut {Macro : Type}
    {κ : BeingCoarsening G Macro} {b : Macro}
    {fr : G.FetterReading} {f : Fetter} {run : List G.Weld}
    (h : G.FetterCut κ b fr f) :
    G.RunQuiet κ b (fr.provocationClass f) run :=
  fun w _hmem hactual hfiber hclass => h w hactual hfiber hclass

theorem runQuietWithin_of_fetterCutWithin {Macro : Type}
    {κ : BeingCoarsening G Macro} {b : Macro}
    {fr : G.FetterReading} {f : Fetter} {ts : G.Being → Prop}
    {run : List G.Weld}
    (h : G.FetterCutWithin κ b fr f ts) :
    G.RunQuietWithin κ b (fr.provocationClass f) ts run :=
  fun w _hmem hactual hfiber hclass htag =>
    h w hactual hfiber hclass htag

/-- The forward-looking guarantee as a conditional: a regime may promote a
    finite class-quiet track record to a whole-fiber cut, but the grid does not
    discharge that antecedent. -/
def WaaIrreversibleRegime {Macro : Type} (κ : BeingCoarsening G Macro)
    (b : Macro) (fr : G.FetterReading) (run : List G.Weld) : Prop :=
  ∀ f : Fetter,
    G.RunQuiet κ b (fr.provocationClass f) run →
      G.FetterCut κ b fr f

theorem waaIrreversibleRegime_conditional {Macro : Type}
    {κ : BeingCoarsening G Macro} {b : Macro}
    {fr : G.FetterReading} {run : List G.Weld} {f : Fetter}
    (hregime : G.WaaIrreversibleRegime κ b fr run)
    (hseen : G.RunQuiet κ b (fr.provocationClass f) run) :
    G.FetterCut κ b fr f :=
  hregime f hseen

/-- The same forward-looking guarantee restricted to a supplied tag-region.
    The guarantee remains conditional; the grid does not infer the regime. -/
def WaaIrreversibleRegimeWithin {Macro : Type}
    (κ : BeingCoarsening G Macro) (b : Macro)
    (fr : G.FetterReading) (ts : G.Being → Prop) (run : List G.Weld) : Prop :=
  ∀ f : Fetter,
    G.RunQuietWithin κ b (fr.provocationClass f) ts run →
      G.FetterCutWithin κ b fr f ts

theorem waaIrreversibleRegimeWithin_conditional {Macro : Type}
    {κ : BeingCoarsening G Macro} {b : Macro}
    {fr : G.FetterReading} {ts : G.Being → Prop}
    {run : List G.Weld} {f : Fetter}
    (hregime : G.WaaIrreversibleRegimeWithin κ b fr ts run)
    (hseen : G.RunQuietWithin κ b (fr.provocationClass f) ts run) :
    G.FetterCutWithin κ b fr f ts :=
  hregime f hseen

end Grid

namespace Path

/-- Which named fetters have been abandoned at a path. Once-return adds no new
    cut classes; it is retained as a path tag for the prose weakening clause. -/
def cutsFetter : Path → Fetter → Prop
  | .streamEntry, f => Fetter.abandonedAt f = .streamEntry
  | .onceReturn, f => Fetter.abandonedAt f = .streamEntry
  | .nonReturn, f =>
      Fetter.abandonedAt f = .streamEntry ∨
        Fetter.abandonedAt f = .nonReturn
  | .arhatship, _ => True

/-- The call-class quieted by a path under a supplied fetter reading. The arhat
    class is total, closing the family back into `FiberAtPole`. -/
def cutClasses {Contrib : Type} [PreorderBot Contrib] {G : Grid Contrib}
    (fr : G.FetterReading) : Path → G.Call → Prop
  | .streamEntry, c =>
      ∃ f : Fetter, cutsFetter .streamEntry f ∧ fr.provocationClass f c
  | .onceReturn, c =>
      ∃ f : Fetter, cutsFetter .onceReturn f ∧ fr.provocationClass f c
  | .nonReturn, c =>
      ∃ f : Fetter, cutsFetter .nonReturn f ∧ fr.provocationClass f c
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
    ∀ c : G.Call, cutClasses fr streamEntry c → cutClasses fr onceReturn c := by
  intro c h
  rcases h with ⟨f, hf, hc⟩
  exact ⟨f, hf, hc⟩

theorem onceReturn_cutClasses_subset_nonReturn
    {Contrib : Type} [PreorderBot Contrib] {G : Grid Contrib}
    (fr : G.FetterReading) :
    ∀ c : G.Call, cutClasses fr onceReturn c → cutClasses fr nonReturn c := by
  intro c h
  rcases h with ⟨f, hf, hc⟩
  exact ⟨f, Or.inl hf, hc⟩

theorem nonReturn_cutClasses_subset_arhatship
    {Contrib : Type} [PreorderBot Contrib] {G : Grid Contrib}
    (fr : G.FetterReading) :
    ∀ c : G.Call, cutClasses fr nonReturn c → cutClasses fr arhatship c :=
  fun _c _h => True.intro

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

/-- Class quietness is monotone under subclass restriction. -/
theorem classQuiet_mono {Macro : Type}
    {κ : BeingCoarsening G Macro} {b : Macro}
    {cs ds : G.Call → Prop}
    (h : κ.FiberAtPoleOn b cs)
    (hsub : ∀ c : G.Call, ds c → cs c) :
    κ.FiberAtPoleOn b ds :=
  κ.fiberAtPoleOn_mono h hsub

/-- Quiet on the total class is exactly ordinary `FiberAtPole`. -/
theorem fiberAtPole_iff_classQuiet_univ {Macro : Type}
    (κ : BeingCoarsening G Macro) (b : Macro) :
    κ.FiberAtPole b ↔ κ.FiberAtPoleOn b (fun _ => True) :=
  (κ.fiberAtPoleOn_univ_iff b).symm

/-- Path quietness inside a supplied tag-region: the same path call-class
    lattice, now restricted to a fine tag-class as well. -/
def PathQuietWithin {Macro : Type} (κ : BeingCoarsening G Macro) (b : Macro)
    (fr : G.FetterReading) (p : Path) (ts : G.Being → Prop) : Prop :=
  κ.FiberAtPoleOnWithin b (Path.cutClasses fr p) ts

/-- The arhat path-class is total, so path quietness at arhatship is ordinary
    fiber-at-pole typing. -/
theorem arhatPathQuiet_iff_fiberAtPole
    {κ : G.PathScheme} (fr : G.FetterReading) :
    κ.FiberAtPoleOn Path.arhatship (Path.cutClasses fr Path.arhatship) ↔
      κ.FiberAtPole Path.arhatship := by
  change κ.FiberAtPoleOn Path.arhatship (fun _ => True) ↔
    κ.FiberAtPole Path.arhatship
  exact (G.fiberAtPole_iff_classQuiet_univ κ Path.arhatship).symm

theorem all_fetters_cut_at_arhatFiber
    {κ : G.PathScheme} (fr : G.FetterReading)
    (h : κ.FiberAtPole Path.arhatship) :
    ∀ f : Fetter, G.FetterCut κ Path.arhatship fr f :=
  fun _f w hactual hfiber _hclass => h w hactual hfiber

/-- At arhatship the call-class is total, so path quietness within a region is
    exactly tag-restricted fiber-at-pole. -/
theorem arhatPathQuietWithin_iff_fiberAtPoleWithin
    {κ : G.PathScheme} (fr : G.FetterReading)
    (ts : G.Being → Prop) :
    G.PathQuietWithin κ Path.arhatship fr Path.arhatship ts ↔
      κ.FiberAtPoleWithin Path.arhatship ts := by
  change κ.FiberAtPoleOnWithin Path.arhatship (fun _ => True) ts ↔
    κ.FiberAtPoleWithin Path.arhatship ts
  exact κ.fiberAtPoleOnWithin_univCalls_iff Path.arhatship ts

/-- At total calls and total tags, the two-axis path lattice closes back to
    ordinary `FiberAtPole`: the top point adds no new predicate. The word
    "buddha" belongs only to the layered reading above this neutral cut:
    `FettersNegative.total_cut_carries_no_function` shows that the top point
    alone carries no function conjunct, while
    `FettersNegative.total_cut_with_function_not_waaFullyEnlightened` and
    `waaFullyEnlightened_of_responsiveTerminus_of_undelivered` keep
    effectiveness regime-relational. Arhat reading remains `PathQuietWithin`
    at a supplied `SomaReading.speechThoughtTag`; vasana is residual clench in
    the complement region after the call-axis closes. -/
theorem arhatWithin_univTags_iff_fiberAtPole
    {κ : G.PathScheme} (fr : G.FetterReading) :
    G.PathQuietWithin κ Path.arhatship fr Path.arhatship (fun _ => True) ↔
      κ.FiberAtPole Path.arhatship := by
  change κ.FiberAtPoleOnWithin Path.arhatship
    (fun _ => True) (fun _ => True) ↔ κ.FiberAtPole Path.arhatship
  exact κ.fiberAtPoleOnWithin_univ_univ_iff Path.arhatship

/-- If a class-restricted cut holds, no actual weld in that fiber and class
    carries a live self-pole index. -/
theorem classQuiet_no_clench_in_class {Macro : Type}
    {κ : BeingCoarsening G Macro} {b : Macro}
    {fr : G.FetterReading} {f : Fetter} {w : G.Weld}
    (h : G.FetterCut κ b fr f)
    (hactual : G.Actual w) (hfiber : κ.InFiber b w)
    (hclass : fr.provocationClass f w.call) :
    ¬ G.HasSelfPoleIndex w :=
  κ.no_live_index_under_fiberAtPoleOn h hactual hfiber hclass

/-- Stream-entry removes identity-view when the arhat fiber is live at pole:
    pole-fiber typing refutes the self-apt tag directly. -/
theorem identityView_excluded_at_arhatFiber
    {κ : G.PathScheme}
    (h : κ.LiveFiberAtPole Path.arhatship) :
    ¬ κ.SelfAptTag Path.arhatship :=
  κ.liveFiberAtPole_not_selfAptTag h

/-- Identity-view is excluded in the supplied speech/thought region once that
    region is live at pole. -/
theorem identityView_excluded_at_speechThoughtRegion {Macro : Type}
    {κ : BeingCoarsening G Macro} {b : Macro}
    (sr : G.SomaReading)
    (h : κ.LiveFiberAtPoleWithin b sr.speechThoughtTag) :
    ¬ κ.SelfAptTagWithin b sr.speechThoughtTag :=
  κ.liveFiberAtPoleWithin_not_selfAptTagWithin h

/-- Conceit as a live self-share is refuted fiber-wide by `FiberAtPole`. -/
theorem conceit_excluded_at_arhatFiber
    {κ : G.PathScheme}
    (h : κ.FiberAtPole Path.arhatship) :
    ∀ w : G.Weld,
      G.Actual w →
        κ.InFiber Path.arhatship w →
          ¬ G.HasSelfPoleIndex w :=
  fun _w hactual hfiber =>
    κ.no_live_index_under_fiberAtPole h hactual hfiber

/-- Conceit as a live self-share is refuted throughout the supplied region by
    tag-restricted fiber-at-pole. -/
theorem conceit_excluded_within {Macro : Type}
    {κ : BeingCoarsening G Macro} {b : Macro} {ts : G.Being → Prop}
    (h : κ.FiberAtPoleWithin b ts) :
    ∀ w : G.Weld,
      G.Actual w →
        κ.InFiber b w →
          ts w.agent →
            ¬ G.HasSelfPoleIndex w :=
  fun _w hactual hfiber htag =>
    κ.no_live_index_under_fiberAtPoleOnWithin h
      hactual hfiber True.intro htag

/-- If every fine tag under the arhat fiber is terminus-typed, the whole
    actual fiber is at pole. -/
theorem arhatFiber_of_termini
    {κ : G.PathScheme}
    (h : ∀ p : G.Being, κ.proj p = Path.arhatship → G.Terminus p) :
    κ.FiberAtPole Path.arhatship :=
  κ.fiberAtPole_of_fiber_termini h

/-- Doctrine-facing name for region-restricted termini sufficiency. -/
theorem regionFiber_of_termini {Macro : Type}
    {κ : BeingCoarsening G Macro} {b : Macro} {ts : G.Being → Prop}
    (h : ∀ p : G.Being, κ.proj p = b → ts p → G.Terminus p) :
    κ.FiberAtPoleWithin b ts :=
  κ.fiberAtPoleWithin_of_class_termini h

/-- The speech/thought region in the register-clock witness: register `0`.
    The boundary is supplied data, not recovered from the grid. -/
def registerSpeechThoughtTag (p : registerClockGrid.Being) : Prop :=
  p = (0 : Nat)

theorem registerSpeechThoughtTag_cut :
    registerClockCoarsening.FiberAtPoleWithin () registerSpeechThoughtTag := by
  intro w _hactual _hfiber _hclass htag
  cases w with
  | mk agent call response =>
      dsimp [registerSpeechThoughtTag] at htag
      rw [htag]
      dsimp [Grid.share, registerClockGrid, AtBot, shareBot]
      show (0 : Nat) ≤ 0
      decide

theorem registerSpeechThoughtTag_mounts :
    registerClockGrid.MountsSomewhere (0 : Nat) :=
  ⟨(), ⟨(1 : Nat), rfl⟩⟩

def registerUncutWeld : registerClockGrid.Weld :=
  ⟨(1 : Nat), (), (2 : Nat)⟩

theorem registerUncutWeld_live_index :
    registerClockGrid.HasSelfPoleIndex registerUncutWeld := by
  dsimp [Grid.HasSelfPoleIndex, Grid.share, registerClockGrid,
    registerUncutWeld, AtBot, shareBot]
  change ¬ (1 : Nat) ≤ 0
  exact Nat.not_succ_le_zero 0

/-- Region cuts constrain share, not function. In the register-clock witness,
    the cut region mounts a response at the pole, while an uncut tag outside
    the region also mounts a response and carries a live self-pole index. -/
theorem unquiet_region_still_functions_witness :
    registerClockCoarsening.FiberAtPoleWithin () registerSpeechThoughtTag ∧
      registerClockGrid.MountsSomewhere (0 : Nat) ∧
        ∃ p : registerClockGrid.Being,
          ¬ registerSpeechThoughtTag p ∧
            registerClockGrid.MountsSomewhere p ∧
              ∃ w : registerClockGrid.Weld,
                registerClockGrid.Actual w ∧
                  w.agent = p ∧ registerClockGrid.HasSelfPoleIndex w :=
  ⟨registerSpeechThoughtTag_cut, registerSpeechThoughtTag_mounts,
    ⟨(1 : Nat), by
      intro h
      dsimp [registerSpeechThoughtTag] at h
      exact Nat.succ_ne_zero 0 h,
      ⟨(), ⟨(2 : Nat), rfl⟩⟩,
      ⟨registerUncutWeld, rfl, rfl, registerUncutWeld_live_index⟩⟩⟩

end Grid

end WAA
