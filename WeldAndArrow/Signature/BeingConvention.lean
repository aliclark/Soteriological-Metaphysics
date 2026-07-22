/-
================================================================================
  WeldAndArrow.Signature.BeingConvention
  Being-convention vocabulary and diagnosis-time coarsenings
================================================================================

Reading and motivation: Identification/Commentary.lean, C.1.
-/

import WeldAndArrow.Signature.SentienceConvention

namespace WAA

namespace Grid

variable {Contrib : Type} [PreorderBot Contrib]
variable (G : Grid Contrib)

namespace DirectedConvention
namespace BeingConvention

/- Reading and motivation: Identification/Commentary.lean, C.1. -/
abbrev MountsAt (b : G.Being) (c : G.Call) : Prop := G.MountsAt b c

/-- Re-rooted name for call-entire response. -/
abbrev RespondsToEveryCall (b : G.Being) : Prop := G.RespondsToEveryCall b

/-- Re-rooted name for the pole-class responder. -/
abbrev Terminus (b : G.Being) : Prop := G.Terminus b

/-- Re-rooted name for non-vacuous terminus response. -/
abbrev LiveTerminus (b : G.Being) : Prop := G.LiveTerminus b

/-- Re-rooted name for call-entire terminus response. -/
abbrev ResponsiveTerminus (b : G.Being) : Prop := G.ResponsiveTerminus b

/-- Re-rooted name for terminus typing at the pole-class. -/
abbrev AtPoleClass (b : G.Being) : Prop := G.AtPoleClass b

/-- Re-rooted name for the probe, because the probe reads a being's
    composition rather than adding a field to the signature. -/
abbrev ProbeConstant (b : G.Being) (cs : G.Call → Prop) : Prop :=
  G.ProbeConstant b cs

/- Reading and motivation: Identification/Commentary.lean, C.1. -/
structure BeingCoarsening (G : Grid Contrib) (Macro : Type) where
  proj : G.Being → Macro

namespace BeingCoarsening

variable {G : Grid Contrib} {Macro : Type} (κ : BeingCoarsening G Macro)

/-- The identity being coarsening: every fine tag remains its own macro tag. -/
protected def id (G : Grid Contrib) : BeingCoarsening G G.Being where
  proj := id

@[simp]
theorem id_proj (p : G.Being) :
    (BeingCoarsening.id G).proj p = p :=
  rfl

/-- The total being coarsening: all fine tags are read as one macro tag. -/
def total (G : Grid Contrib) : BeingCoarsening G Unit where
  proj _ := ()

@[simp]
theorem total_proj (p : G.Being) :
    (BeingCoarsening.total G).proj p = () :=
  rfl

/-- Post-compose a being coarsening with a macro-tag map. -/
def comp {Macro' : Type} (κ : BeingCoarsening G Macro)
    (f : Macro → Macro') :
    BeingCoarsening G Macro' where
  proj := fun p => f (κ.proj p)

@[simp]
theorem comp_proj {Macro' : Type} (κ : BeingCoarsening G Macro)
    (f : Macro → Macro') (p : G.Being) :
    (κ.comp f).proj p = f (κ.proj p) :=
  rfl

/-- A weld lies in a macro tag's fiber when its fine agent projects there. -/
def InFiber (b : Macro) (w : G.Weld) : Prop := κ.proj w.agent = b

/- Reading and motivation: Identification/Commentary.lean, C.1. -/
def SameFiber (p q : G.Being) : Prop := κ.proj p = κ.proj q

theorem total_sameFiber (p q : G.Being) :
    (BeingCoarsening.total G).SameFiber p q :=
  rfl

theorem id_not_sameFiber_of_ne {p q : G.Being} (h : p ≠ q) :
    ¬ (BeingCoarsening.id G).SameFiber p q :=
  fun hsame => h hsame

/-- A fiber has at least one fine tag under it. -/
def FiberInhabited (b : Macro) : Prop := ∃ p : G.Being, κ.proj p = b

/-- A fiber has at least one actual weld under it. This is the live/vacuity
    guard needed for exclusivity facts below. -/
def ActualFiberInhabited (b : Macro) : Prop :=
  ∃ w : G.Weld, G.Actual w ∧ κ.InFiber b w

/-- A macro tag has at least one actual weld marked sentient by the supplied
    reading.  This is quantified display over acts, not a standing property. -/
def SentientTag (S : SentienceReading G) (b : Macro) : Prop :=
  ∃ w : G.Weld, G.SentientAct S w ∧ κ.InFiber b w

/-- A nonempty macro tag all of whose actual welds occupy the insentient
    pole-share cell. -/
def StoneTag (S : SentienceReading G) (b : Macro) : Prop :=
  κ.ActualFiberInhabited b ∧
    ∀ w : G.Weld, G.Actual w → κ.InFiber b w → G.StoneAct S w

/-- A macro tag with both marked and unmarked actual welds.  No scalar degree
    of sentience is inferred from this patchiness. -/
def Intermittent (S : SentienceReading G) (b : Macro) : Prop :=
  (∃ w : G.Weld, G.SentientAct S w ∧ κ.InFiber b w) ∧
    (∃ w : G.Weld, G.InsentientAct S w ∧ κ.InFiber b w)

theorem actualFiberInhabited_of_sentientTag
    (S : SentienceReading G) {b : Macro} (h : κ.SentientTag S b) :
    κ.ActualFiberInhabited b := by
  rcases h with ⟨w, hsentient, hfiber⟩
  exact ⟨w, hsentient.left, hfiber⟩

theorem allSentient_sentientTag_iff_actualFiberInhabited (b : Macro) :
    κ.SentientTag (SentienceReading.allSentient G) b ↔
      κ.ActualFiberInhabited b := by
  constructor
  · exact κ.actualFiberInhabited_of_sentientTag
      (SentienceReading.allSentient G)
  · rintro ⟨w, hactual, hfiber⟩
    exact ⟨w, ⟨hactual, True.intro⟩, hfiber⟩

theorem allInsentient_not_sentientTag (b : Macro) :
    ¬ κ.SentientTag (SentienceReading.allInsentient G) b := by
  rintro ⟨w, hsentient, _hfiber⟩
  exact hsentient.right

/- Reading and motivation: Identification/Commentary.lean, C.1. -/
def FiberAtPole (b : Macro) : Prop :=
  ∀ w : G.Weld, G.Actual w → κ.InFiber b w → AtBot (G.share w)

/-- The live, non-vacuous fiber-at-pole predicate. -/
def LiveFiberAtPole (b : Macro) : Prop :=
  κ.ActualFiberInhabited b ∧ κ.FiberAtPole b

/-- A fiber reads at the pole on a supplied call-class. This is neutral fiber
    vocabulary: downstream doctrines supply the class predicate. -/
def FiberAtPoleOn (b : Macro) (cs : G.Call → Prop) : Prop :=
  ∀ w : G.Weld, G.Actual w → κ.InFiber b w → cs w.call → AtBot (G.share w)

/-- Fiber-at-pole restricted on both axes: over a call-class `cs` and a fine
    tag-class `ts`. The single-axis restrictions and plain fiber reading are
    its specializations. -/
def FiberAtPoleOnWithin (b : Macro) (cs : G.Call → Prop)
    (ts : G.Being → Prop) : Prop :=
  ∀ w : G.Weld, G.Actual w → κ.InFiber b w →
    cs w.call → ts w.agent → AtBot (G.share w)

/-- A fiber reads at the pole within a supplied fine tag-class. -/
def FiberAtPoleWithin (b : Macro) (ts : G.Being → Prop) : Prop :=
  κ.FiberAtPoleOnWithin b (fun _ => True) ts

/-- A fiber has an actual weld in the supplied call-class. -/
def ActualFiberInhabitedOn (b : Macro) (cs : G.Call → Prop) : Prop :=
  ∃ w : G.Weld, G.Actual w ∧ κ.InFiber b w ∧ cs w.call

/-- A fiber has an actual weld whose agent lies in the supplied tag-class. -/
def ActualFiberInhabitedWithin (b : Macro) (ts : G.Being → Prop) : Prop :=
  ∃ w : G.Weld, G.Actual w ∧ κ.InFiber b w ∧ ts w.agent

/-- The live, non-vacuous class-restricted fiber-at-pole predicate. -/
def LiveFiberAtPoleOn (b : Macro) (cs : G.Call → Prop) : Prop :=
  κ.ActualFiberInhabitedOn b cs ∧ κ.FiberAtPoleOn b cs

/-- The live, non-vacuous tag-restricted fiber-at-pole predicate. -/
def LiveFiberAtPoleWithin (b : Macro) (ts : G.Being → Prop) : Prop :=
  κ.ActualFiberInhabitedWithin b ts ∧ κ.FiberAtPoleWithin b ts

/-- Every actual weld in the fiber carries a live self-pole index.
    Vacuous on empty or no-actual fibers; use `LiveSelfAptTag` when
    inhabitation matters. -/
def SelfAptTag (b : Macro) : Prop :=
  ∀ w : G.Weld, G.Actual w → κ.InFiber b w → G.HasSelfPoleIndex w

/-- Every actual weld in the supplied tag-class carries a live self-pole index.
    Vacuous unless paired with a live/inhabited hypothesis. -/
def SelfAptTagWithin (b : Macro) (ts : G.Being → Prop) : Prop :=
  ∀ w : G.Weld, G.Actual w → κ.InFiber b w →
    ts w.agent → G.HasSelfPoleIndex w

/-- The live, non-vacuous self-apt predicate. -/
def LiveSelfAptTag (b : Macro) : Prop :=
  κ.ActualFiberInhabited b ∧ κ.SelfAptTag b

/-- Patchy fiber: neither all actual welds are at the pole nor all actual
    welds are self-apt. No middling scalar is smuggled in. -/
def Patchy (b : Macro) : Prop := ¬ κ.FiberAtPole b ∧ ¬ κ.SelfAptTag b

/-- If every fine tag in the fiber is terminus-typed, the whole actual fiber
    reads at the pole. -/
theorem fiberAtPole_of_fiber_termini {b : Macro}
    (h : ∀ p : G.Being, κ.proj p = b → G.Terminus p) :
    κ.FiberAtPole b := by
  intro w hactual hfiber
  exact G.atBot_of_terminus_response (h w.agent hfiber) hactual

/-- If every fine tag in the fiber and supplied tag-class is terminus-typed,
    the tag-restricted actual fiber reads at the pole. -/
theorem fiberAtPoleWithin_of_class_termini {b : Macro}
    {ts : G.Being → Prop}
    (h : ∀ p : G.Being, κ.proj p = b → ts p → G.Terminus p) :
    κ.FiberAtPoleWithin b ts := by
  intro w hactual hfiber _hclass htag
  exact G.atBot_of_terminus_response (h w.agent hfiber htag) hactual

/-- Under a fiber-at-pole reading, no actual weld in the fiber has a live
    self-pole index. -/
theorem no_live_index_under_fiberAtPole {b : Macro}
    (h : κ.FiberAtPole b) {w : G.Weld}
    (hactual : G.Actual w) (hfiber : κ.InFiber b w) :
    ¬ G.HasSelfPoleIndex w :=
  G.no_self_pole_index_of_atBot w (h w hactual hfiber)

theorem fiberAtPoleOn_mono {b : Macro} {cs ds : G.Call → Prop}
    (h : κ.FiberAtPoleOn b cs)
    (hsub : ∀ c : G.Call, ds c → cs c) :
    κ.FiberAtPoleOn b ds :=
  fun w hactual hfiber hds => h w hactual hfiber (hsub w.call hds)

theorem fiberAtPoleOnWithin_mono_call {b : Macro}
    {cs ds : G.Call → Prop} {ts : G.Being → Prop}
    (h : κ.FiberAtPoleOnWithin b cs ts)
    (hsub : ∀ c : G.Call, ds c → cs c) :
    κ.FiberAtPoleOnWithin b ds ts :=
  fun w hactual hfiber hds htag =>
    h w hactual hfiber (hsub w.call hds) htag

theorem fiberAtPoleOnWithin_mono_tag {b : Macro}
    {cs : G.Call → Prop} {ts us : G.Being → Prop}
    (h : κ.FiberAtPoleOnWithin b cs ts)
    (hsub : ∀ p : G.Being, us p → ts p) :
    κ.FiberAtPoleOnWithin b cs us :=
  fun w hactual hfiber hclass hus =>
    h w hactual hfiber hclass (hsub w.agent hus)

theorem fiberAtPoleOn_univ_iff (b : Macro) :
    κ.FiberAtPoleOn b (fun _ => True) ↔ κ.FiberAtPole b := by
  constructor
  · intro h w hactual hfiber
    exact h w hactual hfiber True.intro
  · intro h w hactual hfiber _hclass
    exact h w hactual hfiber

theorem fiberAtPoleOnWithin_univTags_iff
    (b : Macro) (cs : G.Call → Prop) :
    κ.FiberAtPoleOnWithin b cs (fun _ => True) ↔
      κ.FiberAtPoleOn b cs := by
  constructor
  · intro h w hactual hfiber hclass
    exact h w hactual hfiber hclass True.intro
  · intro h w hactual hfiber hclass _htag
    exact h w hactual hfiber hclass

theorem fiberAtPoleOnWithin_univCalls_iff
    (b : Macro) (ts : G.Being → Prop) :
    κ.FiberAtPoleOnWithin b (fun _ => True) ts ↔
      κ.FiberAtPoleWithin b ts :=
  Iff.rfl

theorem fiberAtPoleOnWithin_univ_univ_iff (b : Macro) :
    κ.FiberAtPoleOnWithin b (fun _ => True) (fun _ => True) ↔
      κ.FiberAtPole b := by
  constructor
  · intro h w hactual hfiber
    exact h w hactual hfiber True.intro True.intro
  · intro h w hactual hfiber _hclass _htag
    exact h w hactual hfiber

theorem fiberAtPoleWithin_of_fiberAtPole {b : Macro}
    {ts : G.Being → Prop}
    (h : κ.FiberAtPole b) :
    κ.FiberAtPoleWithin b ts := by
  intro w hactual hfiber _hclass _htag
  exact h w hactual hfiber

theorem no_live_index_under_fiberAtPoleOn {b : Macro} {cs : G.Call → Prop}
    (h : κ.FiberAtPoleOn b cs) {w : G.Weld}
    (hactual : G.Actual w) (hfiber : κ.InFiber b w) (hclass : cs w.call) :
    ¬ G.HasSelfPoleIndex w :=
  G.no_self_pole_index_of_atBot w (h w hactual hfiber hclass)

theorem no_live_index_under_fiberAtPoleOnWithin {b : Macro}
    {cs : G.Call → Prop} {ts : G.Being → Prop}
    (h : κ.FiberAtPoleOnWithin b cs ts) {w : G.Weld}
    (hactual : G.Actual w) (hfiber : κ.InFiber b w)
    (hclass : cs w.call) (htag : ts w.agent) :
    ¬ G.HasSelfPoleIndex w :=
  G.no_self_pole_index_of_atBot w (h w hactual hfiber hclass htag)

/-- Fiber soul-guard: even where the self-convention is apt, the index is
    only the per-weld agent tag. No macro owner is produced. -/
theorem selfAptTag_indices_are_per_weld_only {b : Macro}
    (h : κ.SelfAptTag b) {w : G.Weld}
    (hactual : G.Actual w) (hfiber : κ.InFiber b w) :
    G.selfPoleIndex w (h w hactual hfiber) = w.agent :=
  rfl

/-- The empty-fiber vacuity guard: fiber-at-pole and self-apt are exclusive
    only once an actual weld in the fiber is supplied. -/
theorem fiberAtPole_selfAptTag_exclusive {b : Macro}
    (hinh : κ.ActualFiberInhabited b)
    (hpole : κ.FiberAtPole b) (hself : κ.SelfAptTag b) :
    False := by
  rcases hinh with ⟨w, hactual, hfiber⟩
  exact hself w hactual hfiber (hpole w hactual hfiber)

theorem liveFiberAtPole_not_selfAptTag {b : Macro}
    (h : κ.LiveFiberAtPole b) :
    ¬ κ.SelfAptTag b :=
  fun hself => κ.fiberAtPole_selfAptTag_exclusive h.left h.right hself

theorem liveFiberAtPoleWithin_not_selfAptTagWithin {b : Macro}
    {ts : G.Being → Prop}
    (h : κ.LiveFiberAtPoleWithin b ts) :
    ¬ κ.SelfAptTagWithin b ts := by
  intro hself
  rcases h.left with ⟨w, hactual, hfiber, htag⟩
  exact hself w hactual hfiber htag
    (h.right w hactual hfiber True.intro htag)

theorem liveSelfAptTag_not_fiberAtPole {b : Macro}
    (h : κ.LiveSelfAptTag b) :
    ¬ κ.FiberAtPole b :=
  fun hpole => κ.fiberAtPole_selfAptTag_exclusive h.left hpole h.right

/-- Internal refinement within sentience: the fiber carries at least one
    internal delivery line. Any persistence theorem built from this owes a
    model-supplied asymmetry or irreflexivity hypothesis on `conditions`. -/
def SelfConditioningTag (b : Macro) : Prop :=
  ∃ deed reception : G.Weld,
    κ.InFiber b deed ∧ κ.InFiber b reception ∧
    G.Actual reception ∧ DeliveredTo G deed reception

/-- A stronger asymptote: every actual reception in the fiber is internally
    fed. It is named and shelved because treating it as the default would
    turn internal conditioning into causal solipsism. -/
def StrongSelfConditioningTag (b : Macro) : Prop :=
  ∀ reception : G.Weld, κ.InFiber b reception → G.Actual reception →
    ∃ deed : G.Weld, κ.InFiber b deed ∧ DeliveredTo G deed reception

/- Reading and motivation: Identification/Commentary.lean, C.1. -/
structure Delegation (b : Macro) where
  weld : G.Weld
  actual : G.Actual weld
  delegate_in_fiber : κ.InFiber b weld

namespace Delegation

/- Reading and motivation: Identification/Commentary.lean, C.1. -/
def share {b : Macro} (d : κ.Delegation b) : Contrib := G.share d.weld

@[simp]
theorem share_eq_delegate_share {b : Macro} (d : κ.Delegation b) :
    d.share = G.share d.weld :=
  rfl

end Delegation

/-- Transpose a being-coarsening across the condition-transpose operation.
    Fine tags are unchanged; only delivery order reverses. -/
def transpose (κ : BeingCoarsening G Macro) :
    BeingCoarsening G.transpose Macro where
  proj := κ.proj

theorem transpose_inFiber_iff
    (κ : BeingCoarsening G Macro) (b : Macro) (w : G.Weld) :
    κ.transpose.InFiber b w ↔ κ.InFiber b w :=
  Iff.rfl

theorem transpose_sentientTag_iff
    (κ : BeingCoarsening G Macro) (S : SentienceReading G) (b : Macro) :
    κ.transpose.SentientTag S.transpose b ↔ κ.SentientTag S b :=
  Iff.rfl

/-- Direction-smuggling detector for the directed refinement: transposition
    reverses the delivery line while leaving fiber membership and actuality
    untouched. -/
theorem transpose_selfConditioningTag
    (κ : BeingCoarsening G Macro) (b : Macro) :
    κ.transpose.SelfConditioningTag b ↔
      ∃ deed reception : G.Weld,
        κ.InFiber b deed ∧ κ.InFiber b reception ∧
        G.Actual reception ∧ DeliveredTo G reception deed := by
  constructor
  · rintro ⟨deed, reception, hdeed, hreception, hactual, hdel⟩
    exact ⟨deed, reception, hdeed, hreception, hactual,
      (DirectedConvention.transpose_deliveredTo_iff G deed reception).mp hdel⟩
  · rintro ⟨deed, reception, hdeed, hreception, hactual, hdel⟩
    exact ⟨deed, reception, hdeed, hreception, hactual,
      (DirectedConvention.transpose_deliveredTo_iff G deed reception).mpr hdel⟩

end BeingCoarsening

/- The innermost `GridConvention` namespace is opened in the Consequences
   files for the concrete claim-language rows. Keeping the abstract machinery
   at `Grid` level for now avoids a churn-only migration of structure fields
   whose eventual home may simply remain signature rather than reading. -/

end BeingConvention

end DirectedConvention

end Grid

end WAA
