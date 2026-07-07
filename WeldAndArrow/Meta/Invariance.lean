/-
================================================================================
  WeldAndArrow.Meta.Invariance
  Display reparameterization and transport lemmas
================================================================================

This module transports grid predicates across display reparameterizations and
keeps transport lemmas centralized so missing invariance facts are conspicuous.

Reading and motivation: Identification/Commentary.lean, C.3.
-/

import WeldAndArrow.Consequences.ContentRows
import WeldAndArrow.Identification
import WeldAndArrow.Doctrines.Sraddha
import WeldAndArrow.Doctrines.Faith
import WeldAndArrow.Doctrines.Correlations

/-!
Any predicate over the contribution carrier added anywhere in the library owes
a `map_*` transport lemma in this file, or it counts as operational residue.
Transport lemmas stay centralized here so a missing lemma is conspicuous.
-/

namespace WAA

/-- A display-reparameterization: preserves and reflects the ordering and the
    pole-class. The invariance theorems below are the formal content of
    "display conventions over that partial order". -/
structure DisplayReparam (Contrib Contrib' : Type)
    [PreorderBot Contrib] [PreorderBot Contrib'] where
  toFun     : Contrib → Contrib'
  le_iff    : ∀ a b, a ≼ b ↔ toFun a ≼ toFun b
  atBot_bot : AtBot (toFun shareBot)

namespace DisplayReparam

variable {Contrib Contrib' : Type} [PreorderBot Contrib] [PreorderBot Contrib']
variable (f : DisplayReparam Contrib Contrib')

/-- The identity display reparameterization. -/
protected def id (Contrib : Type) [PreorderBot Contrib] :
    DisplayReparam Contrib Contrib where
  toFun := id
  le_iff := fun _ _ => Iff.rfl
  atBot_bot := atBot_shareBot

@[simp]
theorem id_toFun (a : Contrib) :
    (DisplayReparam.id Contrib).toFun a = a :=
  rfl

/-- Composition of display reparameterizations. -/
def comp {Contrib'' : Type} [PreorderBot Contrib'']
    (f : DisplayReparam Contrib Contrib')
    (g : DisplayReparam Contrib' Contrib'') :
    DisplayReparam Contrib Contrib'' where
  toFun := fun a => g.toFun (f.toFun a)
  le_iff := fun a b => (f.le_iff a b).trans (g.le_iff (f.toFun a) (f.toFun b))
  atBot_bot :=
    Preorder.le_trans
      ((g.le_iff (f.toFun shareBot) shareBot).mp f.atBot_bot)
      g.atBot_bot

@[simp]
theorem comp_toFun {Contrib'' : Type} [PreorderBot Contrib'']
    (f : DisplayReparam Contrib Contrib')
    (g : DisplayReparam Contrib' Contrib'') (a : Contrib) :
    (DisplayReparam.comp f g).toFun a = g.toFun (f.toFun a) :=
  rfl

/-- Reparameterization preserves and reflects the pole-class. -/
theorem atBot_iff (a : Contrib) :
    AtBot (f.toFun a) ↔ AtBot a := by
  constructor
  · intro h
    exact (f.le_iff a shareBot).mpr
      (Preorder.le_trans h (shareBot_le (f.toFun shareBot)))
  · intro h
    exact Preorder.le_trans ((f.le_iff a shareBot).mp h) f.atBot_bot

/-- Reparameterization preserves and reflects order-equivalence. -/
theorem orderEq_iff (a b : Contrib) :
    OrderEq (f.toFun a) (f.toFun b) ↔ OrderEq a b := by
  constructor
  · intro h
    exact ⟨(f.le_iff a b).mpr h.left, (f.le_iff b a).mpr h.right⟩
  · intro h
    exact ⟨(f.le_iff a b).mp h.left, (f.le_iff b a).mp h.right⟩

theorem strict_iff (a b : Contrib) :
    Strict (f.toFun a) (f.toFun b) ↔ Strict a b := by
  constructor
  · intro h
    exact ⟨(f.le_iff a b).mpr h.left,
      fun hle => h.right ((f.le_iff b a).mp hle)⟩
  · intro h
    exact ⟨(f.le_iff a b).mp h.left,
      fun hle => h.right ((f.le_iff b a).mpr hle)⟩

theorem directionVoid_reflect (f : DisplayReparam Contrib Contrib')
    (h : DirectionVoid Contrib') :
    DirectionVoid Contrib :=
  fun a b hstrict =>
    h (f.toFun a) (f.toFun b) ((f.strict_iff a b).mpr hstrict)

/-- Full preservation of carrier-wide direction-voidness needs the target
    display to be covered by the reparameterization. -/
theorem directionVoid_of_surjective
    (hsurj : ∀ b : Contrib', ∃ a : Contrib, f.toFun a = b)
    (h : DirectionVoid Contrib) :
    DirectionVoid Contrib' := by
  intro a' b' hstrict
  rcases hsurj a' with ⟨a, rfl⟩
  rcases hsurj b' with ⟨b, rfl⟩
  exact h a b ((f.strict_iff a b).mp hstrict)

theorem exists_strict_map (f : DisplayReparam Contrib Contrib')
    (h : ∃ a b : Contrib, Strict a b) :
    ∃ a' b' : Contrib', Strict a' b' := by
  rcases h with ⟨a, b, hstrict⟩
  exact ⟨f.toFun a, f.toFun b, (f.strict_iff a b).mpr hstrict⟩

end DisplayReparam

namespace Config

variable {Contrib Contrib' : Type} [PreorderBot Contrib] [PreorderBot Contrib']

/-- Transport a stored display tendency along a display reparameterization. -/
def map (before : Config Contrib) (f : DisplayReparam Contrib Contrib') :
    Config Contrib' :=
  { tendency := f.toFun before.tendency }

@[simp]
theorem map_tendency (before : Config Contrib)
    (f : DisplayReparam Contrib Contrib') :
    (before.map f).tendency = f.toFun before.tendency :=
  rfl

end Config

namespace Grid

variable {Contrib Contrib' : Type} [PreorderBot Contrib] [PreorderBot Contrib']

/-- Transport a grid by reparameterizing only its Row-2 display carrier. -/
def map (G : Grid Contrib) (f : DisplayReparam Contrib Contrib') :
    Grid Contrib' where
  Being      := G.Being
  Call       := G.Call
  Response   := G.Response
  respondsTo := G.respondsTo
  grade      := fun b c r => f.toFun (G.grade b c r)
  conditions := G.conditions

variable (G : Grid Contrib) (f : DisplayReparam Contrib Contrib')

@[simp]
theorem map_grade (b : G.Being) (c : G.Call) (r : G.Response) :
    (G.map f).grade b c r = f.toFun (G.grade b c r) :=
  rfl

@[simp]
theorem map_share (w : G.Weld) :
    (G.map f).share w = f.toFun (G.share w) :=
  rfl

/-- Function-side predicates do not mention the contribution carrier, so they
    transport by definitional unfolding. -/
theorem map_actual_iff (w : G.Weld) :
    (G.map f).Actual w ↔ G.Actual w :=
  Iff.rfl

theorem map_exists_actual_iff :
    (∃ w : (G.map f).Weld, (G.map f).Actual w) ↔
      ∃ w : G.Weld, G.Actual w := by
  constructor
  · rintro ⟨w, hactual⟩
    exact ⟨w, (G.map_actual_iff f w).mp hactual⟩
  · rintro ⟨w, hactual⟩
    exact ⟨w, (G.map_actual_iff f w).mpr hactual⟩

theorem map_mountsAt_iff (b : G.Being) (c : G.Call) :
    (G.map f).MountsAt b c ↔ G.MountsAt b c :=
  Iff.rfl

theorem map_mountsSomewhere_iff (b : G.Being) :
    (G.map f).MountsSomewhere b ↔ G.MountsSomewhere b :=
  Iff.rfl

theorem map_respondsToEveryCall_iff (b : G.Being) :
    (G.map f).RespondsToEveryCall b ↔ G.RespondsToEveryCall b :=
  Iff.rfl

theorem map_stone_iff (b : G.Being) :
    (G.map f).Stone b ↔ G.Stone b :=
  Iff.rfl

theorem map_allStone_iff :
    (G.map f).AllStone ↔ G.AllStone := by
  constructor
  · intro h b
    exact (G.map_stone_iff f b).mp (h b)
  · intro h b
    exact (G.map_stone_iff f b).mpr (h b)

namespace DirectedConvention

theorem map_deliveredTo_iff (deed reception : G.Weld) :
    DeliveredTo (G.map f) deed reception ↔ DeliveredTo G deed reception :=
  Iff.rfl

theorem map_landsAt_iff (deed reception : G.Weld) :
    LandsAt (G.map f) deed reception ↔ LandsAt G deed reception :=
  Iff.rfl

theorem map_environsLine_iff
    (b : G.Being) (deed reception : G.Weld) :
    EnvironsLine (G.map f) b deed reception ↔ EnvironsLine G b deed reception :=
  Iff.rfl

end DirectedConvention

theorem map_terminus_iff (b : G.Being) :
    (G.map f).Terminus b ↔ G.Terminus b := by
  constructor
  · intro h c r hresp
    exact (f.atBot_iff (G.grade b c r)).mp (h c r hresp)
  · intro h c r hresp
    exact (f.atBot_iff (G.grade b c r)).mpr (h c r hresp)

theorem map_liveTerminus_iff (b : G.Being) :
    (G.map f).LiveTerminus b ↔ G.LiveTerminus b := by
  constructor
  · intro h
    exact ⟨(G.map_mountsSomewhere_iff f b).mp h.left,
      (G.map_terminus_iff f b).mp h.right⟩
  · intro h
    exact ⟨(G.map_mountsSomewhere_iff f b).mpr h.left,
      (G.map_terminus_iff f b).mpr h.right⟩

theorem map_responsiveTerminus_iff (b : G.Being) :
    (G.map f).ResponsiveTerminus b ↔ G.ResponsiveTerminus b := by
  constructor
  · intro h
    exact ⟨(G.map_respondsToEveryCall_iff f b).mp h.left,
      (G.map_terminus_iff f b).mp h.right⟩
  · intro h
    exact ⟨(G.map_respondsToEveryCall_iff f b).mpr h.left,
      (G.map_terminus_iff f b).mpr h.right⟩

theorem map_atPoleClass_iff (b : G.Being) :
    (G.map f).AtPoleClass b ↔ G.AtPoleClass b := by
  constructor
  · intro h
    exact h.elim
      (fun hstone => Or.inl ((G.map_stone_iff f b).mp hstone))
      (fun hterm => Or.inr ((G.map_terminus_iff f b).mp hterm))
  · intro h
    exact h.elim
      (fun hstone => Or.inl ((G.map_stone_iff f b).mpr hstone))
      (fun hterm => Or.inr ((G.map_terminus_iff f b).mpr hterm))

theorem map_hasSelfPoleIndex_iff (w : G.Weld) :
    (G.map f).HasSelfPoleIndex w ↔ G.HasSelfPoleIndex w := by
  constructor
  · intro h hbot
    exact h ((f.atBot_iff (G.share w)).mpr hbot)
  · intro h hbot
    exact h ((f.atBot_iff (G.share w)).mp hbot)

@[simp]
theorem map_waaMismatchGrade (w : G.Weld) :
    (G.map f).WaaMismatchGrade w = f.toFun (G.WaaMismatchGrade w) :=
  rfl

theorem map_waaMismatchLive_iff (w : G.Weld) :
    (G.map f).WaaMismatchLive w ↔ G.WaaMismatchLive w := by
  constructor
  · intro h
    exact ⟨(G.map_actual_iff f w).mp h.left,
      (G.map_hasSelfPoleIndex_iff f w).mp h.right⟩
  · intro h
    exact ⟨(G.map_actual_iff f w).mpr h.left,
      (G.map_hasSelfPoleIndex_iff f w).mpr h.right⟩

theorem map_probeConstant_iff (b : G.Being) (cs : G.Call → Prop) :
    (G.map f).ProbeConstant b cs ↔ G.ProbeConstant b cs := by
  constructor
  · intro h c₁ c₂ hc₁ hc₂ r₁ r₂ hr₁ hr₂
    exact (f.orderEq_iff (G.grade b c₁ r₁) (G.grade b c₂ r₂)).mp
      (h c₁ c₂ hc₁ hc₂ r₁ r₂ hr₁ hr₂)
  · intro h c₁ c₂ hc₁ hc₂ r₁ r₂ hr₁ hr₂
    exact (f.orderEq_iff (G.grade b c₁ r₁) (G.grade b c₂ r₂)).mpr
      (h c₁ c₂ hc₁ hc₂ r₁ r₂ hr₁ hr₂)

theorem map_waaBullSeven_iff (b : G.Being) :
    (G.map f).WaaBullSeven b ↔ G.WaaBullSeven b := by
  constructor
  · rintro ⟨hprobe, w, hactual, hagent, hidx⟩
    exact ⟨(G.map_probeConstant_iff f b (fun _ => True)).mp hprobe,
      ⟨w, (G.map_actual_iff f w).mp hactual, hagent,
        (G.map_hasSelfPoleIndex_iff f w).mp hidx⟩⟩
  · rintro ⟨hprobe, w, hactual, hagent, hidx⟩
    exact ⟨(G.map_probeConstant_iff f b (fun _ => True)).mpr hprobe,
      ⟨w, (G.map_actual_iff f w).mpr hactual, hagent,
        (G.map_hasSelfPoleIndex_iff f w).mpr hidx⟩⟩

namespace DirectedConvention
namespace BeingConvention
namespace BeingCoarsening

variable {G : Grid Contrib} {Macro : Type}

/-- Transport a diagnosis-time being coarsening across a display
    reparameterization. The fine tags are unchanged; only Row-2 display
    values move. -/
def displayMap (κ : BeingCoarsening G Macro)
    (f : DisplayReparam Contrib Contrib') :
    BeingCoarsening (G.map f) Macro where
  proj := κ.proj

theorem map_inFiber_iff (κ : BeingCoarsening G Macro)
    (f : DisplayReparam Contrib Contrib') (b : Macro) (w : G.Weld) :
    (displayMap κ f).InFiber b w ↔ κ.InFiber b w :=
  Iff.rfl

theorem map_sameFiber_iff
    (κ : BeingCoarsening G Macro) (f : DisplayReparam Contrib Contrib')
    (p q : G.Being) :
    (displayMap κ f).SameFiber p q ↔ κ.SameFiber p q :=
  Iff.rfl

theorem map_fiberInhabited_iff
    (κ : BeingCoarsening G Macro) (f : DisplayReparam Contrib Contrib')
    (b : Macro) :
    (displayMap κ f).FiberInhabited b ↔ κ.FiberInhabited b :=
  Iff.rfl

theorem map_actualFiberInhabited_iff
    (κ : BeingCoarsening G Macro) (f : DisplayReparam Contrib Contrib')
    (b : Macro) :
    (displayMap κ f).ActualFiberInhabited b ↔ κ.ActualFiberInhabited b := by
  constructor
  · rintro ⟨w, hactual, hfiber⟩
    exact ⟨w, (G.map_actual_iff f w).mp hactual, hfiber⟩
  · rintro ⟨w, hactual, hfiber⟩
    exact ⟨w, (G.map_actual_iff f w).mpr hactual, hfiber⟩

theorem map_sentientTag_iff
    (κ : BeingCoarsening G Macro) (f : DisplayReparam Contrib Contrib')
    (b : Macro) :
    (displayMap κ f).SentientTag b ↔ κ.SentientTag b := by
  constructor
  · rintro ⟨p, hp, hmounts⟩
    exact ⟨p, hp, (G.map_mountsSomewhere_iff f p).mp hmounts⟩
  · rintro ⟨p, hp, hmounts⟩
    exact ⟨p, hp, (G.map_mountsSomewhere_iff f p).mpr hmounts⟩

theorem map_fiberAtPole_iff
    (κ : BeingCoarsening G Macro) (f : DisplayReparam Contrib Contrib')
    (b : Macro) :
    (displayMap κ f).FiberAtPole b ↔ κ.FiberAtPole b := by
  constructor
  · intro h w hactual hfiber
    have hmapped : AtBot (f.toFun (G.share w)) := by
      simpa [Grid.map_share] using
        h w ((G.map_actual_iff f w).mpr hactual) hfiber
    exact (f.atBot_iff (G.share w)).mp hmapped
  · intro h w hactual hfiber
    have horig : AtBot (G.share w) :=
      h w ((G.map_actual_iff f w).mp hactual) hfiber
    have hmapped : AtBot (f.toFun (G.share w)) :=
      (f.atBot_iff (G.share w)).mpr horig
    simpa [Grid.map_share] using hmapped

theorem map_actualFiberInhabitedOn_iff
    (κ : BeingCoarsening G Macro) (f : DisplayReparam Contrib Contrib')
    (b : Macro) (cs : G.Call → Prop) :
    (displayMap κ f).ActualFiberInhabitedOn b cs ↔
      κ.ActualFiberInhabitedOn b cs := by
  constructor
  · rintro ⟨w, hactual, hfiber, hclass⟩
    exact ⟨w, (G.map_actual_iff f w).mp hactual, hfiber, hclass⟩
  · rintro ⟨w, hactual, hfiber, hclass⟩
    exact ⟨w, (G.map_actual_iff f w).mpr hactual, hfiber, hclass⟩

theorem map_actualFiberInhabitedWithin_iff
    (κ : BeingCoarsening G Macro) (f : DisplayReparam Contrib Contrib')
    (b : Macro) (ts : G.Being → Prop) :
    (displayMap κ f).ActualFiberInhabitedWithin b ts ↔
      κ.ActualFiberInhabitedWithin b ts := by
  constructor
  · rintro ⟨w, hactual, hfiber, htag⟩
    exact ⟨w, (G.map_actual_iff f w).mp hactual, hfiber, htag⟩
  · rintro ⟨w, hactual, hfiber, htag⟩
    exact ⟨w, (G.map_actual_iff f w).mpr hactual, hfiber, htag⟩

theorem map_fiberAtPoleOn_iff
    (κ : BeingCoarsening G Macro) (f : DisplayReparam Contrib Contrib')
    (b : Macro) (cs : G.Call → Prop) :
    (displayMap κ f).FiberAtPoleOn b cs ↔ κ.FiberAtPoleOn b cs := by
  constructor
  · intro h w hactual hfiber hclass
    have hmapped : AtBot (f.toFun (G.share w)) := by
      simpa [Grid.map_share] using
        h w ((G.map_actual_iff f w).mpr hactual) hfiber hclass
    exact (f.atBot_iff (G.share w)).mp hmapped
  · intro h w hactual hfiber hclass
    have horig : AtBot (G.share w) :=
      h w ((G.map_actual_iff f w).mp hactual) hfiber hclass
    have hmapped : AtBot (f.toFun (G.share w)) :=
      (f.atBot_iff (G.share w)).mpr horig
    simpa [Grid.map_share] using hmapped

theorem map_fiberAtPoleOnWithin_iff
    (κ : BeingCoarsening G Macro) (f : DisplayReparam Contrib Contrib')
    (b : Macro) (cs : G.Call → Prop) (ts : G.Being → Prop) :
    (displayMap κ f).FiberAtPoleOnWithin b cs ts ↔
      κ.FiberAtPoleOnWithin b cs ts := by
  constructor
  · intro h w hactual hfiber hclass htag
    have hmapped : AtBot (f.toFun (G.share w)) := by
      simpa [Grid.map_share] using
        h w ((G.map_actual_iff f w).mpr hactual) hfiber hclass htag
    exact (f.atBot_iff (G.share w)).mp hmapped
  · intro h w hactual hfiber hclass htag
    have horig : AtBot (G.share w) :=
      h w ((G.map_actual_iff f w).mp hactual) hfiber hclass htag
    have hmapped : AtBot (f.toFun (G.share w)) :=
      (f.atBot_iff (G.share w)).mpr horig
    simpa [Grid.map_share] using hmapped

theorem map_fiberAtPoleWithin_iff
    (κ : BeingCoarsening G Macro) (f : DisplayReparam Contrib Contrib')
    (b : Macro) (ts : G.Being → Prop) :
    (displayMap κ f).FiberAtPoleWithin b ts ↔
      κ.FiberAtPoleWithin b ts :=
  map_fiberAtPoleOnWithin_iff κ f b (fun _ => True) ts

theorem map_liveFiberAtPoleOn_iff
    (κ : BeingCoarsening G Macro) (f : DisplayReparam Contrib Contrib')
    (b : Macro) (cs : G.Call → Prop) :
    (displayMap κ f).LiveFiberAtPoleOn b cs ↔
      κ.LiveFiberAtPoleOn b cs := by
  constructor
  · intro h
    exact ⟨(map_actualFiberInhabitedOn_iff κ f b cs).mp h.left,
      (map_fiberAtPoleOn_iff κ f b cs).mp h.right⟩
  · intro h
    exact ⟨(map_actualFiberInhabitedOn_iff κ f b cs).mpr h.left,
      (map_fiberAtPoleOn_iff κ f b cs).mpr h.right⟩

theorem map_liveFiberAtPoleWithin_iff
    (κ : BeingCoarsening G Macro) (f : DisplayReparam Contrib Contrib')
    (b : Macro) (ts : G.Being → Prop) :
    (displayMap κ f).LiveFiberAtPoleWithin b ts ↔
      κ.LiveFiberAtPoleWithin b ts := by
  constructor
  · intro h
    exact ⟨(map_actualFiberInhabitedWithin_iff κ f b ts).mp h.left,
      (map_fiberAtPoleWithin_iff κ f b ts).mp h.right⟩
  · intro h
    exact ⟨(map_actualFiberInhabitedWithin_iff κ f b ts).mpr h.left,
      (map_fiberAtPoleWithin_iff κ f b ts).mpr h.right⟩

theorem map_liveFiberAtPole_iff
    (κ : BeingCoarsening G Macro) (f : DisplayReparam Contrib Contrib')
    (b : Macro) :
    (displayMap κ f).LiveFiberAtPole b ↔ κ.LiveFiberAtPole b := by
  constructor
  · intro h
    exact ⟨(map_actualFiberInhabited_iff κ f b).mp h.left,
      (map_fiberAtPole_iff κ f b).mp h.right⟩
  · intro h
    exact ⟨(map_actualFiberInhabited_iff κ f b).mpr h.left,
      (map_fiberAtPole_iff κ f b).mpr h.right⟩

theorem map_selfAptTag_iff
    (κ : BeingCoarsening G Macro) (f : DisplayReparam Contrib Contrib')
    (b : Macro) :
    (displayMap κ f).SelfAptTag b ↔ κ.SelfAptTag b := by
  constructor
  · intro h w hactual hfiber
    have hidx : (G.map f).HasSelfPoleIndex w :=
      h w ((G.map_actual_iff f w).mpr hactual) hfiber
    exact (G.map_hasSelfPoleIndex_iff f w).mp hidx
  · intro h w hactual hfiber
    have hidx : G.HasSelfPoleIndex w :=
      h w ((G.map_actual_iff f w).mp hactual) hfiber
    exact (G.map_hasSelfPoleIndex_iff f w).mpr hidx

theorem map_selfAptTagWithin_iff
    (κ : BeingCoarsening G Macro) (f : DisplayReparam Contrib Contrib')
    (b : Macro) (ts : G.Being → Prop) :
    (displayMap κ f).SelfAptTagWithin b ts ↔
      κ.SelfAptTagWithin b ts := by
  constructor
  · intro h w hactual hfiber htag
    have hidx : (G.map f).HasSelfPoleIndex w :=
      h w ((G.map_actual_iff f w).mpr hactual) hfiber htag
    exact (G.map_hasSelfPoleIndex_iff f w).mp hidx
  · intro h w hactual hfiber htag
    have hidx : G.HasSelfPoleIndex w :=
      h w ((G.map_actual_iff f w).mp hactual) hfiber htag
    exact (G.map_hasSelfPoleIndex_iff f w).mpr hidx

theorem map_liveSelfAptTag_iff
    (κ : BeingCoarsening G Macro) (f : DisplayReparam Contrib Contrib')
    (b : Macro) :
    (displayMap κ f).LiveSelfAptTag b ↔ κ.LiveSelfAptTag b := by
  constructor
  · intro h
    exact ⟨(map_actualFiberInhabited_iff κ f b).mp h.left,
      (map_selfAptTag_iff κ f b).mp h.right⟩
  · intro h
    exact ⟨(map_actualFiberInhabited_iff κ f b).mpr h.left,
      (map_selfAptTag_iff κ f b).mpr h.right⟩

theorem map_patchy_iff
    (κ : BeingCoarsening G Macro) (f : DisplayReparam Contrib Contrib')
    (b : Macro) :
    (displayMap κ f).Patchy b ↔ κ.Patchy b := by
  constructor
  · intro h
    exact ⟨fun hpole => h.left
        ((map_fiberAtPole_iff κ f b).mpr hpole),
      fun hself => h.right
        ((map_selfAptTag_iff κ f b).mpr hself)⟩
  · intro h
    exact ⟨fun hpole => h.left
        ((map_fiberAtPole_iff κ f b).mp hpole),
      fun hself => h.right
        ((map_selfAptTag_iff κ f b).mp hself)⟩

theorem map_selfConditioningTag_iff
    (κ : BeingCoarsening G Macro) (f : DisplayReparam Contrib Contrib')
    (b : Macro) :
    (displayMap κ f).SelfConditioningTag b ↔ κ.SelfConditioningTag b := by
  constructor
  · rintro ⟨deed, reception, hdeed, hreception, hactual, hdel⟩
    exact ⟨deed, reception, hdeed, hreception,
      (G.map_actual_iff f reception).mp hactual,
      (DirectedConvention.map_deliveredTo_iff G f deed reception).mp hdel⟩
  · rintro ⟨deed, reception, hdeed, hreception, hactual, hdel⟩
    exact ⟨deed, reception, hdeed, hreception,
      (G.map_actual_iff f reception).mpr hactual,
      (DirectedConvention.map_deliveredTo_iff G f deed reception).mpr hdel⟩

theorem map_strongSelfConditioningTag_iff
    (κ : BeingCoarsening G Macro) (f : DisplayReparam Contrib Contrib')
    (b : Macro) :
    (displayMap κ f).StrongSelfConditioningTag b ↔ κ.StrongSelfConditioningTag b := by
  constructor
  · intro h reception hfiber hactual
    rcases h reception hfiber ((G.map_actual_iff f reception).mpr hactual) with
      ⟨deed, hdeed, hdel⟩
    exact ⟨deed, hdeed,
      (DirectedConvention.map_deliveredTo_iff G f deed reception).mp hdel⟩
  · intro h reception hfiber hactual
    rcases h reception hfiber ((G.map_actual_iff f reception).mp hactual) with
      ⟨deed, hdeed, hdel⟩
    exact ⟨deed, hdeed,
      (DirectedConvention.map_deliveredTo_iff G f deed reception).mpr hdel⟩

end BeingCoarsening
end BeingConvention
end DirectedConvention

theorem map_waaBullTen_iff {Macro : Type}
    (κ : DirectedConvention.BeingConvention.BeingCoarsening G Macro)
    (b : G.Being) :
    (G.map f).WaaBullTen (κ.displayMap f) b ↔ G.WaaBullTen κ b := by
  constructor
  · intro h
    refine ⟨(G.map_responsiveTerminus_iff f b).mp h.left, ?_⟩
    rcases h.right with
      ⟨deed, reception, hdeed, hactual, hnotSame, hsentient, hdel⟩
    exact ⟨deed, reception,
      (DirectedConvention.BeingConvention.BeingCoarsening.map_inFiber_iff
        κ f (κ.proj b) deed).mp hdeed,
      (G.map_actual_iff f reception).mp hactual,
      (fun hsame =>
        hnotSame
          ((DirectedConvention.BeingConvention.BeingCoarsening.map_sameFiber_iff
            κ f deed.agent reception.agent).mpr hsame)),
      (DirectedConvention.BeingConvention.BeingCoarsening.map_sentientTag_iff
        κ f (κ.proj reception.agent)).mp hsentient,
      (DirectedConvention.map_deliveredTo_iff G f deed reception).mp hdel⟩
  · intro h
    refine ⟨(G.map_responsiveTerminus_iff f b).mpr h.left, ?_⟩
    rcases h.right with
      ⟨deed, reception, hdeed, hactual, hnotSame, hsentient, hdel⟩
    exact ⟨deed, reception,
      (DirectedConvention.BeingConvention.BeingCoarsening.map_inFiber_iff
        κ f (κ.proj b) deed).mpr hdeed,
      (G.map_actual_iff f reception).mpr hactual,
      (fun hsame =>
        hnotSame
          ((DirectedConvention.BeingConvention.BeingCoarsening.map_sameFiber_iff
            κ f deed.agent reception.agent).mp hsame)),
      (DirectedConvention.BeingConvention.BeingCoarsening.map_sentientTag_iff
        κ f (κ.proj reception.agent)).mpr hsentient,
      (DirectedConvention.map_deliveredTo_iff G f deed reception).mpr hdel⟩

theorem map_stateToolFits_iff (w : G.Weld) :
    (G.map f).StateToolFits w ↔ G.StateToolFits w := by
  constructor
  · intro h hidx
    exact h ((G.map_hasSelfPoleIndex_iff f w).mpr hidx)
  · intro h hidx
    exact h ((G.map_hasSelfPoleIndex_iff f w).mp hidx)

namespace Tier

/-- Transport a diagnostic tier along a grid reparameterization. -/
def map {G : Grid Contrib} (f : DisplayReparam Contrib Contrib') :
    Tier G → Tier (G.map f)
  | .floor => .floor
  | .actTime w => .actTime w

end Tier

theorem map_tier_hasLiveShare_iff :
    ∀ t : Tier G,
      Tier.hasLiveShare (G.map f) (Tier.map f t) ↔
        Tier.hasLiveShare G t
  | .floor => Iff.rfl
  | .actTime w => G.map_hasSelfPoleIndex_iff f w

theorem map_exists_liveTier_iff :
    (∃ t : Tier (G.map f), Tier.hasLiveShare (G.map f) t) ↔
      ∃ t : Tier G, Tier.hasLiveShare G t := by
  constructor
  · rintro ⟨t, ht⟩
    cases t with
    | floor =>
        cases ht
    | actTime w =>
        exact ⟨Tier.actTime w, (G.map_hasSelfPoleIndex_iff f w).mp ht⟩
  · rintro ⟨t, ht⟩
    exact ⟨Tier.map f t, (G.map_tier_hasLiveShare_iff f t).mpr ht⟩

theorem map_rePitch (before : Config Contrib) (received : G.Weld) :
    (G.map f).rePitch (before.map f) received =
      (G.rePitch before received).map f :=
  rfl

theorem map_isShareDrop_iff
    (before : Config Contrib) (received : G.Weld) :
    (G.map f).IsShareDrop (before.map f) received ↔
      G.IsShareDrop before received := by
  constructor
  · intro h
    exact ⟨(f.le_iff (G.share received) before.tendency).mpr h.left,
      fun hle => h.right ((f.le_iff before.tendency (G.share received)).mp hle)⟩
  · intro h
    exact ⟨(f.le_iff (G.share received) before.tendency).mp h.left,
      fun hle => h.right ((f.le_iff before.tendency (G.share received)).mpr hle)⟩

theorem map_shareDropRun
    {before : Config Contrib} {run : List G.Weld}
    (h : G.ShareDropRun before run) :
    (G.map f).ShareDropRun (before.map f) run := by
  induction h with
  | nil before =>
      exact ShareDropRun.nil (before.map f)
  | cons hactual hdrop _hrest ih =>
      exact ShareDropRun.cons
        ((G.map_actual_iff f _).mpr hactual)
        ((G.map_isShareDrop_iff f _ _).mpr hdrop)
        (by simpa [Grid.map_rePitch] using ih)

/-- Transport a Bull-ascent run across a display reparameterization. -/
def map_bullAscent (a : G.BullAscent) :
    (G.map f).BullAscent where
  before := a.before.map f
  run    := a.run
  drops  := G.map_shareDropRun f a.drops

namespace DirectedConvention

theorem map_landsWithShareDrop_iff
    (before : Config Contrib) (deed reception : G.Weld) :
    LandsWithShareDrop (G.map f) (before.map f) deed reception ↔
      LandsWithShareDrop G before deed reception := by
  constructor
  · intro h
    exact ⟨(map_landsAt_iff G f deed reception).mp h.left,
      (G.map_isShareDrop_iff f before reception).mp h.right⟩
  · intro h
    exact ⟨(map_landsAt_iff G f deed reception).mpr h.left,
      (G.map_isShareDrop_iff f before reception).mpr h.right⟩

theorem map_hasShareDropLanding_iff
    (before : Config Contrib) (deed : G.Weld) :
    HasShareDropLanding (G.map f) (before.map f) deed ↔
      HasShareDropLanding G before deed := by
  constructor
  · rintro ⟨reception, hland⟩
    exact ⟨reception, (map_landsWithShareDrop_iff G f before deed reception).mp hland⟩
  · rintro ⟨reception, hland⟩
    exact ⟨reception, (map_landsWithShareDrop_iff G f before deed reception).mpr hland⟩

theorem map_shareDropLine_iff
    (before : Config Contrib) (b : G.Being) (deed reception : G.Weld) :
    ShareDropLine (G.map f) (before.map f) b deed reception ↔
      ShareDropLine G before b deed reception := by
  constructor
  · intro h
    exact ⟨(map_environsLine_iff G f b deed reception).mp h.left,
      (G.map_isShareDrop_iff f before reception).mp h.right⟩
  · intro h
    exact ⟨(map_environsLine_iff G f b deed reception).mpr h.left,
      (G.map_isShareDrop_iff f before reception).mpr h.right⟩

theorem map_shortfallClosedAt_iff
    (before : Config Contrib) (deed reception : G.Weld) :
    ShortfallClosedAt (G.map f) (before.map f) deed reception ↔
      ShortfallClosedAt G before deed reception := by
  constructor
  · intro h hlive hdel
    have hmappedLive : ¬ AtBot (f.toFun before.tendency) := by
      intro hbot
      exact hlive ((f.atBot_iff before.tendency).mp hbot)
    have hlanding :=
      h hmappedLive ((map_deliveredTo_iff G f deed reception).mpr hdel)
    exact (map_hasShareDropLanding_iff G f before deed).mp hlanding
  · intro h hlive hdel
    have horigLive : ¬ AtBot before.tendency := by
      intro hbot
      exact hlive ((f.atBot_iff before.tendency).mpr hbot)
    have hlanding :=
      h horigLive ((map_deliveredTo_iff G f deed reception).mp hdel)
    exact (map_hasShareDropLanding_iff G f before deed).mpr hlanding

theorem map_waaFullyEnlightened_reflect
    {b : G.Being} (h : WaaFullyEnlightened (G.map f) b) :
    WaaFullyEnlightened G b := by
  constructor
  · exact (G.map_responsiveTerminus_iff f b).mp h.left
  · intro before deed reception hdeed
    exact (map_shortfallClosedAt_iff G f before deed reception).mp
      (h.right (before.map f) deed reception hdeed)

/-- Preservation of the universally quantified faith closure needs the target
    display carrier to be covered by the reparameterization. -/
theorem map_waaFullyEnlightened_of_surjective
    (hsurj : ∀ b' : Contrib', ∃ a : Contrib, f.toFun a = b')
    {b : G.Being} (h : WaaFullyEnlightened G b) :
    WaaFullyEnlightened (G.map f) b := by
  constructor
  · exact (G.map_responsiveTerminus_iff f b).mpr h.left
  · intro before' deed reception hdeed
    cases before' with
    | mk tendency =>
        rcases hsurj tendency with ⟨a, ha⟩
        let before : Config Contrib := { tendency := a }
        intro hlive hdel
        have horigLive : ¬ AtBot before.tendency := by
          intro hbot
          apply hlive
          have hmapped : AtBot (f.toFun a) :=
            (f.atBot_iff a).mpr hbot
          simpa [before, ha] using hmapped
        have horigDel : DeliveredTo G deed reception :=
          (map_deliveredTo_iff G f deed reception).mp hdel
        have hlanding :=
          h.right before deed reception hdeed horigLive horigDel
        have hmapped :=
          (map_hasShareDropLanding_iff G f before deed).mpr hlanding
        simpa [Config.map, before, ha] using hmapped

/-- Transport of a path claim: reparameterize the stored configuration; the
    welds are carried unchanged. -/
def WaaPathClaim.map (c : WaaPathClaim G) : WaaPathClaim (G.map f) :=
  { before := c.before.map f
    deed := c.deed
    reception := c.reception }

/-- Truth of a path claim is display-invariant. The language ignores the tier,
    so the tiers on the two sides are unconstrained. -/
theorem map_waaPathClaim_holds_iff
    (t' : Tier (G.map f)) (t : Tier G) (c : WaaPathClaim G) :
    (waaPathClaimLanguage (G.map f)).Holds t' (WaaPathClaim.map G f c) ↔
      (waaPathClaimLanguage G).Holds t c := by
  simpa [waaPathClaimLanguage, WaaPathClaim.map] using
    (map_shortfallClosedAt_iff G f c.before c.deed c.reception)

/-- With target-carrier coverage, full enlightenment is display-invariant
    outright. -/
theorem map_waaFullyEnlightened_iff
    (hsurj : ∀ b' : Contrib', ∃ a : Contrib, f.toFun a = b')
    (b : G.Being) :
    WaaFullyEnlightened (G.map f) b ↔ WaaFullyEnlightened G b :=
  ⟨fun h => map_waaFullyEnlightened_reflect G f h,
    fun h => map_waaFullyEnlightened_of_surjective G f hsurj h⟩

/-- Faith has no monotonicity or congruence law. Under coverage, the mapped
    faith-object is propositionally the same object, so transport goes through
    propositional extensionality. -/
theorem map_faith_object_eq
    (hsurj : ∀ b' : Contrib', ∃ a : Contrib, f.toFun a = b')
    (Faith : Prop → Prop) (b : G.Being) :
    Faith (WaaFullyEnlightened (G.map f) b) =
      Faith (WaaFullyEnlightened G b) := by
  rw [propext (map_waaFullyEnlightened_iff G f hsurj b)]

/-- Reflection of the faith principle across a covering display
    reparameterization, for the path-claim language. -/
theorem map_waaFaithPrinciple_reflect
    (hsurj : ∀ b' : Contrib', ∃ a : Contrib, f.toFun a = b')
    {Faith : Prop → Prop}
    (h : WaaFaithPrinciple (G.map f) (waaPathClaimLanguage (G.map f)) Faith) :
    WaaFaithPrinciple G (waaPathClaimLanguage G) Faith := by
  intro b hfaith u hutter
  have hfaith' : Faith (WaaFullyEnlightened (G.map f) b) := by
    rw [map_faith_object_eq G f hsurj Faith b]
    exact hfaith
  let u' : RecordedUtterance (G.map f) (waaPathClaimLanguage (G.map f)) :=
    { weld := u.weld
      actual := u.actual
      offeredAt := Tier.floor
      content := WaaPathClaim.map G f u.content }
  have hfit' : u'.FitsOfferedTier :=
    h b hfaith' u' hutter
  change (waaPathClaimLanguage G).TrueAt u.offeredAt u.content
  have hholds :
      (waaPathClaimLanguage G).Holds u.offeredAt u.content :=
    (map_waaPathClaim_holds_iff G f u'.offeredAt u.offeredAt
      u.content).mp (by
        change (waaPathClaimLanguage (G.map f)).TrueAt u'.offeredAt
          u'.content at hfit'
        simpa [ClaimLanguage.TrueAt, u'] using hfit')
  simpa [ClaimLanguage.TrueAt] using hholds

theorem map_waaAversionContext_iff
    (before : Config Contrib) (reception : G.Weld) :
    WaaAversionContext (G.map f) (before.map f) reception ↔
      WaaAversionContext G before reception := by
  constructor
  · intro h
    refine
      { liveBefore := ?_
        mismatchLive := ?_ }
    · intro hbot
      exact h.liveBefore ((f.atBot_iff before.tendency).mpr hbot)
    · exact (G.map_waaMismatchLive_iff f reception).mp h.mismatchLive
  · intro h
    refine
      { liveBefore := ?_
        mismatchLive := ?_ }
    · intro hbot
      exact h.liveBefore ((f.atBot_iff before.tendency).mp hbot)
    · exact (G.map_waaMismatchLive_iff f reception).mpr h.mismatchLive

end DirectedConvention

namespace DirectedConvention
namespace BeingConvention
namespace GridConvention

theorem map_rowOf_obeys
    [∀ w : (G.map f).Weld, Decidable (AtBot ((G.map f).share w))]
    (r : RowTag) :
    (rowOf (G.map f) r).ObeysSeparateFuse :=
  rowOf_obeys (G.map f) r

theorem map_layerRow_obeys
    [∀ w : (G.map f).Weld, Decidable (AtBot ((G.map f).share w))]
    (l : ConventionLayer) :
    (layerRow (G.map f) l).ObeysSeparateFuse :=
  map_rowOf_obeys G f (.layer l)

theorem map_weldRow_obeys
    [∀ w : (G.map f).Weld, Decidable (AtBot ((G.map f).share w))] :
    (weldRow (G.map f)).ObeysSeparateFuse :=
  map_rowOf_obeys G f (.layer .weldGrain)

theorem map_contentBeforeAfterRow_obeys_of_direction
    (h : ∃ a b : Contrib, Strict a b) :
    (contentBeforeAfterRow (G.map f)).ObeysSeparateFuse :=
  contentBeforeAfterRow_obeys_of_direction (G.map f) (f.exists_strict_map h)

theorem map_contentBeingsRow_obeys_of_being
    (h : ∃ b : G.Being, ¬ G.Stone b) :
    (contentBeingsRow (G.map f)).ObeysSeparateFuse := by
  apply contentBeingsRow_obeys_of_being
  rcases h with ⟨b, hnotStone⟩
  exact ⟨b, fun hstone => hnotStone ((G.map_stone_iff f b).mp hstone)⟩

theorem map_contentGridLensRow_obeys_of_liveTier
    (h : ∃ t : Tier G, Tier.hasLiveShare G t) :
    (contentGridLensRow (G.map f)).ObeysSeparateFuse :=
  contentGridLensRow_obeys_of_liveTier (G.map f)
    ((G.map_exists_liveTier_iff f).mpr h)

theorem map_contentWeldRow_obeys_of_actual
    (h : ∃ w : G.Weld, G.Actual w) :
    (contentWeldRow (G.map f)).ObeysSeparateFuse :=
  contentWeldRow_obeys_of_actual (G.map f)
    ((G.map_exists_actual_iff f).mpr h)

theorem map_beingsLadder_obeys
    [∀ w : (G.map f).Weld, Decidable (AtBot ((G.map f).share w))] :
    ∀ n, (beingsLadder (G.map f) n).ObeysSeparateFuse :=
  beingsLadder_obeys (G.map f)

theorem map_beingsLadder_obeys_succ :
    ∀ n, (beingsLadder (G.map f) (n + 1)).ObeysSeparateFuse :=
  beingsLadder_obeys_succ (G.map f)

theorem map_weldLadder_obeys
    [∀ w : (G.map f).Weld, Decidable (AtBot ((G.map f).share w))] :
    ∀ n, (weldLadder (G.map f) n).ObeysSeparateFuse :=
  weldLadder_obeys (G.map f)

theorem map_weldLadder_obeys_succ :
    ∀ n, (weldLadder (G.map f) (n + 1)).ObeysSeparateFuse :=
  weldLadder_obeys_succ (G.map f)

theorem map_weldLadder_no_level_final :
    ∀ n, ¬ (weldLadder (G.map f) n).Freeze :=
  weldLadder_no_level_final (G.map f)

end GridConvention
end BeingConvention
end DirectedConvention

end Grid

end WAA
