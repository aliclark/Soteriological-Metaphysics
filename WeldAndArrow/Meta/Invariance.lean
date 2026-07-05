/-
================================================================================
  WeldAndArrow.Meta.Invariance
  Display reparameterization and recovery countermodels
================================================================================

This module transports grid predicates across display reparameterizations and
records small countermodels for equality-at-bottom, direction recovery, and
partition recovery.

Reading and motivation: Identification/Commentary.lean, C.3.
-/

import WeldAndArrow.Identification
import WeldAndArrow.Doctrines.Sraddha

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

theorem map_beingsLadder_obeys
    [∀ w : (G.map f).Weld, Decidable (AtBot ((G.map f).share w))] :
    ∀ n, (beingsLadder (G.map f) n).ObeysSeparateFuse :=
  beingsLadder_obeys (G.map f)

theorem map_beingsLadder_obeys_succ :
    ∀ n, (beingsLadder (G.map f) (n + 1)).ObeysSeparateFuse :=
  beingsLadder_obeys_succ (G.map f)

end GridConvention
end BeingConvention
end DirectedConvention

/- --------------------------------------------------------------------------
   Direction-smuggling detector: reverse only `conditions`
-------------------------------------------------------------------------- -/

/-- Reverse the argument order of `conditions`, leaving every other part of the
    grid untouched. Direction-neutral facts should transport across this;
    delivery-facing facts should either reverse or declare the model-side
    asymmetry hypothesis they need. -/
def transpose (G : Grid Contrib) : Grid Contrib where
  Being      := G.Being
  Call       := G.Call
  Response   := G.Response
  respondsTo := G.respondsTo
  grade      := G.grade
  conditions := fun w₁ w₂ => G.conditions w₂ w₁

theorem transpose_conditions (w₁ w₂ : G.Weld) :
    G.transpose.conditions w₁ w₂ = G.conditions w₂ w₁ :=
  rfl

theorem transpose_conditionsEither_iff (w₁ w₂ : G.Weld) :
    G.transpose.ConditionsEither w₁ w₂ ↔ G.ConditionsEither w₁ w₂ :=
  ⟨fun h => h.elim Or.inr Or.inl,
   fun h => h.elim Or.inr Or.inl⟩

namespace DirectedConvention

theorem transpose_deliveredTo_iff (deed reception : G.Weld) :
    DeliveredTo G.transpose deed reception ↔ DeliveredTo G reception deed :=
  Iff.rfl

namespace BeingConvention
namespace BeingCoarsening

variable {Macro : Type}

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
    (κ : BeingCoarsening G Macro) (b : Macro) :
    κ.transpose.SentientTag b ↔ κ.SentientTag b :=
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
end BeingConvention

end DirectedConvention

end Grid

/- ==============================================================================
   Negative example: equality-at-bottom does not transport
============================================================================== -/

namespace InvarianceNegative

inductive TwoBottom
  | chosen
  | other

instance : PreorderBot TwoBottom where
  le       := fun _ _ => True
  le_refl  := fun _ => True.intro
  le_trans := fun _ _ => True.intro
  bot      := TwoBottom.chosen
  bot_le   := fun _ => True.intro

instance : PreorderBot Unit where
  le       := fun _ _ => True
  le_refl  := fun _ => True.intro
  le_trans := fun _ _ => True.intro
  bot      := ()
  bot_le   := fun _ => True.intro

def mergeToUnit : DisplayReparam TwoBottom Unit where
  toFun _ := ()
  le_iff _ _ := ⟨fun _ => True.intro, fun _ => True.intro⟩
  atBot_bot := True.intro

def twoBottomGrid : Grid TwoBottom where
  Being      := Unit
  Call       := Unit
  Response   := Unit
  respondsTo _ _ := some ()
  grade _ _ _ := TwoBottom.other
  conditions _ _ := False

/-- The old, equality-token version of terminus, kept only for this
    counterexample. It is not the system predicate. -/
def OldEqTerminus {Contrib : Type} [PreorderBot Contrib]
    (G : Grid Contrib) (b : G.Being) : Prop :=
  ∀ c r, G.respondsTo b c = some r → G.grade b c r = shareBot

theorem twoBottomGrid_terminus : twoBottomGrid.Terminus () :=
  fun _ _ _ => True.intro

theorem not_oldEqTerminus_twoBottomGrid : ¬ OldEqTerminus twoBottomGrid () := by
  intro h
  have hbad : TwoBottom.other = TwoBottom.chosen := h () () rfl
  cases hbad

theorem oldEqTerminus_map_mergeToUnit : OldEqTerminus (twoBottomGrid.map mergeToUnit) () :=
  fun _ _ _ => rfl

/-- The new predicate transports across the merge, while the old equality-token
    predicate would hold after the merge and fail before it. -/
theorem oldEqTerminus_not_invariant :
    ((twoBottomGrid.map mergeToUnit).Terminus () ↔ twoBottomGrid.Terminus ()) ∧
      OldEqTerminus (twoBottomGrid.map mergeToUnit) () ∧
      ¬ OldEqTerminus twoBottomGrid () :=
  ⟨twoBottomGrid.map_terminus_iff mergeToUnit (),
    fun _ _ _ => rfl,
    by
      intro h
      have hbad : TwoBottom.other = TwoBottom.chosen := h () () rfl
      cases hbad⟩

end InvarianceNegative

/- Reading and motivation: Identification/Commentary.lean, C.3. -/

namespace DirectionNegative

/-- One being, two calls, one response: a small carrier with two orientations. -/
abbrev W := RawWeld Unit Bool Unit

/-- The weld at the `false` call. -/
def wFalse : W := ⟨(), false, ()⟩

/-- The weld at the `true` call. -/
def wTrue : W := ⟨(), true, ()⟩

/-- The web read one way: the `false`-weld conditions the `true`-weld. -/
def forwardGrid : Grid Nat where
  Being      := Unit
  Call       := Bool
  Response   := Unit
  respondsTo _ _ := some ()
  grade _ _ _ := 0
  conditions w₁ w₂ := w₁.call = false ∧ w₂.call = true

/-- The same web read the other way: only `conditions` is reversed. -/
def backwardGrid : Grid Nat where
  Being      := Unit
  Call       := Bool
  Response   := Unit
  respondsTo _ _ := some ()
  grade _ _ _ := 0
  conditions w₁ w₂ := w₁.call = true ∧ w₂.call = false

/-- The two orientations agree on the symmetric closure at every pair. -/
theorem conditionsEither_agrees (w₁ w₂ : W) :
    forwardGrid.ConditionsEither w₁ w₂ ↔ backwardGrid.ConditionsEither w₁ w₂ :=
  ⟨fun h => h.elim (fun ⟨h1, h2⟩ => Or.inr ⟨h2, h1⟩)
                   (fun ⟨h1, h2⟩ => Or.inl ⟨h2, h1⟩),
   fun h => h.elim (fun ⟨h1, h2⟩ => Or.inr ⟨h2, h1⟩)
                   (fun ⟨h1, h2⟩ => Or.inl ⟨h2, h1⟩)⟩

/-- They disagree on `conditions` at the witness pair. -/
theorem conditions_disagree :
    forwardGrid.conditions wFalse wTrue ∧
      ¬ backwardGrid.conditions wFalse wTrue := by
  constructor
  · exact ⟨rfl, rfl⟩
  · intro h
    cases h.left

/- Reading and motivation: Identification/Commentary.lean, C.3. -/
theorem no_direction_recovery_from_conditionsEither :
    ¬ ∃ recover : (W → W → Prop) → (W → W → Prop),
        recover forwardGrid.ConditionsEither = forwardGrid.conditions ∧
        recover backwardGrid.ConditionsEither = backwardGrid.conditions := by
  rintro ⟨recover, hf, hb⟩
  have hsame : forwardGrid.ConditionsEither = backwardGrid.ConditionsEither := by
    funext w₁ w₂
    exact propext (conditionsEither_agrees w₁ w₂)
  have hcond : forwardGrid.conditions = backwardGrid.conditions := by
    rw [← hf, hsame, hb]
  exact conditions_disagree.right (hcond ▸ conditions_disagree.left)

/-- The equilibrium-pole face, on the existing negative carrier: where
    everything is order-equivalent, nothing is strict. -/
theorem not_strict_twoBottom (a b : InvarianceNegative.TwoBottom) : ¬ Strict a b :=
  no_strict_of_all_orderEq (fun _ _ => ⟨True.intro, True.intro⟩) a b

end DirectionNegative

/- ==============================================================================
   Content-row countermodels
============================================================================== -/

namespace ContentNegative

open Grid.DirectedConvention.BeingConvention.GridConvention

def allStoneGrid : Grid InvarianceNegative.TwoBottom where
  Being      := Unit
  Call       := Unit
  Response   := Unit
  respondsTo _ _ := none
  grade _ _ _ := InvarianceNegative.TwoBottom.chosen
  conditions _ _ := False

def allStoneWeld : allStoneGrid.Weld :=
  ⟨(), (), ()⟩

theorem allStoneGrid_allStone : allStoneGrid.AllStone := by
  intro _b _c hmount
  rcases hmount with ⟨_r, hr⟩
  cases hr

theorem allStoneGrid_no_liveTier (t : Grid.Tier allStoneGrid) :
    ¬ Grid.Tier.hasLiveShare allStoneGrid t := by
  cases t with
  | floor =>
      intro h
      exact h
  | actTime _ =>
      intro hidx
      exact hidx True.intro

theorem allStoneWeld_no_live_share :
    ¬ Grid.Tier.hasLiveShare allStoneGrid (Grid.Tier.actTime allStoneWeld) :=
  allStoneGrid_no_liveTier (Grid.Tier.actTime allStoneWeld)

theorem contentBeingsRow_not_fused_allStone :
    ¬ (contentBeingsRow allStoneGrid).Fused (Grid.Tier.actTime allStoneWeld) := by
  intro hfused
  have hiff := hfused allStoneWeld_no_live_share
  have hdenial :
      (contentLayerLanguage allStoneGrid).TrueAt
        (Grid.Tier.actTime allStoneWeld) (.layerDenied .beings) := by
    dsimp [contentLayerLanguage, Grid.ClaimLanguage.TrueAt]
    exact allStoneGrid_allStone
  exact allStoneWeld_no_live_share (hiff.mpr hdenial)

theorem contentBeingsRow_not_obeys_allStone :
    ¬ (contentBeingsRow allStoneGrid).ObeysSeparateFuse := by
  intro h
  exact contentBeingsRow_not_fused_allStone
    (allStoneGrid.fused_of_obeysSeparateFuse h (Grid.Tier.actTime allStoneWeld))

theorem contentGridLensRow_not_fused_noLive :
    ¬ (contentGridLensRow allStoneGrid).Fused (Grid.Tier.actTime allStoneWeld) := by
  intro hfused
  have hiff := hfused allStoneWeld_no_live_share
  have hdenial :
      (contentLayerLanguage allStoneGrid).TrueAt
        (Grid.Tier.actTime allStoneWeld) (.layerDenied .gridLens) := by
    dsimp [contentLayerLanguage, Grid.ClaimLanguage.TrueAt]
    exact allStoneGrid_no_liveTier
  exact allStoneWeld_no_live_share (hiff.mpr hdenial)

theorem contentGridLensRow_not_obeys_noLive :
    ¬ (contentGridLensRow allStoneGrid).ObeysSeparateFuse := by
  intro h
  exact contentGridLensRow_not_fused_noLive
    (allStoneGrid.fused_of_obeysSeparateFuse h (Grid.Tier.actTime allStoneWeld))

def twoBottomWeld : InvarianceNegative.twoBottomGrid.Weld :=
  ⟨(), (), ()⟩

theorem twoBottomGrid_directionVoid :
    DirectionVoid InvarianceNegative.TwoBottom :=
  DirectionNegative.not_strict_twoBottom

theorem twoBottomWeld_no_live_share :
    ¬ Grid.Tier.hasLiveShare InvarianceNegative.twoBottomGrid
        (Grid.Tier.actTime twoBottomWeld) := by
  intro hidx
  exact hidx True.intro

theorem contentBeforeAfterRow_not_fused_twoBottom :
    ¬ (contentBeforeAfterRow InvarianceNegative.twoBottomGrid).Fused
        (Grid.Tier.actTime twoBottomWeld) := by
  intro hfused
  have hiff := hfused twoBottomWeld_no_live_share
  have hdenial :
      (contentLayerLanguage InvarianceNegative.twoBottomGrid).TrueAt
        (Grid.Tier.actTime twoBottomWeld) (.layerDenied .directedTime) := by
    dsimp [contentLayerLanguage, Grid.ClaimLanguage.TrueAt]
    exact twoBottomGrid_directionVoid
  exact twoBottomWeld_no_live_share (hiff.mpr hdenial)

theorem contentBeforeAfterRow_not_obeys_twoBottom :
    ¬ (contentBeforeAfterRow InvarianceNegative.twoBottomGrid).ObeysSeparateFuse := by
  intro h
  exact contentBeforeAfterRow_not_fused_twoBottom
    (InvarianceNegative.twoBottomGrid.fused_of_obeysSeparateFuse h
      (Grid.Tier.actTime twoBottomWeld))

end ContentNegative

/- ==============================================================================
   Sraddha orthogonality countermodel
============================================================================== -/

namespace OrthogonalityNegative

open Grid.DirectedConvention

/-- The same zero-effectiveness witness used by `SraddhaNegative`: a responsive
    terminus whose delivered deed does not land as a share-drop for the live
    receiver context. -/
abbrev zeroEffectGrid : Grid Nat :=
  SraddhaNegative.zeroEffectGrid

theorem responsiveTerminus_with_no_shareDropLanding :
    zeroEffectGrid.ResponsiveTerminus SraddhaNegative.Being.sraddha ∧
      ¬ HasShareDropLanding zeroEffectGrid SraddhaNegative.liveBefore SraddhaNegative.deed :=
  ⟨SraddhaNegative.sraddha_responsiveTerminus,
    SraddhaNegative.not_hasShareDropLanding_liveBefore⟩

theorem terminus_not_waaFullyEnlightened :
    zeroEffectGrid.Terminus SraddhaNegative.Being.sraddha ∧
      ¬ WaaFullyEnlightened zeroEffectGrid SraddhaNegative.Being.sraddha :=
  ⟨SraddhaNegative.sraddha_responsiveTerminus.right,
    SraddhaNegative.not_waaFullyEnlightened⟩

/-- `WaaFullyEnlightened` is strictly stronger than terminus typing: it
    implies terminus, and this concrete responsive terminus still fails the
    shortfall-closure conjunct. -/
theorem waaFullyEnlightened_stronger_than_terminus :
    (WaaFullyEnlightened zeroEffectGrid SraddhaNegative.Being.sraddha →
        zeroEffectGrid.Terminus SraddhaNegative.Being.sraddha) ∧
      zeroEffectGrid.Terminus SraddhaNegative.Being.sraddha ∧
      ¬ WaaFullyEnlightened zeroEffectGrid SraddhaNegative.Being.sraddha := by
  constructor
  · intro h
    exact (responsiveTerminus_of_waaFullyEnlightened zeroEffectGrid h).right
  · exact terminus_not_waaFullyEnlightened

end OrthogonalityNegative

/- ==============================================================================
   §N  Being-boundary freedom: designation is not grid-carried

   The witness is parallel in scope to `DirectionNegative`. A single grid has
   two fact-identical fine tags and admits both a merge and a split coarsening.
   They disagree on the fiber boundary at a concrete pair. This certifies
   freedom, not failure: naming suffices, while holding one partition as floor
   furniture claims a fact the grid's data does not carry.
============================================================================== -/

namespace BeingNegative

open Grid.DirectedConvention.BeingConvention

/-- Two fine tags with the same response, same grade, and symmetric delivery. -/
def twoBeingGrid : Grid Nat where
  Being      := Bool
  Call       := Unit
  Response   := Unit
  respondsTo _ _ := some ()
  grade _ _ _ := 0
  conditions _ _ := True

/-- Merge coarsening: both fine tags are one macro tag. -/
def κmerge : BeingCoarsening twoBeingGrid Unit where
  proj _ := ()

/-- Split coarsening: each fine tag remains its own macro tag. -/
def κsplit : BeingCoarsening twoBeingGrid Bool where
  proj := id

theorem merge_same_fiber : κmerge.SameFiber false true :=
  rfl

theorem split_not_same_fiber : ¬ κsplit.SameFiber false true := by
  intro h
  cases h

/-- The grid data visible to a would-be partition-recovery function. -/
abbrev W := RawWeld Bool Unit Unit

abbrev GridData : Type :=
  (Bool → Unit → Option Unit) × (Bool → Unit → Unit → Nat) × (W → W → Prop)

def gridData : GridData :=
  (twoBeingGrid.respondsTo, twoBeingGrid.grade, twoBeingGrid.conditions)

def mergeBoundary (_p _q : Bool) : Prop := True

def splitBoundary (p q : Bool) : Prop := p = q

/-- No function of this grid's data recovers a unique partition: the same data
    supports both the merge and the split coarsenings, which disagree at
    `false` and `true`. -/
theorem no_partition_recovery :
    ¬ ∃ recover : GridData → Bool → Bool → Prop,
        recover gridData = mergeBoundary ∧
        recover gridData = splitBoundary := by
  rintro ⟨recover, hmerge, hsplit⟩
  have hmerged : recover gridData false true := by
    rw [hmerge]
    exact True.intro
  have hsplitNot : ¬ recover gridData false true := by
    rw [hsplit]
    intro h
    cases h
  exact hsplitNot hmerged

end BeingNegative

/- Reading and motivation: Identification/Commentary.lean, C.3. -/

namespace SelfLineWitness

inductive Being
  | one

inductive Call
  | call

inductive Response
  | response

def selfLineGrid : Grid Nat where
  Being      := Being
  Call       := Call
  Response   := Response
  respondsTo _ _ := some Response.response
  grade _ _ _ := 1
  conditions _ _ := True

def w : selfLineGrid.Weld :=
  ⟨Being.one, Call.call, Response.response⟩

theorem w_has_live_share : selfLineGrid.WaaAppropriates w := by
  intro hbot
  cases hbot

theorem selfLine_conditions_self : selfLineGrid.conditions w w :=
  True.intro

theorem selfLine_landsAt_self : Grid.DirectedConvention.LandsAt selfLineGrid w w :=
  ⟨True.intro, rfl⟩

theorem selfLine_waaOwnershipFace_self :
    Grid.DirectedConvention.WaaOwnershipFace selfLineGrid w w :=
  ⟨⟨True.intro, rfl⟩, w_has_live_share⟩

end SelfLineWitness

end WAA
