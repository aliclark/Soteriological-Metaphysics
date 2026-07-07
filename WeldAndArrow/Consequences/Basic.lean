/-
================================================================================
  WeldAndArrow.Consequences.Basic
  Checked consequences of the signature layer
================================================================================

This module proves consequences of the primitive definitions: order facts,
function/share facts, re-pitch facts, delivery and landing projections, pair
projections, and tier diagnostics.

Reading and motivation: Identification/Commentary.lean, C.2.
-/

import WeldAndArrow.Signature

namespace WAA

section Preorder

variable {α : Type} [Preorder α]

/-- Incomparability is symmetric. -/
theorem incomparable_symm {a b : α} (h : Incomparable a b) :
    Incomparable b a :=
  ⟨h.right, h.left⟩

/-- Incomparability rules out the left-to-right comparison. -/
theorem not_le_of_incomparable {a b : α} (h : Incomparable a b) :
    ¬ a ≼ b :=
  h.left

/-- Incomparability rules out the right-to-left comparison. -/
theorem not_ge_of_incomparable {a b : α} (h : Incomparable a b) :
    ¬ b ≼ a :=
  h.right

end Preorder

namespace Grid

variable {Contrib : Type} [PreorderBot Contrib]
variable (G : Grid Contrib)

/- Reading and motivation: Identification/Commentary.lean, C.2. -/

/-- The share projection is exactly the grade recorded for the weld. -/
@[simp]
theorem share_eq_grade (w : G.Weld) :
    G.share w = G.grade w.agent w.call w.response :=
  rfl

/-- An actual weld witnesses response-function at its own call. -/
theorem mountsAt_of_actual (w : G.Weld) (h : G.Actual w) :
    G.MountsAt w.agent w.call :=
  ⟨w.response, h⟩

/-- An actual weld witnesses response-function somewhere for its agent. -/
theorem mountsSomewhere_of_actual (w : G.Weld) (h : G.Actual w) :
    G.MountsSomewhere w.agent :=
  ⟨w.call, G.mountsAt_of_actual w h⟩

/-- A being with an actual weld is not stone-typed. -/
theorem not_stone_of_actual (w : G.Weld) (h : G.Actual w) :
    ¬ G.Stone w.agent :=
  G.not_stone_of_mountsSomewhere w.agent (G.mountsSomewhere_of_actual w h)

/-- A stone has no actual weld at any call. -/
theorem not_actual_of_stone
    (b : G.Being) (hstone : G.Stone b) {c : G.Call} {r : G.Response} :
    ¬ G.Actual ⟨b, c, r⟩ :=
  fun hactual => hstone c ⟨r, hactual⟩

/-- A stone mounts nowhere. -/
theorem not_mountsSomewhere_of_stone (b : G.Being) (hstone : G.Stone b) :
    ¬ G.MountsSomewhere b :=
  fun hmounts => G.not_stone_of_mountsSomewhere b hmounts hstone

/-- A concrete response at a call rules out stone-typing. -/
theorem not_stone_of_response
    {b : G.Being} {c : G.Call} {r : G.Response}
    (hresp : G.respondsTo b c = some r) :
    ¬ G.Stone b :=
  fun hstone => hstone c ⟨r, hresp⟩

theorem stone_of_no_call (h : G.Call → False) (b : G.Being) :
    G.Stone b :=
  fun c _hmount => False.elim (h c)

theorem respondsToEveryCall_of_no_call (h : G.Call → False) (b : G.Being) :
    G.RespondsToEveryCall b :=
  fun c => False.elim (h c)

theorem stone_iff_respondsToEveryCall_of_no_call
    (h : G.Call → False) (b : G.Being) :
    G.Stone b ↔ G.RespondsToEveryCall b :=
  ⟨fun _ => G.respondsToEveryCall_of_no_call h b,
    fun _ => G.stone_of_no_call h b⟩

theorem allStone_of_no_being (h : G.Being → False) :
    G.AllStone :=
  fun b => False.elim (h b)

/- Reading and motivation: Identification/Commentary.lean, C.2. -/
theorem atPoleClass_of_stone (b : G.Being) (hstone : G.Stone b) :
    G.AtPoleClass b :=
  Or.inl hstone

/- Reading and motivation: Identification/Commentary.lean, C.2. -/
theorem atPoleClass_of_terminus (b : G.Being) (hterm : G.Terminus b) :
    G.AtPoleClass b :=
  Or.inr hterm

/- Reading and motivation: Identification/Commentary.lean, C.2. -/
theorem atPoleClass_and_not_stone_of_liveTerminus
    (b : G.Being) (h : G.LiveTerminus b) :
    G.AtPoleClass b ∧ ¬ G.Stone b :=
  ⟨G.atPoleClass_of_terminus b h.right, G.liveTerminus_not_stone b h⟩

/-- A responsive terminus is not stone-typed whenever the call-domain has a witness. -/
theorem not_stone_of_responsiveTerminus_of_call
    (b : G.Being) (c : G.Call) (h : G.ResponsiveTerminus b) :
    ¬ G.Stone b :=
  G.liveTerminus_not_stone b (G.responsiveTerminus_live_of_call b c h)

/- Reading and motivation: Identification/Commentary.lean, C.2. -/

/- Reading and motivation: Identification/Commentary.lean, C.2. -/
theorem rePitch_tendency_eq_share
    (before : Config Contrib) (received : G.Weld) :
    (G.rePitch before received).tendency = G.share received :=
  rfl

/- Reading and motivation: Identification/Commentary.lean, C.2. -/
theorem isShareDrop_iff_rePitch_tendency_drop
    (before : Config Contrib) (received : G.Weld) :
    G.IsShareDrop before received ↔
      ((G.rePitch before received).tendency ≼ before.tendency ∧
        ¬ (before.tendency ≼ (G.rePitch before received).tendency)) :=
  Iff.rfl

/- Reading and motivation: Identification/Commentary.lean, C.2. -/
theorem rePitch_tendency_le_before_of_shareDrop
    {before : Config Contrib} {received : G.Weld}
    (h : G.IsShareDrop before received) :
    (G.rePitch before received).tendency ≼ before.tendency :=
  h.left

/- Reading and motivation: Identification/Commentary.lean, C.2. -/
theorem not_before_le_rePitch_tendency_of_shareDrop
    {before : Config Contrib} {received : G.Weld}
    (h : G.IsShareDrop before received) :
    ¬ (before.tendency ≼ (G.rePitch before received).tendency) :=
  h.right

/-- A terminus response re-pitches the carried tendency into the pole-class. -/
theorem rePitch_tendency_atBot_of_terminus_response
    (before : Config Contrib) {b : G.Being} {c : G.Call} {r : G.Response}
    (hterm : G.Terminus b) (hresp : G.respondsTo b c = some r) :
    AtBot (G.rePitch before ⟨b, c, r⟩).tendency :=
  G.atBot_of_terminus_response hterm hresp

/- ==============================================================================
   Conditions-free grade checks
============================================================================== -/

/-- Replace only the delivery relation of a grid. Function and grade data are
    left untouched. -/
def withConditions (conditions' : G.Weld -> G.Weld -> Prop) : Grid Contrib where
  Being      := G.Being
  Call       := G.Call
  Response   := G.Response
  respondsTo := G.respondsTo
  grade      := G.grade
  conditions := conditions'

@[simp]
theorem withConditions_respondsTo
    (conditions' : G.Weld -> G.Weld -> Prop)
    (b : G.Being) (c : G.Call) :
    (G.withConditions conditions').respondsTo b c = G.respondsTo b c :=
  rfl

@[simp]
theorem withConditions_grade
    (conditions' : G.Weld -> G.Weld -> Prop)
    (b : G.Being) (c : G.Call) (r : G.Response) :
    (G.withConditions conditions').grade b c r = G.grade b c r :=
  rfl

@[simp]
theorem withConditions_share
    (conditions' : G.Weld -> G.Weld -> Prop) (w : G.Weld) :
    (G.withConditions conditions').share w = G.share w :=
  rfl

@[simp]
theorem withConditions_actual_iff
    (conditions' : G.Weld -> G.Weld -> Prop) (w : G.Weld) :
    (G.withConditions conditions').Actual w ↔ G.Actual w :=
  Iff.rfl

/-- Changing only `conditions` cannot change the grade assigned to a mounted
    response. This is the formal anchor for the cetana correlation at
    signature level: grade is blind to downstream delivery facts. -/
theorem grade_independent_of_conditions
    (conditions₁ conditions₂ : G.Weld -> G.Weld -> Prop)
    (b : G.Being) (c : G.Call) (r : G.Response) :
    (G.withConditions conditions₁).grade b c r =
      (G.withConditions conditions₂).grade b c r :=
  rfl

/-- The same cetana anchor at the weld/share projection: what is graded is the
    weld's agent-call-response composition, not the later delivery relation. -/
theorem share_independent_of_conditions
    (conditions₁ conditions₂ : G.Weld -> G.Weld -> Prop) (w : G.Weld) :
    (G.withConditions conditions₁).share w =
      (G.withConditions conditions₂).share w :=
  rfl

/- ==============================================================================
   Response-function replacement and futility
============================================================================== -/

/-- Replace only the response function of a grid. Grade and delivery data are
    left untouched. The futility mechanism's carrier: adaptive-to-static
    conversion is one instance. -/
def withRespondsTo (respondsTo' : G.Being -> G.Call -> Option G.Response) :
    Grid Contrib where
  Being      := G.Being
  Call       := G.Call
  Response   := G.Response
  respondsTo := respondsTo'
  grade      := G.grade
  conditions := G.conditions

@[simp]
theorem withRespondsTo_grade
    (respondsTo' : G.Being -> G.Call -> Option G.Response)
    (b : G.Being) (c : G.Call) (r : G.Response) :
    (G.withRespondsTo respondsTo').grade b c r = G.grade b c r :=
  rfl

@[simp]
theorem withRespondsTo_share
    (respondsTo' : G.Being -> G.Call -> Option G.Response) (w : G.Weld) :
    (G.withRespondsTo respondsTo').share w = G.share w :=
  rfl

@[simp]
theorem withRespondsTo_conditions
    (respondsTo' : G.Being -> G.Call -> Option G.Response) :
    (G.withRespondsTo respondsTo').conditions = G.conditions :=
  rfl

/-- Death of one being, futility-theorem sense: its response function is
    removed; nothing else in the grid moves. -/
def staticized [DecidableEq G.Being] (b : G.Being) : Grid Contrib :=
  G.withRespondsTo (fun b' c => if b' = b then none else G.respondsTo b' c)

theorem staticized_transpose [h : DecidableEq G.Being] (b : G.Being) :
    (@Grid.staticized Contrib _ G h b).transpose =
      @Grid.staticized Contrib _ G.transpose h b :=
  rfl

/-- Staticizing leaves other beings' response functions untouched. -/
theorem staticized_respondsTo_of_ne
    [DecidableEq G.Being] {b b' : G.Being} (h : b' ≠ b) (c : G.Call) :
    (G.staticized b).respondsTo b' c = G.respondsTo b' c := by
  simp [staticized, withRespondsTo, h]

/-- Staticizing leaves all prior share assignments untouched. -/
theorem staticized_share
    [DecidableEq G.Being] (b : G.Being) (w : G.Weld) :
    (G.staticized b).share w = G.share w :=
  rfl

/-- Staticizing turns the named being into a response-invariant device
    vacuously: no call receives a response from it. -/
theorem staticized_responseInvariant
    [DecidableEq G.Being] (b : G.Being) :
    (G.staticized b).ResponseInvariant b := by
  intro c₁ _c₂ r₁ _r₂ h₁ _h₂
  simp [staticized, withRespondsTo] at h₁

/-- Futility, delivery-loss face: after staticization, the named being mounts
    no response. -/
theorem futility_delivery_loss_real
    [DecidableEq G.Being] (b : G.Being) :
    (G.staticized b).Stone b := by
  intro c hmount
  rcases hmount with ⟨r, hr⟩
  simp [staticized, withRespondsTo] at hr

/-- Futility, object-axis face: staticization does not alter the delivery
    relation. -/
theorem futility_object_axis_subtraction_nil
    [DecidableEq G.Being] (b : G.Being) :
    (G.staticized b).conditions = G.conditions :=
  rfl

namespace DirectedConvention

/-- Object-axis standing is unchanged by staticization, because it reads only
    the delivery relation. -/
theorem staticized_objectAxisStanding_iff
    [DecidableEq G.Being] (b : G.Being) (deed : G.Weld) :
    ObjectAxisStanding (G.staticized b) deed ↔ ObjectAxisStanding G deed :=
  Iff.rfl

end DirectedConvention

/- ==============================================================================
   Accumulation: `rePitch` has no history register
============================================================================== -/

/-- The post-reception configuration ignores the prior configuration and reads
    only the received weld's share. -/
theorem rePitch_forgets
    (before₁ before₂ : Config Contrib) (received : G.Weld) :
    G.rePitch before₁ received = G.rePitch before₂ received :=
  rfl

/-- Any run-valued score that factors through the post-reception `Config` is
    constant across histories that share their final reception. -/
theorem accumulated_attainment_constant_of_same_final
    {α : Type} (score : Config Contrib -> α)
    (before₁ before₂ : Config Contrib) (received : G.Weld) :
    score (G.rePitch before₁ received) =
      score (G.rePitch before₂ received) :=
  congrArg score (G.rePitch_forgets before₁ before₂ received)

/- ==============================================================================
   The environs lens
============================================================================== -/

namespace DirectedConvention

/- Reading and motivation: Identification/Commentary.lean, C.2. -/
theorem environsLine_of_shareDropLine
    {before : Config Contrib} {b : G.Being} {deed reception : G.Weld}
    (h : ShareDropLine G before b deed reception) :
    EnvironsLine G b deed reception :=
  h.left

/- Reading and motivation: Identification/Commentary.lean, C.2. -/
theorem isShareDrop_of_shareDropLine
    {before : Config Contrib} {b : G.Being} {deed reception : G.Weld}
    (h : ShareDropLine G before b deed reception) :
    G.IsShareDrop before reception :=
  h.right

/-- An environs-line is a delivery-fact. -/
theorem deliveredTo_of_environsLine
    {b : G.Being} {deed reception : G.Weld}
    (h : EnvironsLine G b deed reception) :
    DeliveredTo G deed reception :=
  h.right.right

end DirectedConvention

/- Reading and motivation: Identification/Commentary.lean, C.2. -/
theorem not_isShareDrop_of_tendency_atBot
    {before : Config Contrib} (h : AtBot before.tendency)
    (received : G.Weld) :
    ¬ G.IsShareDrop before received := by
  intro hdrop
  exact hdrop.right (Preorder.le_trans h (shareBot_le (G.share received)))

/- Reading and motivation: Identification/Commentary.lean, C.2. -/
theorem not_isShareDrop_of_eq_shareBot_tendency
    {before : Config Contrib} (h : before.tendency = shareBot)
    (received : G.Weld) :
    ¬ G.IsShareDrop before received :=
  G.not_isShareDrop_of_tendency_atBot (atBot_of_eq_shareBot h) received

namespace DirectedConvention

/- Reading and motivation: Identification/Commentary.lean, C.2. -/
theorem no_shareDropLine_of_tendency_atBot
    {before : Config Contrib} (h : AtBot before.tendency)
    (b : G.Being) (deed reception : G.Weld) :
    ¬ ShareDropLine G before b deed reception :=
  fun hline =>
    G.not_isShareDrop_of_tendency_atBot h reception hline.right

/-- Literal equality with the designated bottom gives the pole-class release
    obstruction. -/
theorem no_shareDropLine_of_eq_shareBot_tendency
    {before : Config Contrib} (h : before.tendency = shareBot)
    (b : G.Being) (deed reception : G.Weld) :
    ¬ ShareDropLine G before b deed reception :=
  no_shareDropLine_of_tendency_atBot G (atBot_of_eq_shareBot h) b deed reception

/- Reading and motivation: Identification/Commentary.lean, C.2. -/
theorem hasShareDropLanding_of_shareDropLine_actual
    {before : Config Contrib} {b : G.Being} {deed reception : G.Weld}
    (hline : ShareDropLine G before b deed reception)
    (hact : G.Actual reception) :
    HasShareDropLanding G before deed :=
  ⟨reception, ⟨⟨hline.left.right.right, hact⟩, hline.right⟩⟩

/-- Shortfall is closed at a delivered pair when, for any live prior tendency,
    delivery of the deed is enough to yield a share-drop landing for that deed.
    This is regime-relational effectiveness talk, not a nature possessed by a
    being. -/
def ShortfallClosedAt
    (before : Config Contrib) (deed reception : G.Weld) : Prop :=
  ¬ AtBot before.tendency →
    DeliveredTo G deed reception →
      HasShareDropLanding G before deed

/-- An explicit share-drop line with an actual reception supplies the local
    closure predicate. -/
theorem shortfallClosedAt_of_shareDropLine_actual
    {before : Config Contrib} {b : G.Being} {deed reception : G.Weld}
    (hline : ShareDropLine G before b deed reception)
    (hact : G.Actual reception) :
    ShortfallClosedAt G before deed reception :=
  fun _hlive _hdel =>
    hasShareDropLanding_of_shareDropLine_actual G hline hact

/-- Sraddha faith, stated as a hypothesis: the being is a responsive terminus and
    every delivered reception of one of its deeds closes shortfall for a live
    prior tendency. The universal closure conjunct is exactly the component no
    field-recovery theorem can verify for free. -/
def WaaFullyEnlightened (b : G.Being) : Prop :=
  G.ResponsiveTerminus b ∧
    ∀ before deed reception,
      deed.agent = b →
        ShortfallClosedAt G before deed reception

theorem responsiveTerminus_of_waaFullyEnlightened
    {b : G.Being} (h : WaaFullyEnlightened G b) :
    G.ResponsiveTerminus b :=
  h.left

theorem shortfallClosedAt_of_waaFullyEnlightened
    {b : G.Being} (h : WaaFullyEnlightened G b)
    {before : Config Contrib} {deed reception : G.Weld}
    (hdeed : deed.agent = b) :
    ShortfallClosedAt G before deed reception :=
  h.right before deed reception hdeed

/-- If a responsive terminus has no delivered own deeds in the current regime,
    the universal shortfall-closure conjunct is satisfied vacuously. This is
    the sealed-regime face: teaching/non-teaching is not stored in the being,
    but in the delivery relation around it. -/
theorem waaFullyEnlightened_of_responsiveTerminus_of_undelivered
    {b : G.Being} (hterm : G.ResponsiveTerminus b)
    (hundelivered : ∀ (deed reception : G.Weld),
      deed.agent = b → ¬ DeliveredTo G deed reception) :
    WaaFullyEnlightened G b := by
  refine ⟨hterm, ?_⟩
  intro _before deed reception hdeed _hlive hdel
  exact False.elim ((hundelivered deed reception hdeed) hdel)

end DirectedConvention

/- Reading and motivation: Identification/Commentary.lean, C.2. -/

namespace DirectedConvention

/-- A full reach-back is the same field-side fact as delivery. -/
theorem waaReachBackFull_iff_deliveredTo (deed reception : G.Weld) :
    WaaReachBackFull G deed reception ↔ DeliveredTo G deed reception :=
  Iff.rfl

/-- An aimed call is just delivery, stated from the sowing side. -/
theorem waaAimedAt_iff_deliveredTo (deed reception : G.Weld) :
    WaaAimedAt G deed reception ↔ DeliveredTo G deed reception :=
  Iff.rfl

/-- Landing includes delivery. -/
theorem deliveredTo_of_landsAt
    {deed reception : G.Weld} (h : LandsAt G deed reception) :
    DeliveredTo G deed reception :=
  h.left

/-- Landing includes actuality of the reception. -/
theorem actual_of_landsAt
    {deed reception : G.Weld} (h : LandsAt G deed reception) :
    G.Actual reception :=
  h.right

/- Reading and motivation: Identification/Commentary.lean, C.2. -/
theorem landsAt_of_landsWithShareDrop
    {before : Config Contrib} {deed reception : G.Weld}
    (h : LandsWithShareDrop G before deed reception) :
    LandsAt G deed reception :=
  h.left

/- Reading and motivation: Identification/Commentary.lean, C.2. -/
theorem isShareDrop_of_landsWithShareDrop
    {before : Config Contrib} {deed reception : G.Weld}
    (h : LandsWithShareDrop G before deed reception) :
    G.IsShareDrop before reception :=
  h.right

/- Reading and motivation: Identification/Commentary.lean, C.2. -/
theorem deliveredTo_of_landsWithShareDrop
    {before : Config Contrib} {deed reception : G.Weld}
    (h : LandsWithShareDrop G before deed reception) :
    DeliveredTo G deed reception :=
  deliveredTo_of_landsAt G (landsAt_of_landsWithShareDrop G h)

/- Reading and motivation: Identification/Commentary.lean, C.2. -/
theorem actual_of_landsWithShareDrop
    {before : Config Contrib} {deed reception : G.Weld}
    (h : LandsWithShareDrop G before deed reception) :
    G.Actual reception :=
  actual_of_landsAt G (landsAt_of_landsWithShareDrop G h)

/- Reading and motivation: Identification/Commentary.lean, C.2. -/
theorem exists_landsAt_of_hasShareDropLanding
    {before : Config Contrib} {deed : G.Weld}
    (h : HasShareDropLanding G before deed) :
    ∃ reception, LandsAt G deed reception :=
  h.elim (fun reception hland =>
    ⟨reception, landsAt_of_landsWithShareDrop G hland⟩)

/- Reading and motivation: Identification/Commentary.lean, C.2. -/
theorem exists_actual_reception_of_hasShareDropLanding
    {before : Config Contrib} {deed : G.Weld}
    (h : HasShareDropLanding G before deed) :
    ∃ reception, G.Actual reception :=
  h.elim (fun reception hland =>
    ⟨reception, actual_of_landsWithShareDrop G hland⟩)

/- Reading and motivation: Identification/Commentary.lean, C.2. -/
theorem exists_shareDrop_reception_of_hasShareDropLanding
    {before : Config Contrib} {deed : G.Weld}
    (h : HasShareDropLanding G before deed) :
    ∃ reception, G.IsShareDrop before reception :=
  h.elim (fun reception hland =>
    ⟨reception, isShareDrop_of_landsWithShareDrop G hland⟩)

end DirectedConvention

/- ==============================================================================
   Actual pairs
============================================================================== -/

namespace ReceptionPair

variable {G : Grid Contrib}

/-- The first member of a reception pair is actual. -/
theorem first_actual (p : ReceptionPair G) :
    G.Actual p.first.weld :=
  p.first.actual

/-- The second member of a reception pair is actual. -/
theorem second_actual (p : ReceptionPair G) :
    G.Actual p.second.weld :=
  p.second.actual

/-- The pair's named relation is just delivery from first to second. -/
theorem firstConditionsSecond_iff_deliveredTo (p : ReceptionPair G) :
    p.FirstConditionsSecond ↔
      DirectedConvention.DeliveredTo G p.first.weld p.second.weld :=
  Iff.rfl

/- Reading and motivation: Identification/Commentary.lean, C.2. -/
theorem rePitchSequence_first_tendency
    (before : Config Contrib) (p : ReceptionPair G) :
    (rePitchSequence (G := G) before p).fst.tendency = G.share p.first.weld :=
  rfl

/- Reading and motivation: Identification/Commentary.lean, C.2. -/
theorem rePitchSequence_second_tendency
    (before : Config Contrib) (p : ReceptionPair G) :
    (rePitchSequence (G := G) before p).snd.tendency = G.share p.second.weld :=
  rfl

end ReceptionPair

/- ==============================================================================
   Tiers, utterances, and separate/fuse diagnostics
============================================================================== -/

/- Reading and motivation: Identification/Commentary.lean, C.2. -/
theorem floor_has_no_live_share :
    ¬ Tier.hasLiveShare G (Tier.floor : Tier G) :=
  fun h => h

/- Reading and motivation: Identification/Commentary.lean, C.2. -/
theorem actTime_hasLiveShare_iff_hasSelfPoleIndex (w : G.Weld) :
    Tier.hasLiveShare G (Tier.actTime w) ↔ G.HasSelfPoleIndex w :=
  Iff.rfl

/- Reading and motivation: Identification/Commentary.lean, C.2. -/
theorem not_actTime_hasLiveShare_of_atBot
    {w : G.Weld} (h : AtBot (G.share w)) :
    ¬ Tier.hasLiveShare G (Tier.actTime w) :=
  G.no_self_pole_index_of_atBot w h

/-- Equality with the designated bottom is a bridge into the pole-class
    act-time lemma. -/
theorem not_actTime_hasLiveShare_of_eq_shareBot
    {w : G.Weld} (h : G.share w = shareBot) :
    ¬ Tier.hasLiveShare G (Tier.actTime w) :=
  G.not_actTime_hasLiveShare_of_atBot (atBot_of_eq_shareBot h)

/-- Collapse is impossible at the floor. -/
theorem not_collapse_floor (d : Distinction G) :
    ¬ d.Collapse (Tier.floor : Tier G) :=
  fun hcollapse => G.floor_has_no_live_share hcollapse.left

/- Reading and motivation: Identification/Commentary.lean, C.2. -/
theorem hasLiveShare_of_collapse
    {d : Distinction G} {t : Tier G} (h : d.Collapse t) :
    Tier.hasLiveShare G t :=
  h.left

/- Reading and motivation: Identification/Commentary.lean, C.2. -/
theorem hasLiveShare_of_separated
    {d : Distinction G} {t : Tier G} (h : d.Separated t) :
    Tier.hasLiveShare G t :=
  h.left

/-- Separation rules out collapse at the same tier. -/
theorem not_collapse_of_separated
    {d : Distinction G} {t : Tier G} (h : d.Separated t) :
    ¬ d.Collapse t :=
  fun hcollapse => h.right hcollapse.right

/-- Obeying the rule supplies the fusion clause at every tier. -/
theorem fused_of_obeysSeparateFuse
    {d : Distinction G} (h : d.ObeysSeparateFuse) (t : Tier G) :
    d.Fused t :=
  h.right t

/- Reading and motivation: Identification/Commentary.lean, C.2. -/
theorem separated_of_obeysSeparateFuse
    {d : Distinction G} (h : d.ObeysSeparateFuse)
    {t : Tier G} (ht : Tier.hasLiveShare G t) :
    d.Separated t :=
  ⟨ht, h.left t ht⟩

/-- Fusion at the floor rules out freeze. -/
theorem not_freeze_of_fused_floor
    {d : Distinction G} (h : d.Fused (Tier.floor : Tier G)) :
    ¬ d.Freeze :=
  fun hfreeze => hfreeze (h G.floor_has_no_live_share)

/-- Error-freedom is the refutation-only reading of the separate/fuse rule:
    no live-tier collapse and no floor freeze. -/
def ErrorFree (d : Distinction G) : Prop :=
  (∀ t, ¬ d.Collapse t) ∧ ¬ d.Freeze

/-- Obedience supplies both refutations. The converse is not true for an
    arbitrary distinction; the pole-affirming row language below is the special
    case where the missing genjo-fusion clause is built into the semantics. -/
theorem errorFree_of_obeys
    {d : Distinction G} (h : d.ObeysSeparateFuse) :
    ErrorFree G d :=
  ⟨fun t => Grid.not_collapse_of_obeysSeparateFuse h t,
    Grid.not_freeze_of_obeysSeparateFuse h⟩

namespace RecordedUtterance

variable {G : Grid Contrib} {L : ClaimLanguage G}

/-- The answered call is the call carried by the utterance's weld. -/
@[simp]
theorem answersCall_eq_weld_call (u : RecordedUtterance G L) :
    answersCall u = u.weld.call :=
  rfl

/-- Fitting the offered tier is exactly truth at that tier. -/
theorem fitsOfferedTier_iff_trueAt (u : RecordedUtterance G L) :
    FitsOfferedTier u ↔ L.TrueAt u.offeredAt u.content :=
  Iff.rfl

end RecordedUtterance

namespace ErrorGrade

/-- Verdict errors speak in the assertable voice. -/
theorem verdict_voice_assertable :
    ErrorGrade.voice ErrorGrade.verdict = VerdictVoice.assertable :=
  rfl

/-- Shortfall errors speak in the displayable voice. -/
theorem shortfall_voice_displayable :
    ErrorGrade.voice ErrorGrade.shortfall = VerdictVoice.displayable :=
  rfl

end ErrorGrade


end Grid

end WAA
