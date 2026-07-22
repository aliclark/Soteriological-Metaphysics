/-
================================================================================
  WeldAndArrow.Meta.InvarianceNegative
  Countermodels for invariance and recovery claims
================================================================================

Reading and motivation: Identification/Commentary.lean, C.3.
-/

import WeldAndArrow.Meta.Invariance

namespace WAA
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

/- ==============================================================================
   Configuration leak witnesses: honest limits of non-storage
============================================================================== -/

namespace ConfigLeakWitness

/-- The blanket noninterference reading of "nothing indexed is stored" is
    false: in the register clock, the re-pitched tendency extensionally
    recovers the received weld's agent tag. This is deliberate — grading may
    depend on the agent — and is why the checked non-storage claim is typing
    plus equivariance, never information flow. -/
theorem registerClock_config_recovers_agent :
    ∀ (before : Config Nat) (w : registerClockGrid.Weld),
      (registerClockGrid.rePitch before w).tendency = w.agent := by
  intro _ _
  rfl

/-- Under a share collision, no function from configurations correctly
    recovers the acting agent for every actual weld: the two receptions
    re-pitch to the same configuration. -/
theorem no_agent_recovery_from_config_of_share_collision :
    ¬ ∃ recover : Config Nat → shareCollisionGrid.Being,
        ∀ (before : Config Nat) (w : shareCollisionGrid.Weld),
          shareCollisionGrid.Actual w →
            recover (shareCollisionGrid.rePitch before w) = w.agent := by
  rintro ⟨recover, correct⟩
  let before : Config Nat := { tendency := 0 }
  let leftWeld : shareCollisionGrid.Weld :=
    ⟨ShareCollisionBeing.left, (), ()⟩
  let rightWeld : shareCollisionGrid.Weld :=
    ⟨ShareCollisionBeing.right, (), ()⟩
  have hleft := correct before leftWeld (by rfl)
  have hright := correct before rightWeld (by rfl)
  have hagents : ShareCollisionBeing.left = ShareCollisionBeing.right := by
    exact hleft.symm.trans hright
  cases hagents

end ConfigLeakWitness

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
   Direction-coarsening witnesses
============================================================================== -/

namespace DirectionCoarseningWitness

open Grid.DirectedConvention
open Grid.DirectedConvention.DirectionCoarsening

/-- The raw register-clock read through a one-tick delivery clock. -/
def registerClockUnitTick : DirectionCoarsening registerClockGrid Unit where
  tick _ := ()

def registerClockLow : registerClockGrid.Weld :=
  ⟨(0 : Nat), (), (1 : Nat)⟩

def registerClockHigh : registerClockGrid.Weld :=
  ⟨(1 : Nat), (), (2 : Nat)⟩

/-- Honest snag: the raw `Nat` register display is injective on registers, so a
    universal tick cannot be resolution-bounded. -/
theorem registerClock_unitTick_not_resolutionBounded :
    ¬ registerClockUnitTick.ResolutionBounded := by
  intro h
  have hEq : OrderEq (registerClockGrid.share registerClockLow)
      (registerClockGrid.share registerClockHigh) :=
    h registerClockLow registerClockHigh rfl
  have hle : (1 : Nat) ≼ 0 := by
    simpa [Grid.share, registerClockGrid, registerClockLow, registerClockHigh] using hEq.right
  change (1 : Nat) ≤ 0 at hle
  cases hle

/-- A fully coarse display of the same register-clock response and delivery
    shape. The carrier is already one-point, so this is the slow-clock limit
    after display choice, not a collapse of the raw `Nat` order. -/
def fullyCoarseRegisterClockGrid : Grid Unit where
  Being      := Nat
  Call       := Unit
  Response   := Nat
  respondsTo n _ := some (n + 1)
  grade _ _ _ := ()
  conditions deed reception := reception.agent = deed.response

def fullyCoarseRegisterClockUnitTick :
    DirectionCoarsening fullyCoarseRegisterClockGrid Unit where
  tick _ := ()

/-- The fully coarse display is resolution-bounded by construction. -/
theorem fullyCoarseRegisterClock_resolutionBounded :
    fullyCoarseRegisterClockUnitTick.ResolutionBounded := by
  intro _w₁ _w₂ _hsame
  exact ⟨True.intro, True.intro⟩

/-- The target one-point carrier is direction-void, obtained through the
    existing legal display collapse from the all-equivalent `TwoBottom`
    carrier. -/
theorem unit_directionVoid_via_mergeToUnit : DirectionVoid Unit :=
  DisplayReparam.directionVoid_of_surjective InvarianceNegative.mergeToUnit
    (fun b => ⟨InvarianceNegative.TwoBottom.chosen, by cases b; rfl⟩)
    (fun a b => DirectionNegative.not_strict_twoBottom a b)

/-- In the fully coarse register-clock display, no pair of weld-shares carries
    strict time-direction. -/
theorem fullyCoarseRegisterClock_no_timeDirection
    (w₁ w₂ : fullyCoarseRegisterClockGrid.Weld) :
    ¬ TimeDirection (fullyCoarseRegisterClockGrid.share w₁)
        (fullyCoarseRegisterClockGrid.share w₂) :=
  fullyCoarseRegisterClockUnitTick.no_timeDirection_of_resolutionBounded_subsingleton
    fullyCoarseRegisterClock_resolutionBounded (fun _ _ => rfl) w₁ w₂

/-- Function and internal-delivery witnesses for the macro register clock do
    not consume direction-coarsening or resolution-boundedness hypotheses. -/
theorem registerClock_directionCoarsening_independence :
    (∀ {Tick : Type} (_ρ : DirectionCoarsening registerClockGrid Tick),
        registerClockCoarsening.SentientTag registerClockSentienceReading () ∧
          registerClockCoarsening.SelfConditioningTag ()) ∧
      (∀ {Tick : Type} (ρ : DirectionCoarsening registerClockGrid Tick),
        ρ.ResolutionBounded ->
          registerClockCoarsening.SentientTag registerClockSentienceReading () ∧
            registerClockCoarsening.SelfConditioningTag ()) := by
  constructor
  · intro _Tick _ρ
    exact ⟨registerClock_macro_sentient, registerClock_macro_selfConditioning⟩
  · intro _Tick _ρ _hbounded
    exact ⟨registerClock_macro_sentient, registerClock_macro_selfConditioning⟩

end DirectionCoarseningWitness

/- ==============================================================================
   Content-row countermodels
============================================================================== -/

namespace ContentNegative

open Grid.DirectedConvention.BeingConvention.GridConvention

def noActualGrid : Grid InvarianceNegative.TwoBottom where
  Being      := Unit
  Call       := Unit
  Response   := Unit
  respondsTo _ _ := none
  grade _ _ _ := InvarianceNegative.TwoBottom.chosen
  conditions _ _ := False

def noActualWeld : noActualGrid.Weld :=
  ⟨(), (), ()⟩

theorem noActualGrid_no_actual :
    ¬ ∃ w : noActualGrid.Weld, noActualGrid.Actual w := by
  rintro ⟨w, hactual⟩
  cases w with
  | mk agent call response =>
      cases agent
      cases call
      cases response
      cases hactual

theorem noActualGrid_no_liveTier (t : Grid.Tier noActualGrid) :
    ¬ Grid.Tier.hasLiveShare noActualGrid t := by
  cases t with
  | floor =>
      intro h
      exact h
  | actTime _ =>
      intro hidx
      exact hidx True.intro

theorem noActualWeld_no_live_share :
    ¬ Grid.Tier.hasLiveShare noActualGrid (Grid.Tier.actTime noActualWeld) :=
  noActualGrid_no_liveTier (Grid.Tier.actTime noActualWeld)

theorem contentBeingsRow_not_fused_noActual :
    ¬ (contentBeingsRow noActualGrid).Fused (Grid.Tier.actTime noActualWeld) := by
  intro hfused
  have hiff := hfused noActualWeld_no_live_share
  have hdenial :
      (contentLayerLanguage noActualGrid).TrueAt
        (Grid.Tier.actTime noActualWeld) (.layerDenied .beings) := by
    dsimp [contentLayerLanguage, Grid.ClaimLanguage.TrueAt]
    exact noActualGrid_no_actual
  exact noActualWeld_no_live_share (hiff.mpr hdenial)

theorem contentBeingsRow_not_obeys_noActual :
    ¬ (contentBeingsRow noActualGrid).ObeysSeparateFuse := by
  intro h
  exact contentBeingsRow_not_fused_noActual
    (noActualGrid.fused_of_obeysSeparateFuse h (Grid.Tier.actTime noActualWeld))

theorem contentGridLensRow_not_fused_noLive :
    ¬ (contentGridLensRow noActualGrid).Fused (Grid.Tier.actTime noActualWeld) := by
  intro hfused
  have hiff := hfused noActualWeld_no_live_share
  have hdenial :
      (contentLayerLanguage noActualGrid).TrueAt
        (Grid.Tier.actTime noActualWeld) (.layerDenied .gridLens) := by
    dsimp [contentLayerLanguage, Grid.ClaimLanguage.TrueAt]
    exact noActualGrid_no_liveTier
  exact noActualWeld_no_live_share (hiff.mpr hdenial)

theorem contentGridLensRow_not_obeys_noLive :
    ¬ (contentGridLensRow noActualGrid).ObeysSeparateFuse := by
  intro h
  exact contentGridLensRow_not_fused_noLive
    (noActualGrid.fused_of_obeysSeparateFuse h (Grid.Tier.actTime noActualWeld))

def emptyBeingGrid : Grid InvarianceNegative.TwoBottom where
  Being      := Empty
  Call       := Unit
  Response   := Unit
  respondsTo b _ := Empty.elim b
  grade b _ _ := Empty.elim b
  conditions _ _ := False

theorem emptyBeingGrid_no_actual :
    ¬ ∃ w : emptyBeingGrid.Weld, emptyBeingGrid.Actual w := by
  rintro ⟨w, _hactual⟩
  cases w.agent

theorem emptyBeingGrid_no_liveTier (t : Grid.Tier emptyBeingGrid) :
    ¬ Grid.Tier.hasLiveShare emptyBeingGrid t := by
  cases t with
  | floor =>
      intro h
      exact h
  | actTime w =>
      cases w.agent

theorem emptyBeingGrid_contentBeings_denial
    (w : emptyBeingGrid.Weld) :
    (contentLayerLanguage emptyBeingGrid).TrueAt (.actTime w)
      (.layerDenied .beings) := by
  dsimp [contentLayerLanguage, Grid.ClaimLanguage.TrueAt]
  exact emptyBeingGrid_no_actual

theorem contentBeingsRow_fused_emptyBeing (t : Grid.Tier emptyBeingGrid) :
    (contentBeingsRow emptyBeingGrid).Fused t := by
  intro _hnot
  cases t with
  | floor =>
      exact Iff.rfl
  | actTime w =>
      cases w.agent

theorem contentBeingsRow_obeys_emptyBeing :
    (contentBeingsRow emptyBeingGrid).ObeysSeparateFuse := by
  constructor
  · intro t hlive
    exact False.elim (emptyBeingGrid_no_liveTier t hlive)
  · intro t hnot
    exact contentBeingsRow_fused_emptyBeing t hnot

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

def constantResponseGrid : Grid InvarianceNegative.TwoBottom where
  Being      := Unit
  Call       := Bool
  Response   := Unit
  respondsTo _ _ := some ()
  grade _ _ _ := InvarianceNegative.TwoBottom.chosen
  conditions _ _ := False

def constantResponseWeld : constantResponseGrid.Weld :=
  ⟨(), false, ()⟩

theorem constantResponseGrid_no_variation :
    ∀ b : constantResponseGrid.Being,
      ¬ constantResponseGrid.ResponseVariesWithCall b := by
  intro _b h
  rcases h with ⟨_c₁, _c₂, r₁, r₂, _h₁, _h₂, hne⟩
  cases r₁
  cases r₂
  exact hne rfl

theorem constantResponseWeld_no_live_share :
    ¬ Grid.Tier.hasLiveShare constantResponseGrid
        (Grid.Tier.actTime constantResponseWeld) := by
  intro hidx
  exact hidx True.intro

theorem contentIntraWeldArrowRow_not_fused_constantResponse :
    ¬ (contentIntraWeldArrowRow constantResponseGrid).Fused
        (Grid.Tier.actTime constantResponseWeld) := by
  intro hfused
  have hiff := hfused constantResponseWeld_no_live_share
  have hdenial :
      (contentLayerLanguage constantResponseGrid).TrueAt
        (Grid.Tier.actTime constantResponseWeld)
        (.layerDenied .intraWeldArrow) := by
    dsimp [contentLayerLanguage, Grid.ClaimLanguage.TrueAt]
    exact constantResponseGrid_no_variation
  exact constantResponseWeld_no_live_share (hiff.mpr hdenial)

theorem contentIntraWeldArrowRow_not_obeys_constantResponse :
    ¬ (contentIntraWeldArrowRow constantResponseGrid).ObeysSeparateFuse := by
  intro h
  exact contentIntraWeldArrowRow_not_fused_constantResponse
    (constantResponseGrid.fused_of_obeysSeparateFuse h
      (Grid.Tier.actTime constantResponseWeld))

end ContentNegative

/- ==============================================================================
   §N  Being-boundary freedom: designation is not grid-carried

   The witness is parallel in scope to `DirectionNegative`. A single grid has
   two fact-identical fine tags and supports both a merge and a split coarsening.
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

/- ==============================================================================
   Coverage countermodels

   Reading and motivation: Identification/Commentary.lean, C.3.

   The same strict pair `(0, 1)` does double duty here: it refutes
   carrier-wide direction-voidness after mapping, and it supplies the live
   tendency that the source carrier never quantified over. The
   `WaaEffectiveTerminus` witness also gates the coverage-carrying corollaries
   `map_waaEffectiveTerminus_iff` and `map_effectiveTerminus_eq`.
============================================================================== -/

namespace CoverageNegative

open Grid.DirectedConvention

def embedIntoNat : DisplayReparam Unit Nat where
  toFun _ := 0
  le_iff _ _ := ⟨fun _ => Nat.le_refl 0, fun _ => True.intro⟩
  atBot_bot := Nat.le_refl 0

theorem embedIntoNat_not_surjective (u : Unit) :
    embedIntoNat.toFun u ≠ 1 := by
  intro h
  cases h

theorem directionVoid_unit : DirectionVoid Unit :=
  no_strict_of_all_orderEq (fun _ _ => ⟨True.intro, True.intro⟩)

theorem strict_zero_one : Strict (0 : Nat) 1 :=
  ⟨Nat.zero_le 1, fun h => Nat.not_succ_le_zero 0 h⟩

theorem not_directionVoid_nat : ¬ DirectionVoid Nat :=
  fun h => h 0 1 strict_zero_one

/-- Packaged in the `oldEqTerminus_not_invariant` style: the
    reparameterization exists, coverage fails at `1`, the source is
    direction-void, and the target is not. -/
theorem directionVoid_needs_coverage :
    (∀ u : Unit, embedIntoNat.toFun u ≠ 1) ∧
      DirectionVoid Unit ∧ ¬ DirectionVoid Nat :=
  ⟨embedIntoNat_not_surjective, directionVoid_unit, not_directionVoid_nat⟩

def phantomGrid : Grid Unit where
  Being      := Unit
  Call       := Unit
  Response   := Bool
  respondsTo _ _ := some true
  grade _ _ _ := ()
  conditions _deed reception := reception.response = false

def phantomDeed : phantomGrid.Weld := ⟨(), (), true⟩

def phantomReception : phantomGrid.Weld := ⟨(), (), false⟩

theorem phantom_waaEffectiveTerminus :
    WaaEffectiveTerminus phantomGrid () := by
  refine ⟨?_, ?_⟩
  · exact ⟨fun _ => ⟨true, rfl⟩, fun _ _ _ => True.intro⟩
  · intro before _deed _reception _hdeed hlive _hdel
    exact False.elim (hlive True.intro)

theorem not_waaEffectiveTerminus_map :
    ¬ WaaEffectiveTerminus (phantomGrid.map embedIntoNat) () := by
  intro h
  let liveBefore : Config Nat := ⟨1⟩
  have hlive : ¬ AtBot liveBefore.tendency := by
    intro hbot
    exact Nat.not_succ_le_zero 0 hbot
  have hdel :
      DeliveredTo (phantomGrid.map embedIntoNat) phantomDeed phantomReception := rfl
  have hlanding :
      HasShareDropLanding (phantomGrid.map embedIntoNat) liveBefore phantomDeed :=
    h.right liveBefore phantomDeed phantomReception rfl hlive hdel
  rcases hlanding with ⟨reception, hland⟩
  have hlands :
      LandsAt (phantomGrid.map embedIntoNat) phantomDeed reception :=
    hland.left
  have hdelivered : reception.response = false := hlands.left
  have hactual :
      (phantomGrid.map embedIntoNat).respondsTo reception.agent reception.call =
        some reception.response :=
    hlands.right
  cases reception with
  | mk agent call response =>
      cases agent
      cases call
      cases response
      · cases hactual
      · cases hdelivered

theorem waaEffectiveTerminus_needs_coverage :
    WaaEffectiveTerminus phantomGrid () ∧
      ¬ WaaEffectiveTerminus (phantomGrid.map embedIntoNat) () :=
  ⟨phantom_waaEffectiveTerminus, not_waaEffectiveTerminus_map⟩

end CoverageNegative

/- ==============================================================================
   §O  Weld-boundary freedom: pairing is not grid-carried

   This is one level below the being-boundary witness. `no_partition_recovery`
   freed the who; this frees what counts as one act. The same field data support
   both a merged reading of the call-response pairings and a split reading by
   weld-grain. Holding one weld-grain as floor furniture claims a fact the
   grid's data does not carry.
============================================================================== -/

namespace WeldNegative

/-- A diagnosis-time segmentation of welds into macro pairings. Kept local to
    the witness so weld individuation remains a reading rather than a field of
    `Grid`. -/
structure WeldSegmentation (G : Grid Nat) (Macro : Type) where
  proj : G.Weld → Macro

namespace WeldSegmentation

variable {G : Grid Nat} {Macro : Type} (σ : WeldSegmentation G Macro)

def SamePairing (p q : G.Weld) : Prop := σ.proj p = σ.proj q

end WeldSegmentation

/-- Two fact-identical fine exchanges over a symmetric field. -/
def twoWeldGrid : Grid Nat where
  Being      := Unit
  Call       := Bool
  Response   := Bool
  respondsTo _ c := some c
  grade _ _ _ := 0
  conditions _ _ := True

def wFalse : twoWeldGrid.Weld := ⟨(), false, false⟩

def wTrue : twoWeldGrid.Weld := ⟨(), true, true⟩

/-- Merged reading: both fine welds are one macro act. -/
def σmerge : WeldSegmentation twoWeldGrid Unit where
  proj _ := ()

/-- Split reading: each fine weld remains its own act-grain. -/
def σsplit : WeldSegmentation twoWeldGrid Bool where
  proj w := w.call

theorem merge_same_pairing : σmerge.SamePairing wFalse wTrue :=
  rfl

theorem split_not_same_pairing : ¬ σsplit.SamePairing wFalse wTrue := by
  intro h
  cases h

/-- The grid data visible to a would-be weld-boundary recovery function. -/
abbrev W := RawWeld Unit Bool Bool

abbrev GridData : Type :=
  (Unit → Bool → Option Bool) ×
    (Unit → Bool → Bool → Nat) × (W → W → Prop)

def gridData : GridData :=
  (twoWeldGrid.respondsTo, twoWeldGrid.grade, twoWeldGrid.conditions)

def mergedPairing (_p _q : W) : Prop := True

def splitPairing (p q : W) : Prop := p.call = q.call

/-- The weld's individuation is a segmentation convention over the
    correlational field, never recoverable from it. The same grid data support
    both merge and split readings, which disagree on the concrete false/true
    pair. -/
theorem no_weld_boundary_recovery :
    ¬ ∃ recover : GridData → W → W → Prop,
        recover gridData = mergedPairing ∧
        recover gridData = splitPairing := by
  rintro ⟨recover, hmerge, hsplit⟩
  have hmerged : recover gridData wFalse wTrue := by
    rw [hmerge]
    exact True.intro
  have hsplitNot : ¬ recover gridData wFalse wTrue := by
    rw [hsplit]
    intro h
    cases h
  exact hsplitNot hmerged

end WeldNegative

/- ==============================================================================
   §P  Doer/deed priority freedom: priority is not grid-carried

   MMK 8 anchor: kāraka proceeds dependent on karman; neither side is prior
   or independently based. The witness keeps priority as a reading over visible
   grid data rather than adding a priority primitive to `Grid`.
============================================================================== -/

namespace DoerDeedNegative

/-- Reuse the small two-call grid shape: one visible doer tag and two visible
    deeds, with no priority field in the data. -/
abbrev W := RawWeld Unit Bool Bool

abbrev GridData : Type :=
  (Unit → Bool → Option Bool) ×
    (Unit → Bool → Bool → Nat) × (W → W → Prop)

def gridData : GridData :=
  (WeldNegative.twoWeldGrid.respondsTo,
    WeldNegative.twoWeldGrid.grade,
    WeldNegative.twoWeldGrid.conditions)

/-- Priority reading: the visible being is read as standing prior to its deed. -/
def beingPriorReading (_b : Unit) (_deed : W) : Prop := True

/-- Mutual-dependence reading: the same visible data are read with no prior
    doer standing behind the deed. -/
def mutualReading (_b : Unit) (_deed : W) : Prop := False

theorem priority_readings_disagree :
    beingPriorReading () WeldNegative.wFalse ∧
      ¬ mutualReading () WeldNegative.wFalse := by
  constructor
  · exact True.intro
  · intro h
    exact h

theorem no_priority_recovery :
    ¬ ∃ recover : GridData → Unit → W → Prop,
        recover gridData = beingPriorReading ∧
        recover gridData = mutualReading := by
  rintro ⟨recover, hprior, hmutual⟩
  have hPrior : recover gridData () WeldNegative.wFalse := by
    rw [hprior]
    exact priority_readings_disagree.left
  have hMutualNot : ¬ recover gridData () WeldNegative.wFalse := by
    rw [hmutual]
    exact priority_readings_disagree.right
  exact hMutualNot hPrior

end DoerDeedNegative

end WAA
