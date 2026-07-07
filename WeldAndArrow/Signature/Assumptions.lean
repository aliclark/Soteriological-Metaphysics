import WeldAndArrow.Signature.Order
import WeldAndArrow.Signature.Grid
import WeldAndArrow.Signature.BeingConvention
import WeldAndArrow.Signature.DirectionConvention
import WeldAndArrow.Signature.Models
import WeldAndArrow.Signature.Claims

/-!
Canonical assumption list for the `Signature` layer.

This file states the inputs of the system. `Paper.md` reads the theorem outputs,
and `Identification/Commentary.lean` C.1 gives paper-facing motivation. The
anchors below are deliberately close to the declarations they name, so a rename
or type drift in the Signature surface turns into a build failure.

## A. What Is Asserted

1. No prior agent. A weld is the primitive occurrence. `Grid.index` and
   `Grid.share` are projections from a completed `RawWeld`, not fields recovered
   from a separate performer or act. `no_agent_recovery_of_field_collision`
   records the internal obstruction: the same call-response field residue can
   be produced by distinct actual agents.

2. Nothing self-indexed is stored. `Config` stores only `tendency : Contrib`.
   It has no owner, being, weld, or field-residue slot. `rePitch` uses the
   received weld's share and ignores the prior configuration value.

3. The self-pole index is just live share. `HasSelfPoleIndex w` is
   `not AtBot (share w)`, and when the predicate is live the carried
   `selfPoleIndex` is the weld's agent tag.

4. Stone and terminus split function from share. A `Stone` mounts no response.
   A `Terminus` may mount responses, but every mounted response is at the
   pole-class. `AtPoleClass` intentionally includes the vacuous stone case.

5. Self-lines are permitted, not built in. The bare signature does not impose
   irreflexivity on `conditions`; a model may supply reflexive delivery, and
   then the directed vocabulary can read a self-line.

## B. What Is Deliberately Declined

1. No arrow in `conditions`. The signature assumes no asymmetry,
   irreflexivity, or transitivity for `conditions`. `ConditionsEither` is the
   symmetric field fact; direction enters only in `Grid.DirectedConvention`.
   The downstream `DirectionNegative` witness elaborates this as
   non-recovery from symmetric closure.

2. No `PreorderTop`. The signature supplies only `PreorderBot`. The
   share-zero pole is an attained bottom order-class (`AtBot`); the
   total-share or solipsist pole is an asymptote, not an element of the
   interface. `StrongSelfConditioningTag` is named and shelved in the being
   convention for the same reason.

3. No privileged person-partition. A being boundary is supplied by a
   diagnosis-time `BeingCoarsening`, not stored as a field of `Grid`. The
   signature already admits both identity and total coarsenings for any grid;
   the downstream `BeingNegative` witness elaborates this as non-recovery of a
   unique partition from grid data.

4. Direction resolution is display, not signature furniture. A clock's finite
   delivery-axis resolution is supplied by a diagnosis-time
   `DirectionCoarsening`, not by a `Grid` field and not by any pole or
   legitimacy predicate.

5. Contribution values are display, not operational tokens. The Signature
   layer itself uses only order and pole vocabulary around `share`. The
   downstream `DisplayReparam` / `InvarianceNegative` modules give the full
   transport discipline: order- and pole-preserving display changes preserve
   the legal predicates, while equality to the chosen bottom does not.

## C. Conveniences And Stand-Ins

1. `Preorder` and `PreorderBot` are hand-rolled to keep assumptions visible and
   dependency-free. They play the local role Mathlib order classes would play,
   without importing Mathlib.

2. `rePitch` keeps a `_before` slot because the operation is conceptually a
   re-pitch from a prior configuration. The current implementation ignores that
   slot; the proof anchor below is a tripwire for the day that changes.

3. The scalar is display over a partial order. `WaaMismatchGrade` lives in
   `Doctrines`, so this Signature module does not import it; the Signature-side
   checked fact is that `share` is the only contribution value exported by a
   weld.

4. `Models.lean` witnesses are illustrative. The clock and register-clock
   models anchor possibility checks and taxonomy examples; they are not
   uniqueness claims.
-/

namespace WAA

namespace AssumptionLocalWitnesses

/- Direction witness kept local so `Signature.Assumptions` does not import
   downstream `Meta` modules. -/
abbrev DirectionW := RawWeld Unit Bool Unit

def directionFalse : DirectionW := ⟨(), false, ()⟩

def directionTrue : DirectionW := ⟨(), true, ()⟩

def directionForwardGrid : Grid Nat where
  Being      := Unit
  Call       := Bool
  Response   := Unit
  respondsTo _ _ := some ()
  grade _ _ _ := 0
  conditions w₁ w₂ := w₁.call = false ∧ w₂.call = true

def directionBackwardGrid : Grid Nat where
  Being      := Unit
  Call       := Bool
  Response   := Unit
  respondsTo _ _ := some ()
  grade _ _ _ := 0
  conditions w₁ w₂ := w₁.call = true ∧ w₂.call = false

theorem direction_conditionsEither_agrees (w₁ w₂ : DirectionW) :
    directionForwardGrid.ConditionsEither w₁ w₂ ↔
      directionBackwardGrid.ConditionsEither w₁ w₂ :=
  ⟨fun h => h.elim (fun ⟨h1, h2⟩ => Or.inr ⟨h2, h1⟩)
                   (fun ⟨h1, h2⟩ => Or.inl ⟨h2, h1⟩),
   fun h => h.elim (fun ⟨h1, h2⟩ => Or.inr ⟨h2, h1⟩)
                   (fun ⟨h1, h2⟩ => Or.inl ⟨h2, h1⟩)⟩

theorem direction_conditions_disagree :
    directionForwardGrid.conditions directionFalse directionTrue ∧
      ¬ directionBackwardGrid.conditions directionFalse directionTrue := by
  constructor
  · exact ⟨rfl, rfl⟩
  · intro h
    cases h.left

theorem no_direction_recovery_from_conditionsEither :
    ¬ ∃ recover : (DirectionW → DirectionW → Prop) →
        (DirectionW → DirectionW → Prop),
        recover directionForwardGrid.ConditionsEither =
          directionForwardGrid.conditions ∧
        recover directionBackwardGrid.ConditionsEither =
          directionBackwardGrid.conditions := by
  rintro ⟨recover, hf, hb⟩
  have hsame :
      directionForwardGrid.ConditionsEither =
        directionBackwardGrid.ConditionsEither := by
    funext w₁ w₂
    exact propext (direction_conditionsEither_agrees w₁ w₂)
  have hcond :
      directionForwardGrid.conditions = directionBackwardGrid.conditions := by
    rw [← hf, hsame, hb]
  exact direction_conditions_disagree.right
    (hcond ▸ direction_conditions_disagree.left)

open Grid.DirectedConvention.BeingConvention

def partitionGrid : Grid Nat where
  Being      := Bool
  Call       := Unit
  Response   := Unit
  respondsTo _ _ := some ()
  grade _ _ _ := 0
  conditions _ _ := True

def partitionMerge : BeingCoarsening partitionGrid Unit where
  proj _ := ()

def partitionSplit : BeingCoarsening partitionGrid Bool where
  proj := id

theorem partition_merge_split_disagree :
    partitionMerge.SameFiber false true ∧
      ¬ partitionSplit.SameFiber false true := by
  constructor
  · rfl
  · intro h
    cases h

theorem nat_preorderBot_has_no_top :
    ¬ ∃ t : Nat, ∀ x : Nat, x ≼ t := by
  rintro ⟨t, htop⟩
  exact Nat.not_succ_le_self t (htop (Nat.succ t))

theorem signature_self_line_permitted :
    ∃ w : backslideGrid.Weld,
      Grid.DirectedConvention.LandsAt backslideGrid w w := by
  exact ⟨⟨(), Cue.gentle, ()⟩, True.intro, rfl⟩

end AssumptionLocalWitnesses

namespace InteriorDirectionNegative

/-- A one-being carrier where call and response use the same two-point display
    type, so the two faces can be transposed without changing their raw
    unordered content. -/
abbrev W := RawWeld Unit Bool Bool

def callThenResponse : W := ⟨(), false, true⟩

def responseThenCall : W := callThenResponse.transposeCR

/-- The unordered residue of the two faces: either orientation of the same
    false/true pair counts as the same displayed content. -/
def unorderedCRContent (w : W) : Prop :=
  w = callThenResponse ∨ w = responseThenCall

def callResponseReading (w : W) : Prop :=
  w = callThenResponse

def responseCallReading (w : W) : Prop :=
  w = responseThenCall

theorem call_response_readings_disagree :
    callResponseReading callThenResponse ∧
      ¬ responseCallReading callThenResponse := by
  constructor
  · rfl
  · intro h
    cases h

/-- No recovery function from unordered call/response content can determine
    which face is the call. Reading "something arrives, then something
    answers" is already a direction-projection at the smallest grain: by the
    MMK 8 discipline, doer and deed are mutually dependent, neither prior.
    The `RawWeld` field names remain useful display labels, not a recovered
    before-and-after inside the weld. -/
theorem no_interior_direction_recovery :
    ¬ ∃ recover : (W → Prop) → W → Prop,
        recover unorderedCRContent = callResponseReading ∧
        recover unorderedCRContent = responseCallReading := by
  rintro ⟨recover, hcall, hresponse⟩
  have hcallHolds : recover unorderedCRContent callThenResponse := by
    rw [hcall]
    exact call_response_readings_disagree.left
  have hresponseNot : ¬ recover unorderedCRContent callThenResponse := by
    rw [hresponse]
    exact call_response_readings_disagree.right
  exact hresponseNot hcallHolds

end InteriorDirectionNegative

section AssumptionAnchors

variable {Contrib : Type} [PreorderBot Contrib]
variable (G : Grid Contrib)

/- A.1 No prior agent. -/
#check RawWeld -- proof
#check Grid.index -- proof
#check Grid.share -- proof
#check no_agent_recovery_of_field_collision -- witness
example (w : G.Weld) : G.index w = w.agent := rfl -- proof
example (w : G.Weld) :
    G.share w = G.grade w.agent w.call w.response := rfl -- proof

/- A.2 Nothing self-indexed is stored. -/
#check Config -- proof
#check Config.tendency -- proof
#check Grid.rePitch -- proof
example (c : Config Contrib) : c = ⟨c.tendency⟩ := rfl -- proof
example (before before' : Config Contrib) (received : G.Weld) :
    G.rePitch before received = G.rePitch before' received := rfl -- proof
example (before : Config Contrib) (received : G.Weld) :
    (G.rePitch before received).tendency = G.share received := rfl -- proof

/- A.3 Self-pole index as live share. -/
#check Grid.HasSelfPoleIndex -- proof
#check Grid.selfPoleIndex_eq_agent_of_hasSelfPoleIndex -- proof
#check Grid.no_self_pole_index_of_atBot -- proof
example (w : G.Weld) :
    G.HasSelfPoleIndex w ↔ ¬ AtBot (G.share w) := Iff.rfl -- proof
example (w : G.Weld) (h : G.HasSelfPoleIndex w) :
    G.selfPoleIndex w h = G.index w := rfl -- proof

/- A.4 Stone / terminus function-share split. -/
#check Grid.Stone -- proof
#check Grid.Terminus -- proof
#check Grid.AtPoleClass -- proof
#check Grid.stone_is_terminus_vacuously -- proof
#check clockGrid_function_share_split_witness -- witness

/- A.5 Self-lines are permitted. -/
#check Grid.conditions -- proof
#check Grid.DirectedConvention.DeliveredTo -- proof
#check Grid.DirectedConvention.LandsAt -- proof
#check AssumptionLocalWitnesses.signature_self_line_permitted -- witness
-- TODO(assumptions): `SelfLineWitness` is currently downstream in
-- `Identification.Ownership`; keep this Signature-local witness unless that
-- witness is moved into the Signature layer.

/- B.1 No arrow in conditions. -/
#check Grid.ConditionsEither -- proof
#check Grid.conditionsEither_symm -- proof
#check Grid.DirectedConvention.TimeDirection -- proof
#check Grid.transpose -- witness
#check Grid.transpose_conditionsEither_iff -- witness
#check Grid.DirectedConvention.transpose_deliveredTo_iff -- witness
#check RawWeld.transposeCR -- witness
#check AssumptionLocalWitnesses.no_direction_recovery_from_conditionsEither -- witness
#check InteriorDirectionNegative.no_interior_direction_recovery -- witness
-- TODO(assumptions): The fuller named witness is
-- `DirectionNegative.no_direction_recovery_from_conditionsEither` downstream in
-- `Meta.InvarianceNegative`; importing it here would violate the layer DAG.

/- B.2 No PreorderTop. -/
#check PreorderBot -- proof
#check AtBot -- proof
#check Grid.DirectedConvention.BeingConvention.BeingCoarsening.StrongSelfConditioningTag -- comment
#check AssumptionLocalWitnesses.nat_preorderBot_has_no_top -- witness

/- B.3 No privileged person-partition. -/
#check Grid.DirectedConvention.BeingConvention.BeingCoarsening -- proof
#check Grid.DirectedConvention.BeingConvention.BeingCoarsening.InFiber -- proof
#check Grid.DirectedConvention.BeingConvention.BeingCoarsening.SameFiber -- proof
#check Grid.DirectedConvention.BeingConvention.BeingCoarsening.id -- witness
#check Grid.DirectedConvention.BeingConvention.BeingCoarsening.total -- witness
#check Grid.DirectedConvention.BeingConvention.BeingCoarsening.total_sameFiber -- witness
#check Grid.DirectedConvention.BeingConvention.BeingCoarsening.id_not_sameFiber_of_ne -- witness
#check AssumptionLocalWitnesses.partition_merge_split_disagree -- witness
-- The fuller non-recovery certificate remains
-- `BeingNegative.no_partition_recovery` downstream in `Meta.InvarianceNegative`;
-- importing it here would violate the layer DAG.

/- B.4 Direction resolution is display, not signature furniture. -/
#check Grid.DirectedConvention.DirectionCoarsening -- proof
#check Grid.DirectedConvention.DirectionCoarsening.SameTick -- proof
#check Grid.DirectedConvention.DirectionCoarsening.ResolutionBounded -- proof
#check Grid.DirectedConvention.DirectionCoarsening.no_timeDirection_within_tick -- proof
#check Grid.DirectedConvention.DirectionCoarsening.no_timeDirection_of_resolutionBounded_subsingleton -- proof
#check Grid.DirectedConvention.DirectionCoarsening.transpose_subTickDelivery -- witness
-- TODO(assumptions): The register-clock direction-coarsening witnesses live
-- downstream in `Meta.InvarianceNegative.DirectionCoarseningWitness`; importing
-- them here would violate the layer DAG.

/- B.5 Contribution values are display, not operational tokens. -/
#check Grid.share_eq_grade_check -- proof
#check AtBot -- proof
#check OrderEq -- proof
#check Grid.Terminus -- proof
-- TODO(assumptions): `DisplayReparam`, `DisplayReparam.atBot_iff`, and
-- `InvarianceNegative.oldEqTerminus_not_invariant` live downstream in `Meta`.
-- This Signature module anchors only the order/pole vocabulary they transport.

/- C.1 Hand-rolled order classes. -/
#check Preorder -- proof
#check PreorderBot -- proof
#check shareBot -- proof
#check shareBot_le -- proof

/- C.2 `_before` is retained but currently ignored by `rePitch`. -/
#check Grid.rePitch -- proof
example (before before' : Config Contrib) (received : G.Weld) :
    G.rePitch before received = G.rePitch before' received := rfl -- proof

/- C.3 Scalar display over partial order. -/
#check Grid.share -- proof
#check Grid.share_eq_grade_check -- proof
-- TODO(assumptions): `WaaMismatchGrade` lives in `Doctrines.FourTruths`; this
-- file cannot import it while remaining in the Signature layer.

/- C.4 Model witnesses are illustrative. -/
#check clockGrid -- witness
#check registerClockGrid -- witness
#check registerClock_macro_sentient -- witness
#check registerClock_macro_selfConditioning -- witness

/--
info: 'WAA.no_agent_recovery_of_field_collision' does not depend on any axioms
-/
#guard_msgs in
#print axioms no_agent_recovery_of_field_collision

/--
info: 'WAA.Grid.DirectedConvention.DirectionCoarsening.no_timeDirection_within_tick' does not depend on any axioms
-/
#guard_msgs in
#print axioms Grid.DirectedConvention.DirectionCoarsening.no_timeDirection_within_tick

/--
info: 'WAA.Grid.DirectedConvention.DirectionCoarsening.no_timeDirection_of_resolutionBounded_subsingleton' does not depend on any axioms
-/
#guard_msgs in
#print axioms Grid.DirectedConvention.DirectionCoarsening.no_timeDirection_of_resolutionBounded_subsingleton

end AssumptionAnchors

end WAA
