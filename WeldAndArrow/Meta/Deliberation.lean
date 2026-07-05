/-
================================================================================
  WeldAndArrow.Meta.Deliberation
  Consequentialist display and deliberator-side underdetermination
================================================================================

This module records the checked face of the deliberator block: drop-counting as
a reading, the non-accumulation consequence of `rePitch`, the being-boundary and
transfer countermodels, invariance of grade under delivery conditions, and a
claim-language witness for delivery-arrogation.

Reading and motivation: Identification/Commentary.lean, C.5.
-/

import WeldAndArrow.Meta.Invariance

namespace WAA

namespace Grid

variable {Contrib : Type} [PreorderBot Contrib]
variable (G : Grid Contrib)

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

/-- Changing only `conditions` cannot change the grade assigned to a mounted
    response. -/
theorem grade_independent_of_conditions
    (conditions₁ conditions₂ : G.Weld -> G.Weld -> Prop)
    (b : G.Being) (c : G.Call) (r : G.Response) :
    (G.withConditions conditions₁).grade b c r =
      (G.withConditions conditions₂).grade b c r :=
  rfl

/-- The same check at the weld/share projection. -/
theorem share_independent_of_conditions
    (conditions₁ conditions₂ : G.Weld -> G.Weld -> Prop) (w : G.Weld) :
    (G.withConditions conditions₁).share w =
      (G.withConditions conditions₂).share w :=
  rfl

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
   Consequentialist convention: descriptive readings only
============================================================================== -/

namespace ConsequentialistConvention

open DirectedConvention.BeingConvention

/-- The deliberator's finite sample: an initial configuration and a finite list
    of actual receptions. No measure, utility, probability, or command over
    delivery is added. -/
structure DeliberationSample (G : Grid Contrib) where
  before : Config Contrib
  run    : List (ActualWeld G)

/-- A descriptive objective candidate. Its domain is explicit so that further
    conventions have to be supplied as arguments rather than recovered from the
    grid. -/
abbrev Objective (G : Grid Contrib) (Convention Value : Type) :=
  DeliberationSample G -> Convention -> Value

/-- Count share-drop receptions through a finite actual run, re-pitching after
    every reception. -/
def DropCount
    [∀ before received, Decidable (G.IsShareDrop before received)]
    (before : Config Contrib) : List (ActualWeld G) -> Nat
  | [] => 0
  | aw :: rest =>
      let after := G.rePitch before aw.weld
      let tail := DropCount after rest
      if G.IsShareDrop before aw.weld then tail + 1 else tail

/-- The same count restricted by a supplied being-coarsening. The run still
    re-pitches at every actual reception; only the counted events are filtered
    by the convention. -/
def DropCountInFiber
    [∀ before received, Decidable (G.IsShareDrop before received)]
    {Macro : Type} (κ : BeingCoarsening G Macro)
    [∀ b w, Decidable (κ.InFiber b w)]
    (b : Macro)
    (before : Config Contrib) : List (ActualWeld G) -> Nat
  | [] => 0
  | aw :: rest =>
      let after := G.rePitch before aw.weld
      let tail := DropCountInFiber κ b after rest
      if κ.InFiber b aw.weld then
        if G.IsShareDrop before aw.weld then tail + 1 else tail
      else tail

/-- Claim object for a plan that treats delivery as commanded: this deed's
    fruit is asserted to land at that reception. -/
structure DeliveryCommand (G : Grid Contrib) where
  deed      : G.Weld
  reception : G.Weld

/-- A tiny object language for delivery-command claims. It makes such claims
    satisfiable only where the field-side delivery relation holds. -/
def deliveryCommandLanguage (G : Grid Contrib) : ClaimLanguage G where
  Claim := DeliveryCommand G
  Holds := fun _ claim => DirectedConvention.DeliveredTo G claim.deed claim.reception

/-- A recorded delivery-command utterance fits its offered tier only when the
    commanded delivery is in fact delivered. -/
theorem deliveryCommand_unfit_of_not_delivered
    (u : RecordedUtterance G (deliveryCommandLanguage G))
    (hnot : ¬ DirectedConvention.DeliveredTo G u.content.deed u.content.reception) :
    ¬ u.FitsOfferedTier := by
  intro hfit
  change (deliveryCommandLanguage G).TrueAt u.offeredAt u.content at hfit
  dsimp [deliveryCommandLanguage, ClaimLanguage.TrueAt] at hfit
  exact hnot hfit

end ConsequentialistConvention

end Grid

namespace AccumulationNegative

/-- Named face of `Grid.rePitch_forgets` for the deliberator block. -/
theorem rePitch_forgets
    {Contrib : Type} [PreorderBot Contrib] (G : Grid Contrib)
    (before₁ before₂ : Config Contrib) (received : G.Weld) :
    G.rePitch before₁ received = G.rePitch before₂ received :=
  Grid.rePitch_forgets G before₁ before₂ received

/-- Named face of the no-accumulation corollary for run-valued scores that
    factor through `Config`. -/
theorem accumulated_attainment_constant_of_same_final
    {Contrib α : Type} [PreorderBot Contrib] (G : Grid Contrib)
    (score : Config Contrib -> α)
    (before₁ before₂ : Config Contrib) (received : G.Weld) :
    score (G.rePitch before₁ received) =
      score (G.rePitch before₂ received) :=
  Grid.accumulated_attainment_constant_of_same_final
    G score before₁ before₂ received

end AccumulationNegative

/- ==============================================================================
   Objective negative: "my drops" requires a supplied being-convention
============================================================================== -/

namespace ObjectiveNegative

open Grid
open Grid.ConsequentialistConvention
open Grid.DirectedConvention.BeingConvention

/-- Two fine tags with different live shares. Merging or splitting them is still
    a diagnosis-time convention; the grid itself carries no macro owner. -/
def objectiveGrid : Grid Nat where
  Being      := Bool
  Call       := Unit
  Response   := Unit
  respondsTo _ _ := some ()
  grade b _ _ :=
    match b with
    | false => 2
    | true  => 1
  conditions _ _ := True

instance objectiveGrid_isShareDrop_decidable
    (before : Config Nat) (received : objectiveGrid.Weld) :
    Decidable (objectiveGrid.IsShareDrop before received) := by
  cases received with
  | mk agent _ _ =>
      cases agent
      · dsimp [Grid.IsShareDrop, Grid.share, objectiveGrid, Strict]
        change Decidable (((2 : Nat) ≤ before.tendency) ∧ ¬ before.tendency ≤ (2 : Nat))
        infer_instance
      · dsimp [Grid.IsShareDrop, Grid.share, objectiveGrid, Strict]
        change Decidable (((1 : Nat) ≤ before.tendency) ∧ ¬ before.tendency ≤ (1 : Nat))
        infer_instance

def mergeCoarsening : BeingCoarsening objectiveGrid Unit where
  proj _ := ()

def splitCoarsening : BeingCoarsening objectiveGrid Bool where
  proj := id

instance mergeCoarsening_inFiber_decidable
    (b : Unit) (w : objectiveGrid.Weld) :
    Decidable (mergeCoarsening.InFiber b w) := by
  dsimp [Grid.DirectedConvention.BeingConvention.BeingCoarsening.InFiber,
    mergeCoarsening]
  infer_instance

instance splitCoarsening_inFiber_decidable
    (b : Bool) (w : objectiveGrid.Weld) :
    Decidable (splitCoarsening.InFiber b w) := by
  dsimp [Grid.DirectedConvention.BeingConvention.BeingCoarsening.InFiber,
    splitCoarsening]
  infer_instance

def wFalse : objectiveGrid.Weld := ⟨false, (), ()⟩

def wTrue : objectiveGrid.Weld := ⟨true, (), ()⟩

def before : Config Nat := { tendency := 3 }

def run : List (ActualWeld objectiveGrid) := [
  { weld := wFalse, actual := rfl },
  { weld := wTrue, actual := rfl } ]

def mergedDropCount : Nat :=
  DropCountInFiber objectiveGrid mergeCoarsening () before run

def splitFalseDropCount : Nat :=
  DropCountInFiber objectiveGrid splitCoarsening false before run

def splitTrueDropCount : Nat :=
  DropCountInFiber objectiveGrid splitCoarsening true before run

theorem merge_dropCount :
    mergedDropCount = 2 := by
  decide

theorem split_false_dropCount :
    splitFalseDropCount = 1 := by
  decide

theorem split_true_dropCount :
    splitTrueDropCount = 1 := by
  decide

/-- The same finite run receives different "my drops" counts under different
    legal being conventions. -/
theorem fiber_dropCounts_differ :
    mergedDropCount ≠ splitFalseDropCount := by
  decide

abbrev W := RawWeld Bool Unit Unit

/-- The grid data visible to a convention-free recovery function. -/
abbrev GridData : Type :=
  (Bool -> Unit -> Option Unit) ×
    (Bool -> Unit -> Unit -> Nat) ×
      (W -> W -> Prop)

def gridData : GridData :=
  (objectiveGrid.respondsTo, objectiveGrid.grade, objectiveGrid.conditions)

/-- No convention-free function of the same grid data can return both legal
    "my drop" readings. -/
theorem no_grid_data_objective_for_my_drops :
    ¬ ∃ recover : GridData -> Nat,
        recover gridData = mergedDropCount ∧
        recover gridData = splitFalseDropCount := by
  rintro ⟨_recover, hmerge, hsplit⟩
  exact fiber_dropCounts_differ (hmerge.symm.trans hsplit)

end ObjectiveNegative

/- ==============================================================================
   Transfer negative: track records underdetermine adaptive landing
============================================================================== -/

namespace TransferNegative

inductive Teacher
  | teacher
deriving DecidableEq

inductive Call
  | seen
  | fresh
deriving DecidableEq

inductive Response
  | track
  | lands
  | misses
deriving DecidableEq

def trackClass : Call -> Prop
  | .seen  => True
  | .fresh => False

def landingGrid : Grid Nat where
  Being      := Teacher
  Call       := Call
  Response   := Response
  respondsTo _ c :=
    match c with
    | .seen  => some .track
    | .fresh => some .lands
  grade _ c _ :=
    match c with
    | .seen  => 5
    | .fresh => 0
  conditions _ _ := True

def missingGrid : Grid Nat where
  Being      := Teacher
  Call       := Call
  Response   := Response
  respondsTo _ c :=
    match c with
    | .seen  => some .track
    | .fresh => some .misses
  grade _ c _ :=
    match c with
    | .seen  => 5
    | .fresh => 1
  conditions _ _ := True

/-- The restricted track record: response and grade behavior on the seen call. -/
abbrev TrackData : Type := Option Response × (Response -> Nat)

def landingTrackData : TrackData :=
  (landingGrid.respondsTo Teacher.teacher Call.seen,
    fun r => landingGrid.grade Teacher.teacher Call.seen r)

def missingTrackData : TrackData :=
  (missingGrid.respondsTo Teacher.teacher Call.seen,
    fun r => missingGrid.grade Teacher.teacher Call.seen r)

theorem restricted_track_agrees :
    landingTrackData = missingTrackData :=
  rfl

theorem respondsTo_agrees_on_trackClass
    {c : Call} (hc : trackClass c) :
    landingGrid.respondsTo Teacher.teacher c =
      missingGrid.respondsTo Teacher.teacher c := by
  cases c with
  | seen =>
      rfl
  | fresh =>
      cases hc

theorem grade_agrees_on_trackClass
    {c : Call} (hc : trackClass c) (r : Response) :
    landingGrid.grade Teacher.teacher c r =
      missingGrid.grade Teacher.teacher c r := by
  cases c with
  | seen =>
      rfl
  | fresh =>
      cases hc

def landingFreshEffect : Nat :=
  landingGrid.grade Teacher.teacher Call.fresh Response.lands

def missingFreshEffect : Nat :=
  missingGrid.grade Teacher.teacher Call.fresh Response.misses

theorem fresh_effect_disagrees :
    landingFreshEffect ≠ missingFreshEffect := by
  decide

theorem landing_adaptive :
    landingGrid.ResponseVariesWithCall Teacher.teacher := by
  refine ⟨Call.seen, Call.fresh, Response.track, Response.lands, rfl, rfl, ?_⟩
  intro h
  cases h

theorem missing_adaptive :
    missingGrid.ResponseVariesWithCall Teacher.teacher := by
  refine ⟨Call.seen, Call.fresh, Response.track, Response.misses, rfl, rfl, ?_⟩
  intro h
  cases h

/-- Agreement on the teacher's whole seen track record does not determine the
    fresh-call effect for adaptive responders. -/
theorem no_estimator_from_restricted_track :
    ¬ ∃ estimate : TrackData -> Nat,
        estimate landingTrackData = landingFreshEffect ∧
        estimate missingTrackData = missingFreshEffect := by
  rintro ⟨estimate, hlanding, hmissing⟩
  have heq : landingFreshEffect = missingFreshEffect := by
    calc
      landingFreshEffect = estimate landingTrackData := hlanding.symm
      _ = estimate missingTrackData := congrArg estimate restricted_track_agrees
      _ = missingFreshEffect := hmissing
  exact fresh_effect_disagrees heq

theorem adaptive_track_record_underdetermines_new_effect :
    landingGrid.ResponseVariesWithCall Teacher.teacher ∧
      missingGrid.ResponseVariesWithCall Teacher.teacher ∧
      landingTrackData = missingTrackData ∧
      landingFreshEffect ≠ missingFreshEffect ∧
      ¬ ∃ estimate : TrackData -> Nat,
          estimate landingTrackData = landingFreshEffect ∧
          estimate missingTrackData = missingFreshEffect :=
  ⟨landing_adaptive, missing_adaptive, restricted_track_agrees,
    fresh_effect_disagrees, no_estimator_from_restricted_track⟩

/-- In the invariant/static case, any mounted fresh-call response is the same
    response already seen in the restricted record. This is the contrast case:
    transfer holds exactly where response-adaptivity is absent. -/
theorem responseInvariant_determines_response
    {Contrib : Type} [PreorderBot Contrib] {G : Grid Contrib}
    {b : G.Being} {seen fresh : G.Call} {rSeen rFresh : G.Response}
    (h : G.ResponseInvariant b)
    (hseen : G.respondsTo b seen = some rSeen)
    (hfresh : G.respondsTo b fresh = some rFresh) :
    rFresh = rSeen :=
  h fresh seen rFresh rSeen hfresh hseen

def staticGrid : Grid Nat where
  Being      := Teacher
  Call       := Call
  Response   := Response
  respondsTo _ _ := some Response.track
  grade _ _ _ := 5
  conditions _ _ := True

theorem static_responseInvariant :
    staticGrid.ResponseInvariant Teacher.teacher := by
  intro _c₁ _c₂ _r₁ _r₂ h₁ h₂
  cases h₁
  cases h₂
  rfl

theorem static_fresh_response_determined :
    Response.track = Response.track :=
  responseInvariant_determines_response
    (G := staticGrid) (b := Teacher.teacher)
    (seen := Call.seen) (fresh := Call.fresh)
    (rSeen := Response.track) (rFresh := Response.track)
    static_responseInvariant rfl rfl

end TransferNegative

/- ==============================================================================
   Delivery-arrogation negative: a command is quotable, not satisfiable
============================================================================== -/

namespace DeliveryArrogationNegative

open Grid
open Grid.ConsequentialistConvention

inductive Being
  | planner
deriving DecidableEq

inductive Call
  | deed
  | fruit
deriving DecidableEq

inductive Response
  | utter
deriving DecidableEq

def commandGrid : Grid Nat where
  Being      := Being
  Call       := Call
  Response   := Response
  respondsTo _ _ := some Response.utter
  grade _ _ _ := 1
  conditions _ _ := False

def deed : commandGrid.Weld :=
  ⟨Being.planner, Call.deed, Response.utter⟩

def reception : commandGrid.Weld :=
  ⟨Being.planner, Call.fruit, Response.utter⟩

def commandUtterance :
    RecordedUtterance commandGrid (deliveryCommandLanguage commandGrid) where
  weld      := deed
  actual    := rfl
  offeredAt := Tier.actTime deed
  content   := { deed := deed, reception := reception }

theorem command_not_delivered :
    ¬ DirectedConvention.DeliveredTo commandGrid deed reception := by
  intro h
  cases h

theorem command_utterance_not_fits :
    ¬ commandUtterance.FitsOfferedTier :=
  deliveryCommand_unfit_of_not_delivered
    (G := commandGrid) commandUtterance command_not_delivered

theorem command_utterance_is_quotable :
    commandUtterance.answersCall = Call.deed ∧
      ¬ commandUtterance.FitsOfferedTier :=
  ⟨rfl, command_utterance_not_fits⟩

end DeliveryArrogationNegative

end WAA
