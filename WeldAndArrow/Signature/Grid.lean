/-
================================================================================
  WeldAndArrow.Signature.Grid
  Primitive grid signature and directed-convention primitives
================================================================================

Reading and motivation: Identification/Commentary.lean, C.1.
-/

import WeldAndArrow.Signature.Order

namespace WAA

/- Reading and motivation: Identification/Commentary.lean, C.1. -/
@[ext]
structure RawWeld (Being Call Response : Type) where
  agent    : Being
  call     : Call
  response : Response

/-- The whole signature, bundled. -/
structure Grid (Contrib : Type) [PreorderBot Contrib] where
  /- Reading and motivation: Identification/Commentary.lean, C.1. -/
  Being      : Type
  /-- The input component of an occurrence. -/
  Call       : Type
  /-- what a mounted response produces. -/
  Response   : Type
  /- Reading and motivation: Identification/Commentary.lean, C.1. -/
  respondsTo : Being → Call → Option Response
  /-- The contribution value assigned to a mounted response. -/
  grade      : Being → Call → Response → Contrib
  /- Reading and motivation: Identification/Commentary.lean, C.1. -/
  conditions : RawWeld Being Call Response → RawWeld Being Call Response → Prop

namespace Grid

variable {Contrib : Type} [PreorderBot Contrib]

/-- Shorthand: an occurrence for a specific `Grid`. -/
abbrev Weld (G : Grid Contrib) := RawWeld G.Being G.Call G.Response

variable (G : Grid Contrib)

/-- A weld is *actual* when it witnesses something the being in fact does.
    Self-anchoring is enforced structurally, not by a fancier dependent
    index type: nothing in this file ever produces a `Being` "as an
    index" except by first supplying a `Weld` whose `response` is
    witnessed here. There is no route from `Config` (§2) or from
    field-facts alone to an `Actual` weld — see `no_agent_recovery_of_field_collision`
    in the Preview section for the internal version of that claim. -/
def Actual (w : G.Weld) : Prop := G.respondsTo w.agent w.call = some w.response

/-- The agent-index — token-reflexive because it is nothing but a
    projection out of the very weld that carries it: there is no route to
    "this act's agent" that does not pass through a completed `Weld`. -/
def index (w : G.Weld) : G.Being := w.agent

/- Reading and motivation: Identification/Commentary.lean, C.1. -/
def share (w : G.Weld) : Contrib := G.grade w.agent w.call w.response

/-- Whether this occurrence makes a live self-pole index. The raw
    `index` projection above is still useful as the causal-series tag of a
    weld; this predicate is the theorem-facing notion that disappears at
    the pole-class. -/
def HasSelfPoleIndex (w : G.Weld) : Prop := ¬ AtBot (G.share w)

/- Reading and motivation: Identification/Commentary.lean, C.1. -/
def selfPoleIndex (w : G.Weld) (_h : G.HasSelfPoleIndex w) : G.Being := w.agent

/-- A live self-pole index gives a strict contribution witness above the
    designated bottom. -/
theorem strict_shareBot_of_hasSelfPoleIndex (w : G.Weld)
    (h : G.HasSelfPoleIndex w) :
    Strict (shareBot : Contrib) (G.share w) :=
  ⟨shareBot_le (G.share w), h⟩

/- Reading and motivation: Identification/Commentary.lean, C.1. -/
def WaaAppropriates (reception : G.Weld) : Prop := G.HasSelfPoleIndex reception

/-- At the pole-class, no self-pole index is live. -/
theorem no_self_pole_index_of_atBot (w : G.Weld) (h : AtBot (G.share w)) :
    ¬ G.HasSelfPoleIndex w :=
  fun hidx => hidx h

/-- Literal equality with the designated bottom is a thin bridge into the
    order-class pole vocabulary. -/
theorem no_self_pole_index_of_eq_shareBot
    (w : G.Weld) (h : G.share w = shareBot) :
    ¬ G.HasSelfPoleIndex w :=
  G.no_self_pole_index_of_atBot w (atBot_of_eq_shareBot h)

/-- The evidence-carried index is the agent tag when the self-pole is live. -/
theorem selfPoleIndex_eq_agent_of_hasSelfPoleIndex
    (w : G.Weld) (h : G.HasSelfPoleIndex w) :
    G.selfPoleIndex w h = w.agent := rfl

/-- At the pole-class there is no WAA-appropriation. -/
theorem not_waaAppropriates_of_atBot (w : G.Weld) (h : AtBot (G.share w)) :
    ¬ G.WaaAppropriates w :=
  G.no_self_pole_index_of_atBot w h

/-- Literal equality with the designated bottom rules out WAA-appropriation
    by first entering the pole-class. -/
theorem not_waaAppropriates_of_eq_shareBot
    (w : G.Weld) (h : G.share w = shareBot) :
    ¬ G.WaaAppropriates w :=
  G.not_waaAppropriates_of_atBot w (atBot_of_eq_shareBot h)

/- Reading and motivation: Identification/Commentary.lean, C.1. -/
theorem share_eq_grade_check (w : G.Weld) :
    G.share w = G.grade w.agent w.call w.response := rfl

/- Reading and motivation: Identification/Commentary.lean, C.1. -/
def ProbeConstant (b : G.Being) (cs : G.Call → Prop) : Prop :=
  ∀ c₁ c₂, cs c₁ → cs c₂ →
    ∀ r₁ r₂, G.respondsTo b c₁ = some r₁ → G.respondsTo b c₂ = some r₂ →
      OrderEq (G.grade b c₁ r₁) (G.grade b c₂ r₂)

/- Reading and motivation: Identification/Commentary.lean, C.1. -/

/-- Mounting a response at all — the subject-function. Phrased with an
    existential rather than `Option.isSome` so this stays `Prop`-valued
    without leaning on the `Bool → Prop` coercion. -/
def MountsAt (b : G.Being) (c : G.Call) : Prop := ∃ r, G.respondsTo b c = some r

/-- A being that mounts some response somewhere. This is the weakest
    positive-function predicate, useful for separating a live responder from
    a stone without requiring total response to every call. -/
def MountsSomewhere (b : G.Being) : Prop := ∃ c, G.MountsAt b c

/-- Function-entire in the formal sense: every call in the model receives
    some response. Downstream files can weaken this to a regime-indexed
    version when modelling deaf-blind limits or partial delivery. -/
def RespondsToEveryCall (b : G.Being) : Prop := ∀ c, G.MountsAt b c

/- Reading and motivation: Identification/Commentary.lean, C.1. -/
def Stone (b : G.Being) : Prop := ∀ c, ¬ G.MountsAt b c

/- Reading and motivation: Identification/Commentary.lean, C.1. -/
def AllStone : Prop := ∀ b : G.Being, G.Stone b

/- Reading and motivation: Identification/Commentary.lean, C.1. -/
def Terminus (b : G.Being) : Prop :=
  ∀ c r, G.respondsTo b c = some r → AtBot (G.grade b c r)

/-- The non-vacuous terminus: function is present somewhere and every
    mounted response is at the pole-class. This is often the right formal analogue
    of the "responsive stone" when the model's call-domain is intentionally
    sparse. -/
def LiveTerminus (b : G.Being) : Prop := G.MountsSomewhere b ∧ G.Terminus b

/- Reading and motivation: Identification/Commentary.lean, C.1. -/
def ResponsiveTerminus (b : G.Being) : Prop :=
  G.RespondsToEveryCall b ∧ G.Terminus b

/-- A response by a terminus-typed being lies in the pole-class. -/
theorem atBot_of_terminus_response
    {b : G.Being} {c : G.Call} {r : G.Response}
    (hterm : G.Terminus b) (hresp : G.respondsTo b c = some r) :
    AtBot (G.share ⟨b, c, r⟩) :=
  hterm c r hresp

/-- A terminus response carries no self-pole index. -/
theorem no_self_pole_index_of_terminus_response
    {b : G.Being} {c : G.Call} {r : G.Response}
    (hterm : G.Terminus b) (hresp : G.respondsTo b c = some r) :
    ¬ G.HasSelfPoleIndex ⟨b, c, r⟩ :=
  G.no_self_pole_index_of_atBot ⟨b, c, r⟩
    (G.atBot_of_terminus_response hterm hresp)

/-- A terminus response does not WAA-appropriate. -/
theorem not_waaAppropriates_of_terminus_response
    {b : G.Being} {c : G.Call} {r : G.Response}
    (hterm : G.Terminus b) (hresp : G.respondsTo b c = some r) :
    ¬ G.WaaAppropriates ⟨b, c, r⟩ :=
  G.not_waaAppropriates_of_atBot ⟨b, c, r⟩
    (G.atBot_of_terminus_response hterm hresp)

/- Reading and motivation: Identification/Commentary.lean, C.1. -/
def AtPoleClass (b : G.Being) : Prop := G.Stone b ∨ G.Terminus b

/- Reading and motivation: Identification/Commentary.lean, C.1. -/
theorem stone_is_terminus_vacuously (b : G.Being) (h : G.Stone b) : G.Terminus b :=
  fun c r hr => absurd ⟨r, hr⟩ (h c)

/-- Positive function at even one call rules out stone-typing. -/
theorem not_stone_of_mountsSomewhere (b : G.Being) (h : G.MountsSomewhere b) :
    ¬ G.Stone b :=
  fun hs => h.elim (fun c hc => hs c hc)

/-- A live terminus is not a stone. -/
theorem liveTerminus_not_stone (b : G.Being) (h : G.LiveTerminus b) :
    ¬ G.Stone b :=
  G.not_stone_of_mountsSomewhere b h.left

/-- A responsive terminus is live whenever the call-domain has a witness. -/
theorem responsiveTerminus_live_of_call
    (b : G.Being) (c : G.Call) (h : G.ResponsiveTerminus b) :
    G.LiveTerminus b :=
  ⟨⟨c, h.left c⟩, h.right⟩

end Grid

/- Reading and motivation: Identification/Commentary.lean, C.1. -/

/-- A carried contribution tendency. It stores no weld or being component. -/
@[ext]
structure Config (Contrib : Type) where
  tendency : Contrib

namespace Grid

variable {Contrib : Type} [PreorderBot Contrib] (G : Grid Contrib)

/- Reading and motivation: Identification/Commentary.lean, C.1. -/
def rePitch (_before : Config Contrib) (received : G.Weld) : Config Contrib :=
  { tendency := G.share received }

/- Reading and motivation: Identification/Commentary.lean, C.1. -/
def IsShareDrop (before : Config Contrib) (received : G.Weld) : Prop :=
  Strict (G.share received) before.tendency

/- Reading and motivation: Identification/Commentary.lean, C.1. -/

/- --------------------------------------------------------------------------
   Delivery structure and symmetric closure
-------------------------------------------------------------------------- -/

/- Reading and motivation: Identification/Commentary.lean, C.1. -/
def ConditionsEither (w₁ w₂ : G.Weld) : Prop :=
  G.conditions w₁ w₂ ∨ G.conditions w₂ w₁

/-- Symmetry, definitional to the closure. -/
theorem conditionsEither_symm {w₁ w₂ : G.Weld} (h : G.ConditionsEither w₁ w₂) :
    G.ConditionsEither w₂ w₁ :=
  h.elim Or.inr Or.inl

/-- Reflexive-transitive closure of `ConditionsEither`. -/
inductive ConditionsEitherChain : G.Weld → G.Weld → Prop
  | refl (w : G.Weld) : ConditionsEitherChain w w
  | step {w₁ w₂ w₃ : G.Weld} :
      G.ConditionsEither w₁ w₂ →
      ConditionsEitherChain w₂ w₃ →
      ConditionsEitherChain w₁ w₃

namespace DirectedConvention

/-- The strictness relation, exposed under the name used by this namespace. -/
abbrev TimeDirection {α : Type} [Preorder α] (a b : α) : Prop := Strict a b

/-- Re-rooted arrow reading of the neutral bottom-to-live-share witness. -/
theorem timeDirection_of_hasSelfPoleIndex
    (w : G.Weld) (h : G.HasSelfPoleIndex w) :
    TimeDirection (shareBot : Contrib) (G.share w) :=
  G.strict_shareBot_of_hasSelfPoleIndex w h

/- Reading and motivation: Identification/Commentary.lean, C.1. -/

/- --------------------------------------------------------------------------
   The reception-weld: reach-back
-------------------------------------------------------------------------- -/

/- Reading and motivation: Identification/Commentary.lean, C.1. -/
def WaaReachBackFull (deed reception : G.Weld) : Prop := G.conditions deed reception

/- Reading and motivation: Identification/Commentary.lean, C.1. -/

/-- A delivery-line from one occurrence to another, stated in field
    vocabulary. This is definitionally the same relation as
    `WaaReachBackFull`; the different name is for theorem statements where the
    field-side role matters more than the reception-side appropriation. -/
def DeliveredTo (deed reception : G.Weld) : Prop := G.conditions deed reception

/-- Non-delivery: the relation does not hold from this deed to this reception. -/
def NotDeliveredTo (deed reception : G.Weld) : Prop := ¬ G.conditions deed reception

/-- When a concrete model gives a decision procedure for delivery, delivery
    or non-delivery is exhaustive. Abstractly, the theory keeps only the
    predicates: asserting this disjunction for every proposition would be
    excluded middle. -/
theorem deliveredTo_or_not (deed reception : G.Weld)
    [hdec : Decidable (G.conditions deed reception)] :
    DeliveredTo G deed reception ∨ NotDeliveredTo G deed reception :=
  match hdec with
  | isTrue h => Or.inl h
  | isFalse h => Or.inr h

/-- A fruit has landed when delivery reaches an actual reception. -/
def LandsAt (deed reception : G.Weld) : Prop :=
  DeliveredTo G deed reception ∧ G.Actual reception

/-- Object-axis standing: the occurrence is available to be received
    somewhere. No self-pole index is implied for the occurrence pointed at. -/
def ObjectAxisStanding (deed : G.Weld) : Prop := ∃ reception, DeliveredTo G deed reception

/- Reading and motivation: Identification/Commentary.lean, C.1. -/
def LandsWithShareDrop
    (before : Config Contrib) (deed reception : G.Weld) : Prop :=
  LandsAt G deed reception ∧ G.IsShareDrop before reception

/- Reading and motivation: Identification/Commentary.lean, C.1. -/
def HasShareDropLanding (before : Config Contrib) (deed : G.Weld) : Prop :=
  ∃ reception, LandsWithShareDrop G before deed reception

/- Reading and motivation: Identification/Commentary.lean, C.1. -/

/- Reading and motivation: Identification/Commentary.lean, C.1. -/

/-- A standing line of the web incident on a being: an actual deed that
    the field delivers to one of the being's candidate receptions. The
    reception need NOT be actual — the lens reads over the family of
    receptions the being might make (the same hypothetical variation
    `RawWeld` is closed under for the probe). Field-side and tenseless:
    a relational fact of the web, never a potency carried by the being. -/
def EnvironsLine (b : G.Being) (deed reception : G.Weld) : Prop :=
  G.Actual deed ∧ reception.agent = b ∧ G.conditions deed reception

/- Reading and motivation: Identification/Commentary.lean, C.1. -/
def ShareDropLine
    (before : Config Contrib) (b : G.Being) (deed reception : G.Weld) : Prop :=
  EnvironsLine G b deed reception ∧ G.IsShareDrop before reception

end DirectedConvention

/-- A fixed/static responder gives the same response whenever it responds.
    This is only the response-shape; a clock that never responds to the
    listener at all is still handled by `Stone`. -/
def ResponseInvariant (b : G.Being) : Prop :=
  ∀ c₁ c₂ r₁ r₂,
    G.respondsTo b c₁ = some r₁ →
    G.respondsTo b c₂ = some r₂ →
      r₁ = r₂

/-- A minimal adaptivity witness: two calls receive different responses from
    the same being. This is deliberately weak and extensional. -/
def ResponseVariesWithCall (b : G.Being) : Prop :=
  ∃ c₁ c₂ r₁ r₂,
    G.respondsTo b c₁ = some r₁ ∧
    G.respondsTo b c₂ = some r₂ ∧
    r₁ ≠ r₂

namespace DirectedConvention

/-- Sowing-side aiming, in the thin extensional sense the glossary
    licenses: the deed counts as aimed at this landing exactly when the
    field in fact delivers it there. No intention-primitive is introduced;
    stronger causal or intentional stories belong in downstream models. -/
def WaaAimedAt (deed reception : G.Weld) : Prop := DeliveredTo G deed reception

theorem deliveredTo_iff_waaReachBackFull (deed reception : G.Weld) :
    DeliveredTo G deed reception ↔ WaaReachBackFull G deed reception :=
  Iff.rfl

theorem objectAxisStanding_of_landsAt
    (deed reception : G.Weld) (h : LandsAt G deed reception) :
    ObjectAxisStanding G deed :=
  ⟨reception, h.left⟩

theorem objectAxisStanding_of_hasShareDropLanding
    (before : Config Contrib) (deed : G.Weld) (h : HasShareDropLanding G before deed) :
    ObjectAxisStanding G deed :=
  h.elim (fun reception hland => ⟨reception, hland.left.left⟩)

namespace BeingConvention

/- Reading and motivation: Identification/Commentary.lean, C.1. -/

/- Reading and motivation: Identification/Commentary.lean, C.1. -/
abbrev MountsAt (b : G.Being) (c : G.Call) : Prop := G.MountsAt b c

/-- Re-rooted name for mounting at some call. -/
abbrev MountsSomewhere (b : G.Being) : Prop := G.MountsSomewhere b

/-- Re-rooted name for call-entire response. -/
abbrev RespondsToEveryCall (b : G.Being) : Prop := G.RespondsToEveryCall b

/- Reading and motivation: Identification/Commentary.lean, C.1. -/
abbrev Stone (b : G.Being) : Prop := G.Stone b

/-- Re-rooted name for the pole-class responder. -/
abbrev Terminus (b : G.Being) : Prop := G.Terminus b

/-- Re-rooted name for non-vacuous terminus response. -/
abbrev LiveTerminus (b : G.Being) : Prop := G.LiveTerminus b

/-- Re-rooted name for call-entire terminus response. -/
abbrev ResponsiveTerminus (b : G.Being) : Prop := G.ResponsiveTerminus b

/-- Re-rooted name for the two attested arrivals at the pole-class. -/
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

/-- A weld lies in a macro tag's fiber when its fine agent projects there. -/
def InFiber (b : Macro) (w : G.Weld) : Prop := κ.proj w.agent = b

/- Reading and motivation: Identification/Commentary.lean, C.1. -/
def SameFiber (p q : G.Being) : Prop := κ.proj p = κ.proj q

/-- A fiber has at least one fine tag under it. -/
def FiberInhabited (b : Macro) : Prop := ∃ p : G.Being, κ.proj p = b

/-- A fiber has at least one actual weld under it. This is the live/vacuity
    guard needed for exclusivity facts below. -/
def ActualFiberInhabited (b : Macro) : Prop :=
  ∃ w : G.Weld, G.Actual w ∧ κ.InFiber b w

/-- Some fine tag in the fiber mounts a response somewhere. -/
def SentientTag (b : Macro) : Prop :=
  ∃ p : G.Being, κ.proj p = b ∧ G.MountsSomewhere p

/-- A tag is not sentient exactly when every fine tag in its fiber is stone-typed. -/
theorem not_sentientTag_iff_fiber_all_stone (b : Macro) :
    ¬ κ.SentientTag b ↔ ∀ p : G.Being, κ.proj p = b → G.Stone p := by
  constructor
  · intro hnot p hp c hmount
    exact hnot ⟨p, hp, ⟨c, hmount⟩⟩
  · intro hall hsent
    rcases hsent with ⟨p, hp, c, hmount⟩
    exact hall p hp c hmount

/- Reading and motivation: Identification/Commentary.lean, C.1. -/
def FiberAtPole (b : Macro) : Prop :=
  ∀ w : G.Weld, G.Actual w → κ.InFiber b w → AtBot (G.share w)

/-- The live, non-vacuous fiber-at-pole predicate. -/
def LiveFiberAtPole (b : Macro) : Prop :=
  κ.ActualFiberInhabited b ∧ κ.FiberAtPole b

/-- Every actual weld in the fiber carries a live self-pole index.
    Vacuous on empty or no-actual fibers; use `LiveSelfAptTag` when
    inhabitation matters. -/
def SelfAptTag (b : Macro) : Prop :=
  ∀ w : G.Weld, G.Actual w → κ.InFiber b w → G.HasSelfPoleIndex w

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

/-- Under a fiber-at-pole reading, no actual weld in the fiber has a live
    self-pole index. -/
theorem no_live_index_under_fiberAtPole {b : Macro}
    (h : κ.FiberAtPole b) {w : G.Weld}
    (hactual : G.Actual w) (hfiber : κ.InFiber b w) :
    ¬ G.HasSelfPoleIndex w :=
  G.no_self_pole_index_of_atBot w (h w hactual hfiber)

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

end BeingCoarsening

/- The innermost `GridConvention` namespace is opened in Consequences/Basic.lean for the
   concrete claim-language rows. Keeping the abstract machinery at `Grid`
   level for now avoids a churn-only migration of structure fields whose
   eventual home may simply remain signature rather than reading. -/

end BeingConvention

end DirectedConvention

/-- An actual weld packaged with its actuality proof. This is the small
    carrier downstream files need when they reason about remembered deeds,
    future receptions, or paired receptions without repeatedly passing the
    same `Actual` hypotheses around by hand. -/
structure ActualWeld (G : Grid Contrib) where
  weld   : G.Weld
  actual : G.Actual weld

/- Reading and motivation: Identification/Commentary.lean, C.1. -/
structure ReceptionPair (G : Grid Contrib) where
  first  : ActualWeld G
  second : ActualWeld G

namespace ReceptionPair

/-- Reach-back from the first reception in the pair to the second, phrased
    through the existing delivery relation. Whether this is the relation a
    downstream prudence theorem needs is a theorem-level choice; the carrier
    merely makes the relevant actual pair available. -/
def FirstConditionsSecond {G : Grid Contrib} (p : ReceptionPair G) : Prop :=
  DirectedConvention.WaaReachBackFull G p.first.weld p.second.weld

/-- The pair's sequential re-pitched configurations, exposed for future
    two-step arguments. No ordering or privilege between them is asserted
    here. -/
def rePitchSequence {G : Grid Contrib} (before : Config Contrib)
    (p : ReceptionPair G) : Config Contrib × Config Contrib :=
  let afterFirst := G.rePitch before p.first.weld
  (afterFirst, G.rePitch afterFirst p.second.weld)

end ReceptionPair

end Grid

/- ==============================================================================
   Preview: the two outside wrinkles

   Neither item below is Theory content proper — both anticipate later
   proof/theorem files and provide checked witnesses that the definitions
   above actually support what those files will need. Nothing above this
   point depends on anything below it.
============================================================================== -/

section Preview

variable {Contrib : Type} [PreorderBot Contrib] (G : Grid Contrib)

/- --------------------------------------------------------------------------
   Wrinkle 1 — field residue under-determines the agent: internal version

   Outside note this responds to: "Non-typeability is demonstrated by failed
   elaboration, not proved. The internal alternative is to model a universe of
   designations and prove ¬∃ f : FieldFact → Index ... under your axioms."

   The internal route is used here, with the modest scope made explicit.
-------------------------------------------------------------------------- -/

/-- The field-side residue of a weld: everything left once the agent is not
    part of the data. The honest field-fact for recovering an index is
    `Call × Response`, never `Being`. -/
def Grid.fieldOf (w : G.Weld) : G.Call × G.Response := (w.call, w.response)

/-- Naively, "no function `Call × Response → Being` exists" is false whenever
    `Being` is nonempty: a constant function typechecks. What matters is the
    correctness-carrying version, a function claimed to recover, for every
    actual weld, the agent that in fact produced its field residue.

    The theorem below therefore has the honest scope of the claim: no such
    recovery can be correct when two different beings can actually produce the
    same response to the same call. It is not a blanket claim about every
    `Grid`; it is the internal witness that field residues under-determine who
    acted. -/
theorem no_agent_recovery_of_field_collision
    (a₁ a₂ : G.Being) (c : G.Call) (r : G.Response)
    (h1 : G.Actual ⟨a₁, c, r⟩) (h2 : G.Actual ⟨a₂, c, r⟩) (hne : a₁ ≠ a₂) :
    ¬ ∃ recover : G.Call × G.Response → G.Being,
        ∀ w : G.Weld, G.Actual w → recover (G.fieldOf w) = G.index w :=
  fun hex =>
    hne (hex.elim (fun _recover hrec =>
      (hrec ⟨a₁, c, r⟩ h1).symm.trans (hrec ⟨a₂, c, r⟩ h2)))

/- Reading and motivation: Identification/Commentary.lean, C.1. -/

/-- Two devices, differing only in whether their chime is a function of
    who is listening. -/
inductive Clock
  | rigid
  | adaptive

/-- The one call in play: whether a listener is actually present to hear
    the chime. -/
inductive Listener
  | present
  | absent

/-- The chime itself; its content is immaterial, only whether it occurs
    and what drove it matters. -/
inductive Chime
  | chime

instance : PreorderBot Nat where
  le       := Nat.le
  le_refl  := Nat.le_refl
  le_trans := fun h1 h2 => Nat.le_trans h1 h2
  bot      := 0
  bot_le   := Nat.zero_le

/- Reading and motivation: Identification/Commentary.lean, C.1. -/
def clockGrid : Grid Nat where
  Being      := Clock
  Call       := Listener
  Response   := Chime
  respondsTo b c :=
    match b, c with
    | .rigid,    _        => none
    | .adaptive, .present => some .chime
    | .adaptive, .absent  => none
  grade _ _ _ := 0
  conditions _ _ := False

theorem rigid_is_stone : clockGrid.Stone Clock.rigid :=
  fun _c ⟨_r, hr⟩ => by cases hr

theorem adaptive_is_terminus : clockGrid.Terminus Clock.adaptive :=
  fun _c _r _h => Nat.le_refl 0

theorem adaptive_not_stone : ¬ clockGrid.Stone Clock.adaptive :=
  fun h => h Listener.present ⟨Chime.chime, rfl⟩

/- Reading and motivation: Identification/Commentary.lean, C.1. -/
theorem clockGrid_function_share_split_witness :
    clockGrid.Stone Clock.rigid ∧
    clockGrid.Terminus Clock.adaptive ∧
    ¬ clockGrid.Stone Clock.adaptive :=
  ⟨rigid_is_stone, adaptive_is_terminus, adaptive_not_stone⟩

/- --------------------------------------------------------------------------
   Second concrete display — integer registers with diagnosis-time κ

   The adaptive register clock builds its fine tags as integer-like registers.
   The macro designation is still supplied outside the signature, by a
   `BeingCoarsening`: the model may implement stable internal registers, but
   the standing partition is not stored as "the" being-boundary.
-------------------------------------------------------------------------- -/

/-- A register clock whose fine tags are natural-numbered registers. Each
    register answers the tick by handing off to the next register, and
    delivery follows that hand-off. -/
def registerClockGrid : Grid Nat where
  Being      := Nat
  Call       := Unit
  Response   := Nat
  respondsTo n _ := some (n + 1)
  grade n _ _ := n
  conditions deed reception := reception.agent = deed.response

/-- A macro coarsening that sends all fine registers to one macro tag. -/
def registerClockCoarsening :
    Grid.DirectedConvention.BeingConvention.BeingCoarsening registerClockGrid Unit where
  proj _ := ()

theorem registerClock_macro_sentient :
    registerClockCoarsening.SentientTag () :=
  ⟨(0 : Nat), rfl, ⟨(), ⟨(1 : Nat), rfl⟩⟩⟩

theorem registerClock_macro_selfConditioning :
    registerClockCoarsening.SelfConditioningTag () := by
  refine ⟨⟨(0 : Nat), (), (1 : Nat)⟩, ⟨(1 : Nat), (), (2 : Nat)⟩,
    rfl, rfl, rfl, ?_⟩
  rfl

/- `clockGrid` is a genuine, finite, computable term of type `Grid Nat` —
    direct evidence that "a model of the theory" is a buildable Lean
    object, and that facts about a concrete instance are provable at
    `rfl`-level once the instance is fixed. That is the tool a later
    independence result needs: fix a small `Grid`, choose an actual
    `ReceptionPair`, run the relevant `Config`/`rePitch` steps, phrase
    whatever "privilege" would have to assert as a further `Prop` over that
    data, and show it fails in the instance. That construction is not
    carried out here — deciding how to phrase "privilege" formally is itself
    a nontrivial choice belonging to whoever proves the theorem, not to the
    scaffolding. What this section checks is only that the scaffolding does
    not get in the way. -/

end Preview


end WAA