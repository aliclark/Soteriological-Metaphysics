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

namespace RawWeld

/-- Swap the call and response faces of a weld when they use the same carrier.
    This changes no signature fields; it is a display-side involution for
    checking whether an interior call→response arrow has been smuggled in. -/
def transposeCR {Being CR : Type} (w : RawWeld Being CR CR) :
    RawWeld Being CR CR :=
  ⟨w.agent, w.response, w.call⟩

@[simp]
theorem transposeCR_agent {Being CR : Type} (w : RawWeld Being CR CR) :
    w.transposeCR.agent = w.agent :=
  rfl

@[simp]
theorem transposeCR_call {Being CR : Type} (w : RawWeld Being CR CR) :
    w.transposeCR.call = w.response :=
  rfl

@[simp]
theorem transposeCR_response {Being CR : Type} (w : RawWeld Being CR CR) :
    w.transposeCR.response = w.call :=
  rfl

@[simp]
theorem transposeCR_transposeCR {Being CR : Type} (w : RawWeld Being CR CR) :
    w.transposeCR.transposeCR = w :=
  rfl

end RawWeld

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

/-- A delivery-line whose deed and reception carry the same agent tag. This is
    only a fact about the supplied delivery relation and weld fields; see
    `Identification/Commentary.lean`, C.9. -/
def SameAgentDelivery (deed reception : G.Weld) : Prop :=
  DeliveredTo G deed reception ∧ deed.agent = reception.agent

/-- A delivery-line whose deed and reception carry different agent tags. This is
    only a fact about the supplied delivery relation and weld fields; see
    `Identification/Commentary.lean`, C.9. -/
def CrossAgentDelivery (deed reception : G.Weld) : Prop :=
  DeliveredTo G deed reception ∧ deed.agent ≠ reception.agent

theorem transpose_deliveredTo_iff (deed reception : G.Weld) :
    DeliveredTo G.transpose deed reception ↔ DeliveredTo G reception deed :=
  Iff.rfl

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
   designations and prove ¬∃ f : FieldFact → Index ... under your assumptions."

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

end Preview


end WAA
