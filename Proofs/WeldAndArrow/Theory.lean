/-
================================================================================
  The Weld and the Arrow — I. Theory
  A Lean 4 formalization of `paper/Theory.md`
================================================================================

STATUS: checked by `lake build`. The file is intentionally conservative:
mostly term-mode proofs, no Mathlib dependency, and only the small amount of
core Lean needed to keep the theory's primitive signature executable.

No `import`s. Every order-theoretic notion is hand-rolled rather than reached
for from Mathlib, on purpose (see §0) — both to stay self-contained and
because Mathlib's `Preorder` carries expectations this file does not need.

Downstream proof/theorem files should import this module, or the library root
that re-exports it. This file is *only* Theory: the primitive sorts and the
rules, plus a handful of sanity lemmas that check a definition does what the
prose claims of it. Real theorems (backsliding is the one exception — see §2,
it is stated as a theorem already in `Theory.md` itself) belong downstream.

--------------------------------------------------------------------------------
Design log
--------------------------------------------------------------------------------

* "Nothing self-indexed is stored" is enforced by TYPE DISCIPLINE, not by a
  proved proposition. `Config` (§2) has exactly one field, a `Contrib`-valued
  tendency, and no field of type `Weld` or `Being`-as-owner. That absence is
  not a lemma with a proof term; it is a fact about a `structure` command,
  visible by reading it. This is the positive-direction analogue of the
  paper's internal mis-feed discipline: the elaborator accepts the field
  residue and the stored tendency, but it is never given a stored owner.
  `kenshō_not_held` in §2 turns this into an actual, if easy, theorem: a later
  weld's share is *never* a function of any `Config`, because no such function
  exists anywhere in this signature for it to be one of.

* The `Weld`/`Index` order follows the central modelling choice here:
  `Weld` is primitive (an agent, a call, a response, bundled — nothing else,
  and in particular no separate prior `Act` a
  `Weld` could be said to interpret, since MMK 8 is explicitly "neither
  prior, neither based"), and `index`/`share` are *projections out of* a
  completed `Weld`, never inputs to constructing one. There is no function
  in this file of type `Config _ → Being` or `Call × Response → Being`
  that is asserted total and correct — the one candidate that would be
  (`recover`, in the Preview section) is refuted, not built. That is the
  file's whole enforcement of "self-anchoring": no prior performer, because
  nothing here ever manufactures an index without first being handed a
  complete occurrence to project it from.

* The tier machinery (separate/fuse) exposes the small deep interface
  downstream theorem files will need: a `ClaimLanguage` gives an
  object-language of claims together with tier-indexed satisfaction, a
  `Distinction` stores two claim-objects rather than two bare `Tier → Prop`
  predicates, and a `RecordedUtterance` stores the utterance's weld, offered
  tier, and content. Theory.lean does not choose the concrete language or run
  the taxonomy generator. That remains theorem-level content. The point of
  the interface is only to prevent a shallow encoding from becoming a dead
  end once the fox's sentence, Baizhang's rule, and other recorded utterances
  have to be graded as inspectable objects.

* Every `Contrib`-valued magnitude is kept under a hand-rolled `WeakOrder` —
  reflexive and transitive, deliberately NOT required to be total. This is
  not a shortcut, it is required by the source text: "some of them, where
  call and self-maintenance interact in the driving, simply incomparable"
  (Theory: Attainment). Mathlib's `Preorder`, notionally the "right" class,
  would have worked identically here; a `LinearOrder` would have silently
  contradicted the paper, which is the reason `WeakOrder` exists at all
  rather than just importing whatever the standard library offers.

* Kept at plain `Type` throughout rather than universe-polymorphic `Type*`
  because the current examples and intended signatures all live in the first
  universe. Upgrading to universe polymorphism later is routine and touches
  no proofs, only signatures.
-/

namespace WAA

/- ==============================================================================
   §0  A deliberately weak order for display-scalars

   Row 2 "states a partial ordering, not a measure" (Theory: Attainment).
   `WeakOrder` asks for exactly reflexivity and transitivity: nothing else,
   on purpose, so that `Incomparable` below is a genuine possibility rather
   than a defect a total order would rule out by fiat.
============================================================================== -/

/-- A bare preorder, rolled by hand and *not* assumed total. -/
class WeakOrder (α : Type) where
  /-- The display-order relation: `a ≼ b` means `a` is no more self-driven
      than `b` in the ordinal Row-2 sense. -/
  le       : α → α → Prop
  le_refl  : ∀ a, le a a
  le_trans : ∀ {a b c : α}, le a b → le b c → le a c

@[inherit_doc] infix:50 " ≼ " => WeakOrder.le

/-- Neither side dominates — the formal home of "simply incomparable"
    (Theory: Attainment), not a defect to be patched but a shape Row 2's
    ordering is allowed to have. -/
def Incomparable [WeakOrder α] (a b : α) : Prop := ¬ a ≼ b ∧ ¬ b ≼ a

/-- The bottom is a genuine, ATTAINED element — the terminus, share-zero
    (Theory: Attainment, "an interior pole"), comparable to everything
    below it by fiat, exactly as a least-arrogated placement should be.
    There is deliberately no dual `WeakOrderTop`: the solipsist is glossed
    in the source as an ASYMPTOTE ("the share tending to totality" — never
    reached, Theorems: Compound positions, "the grade's own asymptote"),
    so positing an attained top would misrepresent the text. Its absence
    here is a decision, not an oversight. -/
class WeakOrderBot (α : Type) extends WeakOrder α where
  bot    : α
  bot_le : ∀ a, le bot a

/-- Shorthand for the bottom of whatever `Contrib` is in scope. -/
def shareZero [WeakOrderBot α] : α := WeakOrderBot.bot

/- ==============================================================================
   §1  The signature

   `RawWeld` and `DriveComposition` are free-standing (no `Grid` needed to
   state them) so that `Grid` itself can use them in its own field types
   without a self-reference problem. `Grid` bundles everything else: a term
   of type `Grid Contrib` *is a model of the theory* — which is exactly the
   scaffolding a later countermodel (e.g. for prudential privilege,
   Theorems §1) needs: build one concretely and show a property fails in
   it. A worked instance is built in the Preview section to check the
   scaffolding is actually usable for this, not just usable in principle.
============================================================================== -/

/-- An occurrence: a candidate agent, call, and response, bundled. There is
    deliberately no separate `Act` type prior to this — modelling the doer
    as available before the deed would already be the state-tool MMK 8
    forecloses ("neither prior, neither based"). Not every `RawWeld` need
    be `Grid.Actual` (below); the type is closed under hypothetical
    variation on purpose, since the probe (§1, `ProbeConstant`) reasons
    about a *family* of calls a being might face, most of which it never
    actually answers. -/
structure RawWeld (Being Call Response : Type) where
  agent    : Being
  call     : Call
  response : Response

/-- The determination clause (Theory: Attainment, "What fixes a
    placement"): the share is not a modal profile but the actual
    composition of what drove *this* response. No arithmetic relation is
    imposed between the two fields — summing them into a single total
    would already be the measure the text prices away; only `selfDriven`,
    read through `≼`, is ever consulted below. -/
structure DriveComposition (Contrib : Type) where
  callDriven : Contrib
  selfDriven : Contrib

/-- The whole signature, bundled. -/
structure Grid (Contrib : Type) [WeakOrderBot Contrib] where
  /-- the primitive identity of a causal series (Proofs, disclaimer 4) — a
      tag over a causally-connected run, not a first-personal owner.
      Individuation is not ownership, which is the entire content of
      disclaimer 4; `Being` is exactly as innocent as "chariot" is for
      Siderits. -/
  Being      : Type
  /-- a dharma arriving at Row 2. -/
  Call       : Type
  /-- what a mounted response produces. -/
  Response   : Type
  /-- the dispositional, field-side fact: does this being mount a response
      to this call at all, and which one. `none` for every call is the
      stone (Theory: Attainment, "function-zero, outside the predicate's
      domain") — an `Option`, so that "no response" is not a value of
      `Response` but an absence, undefined rather than a numerically small
      share. -/
  respondsTo : Being → Call → Option Response
  /-- the determination clause, read off wherever a response is actually
      mounted. -/
  driveOf    : Being → Call → Response → DriveComposition Contrib
  /-- delivery: whether an earlier weld's deed conditions a later weld's
      arrival — the field's business, index-free (Theory: Karma, "the
      weld answers only the index-question over what arrives"). Kept
      entirely separate from `respondsTo`/`driveOf`, which are about
      *drive*, never about *delivery*: conflating the two is a taxonomy
      error in its own right (Theorems, Grade 1, "Delivery-question /
      index-question"). -/
  conditions : RawWeld Being Call Response → RawWeld Being Call Response → Prop

namespace Grid

variable {Contrib : Type} [WeakOrderBot Contrib]

/-- Shorthand: an occurrence for a specific `Grid`. -/
abbrev Weld (G : Grid Contrib) := RawWeld G.Being G.Call G.Response

variable (G : Grid Contrib)

/-- A weld is *actual* when it witnesses something the being in fact does.
    Self-anchoring is enforced structurally, not by a fancier dependent
    index type: nothing in this file ever produces a `Being` "as an
    index" except by first supplying a `Weld` whose `response` is
    witnessed here. There is no route from `Config` (§2) or from
    field-facts alone to an `Actual` weld — see `no_agent_recovery_from_field`
    in the Preview section for the internal version of that claim. -/
def Actual (w : G.Weld) : Prop := G.respondsTo w.agent w.call = some w.response

/-- The agent-index — token-reflexive because it is nothing but a
    projection out of the very weld that carries it: there is no route to
    "this act's agent" that does not pass through a completed `Weld`. -/
def index (w : G.Weld) : G.Being := w.agent

/-- Row 2, the grade, read off the determination clause: the self-driven
    component of the actual drive-composition. States an indexical fact
    (*this* weld's placement) in a third-personal register (a plain
    `Contrib`-valued projection) — Theory: Attainment, "Row 2 ... states
    an indexical fact in a third-personal register". -/
def share (w : G.Weld) : Contrib := (G.driveOf w.agent w.call w.response).selfDriven

/-- Whether this occurrence makes a live self-pole index. The raw
    `index` projection above is still useful as the causal-series tag of a
    weld; this predicate is the theorem-facing notion that disappears at
    share-zero. -/
def HasSelfPoleIndex (w : G.Weld) : Prop := G.share w ≠ shareZero

/-- The live self-pole index, when there is evidence that one is present.
    This is proof-carrying rather than `Option`-valued on purpose: deciding
    whether an arbitrary share is nonzero would import excluded middle unless
    a concrete model supplied a decision procedure. -/
def selfPoleIndex (w : G.Weld) (_h : G.HasSelfPoleIndex w) : G.Being := w.agent

/-- Appropriation, in the thin formal sense needed downstream: a reception
    has a live self-pole index exactly when the share is nonzero. -/
def Appropriates (reception : G.Weld) : Prop := G.HasSelfPoleIndex reception

/-- Share-zero entails that no self-pole index is live. -/
theorem no_self_pole_index_of_shareZero (w : G.Weld) (h : G.share w = shareZero) :
    ¬ G.HasSelfPoleIndex w :=
  fun hidx => hidx h

/-- The evidence-carried index is the agent tag when the self-pole is live. -/
theorem selfPoleIndex_eq_agent_of_hasSelfPoleIndex
    (w : G.Weld) (h : G.HasSelfPoleIndex w) :
    G.selfPoleIndex w h = w.agent := rfl

/-- At share-zero there is no appropriation. -/
theorem no_appropriation_of_shareZero (w : G.Weld) (h : G.share w = shareZero) :
    ¬ G.Appropriates w :=
  G.no_self_pole_index_of_shareZero w h

/-- Sanity check: the determination is not secretly the probe. This holds
    by `rfl`, and holds *because* `share`'s definition above never
    mentions anything the probe will be built from (`ProbeConstant`,
    defined only after this point) — the file cannot be rearranged to
    make this lemma non-trivial without changing `share` itself, which is
    the point: "counterfactual variation ... is how a third party probes
    the composition, a display over it, never what it consists in"
    (Theory: Attainment). -/
example (w : G.Weld) :
    G.share w = (G.driveOf w.agent w.call w.response).selfDriven := rfl

/-- The probe (Theory: Attainment): counterfactual call-variation,
    available to any outside observer, that DISPLAYS a drive-composition
    without being what the composition consists in. Formalized as the
    bare fact that the same self-driven value recurs across a family of
    ACTUAL welds by the same being at different calls in some class `cs`
    — a symptom a third party can check, never the determination itself
    (`Grid.share`, defined above, prior to and independently of any
    probing). -/
def ProbeConstant (b : G.Being) (cs : G.Call → Prop) : Prop :=
  ∀ c₁ c₂, cs c₁ → cs c₂ →
    ∀ r₁ r₂, G.respondsTo b c₁ = some r₁ → G.respondsTo b c₂ = some r₂ →
      (G.driveOf b c₁ r₁).selfDriven = (G.driveOf b c₂ r₂).selfDriven

/- --------------------------------------------------------------------------
   Function / share
-------------------------------------------------------------------------- -/

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

/-- The stone: function-zero at EVERY call — "outside the predicate's
    domain" rather than a limiting case within it (Theory: Attainment). -/
def Stone (b : G.Being) : Prop := ∀ c, ¬ G.MountsAt b c

/-- The terminus: function *entire* wherever a call is actually mounted,
    together with share zero throughout — "the other pole of the domain,
    not its far edge" (Theory: Attainment). -/
def Terminus (b : G.Being) : Prop :=
  ∀ c r, G.respondsTo b c = some r → (G.driveOf b c r).selfDriven = shareZero

/-- The non-vacuous terminus: function is present somewhere and every
    mounted response is share-zero. This is often the right formal analogue
    of the "responsive stone" when the model's call-domain is intentionally
    sparse. -/
def LiveTerminus (b : G.Being) : Prop := G.MountsSomewhere b ∧ G.Terminus b

/-- The strongest terminus predicate: every call gets a response, and every
    response is share-zero. This is the theorem-facing version of "function
    entire, share zero." -/
def ResponsiveTerminus (b : G.Being) : Prop :=
  G.RespondsToEveryCall b ∧ G.Terminus b

/-- A response by a terminus-typed being has share-zero. -/
theorem shareZero_of_terminus_response
    {b : G.Being} {c : G.Call} {r : G.Response}
    (hterm : G.Terminus b) (hresp : G.respondsTo b c = some r) :
    G.share ⟨b, c, r⟩ = shareZero :=
  hterm c r hresp

/-- A terminus response carries no self-pole index. -/
theorem no_self_pole_index_of_terminus_response
    {b : G.Being} {c : G.Call} {r : G.Response}
    (hterm : G.Terminus b) (hresp : G.respondsTo b c = some r) :
    ¬ G.HasSelfPoleIndex ⟨b, c, r⟩ :=
  G.no_self_pole_index_of_shareZero ⟨b, c, r⟩
    (G.shareZero_of_terminus_response hterm hresp)

/-- A terminus response does not appropriate. -/
theorem no_appropriation_of_terminus_response
    {b : G.Being} {c : G.Call} {r : G.Response}
    (hterm : G.Terminus b) (hresp : G.respondsTo b c = some r) :
    ¬ G.Appropriates ⟨b, c, r⟩ :=
  G.no_appropriation_of_shareZero ⟨b, c, r⟩
    (G.shareZero_of_terminus_response hterm hresp)

/-- Genjō's two attested arrivals (Theory: Attainment): a being sits at the
    pole either by never mounting a response at all, or by mounting every
    response with nothing self-pole driving it. Phrased as `∨`, not as an
    iff or a case split, on purpose — the source is explicit these are
    "two attested arrivals, not an exhaustive partition": nothing here
    forbids a third witness satisfying neither disjunct trivially (an
    ordinary partial-share agent), and nothing here forces the two
    disjuncts to be exclusive either. -/
def AtGenjōPole (b : G.Being) : Prop := G.Stone b ∨ G.Terminus b

/-- The function/share split is not vacuous in one easy direction: a stone
    is *vacuously* a terminus (there is nothing to check, since it never
    mounts a response for the hypothesis of `Terminus` to fire on). The
    interesting content of the split — that a `Terminus` being need NOT be
    a `Stone` — is not a theorem of this shape (a universal witness would
    need a specific counterexample instance); it is exhibited concretely
    by `Clock.adaptive` in `clockGrid`, in the Preview section
    (`adaptive_is_terminus`, `adaptive_not_stone`). -/
theorem stone_is_terminus (b : G.Being) (h : G.Stone b) : G.Terminus b :=
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

/-- At an actual share-zero weld, no live self-pole index can be supplied. -/
theorem no_self_pole_index_of_terminus_weld
    (w : G.Weld) (_hactual : G.Actual w) (hshare : G.share w = shareZero) :
    ¬ G.HasSelfPoleIndex w :=
  G.no_self_pole_index_of_shareZero w hshare

end Grid

/- ==============================================================================
   §2  What is carried, what is made, what is stated

   The load-bearing invariant of the whole system — "nothing self-indexed
   is stored" — is enforced by what `Config` does NOT contain, not by a
   proposition about what it contains. `Config` carries exactly one thing:
   a `Contrib`-valued tendency (the seed), a field-fact about the series.
   There is no field of type `Weld`, and — just as importantly — nothing
   below ever defines a function FROM `Config` back INTO a `driveOf`
   argument: the causal machinery that actually determines a later weld's
   share (`Grid.driveOf`) never once takes a `Config` as input. That
   disconnection is deliberate and is the architectural content of the
   retyped disposition/act cell (Theory: Attainment, "the collapse is
   inferential — the dated occurrence read off the standing tendency"):
   there is no function in this signature for a later act's share to be
   read off a standing tendency THROUGH, so the error the retype names is
   not merely discouraged here, it is inexpressible.
============================================================================== -/

/-- What the field carries between acts for a being: a tendency to
    arrogate, and nothing else. This *is* the formalization of "nothing
    self-indexed is stored" — not a theorem about `Config`, but `Config`'s
    definition, read by what is and is not present in the type, not by a
    proof. -/
structure Config (Contrib : Type) where
  tendency : Contrib

namespace Grid

variable {Contrib : Type} [WeakOrderBot Contrib] (G : Grid Contrib)

/-- Reception re-pitches the configuration the field carries forward — an
    inga-fact, never a stored index (Theory: Karma). The new tendency is
    read off the reception's OWN share and nothing else: no formula
    relates it to `before`, which is one license-respecting instantiation
    of "unconstrained by construction" (Theory: Karma, "one magnitude is
    deliberately unconstrained... owned here as a feature") — not the
    only possible one, but a simple one, and it already allows arbitrarily
    large jumps between successive configs (Theorems: "Sudden and
    gradual", "a one-step re-pitch from hell-typed to pole"). -/
def rePitch (_before : Config Contrib) (received : G.Weld) : Config Contrib :=
  { tendency := G.share received }

/-- Kenshō: a per-call share-ceding event, priced as the scalar itself is
    priced — comparatively, not by how much (Theory: Attainment, "the
    scalar priced as display"). A reception counts as kenshō against a
    prior tendency when its share sits at or below that tendency in the
    order, and NOT at or above it — "markedly less claimed" read off `≼`
    alone, no subtraction, no measure. -/
def IsKenshō (before : Config Contrib) (received : G.Weld) : Prop :=
  G.share received ≼ before.tendency ∧ ¬ before.tendency ≼ G.share received

/-- **Backsliding cannot be blocked, because nothing blocks it.** The
    determination of a LATER weld's share never consults any `Config` —
    there is no function `Config Contrib → DriveComposition Contrib`
    anywhere in `Grid`'s signature for a later act to be constrained by.
    In particular, `before` and `kensho` are both present as hypotheses
    below and neither appears on the right-hand side of the equation: the
    re-pitched configuration a kenshō produces plays no role in the value
    of `G.share later`, for ANY later weld `later`, of the same being or
    otherwise. The proof is `rfl`, precisely because `share` was never
    defined in terms of `Config` to begin with; the intentionally unused
    binders are named with leading underscores for that reason. This is the
    theorem `Theory.md` itself promises (Theory: Attainment, "Kenshō:
    rungs on the grade" —
    "post-kenshō backsliding ... falls out here as a theorem"): the being
    loses no attainment because there was never a stored attainment for a
    later act to be held to. -/
theorem kenshō_not_held
    (_before : Config Contrib) (_kensho later : G.Weld) :
    G.share later = (G.driveOf later.agent later.call later.response).selfDriven :=
  rfl

/- --------------------------------------------------------------------------
   The reception-weld: reach-back
-------------------------------------------------------------------------- -/

/-- The reach-back is *full* when the claimed deed actually conditions the
    reception — a delivery-fact (Theory: Karma, "The reception-weld: loop-
    closure as theorem"). -/
def ReachBackFull (deed reception : G.Weld) : Prop := G.conditions deed reception

/-- ... and *vacuous* otherwise: an appropriating with nothing arrived to
    appropriate, not a falsehood (Theory: Karma, "A reach-back along an
    undrawn line is therefore not false ... but vacuous"). -/
def ReachBackVacuous (deed reception : G.Weld) : Prop := ¬ G.conditions deed reception

/-- When a concrete model gives a decision procedure for delivery, the two
    reach-back cases are exhaustive. Abstractly, the theory keeps only the
    predicates: asserting this disjunction for every proposition would be
    excluded middle. -/
theorem reachBack_full_or_vacuous (deed reception : G.Weld)
    [hdec : Decidable (G.conditions deed reception)] :
    G.ReachBackFull deed reception ∨ G.ReachBackVacuous deed reception :=
  match hdec with
  | isTrue h => Or.inl h
  | isFalse h => Or.inr h

/- --------------------------------------------------------------------------
   Delivery, landing, effectiveness, adaptivity
-------------------------------------------------------------------------- -/

/-- A delivery-line from one occurrence to another, stated in field
    vocabulary. This is definitionally the same relation as
    `ReachBackFull`; the different name is for theorem statements where the
    field-side role matters more than the reception-side appropriation. -/
def DeliveredTo (deed reception : G.Weld) : Prop := G.conditions deed reception

/-- A fruit has landed when delivery reaches an actual reception. -/
def LandsAt (deed reception : G.Weld) : Prop :=
  G.DeliveredTo deed reception ∧ G.Actual reception

/-- Object-axis standing: the occurrence is available to be received
    somewhere. No self-pole index is implied for the occurrence pointed at. -/
def ObjectAxisStanding (deed : G.Weld) : Prop := ∃ reception, G.DeliveredTo deed reception

/-- A share-ceding landing, relative to the receiver's prior configuration.
    This is the local witness used by effectiveness talk; it asserts an
    actual landing and a kenshō-typed reception, but no value. -/
def LandsWithKenshō
    (before : Config Contrib) (deed reception : G.Weld) : Prop :=
  G.LandsAt deed reception ∧ G.IsKenshō before reception

/-- A call/deed is effective relative to a prior receiver-configuration when
    at least one of its landings is share-ceding. This is intentionally only
    existential; no probability or measure is introduced. -/
def EffectiveFor (before : Config Contrib) (deed : G.Weld) : Prop :=
  ∃ reception, G.LandsWithKenshō before deed reception

/-- An ordinal effectiveness comparison: every share-ceding landing of the
    second deed can be matched by one of the first. This is a preorder-style
    display convention, not a probability calculus. -/
def AtLeastAsEffective
    (before : Config Contrib) (deed₁ deed₂ : G.Weld) : Prop :=
  ∀ reception₂,
    G.LandsWithKenshō before deed₂ reception₂ →
      ∃ reception₁, G.LandsWithKenshō before deed₁ reception₁

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

/-- Sowing-side delivery-engineering: the deed is configured for this
    landing exactly when the field in fact delivers it there. Stronger
    causal stories belong in downstream models. -/
def AimedAt (deed reception : G.Weld) : Prop := G.DeliveredTo deed reception

theorem deliveredTo_iff_reachBackFull (deed reception : G.Weld) :
    G.DeliveredTo deed reception ↔ G.ReachBackFull deed reception :=
  Iff.rfl

theorem objectAxisStanding_of_landsAt
    (deed reception : G.Weld) (h : G.LandsAt deed reception) :
    G.ObjectAxisStanding deed :=
  ⟨reception, h.left⟩

theorem effectiveFor_has_objectAxisStanding
    (before : Config Contrib) (deed : G.Weld) (h : G.EffectiveFor before deed) :
    G.ObjectAxisStanding deed :=
  h.elim (fun reception hland => ⟨reception, hland.left.left⟩)

theorem atLeastAsEffective_refl (before : Config Contrib) (deed : G.Weld) :
    G.AtLeastAsEffective before deed deed :=
  fun reception h => ⟨reception, h⟩

theorem atLeastAsEffective_trans
    (before : Config Contrib) {a b c : G.Weld}
    (hab : G.AtLeastAsEffective before a b)
    (hbc : G.AtLeastAsEffective before b c) :
    G.AtLeastAsEffective before a c :=
  fun reception h =>
    (hbc reception h).elim (fun receptionB hB => hab receptionB hB)

/-- An actual weld packaged with its actuality proof. This is the small
    carrier downstream files need when they reason about remembered deeds,
    future receptions, or paired receptions without repeatedly passing the
    same `Actual` hypotheses around by hand. -/
structure ActualWeld (G : Grid Contrib) where
  weld   : G.Weld
  actual : G.Actual weld

/-- A pair of actual receptions, kept deliberately neutral. Theory does not
    say that either reception has prudential privilege over the other; it
    only supplies the typed pair over which Theorems can formulate, test, or
    refute such a privilege claim by countermodel. -/
structure ReceptionPair (G : Grid Contrib) where
  first  : ActualWeld G
  second : ActualWeld G

namespace ReceptionPair

/-- Reach-back from the first reception in the pair to the second, phrased
    through the existing delivery relation. Whether this is the relation a
    downstream prudence theorem needs is a theorem-level choice; the carrier
    merely makes the relevant actual pair available. -/
def FirstConditionsSecond {G : Grid Contrib} (p : ReceptionPair G) : Prop :=
  G.ReachBackFull p.first.weld p.second.weld

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
   §3  Row 1 and Row 3, briefly

   "All acting is Row 3" (Theory: the act-grammar): Row 3 (shu) is not a
   further reading that needs its own type, it IS `Weld` — there is no
   separate act underneath the weld for shu to be a fact about. Likewise
   Row 1 (genjō) at the grain of a single act is not a further condition,
   it is the weld under its enactment-reading, and every weld satisfies it
   trivially — which is why no `def` for either appears here: manufacturing
   a nontrivial predicate for "this act manifests, full stop" or "this act
   is practice" would be adding content the source explicitly declines to
   add ("its three cells are the three parts of one sentence ... not three
   agents"). The one Row-1 usage with real content is the DERIVED,
   narrower sense — "genjō" as the grade's share-zero pole — and that one
   already has a definition: `Grid.AtGenjōPole` in §1. Row 2 (kannō-sōe,
   the grade) is the only row this file gives independent definitional
   content to, via `Grid.share`, which is exactly the source's own claim:
   "Row 2 still does exactly one thing, the adverb."
============================================================================== -/

/- ==============================================================================
   §4  The separate/fuse rule

   The rule is stated against a deliberately small deep interface. The
   object language itself is abstract: future files choose a concrete
   `Claim` type and a tier-indexed satisfaction relation. What Theory fixes
   is the shape that later work needs: distinctions are pairs of claim
   objects, and recorded utterances carry enough inspectable information for
   a taxonomy generator to ask which call was answered, at which tier the
   utterance was offered, and whether the content is satisfied there.
============================================================================== -/

namespace Grid

variable {Contrib : Type} [WeakOrderBot Contrib]

/-- A tier at which a claim can be diagnosed: the self-emptying floor
    (atemporal, one per `Grid` — Proofs, "The verdict's tier"), or a live
    act-time diagnosis pinned to a specific weld. -/
inductive Tier (G : Grid Contrib)
  | floor
  | actTime (w : G.Weld)

variable (G : Grid Contrib)

/-- Whether a tier still has arrogation for a distinction to separate over:
    never at the floor (Proofs: "there is no agent and no fruit-for-anyone"
    there), and not at an act-time tier whose weld is already share-zero
    (Theory: Attainment, "fuse ... at genjō — the share-zero pole, no
    arrogation left"). -/
def Tier.hasArrogation : Tier G → Prop
  | .floor     => False
  | .actTime w => G.share w ≠ shareZero

/-- An abstract object language of claims, together with its tier-indexed
    satisfaction relation. This is intentionally only an interface: later
    files can instantiate `Claim` with the concrete syntax their theorem or
    taxonomy needs, while Theory can already state the separate/fuse rule
    over inspectable claim-objects rather than over anonymous predicates. -/
structure ClaimLanguage (G : Grid Contrib) where
  Claim : Type
  Holds : Tier G → Claim → Prop

namespace ClaimLanguage

/-- The judgement form a later file can read as `⊢_t P`: claim `p` is
    satisfied at tier `t` in language `L`. It is still a `Prop`, but it is
    not merely a free-floating `Tier → Prop`; the claim being judged is an
    object of the chosen language. -/
def TrueAt {G : Grid Contrib} (L : ClaimLanguage G) (t : Tier G) (p : L.Claim) :
    Prop :=
  L.Holds t p

end ClaimLanguage

/-- A recorded utterance, typed as data the taxonomy can inspect. The `weld`
    records who answered which call with which response; `offeredAt` records
    the tier at which the utterance was made; `content` is a claim-object in
    the chosen language. The proof of `actual` keeps this type for actual
    recorded utterances rather than hypothetical ones. -/
structure RecordedUtterance (G : Grid Contrib) (L : ClaimLanguage G) where
  weld      : G.Weld
  actual    : G.Actual weld
  offeredAt : Tier G
  content   : L.Claim

namespace RecordedUtterance

/-- The call this utterance answers, exposed as a projection so future
    classifiers do not have to unpack the weld by hand. -/
def answersCall {G : Grid Contrib} {L : ClaimLanguage G}
    (u : RecordedUtterance G L) : G.Call :=
  u.weld.call

/-- Whether the utterance's content is satisfied at the tier at which it was
    offered. Fox-style tier-errors are expected to fail this test; the
    taxonomy that classifies such failures belongs downstream. -/
def FitsOfferedTier {G : Grid Contrib} {L : ClaimLanguage G}
    (u : RecordedUtterance G L) : Prop :=
  L.TrueAt u.offeredAt u.content

end RecordedUtterance

/-- A distinction: two claim-objects a diagnosis might hold apart. -/
structure Distinction (G : Grid Contrib) where
  language : ClaimLanguage G
  sideA : language.Claim
  sideB : language.Claim

/-- Fusion: at a tier with no arrogation left, the two sides of a
    distinction are equivalent — read as the two sides becoming logically
    interchangeable rather than as either being individually false, which
    is the reading "held each at its tier, non-dual" (the fox's release,
    Theory: "One act through the grid") licenses. This is a real
    requirement, not a vacuous one: at `t = .floor` the antecedent
    `¬ Tier.hasArrogation G .floor` is `¬ False`, i.e. always true, so `Fused .floor`
    reduces to requiring `sideA .floor ↔ sideB .floor` unconditionally —
    exactly the non-duality the floor is supposed to make available, and
    exactly the content a genuinely doctrinal `Distinction` (not the
    trivial witness in the sanity example below) would have to earn. -/
def Distinction.Fused {G : Grid Contrib} (d : Distinction G) (t : Tier G) : Prop :=
  ¬ Tier.hasArrogation G t →
    (d.language.TrueAt t d.sideA ↔ d.language.TrueAt t d.sideB)

/-- Collapse: fusing a distinction WHERE IT SHOULD SEPARATE — asserting a
    floor-tier content as though it settled a live, act-time diagnosis.
    The fox's shape (Theorems, "The fox: not-fall asserted conventionally
    — antinomianism"). -/
def Distinction.Collapse {G : Grid Contrib} (d : Distinction G) (t : Tier G) : Prop :=
  Tier.hasArrogation G t ∧
    (d.language.TrueAt t d.sideA ↔ d.language.TrueAt t d.sideB)

/-- Freeze: the rule's other violation — holding a distinction SEPARATE at
    the floor, where it should fuse. -/
def Distinction.Freeze {G : Grid Contrib} (d : Distinction G) : Prop :=
  ¬ (d.language.TrueAt Tier.floor d.sideA ↔
      d.language.TrueAt Tier.floor d.sideB)

/-- Separation: at a live act-time tier, the two sides are not
    interchangeable. -/
def Distinction.Separated {G : Grid Contrib} (d : Distinction G) (t : Tier G) :
    Prop :=
  Tier.hasArrogation G t ∧
    ¬ (d.language.TrueAt t d.sideA ↔ d.language.TrueAt t d.sideB)

/-- A distinction obeys the separate/fuse rule when it separates wherever
    arrogation is live and fuses wherever it is not. This is a property of
    concrete doctrinal distinctions, not an axiom imposed on every pair of
    arbitrary claims. -/
def Distinction.ObeysSeparateFuse {G : Grid Contrib} (d : Distinction G) :
    Prop :=
  (∀ t, Tier.hasArrogation G t →
      ¬ (d.language.TrueAt t d.sideA ↔ d.language.TrueAt t d.sideB)) ∧
  (∀ t, ¬ Tier.hasArrogation G t →
      (d.language.TrueAt t d.sideA ↔ d.language.TrueAt t d.sideB))

/-- The two voices of the system's diagnostics. -/
inductive VerdictVoice
  | assertable
  | displayable

/-- The two grades of error described in the theorem file. -/
inductive ErrorGrade
  | grammatical
  | soteriological

namespace ErrorGrade

/-- Grade 1 verdicts are asserted inside the lens; Grade 2 verdicts are
    displayed without adding a value-command. -/
def voice : ErrorGrade → VerdictVoice
  | .grammatical => .assertable
  | .soteriological => .displayable

end ErrorGrade

/-- The generator's four possible public outcomes: the two violations of a
    distinction, a declined classification, or a retyping that redraws the
    distinction itself. -/
inductive GeneratorOutcome (G : Grid Contrib)
  | collapse (d : Distinction G) (t : Tier G) (h : d.Collapse t)
  | freeze (d : Distinction G) (h : d.Freeze)
  | declined
  | retype (oldDistinction newDistinction : Distinction G)

theorem not_collapse_of_obeysSeparateFuse
    {G : Grid Contrib} {d : Distinction G} (h : d.ObeysSeparateFuse)
    (t : Tier G) :
    ¬ d.Collapse t :=
  fun hc => (h.left t hc.left) hc.right

theorem not_freeze_of_obeysSeparateFuse
    {G : Grid Contrib} {d : Distinction G} (h : d.ObeysSeparateFuse) :
    ¬ d.Freeze :=
  fun hf => hf (h.right Tier.floor (fun hfloor => hfloor))

/-- Sanity check, not a doctrinal claim: the definitions above are not
    degenerate. A distinction whose two sides are the SAME claim-object
    cannot freeze — confirming `Freeze` is not trivially true of every
    `Distinction` and that `Fused`/`Freeze` actually consult the language's
    satisfaction relation. This says nothing about which doctrinally-
    motivated distinctions (function/share, the two middles, shō/satori,
    ...) actually obey the rule; each of those needs its own, separate check
    once it is built, which is Theorems.lean's job. -/
example (L : ClaimLanguage G) (p : L.Claim) :
    ¬ ({ language := L, sideA := p, sideB := p } : Distinction G).Freeze :=
  fun h => h Iff.rfl

end Grid

/- ==============================================================================
   Preview: the two outside wrinkles

   Neither item below is Theory content proper — both anticipate later
   proof/theorem files and provide checked witnesses that the definitions
   above actually support what those files will need. Nothing above this
   point depends on anything below it.
============================================================================== -/

section Preview

variable {Contrib : Type} [WeakOrderBot Contrib] (G : Grid Contrib)

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
theorem no_agent_recovery_from_field
    (a₁ a₂ : G.Being) (c : G.Call) (r : G.Response)
    (h1 : G.Actual ⟨a₁, c, r⟩) (h2 : G.Actual ⟨a₂, c, r⟩) (hne : a₁ ≠ a₂) :
    ¬ ∃ recover : G.Call × G.Response → G.Being,
        ∀ w : G.Weld, G.Actual w → recover (G.fieldOf w) = G.index w :=
  fun hex =>
    hne (hex.elim (fun _recover hrec =>
      (hrec ⟨a₁, c, r⟩ h1).symm.trans (hrec ⟨a₂, c, r⟩ h2)))

/- --------------------------------------------------------------------------
   Wrinkle 2 — underivability claims need countermodels: scaffold checked

   Outside note this responds to: "Underivability claims need
   countermodels. 'Prudential privilege is underivable' is a non-
   derivability result — you'd exhibit a model satisfying the axioms
   where the privilege fails."

   Prudential privilege itself is theorem-level content. This file supplies
   the neutral carrier it will need (`ActualWeld`/`ReceptionPair`) but does
   not formulate the privilege predicate or prove its failure.
   What is checked here is narrower and prior: that "a model of the theory"
   is not just a phrase but a term one can actually build and compute with,
   because that is the one thing a later countermodel construction cannot
   do without. `clockGrid` below is also, independently, the worked example
   `Theory.md` itself gives for the domain joint (Theory: Attainment,
   "The domain joint" — the manufactured cuckoo clock), so it is in scope
   for this file on its own terms, not only as a preview.
-------------------------------------------------------------------------- -/

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

instance : WeakOrderBot Nat where
  le       := Nat.le
  le_refl  := Nat.le_refl
  le_trans := fun h1 h2 => Nat.le_trans h1 h2
  bot      := 0
  bot_le   := Nat.zero_le

/-- The rigid clock never mounts a response *to the call* at all — it
    chimes on schedule regardless of who is present, which is not a
    response with a small or zero share, it is outside the responds-to
    relation altogether, exactly as the stone is (Theory: Attainment,
    "The non-adaptive build chimes on schedule regardless of who is
    present: no response mounted, function-zero, the stone's typing").
    The adaptive clock times its chime for a listener that is actually
    there, and — this is the manufactured case's whole point — its
    response is read, via `driveOf`, as driven by the call entire: share
    zero, function mounted (Theory: Attainment, "So it reads function
    mounted, share zero: terminus-typed"). -/
def clockGrid : Grid Nat where
  Being      := Clock
  Call       := Listener
  Response   := Chime
  respondsTo b c :=
    match b, c with
    | .rigid,    _        => none
    | .adaptive, .present => some .chime
    | .adaptive, .absent  => none
  driveOf _ _ _ := { callDriven := 1, selfDriven := 0 }
  conditions _ _ := False

theorem rigid_is_stone : clockGrid.Stone Clock.rigid :=
  fun _c ⟨_r, hr⟩ => by cases hr

theorem adaptive_is_terminus : clockGrid.Terminus Clock.adaptive :=
  fun _c _r _h => rfl

theorem adaptive_not_stone : ¬ clockGrid.Stone Clock.adaptive :=
  fun h => h Listener.present ⟨Chime.chime, rfl⟩

/-- The payoff stated together: one being is `Stone`, a different being of
    the SAME `Grid` is `Terminus` and demonstrably NOT `Stone` — the
    function/share split is not vacuous, exhibited rather than merely
    defined. This is the concrete witness `Grid.stone_is_terminus`
    promised was not the whole story. -/
example :
    clockGrid.Stone Clock.rigid ∧
    clockGrid.Terminus Clock.adaptive ∧
    ¬ clockGrid.Stone Clock.adaptive :=
  ⟨rigid_is_stone, adaptive_is_terminus, adaptive_not_stone⟩

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
