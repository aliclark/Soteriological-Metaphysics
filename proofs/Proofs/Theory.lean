/-
================================================================================
  The Weld and the Arrow — I. Theory
  A first-draft Lean 4 formalization of `01-theory.md`
================================================================================

STATUS: unverified. No Lean toolchain was reachable in the environment this
draft was written in (no local install, and no network access to fetch one),
so nothing below has been through the elaborator. It is written conservatively
— term-mode proofs over tactics wherever a term-mode proof was available, only
core-Lean4 lemmas whose exact signature I was confident of (`Nat.le_refl`,
`Nat.le_trans`, `Nat.zero_le`, `Option.noConfusion`, `Classical.em`), no
`simp`/`decide`/`rcases`/`obtain` calls whose success depends on a simp-set or
tactic availability I couldn't check. Treat every `theorem`/`example` as a
claim to be checked, not a checked fact. The most likely failure points, if
any, are noted inline where a design choice was genuinely uncertain rather
than just tedious.

No `import`s. Every order-theoretic notion is hand-rolled rather than reached
for from Mathlib, on purpose (see §0) — both to stay self-contained without
network access, and because Mathlib's `Preorder` carries expectations (and a
large elaboration cost) this file doesn't want.

Companion files, not yet written: `Theorems.lean`, `Proofs.lean`. This file is
*only* Theory: the primitive sorts and the rules, plus a handful of sanity
lemmas that check a definition does what the prose claims of it. Real
theorems (backsliding is the one exception — see §2, it is stated as a
theorem already in `01-theory.md` itself) belong downstream.

--------------------------------------------------------------------------------
Design log
--------------------------------------------------------------------------------

* "Nothing self-indexed is stored" is enforced by TYPE DISCIPLINE, not by a
  proved proposition. `Config` (§2) has exactly one field, a `Contrib`-valued
  tendency, and no field of type `Weld` or `Being`-as-owner. That absence is
  not a lemma with a proof term; it is a fact about a `structure` command,
  visible by reading it. This is the positive-direction analogue of the
  paper's own remark that `malformed` is "demonstrated by failed elaboration,
  not proved" (see the outside note reproduced in the Preview section): the
  discipline that keeps a stored index out of `Config` is enforced the same
  way the reduction is refused — by what the elaborator will accept as
  well-typed, not by an internal theorem. `kenshō_not_held` in §2 turns this
  into an actual, if easy, theorem: a later weld's share is *never* a
  function of any `Config`, because no such function exists anywhere in this
  signature for it to be one of.

* The `Weld`/`Index` order follows the one piece of outside advice this
  draft had going in: `Weld` is primitive (an agent, a call, a response,
  bundled — nothing else, and in particular no separate prior `Act` a
  `Weld` could be said to interpret, since MMK 8 is explicitly "neither
  prior, neither based"), and `index`/`share` are *projections out of* a
  completed `Weld`, never inputs to constructing one. There is no function
  in this file of type `Config _ → Being` or `Call × Response → Being`
  that is asserted total and correct — the one candidate that would be
  (`recover`, in the Preview section) is refuted, not built. That is the
  file's whole enforcement of "self-anchoring": no prior performer, because
  nothing here ever manufactures an index without first being handed a
  complete occurrence to project it from.

* The tier machinery (separate/fuse) is a SHALLOW embedding: a `Distinction`
  is a bare pair of tier-indexed propositions (`Tier → Prop`), and fusing is
  a `Prop` computed from a tier, not an independent judgement relation with
  its own syntax. This is adequate for everything Theory.lean itself needs —
  stating which claims are live at which tier, and that the floor and any
  share-zero act both dissolve a distinction that is live elsewhere — and it
  is checked against one non-degenerate sanity example below. It will NOT be
  adequate once Theorems.lean starts grading *actually uttered* sentences
  against the two-truths machinery (the fox's sentence, Baizhang's rule):
  grading an utterance needs the utterance as an object the taxonomy can
  inspect — which call it answers, what tier it was offered at, whether that
  matches its content — and that is a deep embedding: an object language of
  claims together with a tier-indexed satisfaction relation and a genuine
  judgement `⊢_t P`, not a `Prop`-valued function. Theory.lean only ever
  needs to *state* the rule; running a generator over recorded utterances is
  Theorems.lean's job, and the honest prediction is that the shallow
  encoding gets *replaced*, not extended, before the taxonomy is built. This
  verdict is argued again, briefly, at the definition site (§4).

* Every `Contrib`-valued magnitude is kept under a hand-rolled `WeakOrder` —
  reflexive and transitive, deliberately NOT required to be total. This is
  not a shortcut, it is required by the source text: "some of them, where
  call and self-maintenance interact in the driving, simply incomparable"
  (Theory: Attainment). Mathlib's `Preorder`, notionally the "right" class,
  would have worked identically here; a `LinearOrder` would have silently
  contradicted the paper, which is the reason `WeakOrder` exists at all
  rather than just importing whatever the standard library offers.

* Kept at plain `Type` throughout rather than universe-polymorphic `Type*`,
  to remove one more axis of things that could be subtly wrong in a draft
  nobody has compiled yet. Upgrading to universe polymorphism later is
  routine and touches no proofs, only signatures.
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
    field-facts alone to an `Actual` weld — see `malformed_no_recovery`
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

/-- The stone: function-zero at EVERY call — "outside the predicate's
    domain" rather than a limiting case within it (Theory: Attainment). -/
def Stone (b : G.Being) : Prop := ∀ c, ¬ G.MountsAt b c

/-- The terminus: function *entire* wherever a call is actually mounted,
    together with share zero throughout — "the other pole of the domain,
    not its far edge" (Theory: Attainment). -/
def Terminus (b : G.Being) : Prop :=
  ∀ c r, G.respondsTo b c = some r → (G.driveOf b c r).selfDriven = shareZero

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
    definition, read the way the outside note reproduced in the Preview
    section reads a failed elaboration: by what is and is not present in
    the type, not by a proof. -/
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
    theorem `01-theory.md` itself promises (Theory: Attainment, "Kenshō:
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

/-- The two are exhaustive by construction (classical logic; `Classical.em`
    is part of Lean 4's `Init` prelude, no `import` required) — every
    reach-back is one or the other, which is the source text's own point:
    "confabulated ownership feels exactly like the real thing from within
    the act" because full and vacuous are not distinguishable from inside
    the weld, only by whether `conditions` in fact holds. -/
theorem reachBack_full_or_vacuous (deed reception : G.Weld) :
    G.ReachBackFull deed reception ∨ G.ReachBackVacuous deed reception :=
  Classical.em (G.conditions deed reception)

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

   Shallow embedding, as flagged in the design log: a `Distinction` is
   nothing but a pair of tier-indexed propositions, and `Fused`/`Collapse`/
   `Freeze` are `Prop`s computed from a tier, not an independent judgement
   calculus. Adequate for stating the rule; almost certainly inadequate for
   Theorems.lean's taxonomy generator, which needs to grade objects with
   their own content and tier of assertion (recorded utterances), i.e. a
   deep embedding — an object language of claims, a tier-indexed
   satisfaction relation, a genuine `⊢_t P`. That is not built here. Moving
   to it later means re-deriving this section's lemmas against new
   definitions, not importing them: the shallow `Distinction.Fused` below
   and a deep-embedding `⊢_t` are different formal objects that happen to
   share a name in the prose.
============================================================================== -/

namespace Grid

variable {Contrib : Type} [WeakOrderBot Contrib]

/-- A tier at which a claim can be diagnosed: the self-emptying floor
    (atemporal, one per `Grid` — Proofs, "Two guards and the verdict's own
    tier"), or a live act-time diagnosis pinned to a specific weld. -/
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

/-- A distinction: two tier-indexed claims a diagnosis might hold apart. -/
structure Distinction (G : Grid Contrib) where
  sideA : Tier G → Prop
  sideB : Tier G → Prop

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
  ¬ Tier.hasArrogation G t → (d.sideA t ↔ d.sideB t)

/-- Collapse: fusing a distinction WHERE IT SHOULD SEPARATE — asserting a
    floor-tier content as though it settled a live, act-time diagnosis.
    The fox's shape (Theorems, "The fox: not-fall asserted conventionally
    — antinomianism"). -/
def Distinction.Collapse {G : Grid Contrib} (d : Distinction G) (t : Tier G) : Prop :=
  Tier.hasArrogation G t ∧ (d.sideA t ↔ d.sideB t)

/-- Freeze: the rule's other violation — holding a distinction SEPARATE at
    the floor, where it should fuse. -/
def Distinction.Freeze {G : Grid Contrib} (d : Distinction G) : Prop :=
  ¬ (d.sideA Tier.floor ↔ d.sideB Tier.floor)

/-- Sanity check, not a doctrinal claim: the definitions above are not
    degenerate. A distinction whose two sides are definitionally the SAME
    proposition at every tier cannot freeze — confirming `Freeze` is not
    trivially true of every `Distinction` (which would make it useless as
    a diagnostic) and that `Fused`/`Freeze` actually consult `sideA`/
    `sideB` rather than being constant. This says nothing about which
    doctrinally-motivated distinctions (function/share, the two middles,
    shō/satori, ...) actually obey the rule; each of those needs its own,
    separate check once it is built, which is Theorems.lean's job. -/
example (P : Tier G → Prop) : ¬ (⟨P, P⟩ : Distinction G).Freeze :=
  fun h => h Iff.rfl

end Grid

/- ==============================================================================
   Preview: the two outside wrinkles

   Neither item below is Theory content proper — both anticipate
   Proofs.lean / Theorems.lean and are included only to check, as far as a
   single unverified file can, that the definitions above actually support
   what those files will need. Nothing above this point depends on
   anything below it.
============================================================================== -/

section Preview

variable {Contrib : Type} [WeakOrderBot Contrib] (G : Grid Contrib)

/- --------------------------------------------------------------------------
   Wrinkle 1 — "malformed" is a meta-level fact: internal version attempted

   Outside note this responds to: "'Malformed' is a meta-level fact. 'The
   reduction doesn't typecheck' isn't a theorem you can state inside Lean —
   non-typeability is demonstrated by failed elaboration, not proved. The
   internal alternative is to model a universe of 'designations' and prove
   ¬∃ f : FieldFact → Index ... under your axioms. Both are legitimate."

   Both routes are attempted here, and the first is corrected en route.
-------------------------------------------------------------------------- -/

/-- The field-side residue of a weld: everything left once the agent is
    forgotten. The honest candidate for a "field-fact" a reduction would
    have to reconstruct an index from — `Call × Response`, never `Being`. -/
def Grid.fieldOf (w : G.Weld) : G.Call × G.Response := (w.call, w.response)

/-- Route (a), attempted and immediately corrected: naively, "no function
    `Call × Response → Being` exists" is FALSE whenever `Being` is
    nonempty — a constant function always typechecks, so the naive framing
    of "try to write the reduction and watch it fail to elaborate" is not
    quite right for this case: Lean will happily accept a constant, and
    accepting it is not a bug. What fails to elaborate is something
    narrower and gets no further than a hole: the correctness-carrying
    version — a function claimed to RECOVER, for every actual weld, the
    agent that in fact produced its field-facts. There is no way to write
    such a function's BODY that does not either (i) ignore the input,
    which typechecks but is not a recovery, or (ii) smuggle in a
    `Being`-valued primitive that did not come from `Call × Response` —
    and there is no third option, because `Being` is an opaque field of
    `Grid` with no operation into it from `Call` or `Response` anywhere in
    the signature. That is this file's own version of "failed
    elaboration": not a red squiggle, but a content failure visible in the
    signature itself, one level prior to any proof attempt.

    Route (b), the internal, quantified alternative, is `malformed_no_
    recovery` below: not "no function exists" (false, as just noted), but
    "no function exists that is correct on the actual welds" — which is
    exactly false whenever two DIFFERENT beings can actually produce the
    SAME response to the SAME call, something nothing in `Grid`'s
    signature forbids and everything about "the field is index-free"
    predicts should be possible in general (two different practitioners
    can, after all, both answer "not fall"). This is deliberately not a
    blanket claim about every `Grid` — a `Grid` with only one inhabited
    `Being` would trivially admit a correct constant `recover`, and a
    formalization asserting otherwise would simply be a bug. The
    hypotheses below are the honest scope of the claim: malformedness
    is witnessed exactly where the field under-determines who acted,
    which is the generic case, not a universal one. -/
theorem malformed_no_recovery
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

   Prudential privilege itself is Theorems content (§1 there), and needs
   the reach-back apparatus applied across an actual PAIR of receptions —
   a step this file's job is only to make possible, not to take. What is
   checked here is narrower and prior: that "a model of the theory" is not
   just a phrase but a term one can actually build and compute with,
   because that is the one thing a later countermodel construction cannot
   do without. `clockGrid` below is also, independently, the worked
   example `01-theory.md` itself gives for the domain joint (Theory:
   Attainment, "The domain joint" — the manufactured cuckoo clock), so it
   is in scope for this file on its own terms, not only as a preview.
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
  fun _c hc => hc.elim (fun _r hr => by cases hr)

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
    independence result needs: fix a small `Grid`, add a second `Config`/
    `rePitch` step for a being's own future reception, phrase whatever
    "privilege" would have to assert as a further `Prop` over `Grid` +
    `Config`, and show it fails in the instance. That construction is not
    carried out here — prudence needs the reach-back apparatus (§2)
    applied across an actual pair of receptions, and deciding how to
    phrase "privilege" formally is itself a nontrivial choice belonging to
    whoever proves the theorem, not to the scaffolding. What this section
    checks is only that the scaffolding does not get in the way. -/

end Preview

end WAA
