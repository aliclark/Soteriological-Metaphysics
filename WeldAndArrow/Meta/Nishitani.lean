/-
================================================================================
  WeldAndArrow.Meta.Nishitani
  Śūnyatā on the re-emptying ladder — the Nishitani/Jizang layer as a
  consumer of the checked ladder in WeldAndArrow.Consequences.ContentRows
================================================================================

This file is a *consumer* of the re-emptying ladder: it defines philosophical
vocabulary as thin wrappers over the ladder's API and re-derives the v1/v2
results as corollaries. It introduces no new distinctions, no new ladders,
and proves nothing the ladder does not already license.

On placement: metaphysically upstream, import-graph downstream. The file sits
in `Meta/` because it is the metaphysical reading of the whole development,
but it *imports* `WeldAndArrow.Consequences.ContentRows`, since every theorem here is a
one-liner over the ladder. That the direction of `import` runs opposite to
the direction of philosophical priority is itself a conventional designation,
and the file is content to let it fuse at the floor.

Namespace placement follows the project's discipline — names are placed by
what their reading presupposes, not by what their definition consumes. The
śūnyatā vocabulary presupposes the innermost grid-lens reading, so it lives at
`Grid.DirectedConvention.BeingConvention.GridConvention.Nishitani`. The modal
appendix presupposes nothing of the grid and lives at `WAA.Nishitani`.

## What the rebase changes (relative to v2's syntactic Position ladder)

v2's Part III (the syntactic `Position` ladder) is **superseded**:

* **Conventionalization is now semantic.** In v2, each stated ultimate
  reappeared as a *subterm* of the next conventional (`rfl` on syntax). Here,
  rung n+1's claim `finalBelow` has as its truth-condition *the lower rung's
  `Freeze`*: the absolutization of level n becomes an evaluable sentence of
  level n+1's object language — and, given an error-free seed, is refuted at
  every live tier. The un-saying is a theorem, not a constructor. Meanwhile
  `liveBelow` preserves the lower rung's live separation: re-emptying negates
  only the grasping (執), never the provisional function (仮).

* **言忘慮絶 lives at the floor.** v2 faced a fork: represent the fourth
  ultimate as a marked gap (`Option Position` / `none`) or exile it to a
  meta-theorem. The ladder's design is a third option superior to both: the
  ground tier is *in* the tier type, nothing is `Live` there, and every claim
  trivializes — at the floor, all words are idle and every obedient
  distinction fuses. Ineffability without a gap and without ascent.

* **真空妙有 is a hypothesis, structurally.** The contentful-beings ladder
  obeys only given `∃ b, ¬ G.Stone b`: the emptiness of beings is available
  only where there is a being. v1's vacuity disease is not merely avoided
  but *excluded by the signature*.

* **The Middle is two-sided.** `ObeysSeparateFuse` = separate where live
  (仮), fuse where not (空); `¬Freeze` rules out eternalism/absolutization,
  `¬Collapse` rules out annihilationism (emptiness-sickness on the other
  flank). 中 is the conjunction, and `ladder_obeys` says the Middle is stable
  under re-emptying.

## Dictionary (v1/v2 → this development)

| v1/v2                                   | here                                       |
|-----------------------------------------|--------------------------------------------|
| `Polarity.being` / `.nonbeing`          | `sideA` / `sideB` of a seed distinction    |
| `Field.Context`                         | live tiers (`Tier.actTime _` with a live share) |
| totality of `Field.polarity`            | totality of `language.Holds`               |
| `SelfNature`, `AbsoluteNothingEntity`   | `Distinction.Freeze` ("survives the floor") |
| `no_reified_absolute_nothing`           | `Grid.not_freeze_of_obeysSeparateFuse`     |
| `Position` ladder, `no_final_ultimate`  | `ladder`, `no_final_level`                 |
| rung-4 ineffability                     | floor trivialization (`words_idle_at_floor`) |
| `provisionally_designated_middle`       | `ObeysSeparateFuse` + `ladder_obeys`       |
| (unguarded flank in v1/v2)              | `Collapse`, `ladder_collapse_self_refuting` |

## API consumed (all from WeldAndArrow.Theory / WeldAndArrow.Theorems)

At `Grid` level: `Grid Contrib`, `G.Weld`, `G.Being`, `G.Stone`,
`Tier.floor`, `Tier.actTime`, `Distinction` (with `language`, `sideA`,
`sideB`, `Separated`, `Freeze`, `Collapse`, `ObeysSeparateFuse`),
`ClaimLanguage` (with `Claim`, `Holds`), `ErrorFree`,
`Grid.not_freeze_of_obeysSeparateFuse`.

At `GridConvention` level: `LadderSide`, `reEmptied`, `ladder`,
`ladder_obeys`, `ladder_errorFree_of_errorFree`,
`ladder_collapse_self_refuting`, `no_level_final`, `no_final_level`,
`beingsRow`, `beingsLadder_no_level_final`, `beforeAfterRow`,
`beforeAfterLadder_no_level_final`, `intraWeldArrowRow`,
`intraWeldArrowLadder_no_level_final`, `weldRow`,
`weldLadder_no_level_final`, `doerDeedRow`,
`doerDeedLadder_no_level_final`, `contentBeingsRow`,
`contentBeingsLadder_no_level_final_of_being`.

The two theorems the draft marked (†) — the only places a tier is mentioned
explicitly — go through unchanged: `Tier` is per-grid (`Tier G`) and
`actTime` is indexed by `G.Weld`, exactly as assumed.
-/

import WeldAndArrow.Consequences.ContentRows

namespace WAA

namespace Grid
namespace DirectedConvention
namespace BeingConvention
namespace GridConvention
namespace Nishitani

open LadderSide

variable {Contrib : Type} [PreorderBot Contrib]
variable {G : Grid Contrib}

/-! ## The vocabulary, as wrappers -/

/-- 執 — absolutization, the reified Absolute Nothing generalized: a
    distinction freezes when it claims to survive the floor, i.e. to hold
    where nothing is live. v1 modeled this as an *entity* that is non-being
    in every context; the ladder's `Freeze` is the better rendering, since
    what gets absolutized is never a thing but a *distinction* — including,
    for the metaphysical nihilist, the Nothing/Something distinction itself. -/
abbrev Absolutized (d : Distinction G) : Prop := d.Freeze

/-- 断 — the annihilationist error at a tier: a live distinction whose sides
    have been fused. Emptiness-sickness erases working distinctions; the
    Middle refuses this flank as firmly as the other. -/
abbrev Annihilated (d : Distinction G) (t : Tier G) : Prop := d.Collapse t

/-- 中 — the Middle, rebased: separate exactly where live (仮, provisional
    validity), fuse exactly where not (空, no residue at the ground). Not a
    compromise between the flanks but the discipline that excludes both. -/
abbrev MiddleWay (d : Distinction G) : Prop := d.ObeysSeparateFuse

/-- 空 — śūnyatā of a distinction: no level of its re-emptying ladder ever
    freezes. Not a property of the seed alone but a fact about the whole
    unbounded process of its de-absolutization: there is no final level at
    which the distinction — or its emptying, or the emptying of *that* —
    congeals into an ultimate. -/
def Sunyata (d : Distinction G) : Prop :=
  ¬ ∃ n, (ladder d n).Freeze

/-! ## The core theorems, as corollaries -/

/-- An error-free seed suffices for śūnyatā: the ladder's cumulative form, in
    which each level's non-freezing is supplied by the level below rather
    than by fresh premises. Emptying, once begun without error, propagates
    for free — 空空 costs nothing after the first emptying. -/
theorem sunyata_of_errorFree {d : Distinction G} (h : ErrorFree G d) :
    Sunyata d :=
  no_final_level (G := G) h

/-- Alternatively, from full obedience of the seed. -/
theorem sunyata_of_middle {d : Distinction G} (h : d.ObeysSeparateFuse) :
    Sunyata d :=
  fun ⟨n, hf⟩ => no_level_final (G := G) h n hf

/-- 空空 — the emptiness of emptiness, rebased: every re-emptied level is
    itself error-free, hence itself empty-able. In v1 this was a hypothesis
    applied to a reified emptiness-entity; here it is *generated*: the ladder
    manufactures its own next emptying. -/
theorem emptiness_of_emptiness {d : Distinction G} (h : ErrorFree G d) :
    ∀ n, ErrorFree G (ladder d (n + 1)) :=
  ladder_errorFree_of_errorFree (G := G) h

/-- The Middle is stable under re-emptying: no rung of the ladder is anything
    other than the Middle. Jizang's four levels are not four positions but one
    discipline, iterated. -/
theorem middle_at_every_level {d : Distinction G} (h : d.ObeysSeparateFuse) :
    ∀ n, MiddleWay (ladder d n) :=
  ladder_obeys (G := G) h

/-- The annihilationist flank, closed at every level: no rung ever collapses a
    live distinction. Emptiness that erased the conventional would not be the
    Middle; the ladder proves it never does. -/
theorem no_annihilation_at_any_level {d : Distinction G}
    (h : d.ObeysSeparateFuse) :
    ∀ n t, ¬ Annihilated (ladder d n) t :=
  ladder_collapse_self_refuting (G := G) h

/-! ## Jizang's rungs, located on the ladder

Rung n's conventional truth = the live separation of `ladder d n` (its 仮);
rung n's ultimate           = the fact `¬ (ladder d n).Freeze` (its 空);
and rung n+1 *internalizes* rung n's ultimate: the claim `finalBelow` of
level n+1's language means, at every act-time tier, exactly that level n
froze. The two `Iff.rfl`s below are the philosophical heart of the rebase:
the internalization is definitional, and it preserves 仮 while targeting 執. -/

/-- Rung n's absolutization is a *sentence* of rung n+1: the truth-condition
    of `finalBelow` at any act-time tier is definitionally the lower rung's
    `Freeze`. Every stated ultimate is already the next level's conventional
    material — conventionalization by `Iff.rfl`. -/
theorem ultimate_internalized (d : Distinction G) (n : Nat) (w : G.Weld) :
    (ladder d (n + 1)).language.Holds (Tier.actTime w) finalBelow ↔
      (ladder d n).Freeze :=
  Iff.rfl

/-- The provisional is preserved: `liveBelow` at rung n+1 means exactly the
    lower rung's live separation. Re-emptying un-says the finality claim and
    *only* the finality claim; the working distinction passes upward intact.
    色 is not consumed by 空. -/
theorem provisional_preserved (d : Distinction G) (n : Nat) (w : G.Weld) :
    (ladder d (n + 1)).language.Holds (Tier.actTime w) liveBelow ↔
      (ladder d n).Separated (Tier.actTime w) :=
  Iff.rfl

/-- 言忘慮絶 — at the floor, every claim of a re-emptied level holds
    trivially: all words are idle at the ground, so no separation survives
    there and every obedient distinction fuses. The fourth "ultimate" is
    neither a gap in the language nor a meta-theorem in exile: it is the tier
    at which language, still present, does no work. -/
theorem words_idle_at_floor (d : Distinction G) (c : LadderSide) :
    (reEmptied d).language.Holds Tier.floor c := by
  cases c <;> exact True.intro

/-! ## The metaphysical nihilist, relocated

In v2, the nihilist's "there could have been Absolute Nothing instead of
Something" was rung 0's ultimate, conventionalized at rung 1. On the ladder
the diagnosis sharpens into three theorems:

1. The thesis is *statable*: it is `finalBelow`, a `Claim` of rung 1's
   language — and a claim in a language is a something. Asserting the
   ultimacy of Nothing manufactures the linguistic being that asserts it
   (v2's `nihilism_is_an_existence_proof`, now internal to the ladder).
2. The thesis is *evaluable and false* wherever anything is alive
   (`nihilist_refuted_at_every_rung` below): given an error-free seed, no
   rung freezes, so `finalBelow` fails at every live tier.
3. At the floor the thesis "holds" — but only as everything does
   (`words_idle_at_floor`): trivially, idly, doing no separating work. The
   nihilist may retreat to the ground, but at the ground their thesis says
   nothing that silence does not.

And the nihilist is not a *position* on the ladder but a recurring *side*:
at every rung n+1 they reappear as that rung's `finalBelow` — the voice
claiming the previous level was final after all — and are refuted uniformly.
Not wrong so much as perpetually early, at every level at once. -/

/-- The nihilist's thesis exists: rung 1's language contains it. Statability
    is somethinghood. -/
theorem nihilist_thesis_is_something (d : Distinction G) :
    Nonempty ((reEmptied d).language.Claim) :=
  ⟨finalBelow⟩

/-- The nihilist refuted at every rung: no level of the ladder is absolute,
    so the claim "the level below was final" fails wherever it is live. -/
theorem nihilist_refuted_at_every_rung {d : Distinction G}
    (h : ErrorFree G d) :
    ∀ n, ¬ Absolutized (ladder d n) :=
  fun n hf => no_final_level (G := G) h ⟨n, hf⟩

/-! ## Instantiations at the concrete rows -/

/-- 有無 — śūnyatā of the beings distinction: no level of its re-emptying
    ladder freezes. Nishitani's central claim, at the schema's native row. -/
theorem beings_sunyata (G : Grid Contrib) : Sunyata (beingsRow G) :=
  fun ⟨n, hf⟩ => beingsLadder_no_level_final G n hf

/-- Śūnyatā of the before/after distinction: time's arrow functions where
    live and claims no floor — Nishitani's non-reified time, on which
    impermanence is neither an illusion (collapse) nor an absolute (freeze). -/
theorem time_sunyata (G : Grid Contrib) : Sunyata (beforeAfterRow G) :=
  fun ⟨n, hf⟩ => beforeAfterLadder_no_level_final G n hf

/-- Śūnyatā of the intra-weld arrow: the interior order functions where live
    and claims no floor. MMK 8's checked interior form joins the ladder rather
    than becoming hidden furniture inside a weld. -/
theorem intraWeldArrow_sunyata (G : Grid Contrib) :
    Sunyata (intraWeldArrowRow G) :=
  fun ⟨n, hf⟩ => intraWeldArrowLadder_no_level_final G n hf

/-- Śūnyatā of the weld-grain distinction: the weld held as svabhāva is the
    last unemptied level only while unnamed. Once named as a convention layer,
    it enters the same re-emptying ladder as the other readings. -/
theorem weld_sunyata (G : Grid Contrib) : Sunyata (weldRow G) :=
  fun ⟨n, hf⟩ => weldLadder_no_level_final G n hf

/-- Śūnyatā of doer/deed dependence: the mutual dependence itself is empty,
    so the row that denies a prior doer also refuses to freeze that denial as
    a final floor. -/
theorem doerDeed_sunyata (G : Grid Contrib) : Sunyata (doerDeedRow G) :=
  fun ⟨n, hf⟩ => doerDeedLadder_no_level_final G n hf

/-- 真空妙有 — true emptiness, wondrous being: the śūnyatā of contentful
    beings is available *only given a being*. The hypothesis is not a
    technical convenience but the doctrine itself in signature form: 色即是空
    requires 色. An empty world does not model this emptiness; it fails to
    supply `h`. v1's vacuity disease is excluded by the type. -/
theorem wondrous_being (G : Grid Contrib) (h : ∃ b : G.Being, ¬ G.Stone b) :
    Sunyata (contentBeingsRow G) :=
  fun ⟨n, hf⟩ => contentBeingsLadder_no_level_final_of_being (G := G) h n hf

end Nishitani
end GridConvention
end BeingConvention
end DirectedConvention
end Grid

/-! ## Appendix — the modal argument (self-contained, unchanged in substance)

Part II of v2 survives the rebase intact because it never depended on the
Position ladder; it is retained here as the frame-level companion to the
ladder-level relocation above. Placed at `WAA.Nishitani` rather than under
the grid lens because, per the naming discipline, it presupposes nothing of
the grid: worlds and concreta only. The correspondence:
`MetaphysicalNihilism`'s frame-relativity (`Frame → Prop`) is the external
face of what `nihilist_thesis_is_something` shows internally — the thesis
cannot be had without the field it was meant to escape. -/

namespace Nishitani

/-- A modal frame: worlds, and the concreta each world contains. -/
structure Frame where
  World    : Type
  Concreta : World → Type

/-- The nihilist's candidate Absolute Nothing: a world with no concreta. -/
def IsEmptyWorld (M : Frame) (w : M.World) : Prop :=
  ¬ Nonempty (M.Concreta w)

/-- Metaphysical nihilism, as statable: some world is empty. Note the type
    `Frame → Prop` — no frame-free formulation exists to assert. -/
def MetaphysicalNihilism (M : Frame) : Prop :=
  ∃ w : M.World, IsEmptyWorld M w

/-- Asserting the possibility of Nothing is an existence proof of Something:
    the thesis's truth requires a witness, and a possibility is a something. -/
theorem nihilism_is_an_existence_proof (M : Frame)
    (h : MetaphysicalNihilism M) : Nonempty M.World :=
  h.elim fun w _ => ⟨w⟩

/-- The absolute reading — nothing at all, not even the possibility — is
    unassertible: with no worlds, the thesis is unavailable, not true. -/
theorem no_worlds_no_thesis (M : Frame) (h : ¬ Nonempty M.World) :
    ¬ MetaphysicalNihilism M :=
  fun hn => h (nihilism_is_an_existence_proof M hn)

end Nishitani

/-! Closing caveat, one rung higher than before: `Sunyata` above is a name,
`sunyata_of_errorFree` a stated theorem, and by `ultimate_internalized` the
ladder is already prepared to treat this file's own conclusions as the
`finalBelow` of a level it has not yet built. It was built to climb through
this file too — and, this time, that is a theorem about *its* ladder rather
than mine. -/

end WAA
