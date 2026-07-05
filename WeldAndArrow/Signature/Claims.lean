/-
================================================================================
  WeldAndArrow.Signature.Claims
  Separate/fuse claim interface
================================================================================

Reading and motivation: Identification/Commentary.lean, C.1.
-/

import WeldAndArrow.Signature.Grid

namespace WAA

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

variable {Contrib : Type} [PreorderBot Contrib]

/- Reading and motivation: Identification/Commentary.lean, C.1. -/
inductive Tier (G : Grid Contrib)
  | floor
  | actTime (w : G.Weld)

variable (G : Grid Contrib)

/- Reading and motivation: Identification/Commentary.lean, C.1. -/
def Tier.hasLiveShare : Tier G → Prop
  | .floor     => False
  | .actTime w => G.HasSelfPoleIndex w

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

/- Reading and motivation: Identification/Commentary.lean, C.1. -/
def Distinction.Fused {G : Grid Contrib} (d : Distinction G) (t : Tier G) : Prop :=
  ¬ Tier.hasLiveShare G t →
    (d.language.TrueAt t d.sideA ↔ d.language.TrueAt t d.sideB)

/- Reading and motivation: Identification/Commentary.lean, C.1. -/
def Distinction.Collapse {G : Grid Contrib} (d : Distinction G) (t : Tier G) : Prop :=
  Tier.hasLiveShare G t ∧
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
  Tier.hasLiveShare G t ∧
    ¬ (d.language.TrueAt t d.sideA ↔ d.language.TrueAt t d.sideB)

/- Reading and motivation: Identification/Commentary.lean, C.1. -/
def Distinction.ObeysSeparateFuse {G : Grid Contrib} (d : Distinction G) :
    Prop :=
  (∀ t, Tier.hasLiveShare G t →
      ¬ (d.language.TrueAt t d.sideA ↔ d.language.TrueAt t d.sideB)) ∧
  (∀ t, ¬ Tier.hasLiveShare G t →
      (d.language.TrueAt t d.sideA ↔ d.language.TrueAt t d.sideB))

/-- The two voices of the system's diagnostics. -/
inductive VerdictVoice
  | assertable
  | displayable

/-- The two grades of error described in the theorem file. -/
inductive ErrorGrade
  | verdict
  | shortfall

namespace ErrorGrade

/-- Grade 1 verdicts are asserted inside the lens; Grade 2 verdicts are
    displayed without adding a value-command. -/
def voice : ErrorGrade → VerdictVoice
  | .verdict => .assertable
  | .shortfall => .displayable

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

/- Reading and motivation: Identification/Commentary.lean, C.1. -/
theorem not_freeze_of_same_claim (L : ClaimLanguage G) (p : L.Claim) :
    ¬ ({ language := L, sideA := p, sideB := p } : Distinction G).Freeze :=
  fun h => h Iff.rfl

end Grid

namespace Grid

namespace DirectedConvention
namespace BeingConvention
namespace GridConvention

variable {Contrib : Type} [PreorderBot Contrib]

/- The abstract separate/fuse machinery remains defined at `Grid` level for
   compatibility; these aliases expose its innermost reading-home. -/

abbrev Tier (G : Grid Contrib) := Grid.Tier G

abbrev ClaimLanguage (G : Grid Contrib) := Grid.ClaimLanguage G

abbrev RecordedUtterance (G : Grid Contrib) (L : Grid.ClaimLanguage G) :=
  Grid.RecordedUtterance G L

abbrev Distinction (G : Grid Contrib) := Grid.Distinction G

abbrev VerdictVoice := Grid.VerdictVoice

abbrev ErrorGrade := Grid.ErrorGrade

abbrev GeneratorOutcome (G : Grid Contrib) := Grid.GeneratorOutcome G

end GridConvention
end BeingConvention
end DirectedConvention

end Grid

end WAA