/-
================================================================================
  WeldAndArrow.Consequences.ContentRows
  Content-bearing layer rows and the content beings ladder
================================================================================

Reading and motivation: Identification/Commentary.lean, C.2.
-/

import WeldAndArrow.Consequences.Ladder
namespace WAA

namespace Grid

variable {Contrib : Type} [PreorderBot Contrib]
variable (G : Grid Contrib)

namespace DirectedConvention
namespace BeingConvention
namespace GridConvention
/- --------------------------------------------------------------------------
   Content-bearing layer rows
-------------------------------------------------------------------------- -/

/-- Content-bearing language for the same layer claims. The convention-live
    side is still the live-share condition; the denial side now has content
    specific to the row. -/
def contentLayerLanguage (G : Grid Contrib) : ClaimLanguage G where
  Claim := LayerClaim
  Holds
    | .floor, _ => True
    | .actTime w, .conventionLive _ => G.HasSelfPoleIndex w
    | .actTime _, .layerDenied .directedTime => DirectionVoid Contrib
    | .actTime _, .layerDenied .intraWeldArrow =>
        ∀ b : G.Being, ¬ G.ResponseVariesWithCall b
    | .actTime _, .layerDenied .beings => G.AllStone
    | .actTime _, .layerDenied .gridLens => ∀ t : Tier G, ¬ Tier.hasLiveShare G t
    | .actTime _, .layerDenied .weldGrain => ¬ ∃ w : G.Weld, G.Actual w

def contentLayerRow (G : Grid Contrib) (l : ConventionLayer) : Distinction G :=
  { language := contentLayerLanguage G
    sideA := .conventionLive l
    sideB := .layerDenied l }

def contentBeforeAfterRow (G : Grid Contrib) : Distinction G :=
  contentLayerRow G .directedTime

def contentIntraWeldArrowRow (G : Grid Contrib) : Distinction G :=
  contentLayerRow G .intraWeldArrow

def contentBeingsRow (G : Grid Contrib) : Distinction G :=
  contentLayerRow G .beings

def contentGridLensRow (G : Grid Contrib) : Distinction G :=
  contentLayerRow G .gridLens

def contentWeldRow (G : Grid Contrib) : Distinction G :=
  contentLayerRow G .weldGrain

theorem contentLayerRow_obeys_of_direction
    (h : ∃ a b : Contrib, Strict a b) :
    (contentLayerRow G .directedTime).ObeysSeparateFuse := by
  rcases h with ⟨a, b, hstrict⟩
  constructor
  · intro t hLive
    cases t with
    | floor =>
        cases hLive
    | actTime _ =>
        dsimp [contentLayerRow, contentLayerLanguage, ClaimLanguage.TrueAt]
        intro hiff
        exact (hiff.mp hLive) a b hstrict
  · intro t hNotLive
    cases t with
    | floor =>
        constructor <;> intro _ <;> exact True.intro
    | actTime _ =>
        dsimp [contentLayerRow, contentLayerLanguage, ClaimLanguage.TrueAt]
        constructor
        · intro hLive
          exact False.elim (hNotLive hLive)
        · intro hvoid
          exact False.elim (hvoid a b hstrict)

theorem contentLayerRow_obeys_of_being
    (h : ∃ b : G.Being, ¬ G.Stone b) :
    (contentLayerRow G .beings).ObeysSeparateFuse := by
  rcases h with ⟨b, hnotStone⟩
  constructor
  · intro t hLive
    cases t with
    | floor =>
        cases hLive
    | actTime _ =>
        dsimp [contentLayerRow, contentLayerLanguage, ClaimLanguage.TrueAt]
        intro hiff
        exact hnotStone ((hiff.mp hLive) b)
  · intro t hNotLive
    cases t with
    | floor =>
        constructor <;> intro _ <;> exact True.intro
    | actTime _ =>
        dsimp [contentLayerRow, contentLayerLanguage, ClaimLanguage.TrueAt]
        constructor
        · intro hLive
          exact False.elim (hNotLive hLive)
        · intro hall
          exact False.elim (hnotStone (hall b))

theorem contentLayerRow_obeys_of_variation
    (h : ∃ b : G.Being, G.ResponseVariesWithCall b) :
    (contentLayerRow G .intraWeldArrow).ObeysSeparateFuse := by
  rcases h with ⟨b, hvaries⟩
  constructor
  · intro t hLive
    cases t with
    | floor =>
        cases hLive
    | actTime _ =>
        dsimp [contentLayerRow, contentLayerLanguage, ClaimLanguage.TrueAt]
        intro hiff
        exact (hiff.mp hLive) b hvaries
  · intro t hNotLive
    cases t with
    | floor =>
        constructor <;> intro _ <;> exact True.intro
    | actTime _ =>
        dsimp [contentLayerRow, contentLayerLanguage, ClaimLanguage.TrueAt]
        constructor
        · intro hLive
          exact False.elim (hNotLive hLive)
        · intro hstable
          exact False.elim (hstable b hvaries)

theorem contentLayerRow_obeys_of_liveTier
    (h : ∃ t : Tier G, Tier.hasLiveShare G t) :
    (contentLayerRow G .gridLens).ObeysSeparateFuse := by
  rcases h with ⟨liveTier, hLiveTier⟩
  constructor
  · intro t hLive
    cases t with
    | floor =>
        cases hLive
    | actTime _ =>
        dsimp [contentLayerRow, contentLayerLanguage, ClaimLanguage.TrueAt]
        intro hiff
        exact (hiff.mp hLive) liveTier hLiveTier
  · intro t hNotLive
    cases t with
    | floor =>
        constructor <;> intro _ <;> exact True.intro
    | actTime _ =>
        dsimp [contentLayerRow, contentLayerLanguage, ClaimLanguage.TrueAt]
        constructor
        · intro hLive
          exact False.elim (hNotLive hLive)
        · intro hnoLive
          exact False.elim (hnoLive liveTier hLiveTier)

theorem contentLayerRow_obeys_of_actual
    (h : ∃ w : G.Weld, G.Actual w) :
    (contentLayerRow G .weldGrain).ObeysSeparateFuse := by
  constructor
  · intro t hLive
    cases t with
    | floor =>
        cases hLive
    | actTime _ =>
        dsimp [contentLayerRow, contentLayerLanguage, ClaimLanguage.TrueAt]
        intro hiff
        exact (hiff.mp hLive) h
  · intro t hNotLive
    cases t with
    | floor =>
        constructor <;> intro _ <;> exact True.intro
    | actTime _ =>
        dsimp [contentLayerRow, contentLayerLanguage, ClaimLanguage.TrueAt]
        constructor
        · intro hLive
          exact False.elim (hNotLive hLive)
        · intro hnone
          exact False.elim (hnone h)

theorem contentBeforeAfterRow_obeys_of_direction
    (h : ∃ a b : Contrib, Strict a b) :
    (contentBeforeAfterRow G).ObeysSeparateFuse :=
  contentLayerRow_obeys_of_direction G h

theorem contentIntraWeldArrowRow_obeys_of_variation
    (h : ∃ b : G.Being, G.ResponseVariesWithCall b) :
    (contentIntraWeldArrowRow G).ObeysSeparateFuse :=
  contentLayerRow_obeys_of_variation G h

theorem contentBeingsRow_obeys_of_being
    (h : ∃ b : G.Being, ¬ G.Stone b) :
    (contentBeingsRow G).ObeysSeparateFuse :=
  contentLayerRow_obeys_of_being G h

theorem contentGridLensRow_obeys_of_liveTier
    (h : ∃ t : Tier G, Tier.hasLiveShare G t) :
    (contentGridLensRow G).ObeysSeparateFuse :=
  contentLayerRow_obeys_of_liveTier G h

theorem contentWeldRow_obeys_of_actual
    (h : ∃ w : G.Weld, G.Actual w) :
    (contentWeldRow G).ObeysSeparateFuse :=
  contentLayerRow_obeys_of_actual G h

/-- An actual utterance of the beings-denial cannot fit an act-time tier:
    the utterer's actual response supplies a non-stone witness. -/
theorem beings_denial_fits_only_floor
    (u : RecordedUtterance G (contentLayerLanguage G))
    (hc : u.content = .layerDenied .beings)
    (w' : G.Weld) (ht : u.offeredAt = .actTime w') :
    ¬ u.FitsOfferedTier := by
  intro hfit
  change (contentLayerLanguage G).TrueAt u.offeredAt u.content at hfit
  rw [ht, hc] at hfit
  dsimp [contentLayerLanguage, ClaimLanguage.TrueAt] at hfit
  exact (G.not_stone_of_actual u.weld u.actual) (hfit u.weld.agent)

/-- A directed-time denial offered by an appropriating utterer cannot fit an
    act-time tier: the utterer's live share is itself a strict direction. -/
theorem time_denial_unfit_for_appropriating_utterer
    (u : RecordedUtterance G (contentLayerLanguage G))
    (hc : u.content = .layerDenied .directedTime)
    (hidx : G.HasSelfPoleIndex u.weld)
    (w' : G.Weld) (ht : u.offeredAt = .actTime w') :
    ¬ u.FitsOfferedTier := by
  intro hfit
  change (contentLayerLanguage G).TrueAt u.offeredAt u.content at hfit
  rw [ht, hc] at hfit
  dsimp [contentLayerLanguage, ClaimLanguage.TrueAt] at hfit
  exact hfit (shareBot : Contrib) (G.share u.weld)
    (G.strict_shareBot_of_hasSelfPoleIndex u.weld hidx)

/-- The schema-level intra-weld arrow denial is still live-tier unfit by the
    row-language check. A single recorded content utterance does not by itself
    extract two different responses, so the stronger content-variation form is
    intentionally not claimed here. -/
theorem interior_order_denial_unfit_for_live_utterer
    (u : RecordedUtterance G (rowLanguage G))
    (hcontent : u.content = .denied (.layer .intraWeldArrow))
    (hlive : Tier.hasLiveShare G u.offeredAt) :
    ¬ RecordedUtterance.FitsOfferedTier u :=
  denied_misfits_live_offer G (.layer .intraWeldArrow) u hcontent hlive

def contentBeingsLadder (G : Grid Contrib) : Nat → Distinction G :=
  ladder (contentBeingsRow G)

theorem contentBeingsLadder_obeys_of_being
    (h : ∃ b : G.Being, ¬ G.Stone b) :
    ∀ n, (contentBeingsLadder G n).ObeysSeparateFuse :=
  ladder_obeys (G := G) (contentBeingsRow_obeys_of_being G h)

theorem contentBeingsLadder_no_level_final_of_being
    (h : ∃ b : G.Being, ¬ G.Stone b) :
    ∀ n, ¬ (contentBeingsLadder G n).Freeze :=
  no_level_final_of_obeys (G := G) (contentBeingsRow_obeys_of_being G h)
end GridConvention
end BeingConvention
end DirectedConvention

end Grid

end WAA
