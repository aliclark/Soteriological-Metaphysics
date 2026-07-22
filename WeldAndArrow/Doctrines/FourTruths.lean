/-
================================================================================
  WeldAndArrow.Doctrines.FourTruths
  Checked four-truth-facing consequences in the grid's own vocabulary
================================================================================

This module separates the grid-derived clench mismatch from its supplied
phenomenal reading.  Mismatch covaries with share because it is read from the
same Row-2 display value; whether that mismatch is suffered is relative to a
`SentienceReading`.
-/

import WeldAndArrow.Consequences.Basic

namespace WAA

namespace Grid

variable {Contrib : Type} [PreorderBot Contrib]
variable (G : Grid Contrib)

/- ==============================================================================
   Truths 1-3: mismatch as a display reading
============================================================================== -/

/-- `WaaMismatchGrade` is read from the same structure as share. This is
    covariation, not a second operational measure. -/
def WaaMismatchGrade (w : G.Weld) : Contrib :=
  G.share w

@[simp]
theorem waaMismatchGrade_eq_share (w : G.Weld) :
    G.WaaMismatchGrade w = G.share w :=
  rfl

/-- Ordinal covariation: lowering share lowers mismatch grade in the same
    display order, because the two readings unfold to the same value. -/
theorem waaMismatchGrade_le_of_share_le {w₁ w₂ : G.Weld}
    (h : G.share w₁ ≼ G.share w₂) :
    G.WaaMismatchGrade w₁ ≼ G.WaaMismatchGrade w₂ :=
  h

/-- The structural content formerly carried by `WaaMismatchLive`: an actual
    occurrence with a live self-pole index.  It is grid-statable for sentient
    and insentient acts alike. -/
def ClenchMismatch (w : G.Weld) : Prop :=
  G.Actual w ∧ G.HasSelfPoleIndex w

/-- Given occurrence actuality, clench mismatch is exactly the live self-pole
    index condition. -/
theorem clenchMismatch_iff_hasSelfPoleIndex
    {w : G.Weld} (hactual : G.Actual w) :
    G.ClenchMismatch w ↔ G.HasSelfPoleIndex w := by
  constructor
  · intro h
    exact h.right
  · intro hidx
    exact ⟨hactual, hidx⟩

/-- Dukkha is the sentient reading of a structural clench mismatch.  The
    structure is derived; the suffering is supplied. -/
def WaaDukkha (S : SentienceReading G) (w : G.Weld) : Prop :=
  S.sentient w ∧ G.ClenchMismatch w

theorem clenchMismatch_of_waaDukkha
    {S : SentienceReading G} {w : G.Weld} (h : G.WaaDukkha S w) :
    G.ClenchMismatch w :=
  h.right

theorem sentientAct_of_waaDukkha
    {S : SentienceReading G} {w : G.Weld} (h : G.WaaDukkha S w) :
    G.SentientAct S w :=
  ⟨h.right.left, h.left⟩

/-- Insentient appropriation carries the same structural mismatch without a
    dukkha reading. -/
theorem clenchMismatch_of_insentientAppropriation
    {S : SentienceReading G} {w : G.Weld}
    (h : G.InsentientAppropriation S w) :
    G.ClenchMismatch w :=
  ⟨h.left.left, h.right⟩

theorem not_waaDukkha_of_insentientAct
    {S : SentienceReading G} {w : G.Weld}
    (h : G.InsentientAct S w) :
    ¬ G.WaaDukkha S w :=
  fun hdukkha => h.right hdukkha.left

/-- A terminus response has mismatch grade at the pole-class. -/
theorem waaMismatch_atBot_of_terminus_response
    {b : G.Being} {c : G.Call} {r : G.Response}
    (hterm : G.Terminus b) (hresp : G.respondsTo b c = some r) :
    AtBot (G.WaaMismatchGrade ⟨b, c, r⟩) :=
  G.atBot_of_terminus_response hterm hresp

/-- A terminus response has no clench mismatch. -/
theorem not_clenchMismatch_of_terminus_response
    {b : G.Being} {c : G.Call} {r : G.Response}
    (hterm : G.Terminus b) (hresp : G.respondsTo b c = some r) :
    ¬ G.ClenchMismatch ⟨b, c, r⟩ := by
  intro h
  exact h.right (G.waaMismatch_atBot_of_terminus_response hterm hresp)

theorem not_waaDukkha_of_terminus_response
    (S : SentienceReading G)
    {b : G.Being} {c : G.Call} {r : G.Response}
    (hterm : G.Terminus b) (hresp : G.respondsTo b c = some r) :
    ¬ G.WaaDukkha S ⟨b, c, r⟩ :=
  fun h => G.not_clenchMismatch_of_terminus_response hterm hresp h.right

end Grid

end WAA
