/-
================================================================================
  WeldAndArrow.Consequences.Ladder
  Re-emptying ladder generated from taxonomy rows
================================================================================

Reading and motivation: Identification/Commentary.lean, C.2.
-/

import WeldAndArrow.Consequences.Taxonomy
namespace WAA

namespace Grid

variable {Contrib : Type} [PreorderBot Contrib]
variable (G : Grid Contrib)

namespace DirectedConvention
namespace BeingConvention
namespace GridConvention
/- --------------------------------------------------------------------------
   Re-emptying ladder
-------------------------------------------------------------------------- -/

/-- The two sides used to re-empty a distinction. Deliberately, neither side
    quantifies over ladder levels; level-quantification stays in meta-theorems. -/
inductive LadderSide
  | liveBelow
  | finalBelow

/-- Re-empty a distinction: the new row separates the lower row's live
    separation from the claim that the lower row survives the floor. -/
def reEmptied {G : Grid Contrib} (d : Distinction G) : Distinction G where
  language :=
    { Claim := LadderSide
      Holds := fun t c =>
        match t, c with
        | .floor, _ => True
        | .actTime w, .liveBelow => d.Separated (.actTime w)
        | .actTime _, .finalBelow => d.Freeze }
  sideA := .liveBelow
  sideB := .finalBelow

def ladder {G : Grid Contrib} (d : Distinction G) : Nat → Distinction G
  | 0 => d
  | n + 1 => reEmptied (ladder d n)

theorem reEmptied_obeysSeparateFuse
    {d : Distinction G} (h : d.ObeysSeparateFuse) :
    (reEmptied d).ObeysSeparateFuse := by
  constructor
  · intro t hLive
    cases t with
    | floor =>
        cases hLive
    | actTime _ =>
        dsimp [reEmptied, ClaimLanguage.TrueAt]
        intro hiff
        exact (Grid.not_freeze_of_obeysSeparateFuse h)
          (hiff.mp (G.separated_of_obeysSeparateFuse h hLive))
  · intro t hNotLive
    cases t with
    | floor =>
        constructor <;> intro _ <;> exact True.intro
    | actTime _ =>
        dsimp [reEmptied, ClaimLanguage.TrueAt]
        constructor
        · intro hsep
          exact False.elim (hNotLive hsep.left)
        · intro hfreeze
          exact False.elim ((Grid.not_freeze_of_obeysSeparateFuse h) hfreeze)

/-- Error-freedom below is enough for the re-emptying row above to obey the
    full rule. This is the cumulative ladder form: `finalBelow` is exactly the
    lower row's freeze, so the non-live clause is supplied by the lower row's
    refutation rather than by a new stability premise. -/
theorem reEmptied_obeys_of_errorFree
    {d : Distinction G} (h : ErrorFree G d) :
    (reEmptied d).ObeysSeparateFuse := by
  constructor
  · intro t hLive
    cases t with
    | floor =>
        cases hLive
    | actTime w =>
        dsimp [reEmptied, ClaimLanguage.TrueAt]
        have hnotIff :
            ¬ (d.language.TrueAt (Tier.actTime w) d.sideA ↔
              d.language.TrueAt (Tier.actTime w) d.sideB) := by
          intro hiff
          exact h.left (Tier.actTime w) ⟨hLive, hiff⟩
        have hsep : d.Separated (Tier.actTime w) := ⟨hLive, hnotIff⟩
        intro hiff
        exact h.right (hiff.mp hsep)
  · intro t hNotLive
    cases t with
    | floor =>
        dsimp [reEmptied, ClaimLanguage.TrueAt]
        constructor <;> intro _ <;> exact True.intro
    | actTime _ =>
        dsimp [reEmptied, ClaimLanguage.TrueAt]
        constructor
        · intro hsep
          exact False.elim (hNotLive hsep.left)
        · intro hfreeze
          exact False.elim (h.right hfreeze)

theorem ladder_obeys {d : Distinction G} (h : d.ObeysSeparateFuse) :
    ∀ n, (ladder d n).ObeysSeparateFuse := by
  intro n
  induction n with
  | zero =>
      exact h
  | succ _ ih =>
      exact reEmptied_obeysSeparateFuse (G := G) ih

/-- Once a seed is error-free, every positive ladder level obeys without a
    separate obedience hypothesis at level zero. -/
theorem ladder_obeys_of_errorFree
    {d : Distinction G} (h : ErrorFree G d) :
    ∀ n, (ladder d (n + 1)).ObeysSeparateFuse := by
  intro n
  induction n with
  | zero =>
      exact reEmptied_obeys_of_errorFree (G := G) h
  | succ _ ih =>
      exact reEmptied_obeysSeparateFuse (G := G) ih

theorem ladder_errorFree_of_errorFree
    {d : Distinction G} (h : ErrorFree G d) :
    ∀ n, ErrorFree G (ladder d (n + 1)) := by
  intro n
  exact Grid.errorFree_of_obeys G (ladder_obeys_of_errorFree (G := G) h n)

theorem no_level_final_of_obeys {d : Distinction G} (h : d.ObeysSeparateFuse) :
    ∀ n, ¬ (ladder d n).Freeze := by
  intro n
  exact Grid.not_freeze_of_obeysSeparateFuse (ladder_obeys (G := G) h n)

/-- Emptiness-sickness has no final level to name: with an error-free seed,
    neither level zero nor any positive re-emptying level can freeze. -/
theorem no_final_level_of_errorFree {d : Distinction G} (h : ErrorFree G d) :
    ¬ ∃ n, (ladder d n).Freeze := by
  rintro ⟨n, hfreeze⟩
  cases n with
  | zero =>
      exact h.right hfreeze
  | succ n =>
      exact (Grid.not_freeze_of_obeysSeparateFuse
        (ladder_obeys_of_errorFree (G := G) h n)) hfreeze

theorem ladder_collapse_self_refuting
    {d : Distinction G} (h : d.ObeysSeparateFuse) :
    ∀ n t, ¬ (ladder d n).Collapse t := by
  intro n t
  exact Grid.not_collapse_of_obeysSeparateFuse (ladder_obeys (G := G) h n) t

def beingsLadder (G : Grid Contrib) : Nat → Distinction G :=
  ladder (beingsRow G)

def beforeAfterLadder (G : Grid Contrib) : Nat → Distinction G :=
  ladder (beforeAfterRow G)

def intraWeldArrowLadder (G : Grid Contrib) : Nat → Distinction G :=
  ladder (intraWeldArrowRow G)

def gridLensLadder (G : Grid Contrib) : Nat → Distinction G :=
  ladder (gridLensRow G)

def weldLadder (G : Grid Contrib) : Nat → Distinction G :=
  ladder (weldRow G)

def doerDeedLadder (G : Grid Contrib) : Nat → Distinction G :=
  ladder (doerDeedRow G)

theorem beingsLadder_obeys
    [∀ w : G.Weld, Decidable (AtBot (G.share w))] :
    ∀ n, (beingsLadder G n).ObeysSeparateFuse :=
  ladder_obeys (G := G) (beingsRow_obeys G)

theorem beingsLadder_obeys_succ :
    ∀ n, (beingsLadder G (n + 1)).ObeysSeparateFuse :=
  ladder_obeys_of_errorFree (G := G) (rowOf_errorFree G (.layer .beings))

theorem beingsLadder_no_level_final :
    ∀ n, ¬ (beingsLadder G n).Freeze := by
  intro n
  cases n with
  | zero =>
      exact beingsRow_not_freeze G
  | succ n =>
      exact Grid.not_freeze_of_obeysSeparateFuse (beingsLadder_obeys_succ G n)

theorem beforeAfterLadder_obeys
    [∀ w : G.Weld, Decidable (AtBot (G.share w))] :
    ∀ n, (beforeAfterLadder G n).ObeysSeparateFuse :=
  ladder_obeys (G := G) (beforeAfterRow_obeys G)

theorem beforeAfterLadder_obeys_succ :
    ∀ n, (beforeAfterLadder G (n + 1)).ObeysSeparateFuse :=
  ladder_obeys_of_errorFree (G := G) (rowOf_errorFree G (.layer .directedTime))

theorem beforeAfterLadder_no_level_final :
    ∀ n, ¬ (beforeAfterLadder G n).Freeze := by
  intro n
  cases n with
  | zero =>
      exact beforeAfterRow_not_freeze G
  | succ n =>
      exact Grid.not_freeze_of_obeysSeparateFuse (beforeAfterLadder_obeys_succ G n)

theorem intraWeldArrowLadder_obeys
    [∀ w : G.Weld, Decidable (AtBot (G.share w))] :
    ∀ n, (intraWeldArrowLadder G n).ObeysSeparateFuse :=
  ladder_obeys (G := G) (intraWeldArrowRow_obeys G)

theorem intraWeldArrowLadder_obeys_succ :
    ∀ n, (intraWeldArrowLadder G (n + 1)).ObeysSeparateFuse :=
  ladder_obeys_of_errorFree (G := G)
    (rowOf_errorFree G (.layer .intraWeldArrow))

theorem intraWeldArrowLadder_no_level_final :
    ∀ n, ¬ (intraWeldArrowLadder G n).Freeze := by
  intro n
  cases n with
  | zero =>
      exact intraWeldArrowRow_not_freeze G
  | succ n =>
      exact Grid.not_freeze_of_obeysSeparateFuse
        (intraWeldArrowLadder_obeys_succ G n)

theorem gridLensLadder_obeys
    [∀ w : G.Weld, Decidable (AtBot (G.share w))] :
    ∀ n, (gridLensLadder G n).ObeysSeparateFuse :=
  ladder_obeys (G := G) (gridLensRow_obeys G)

theorem gridLensLadder_obeys_succ :
    ∀ n, (gridLensLadder G (n + 1)).ObeysSeparateFuse :=
  ladder_obeys_of_errorFree (G := G) (rowOf_errorFree G (.layer .gridLens))

theorem gridLensLadder_no_level_final :
    ∀ n, ¬ (gridLensLadder G n).Freeze := by
  intro n
  cases n with
  | zero =>
      exact gridLensRow_not_freeze G
  | succ n =>
      exact Grid.not_freeze_of_obeysSeparateFuse (gridLensLadder_obeys_succ G n)

theorem weldLadder_obeys
    [∀ w : G.Weld, Decidable (AtBot (G.share w))] :
    ∀ n, (weldLadder G n).ObeysSeparateFuse :=
  ladder_obeys (G := G) (weldRow_obeys G)

theorem weldLadder_obeys_succ :
    ∀ n, (weldLadder G (n + 1)).ObeysSeparateFuse :=
  ladder_obeys_of_errorFree (G := G) (rowOf_errorFree G (.layer .weldGrain))

theorem weldLadder_no_level_final :
    ∀ n, ¬ (weldLadder G n).Freeze := by
  intro n
  cases n with
  | zero =>
      exact weldRow_not_freeze G
  | succ n =>
      exact Grid.not_freeze_of_obeysSeparateFuse (weldLadder_obeys_succ G n)

theorem doerDeedLadder_obeys
    [∀ w : G.Weld, Decidable (AtBot (G.share w))] :
    ∀ n, (doerDeedLadder G n).ObeysSeparateFuse :=
  ladder_obeys (G := G) (doerDeedRow_obeys G)

theorem doerDeedLadder_obeys_succ :
    ∀ n, (doerDeedLadder G (n + 1)).ObeysSeparateFuse :=
  ladder_obeys_of_errorFree (G := G) (rowOf_errorFree G .doerDeed)

theorem doerDeedLadder_no_level_final :
    ∀ n, ¬ (doerDeedLadder G n).Freeze := by
  intro n
  cases n with
  | zero =>
      exact doerDeedRow_not_freeze G
  | succ n =>
      exact Grid.not_freeze_of_obeysSeparateFuse
        (doerDeedLadder_obeys_succ G n)

end GridConvention
end BeingConvention
end DirectedConvention

end Grid

end WAA
