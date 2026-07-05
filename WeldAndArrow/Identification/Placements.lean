/-
================================================================================
  WeldAndArrow.Identification.Placements
  Contemporary placements
================================================================================

Reading and motivation: Identification/Commentary.lean.
-/

import WeldAndArrow.Identification.Ownership

namespace WAA

/-- Contemporary positions placed by `Paper/Proofs.md`. -/
inductive ContemporaryPosition
  | siderits
  | ganeri
  | zahavi
  | sartre

/-- Their grid placement. -/
inductive ContemporaryPlacement
  | seriesQuestions
  | nearestAlly
  | retype
  | occupant

namespace ContemporaryPosition

/-- The grid placement assigned to each contemporary position in the paper. -/
def waaPlacement : ContemporaryPosition → ContemporaryPlacement
  | .siderits => .seriesQuestions
  | .ganeri => .nearestAlly
  | .zahavi => .retype
  | .sartre => .occupant

theorem siderits_waaPlacement :
    waaPlacement ContemporaryPosition.siderits = ContemporaryPlacement.seriesQuestions := rfl

theorem ganeri_waaPlacement :
    waaPlacement ContemporaryPosition.ganeri = ContemporaryPlacement.nearestAlly := rfl

theorem zahavi_waaPlacement :
    waaPlacement ContemporaryPosition.zahavi = ContemporaryPlacement.retype := rfl

theorem sartre_waaPlacement :
    waaPlacement ContemporaryPosition.sartre = ContemporaryPlacement.occupant := rfl

end ContemporaryPosition

namespace Grid

variable {Contrib : Type} [PreorderBot Contrib]
variable (G : Grid Contrib)

/- Encoding check: the `retype` constructor exists and applies to any pair
   of distinctions (used by the Zahavi placement and the disposition/act
   redrawing). An `example`, not a theorem, for the same reason the voice
   and placement checks are. -/
theorem retype_constructor_exists
    (oldDistinction newDistinction : Distinction G) :
    ∃ out : GeneratorOutcome G,
      out = GeneratorOutcome.retype oldDistinction newDistinction :=
  ⟨GeneratorOutcome.retype oldDistinction newDistinction, rfl⟩

end Grid

end WAA