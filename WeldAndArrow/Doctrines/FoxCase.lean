/-
================================================================================
  WeldAndArrow.Doctrines.FoxCase
  Dukkha-facing fox case checks
================================================================================

The concrete fox grid lives in `Consequences/FoxCase.lean`. This adjacent
doctrine module adds only the Four Truths vocabulary needed to say that a
clenched fox-life reception is the worked dukkha example.

Reading and motivation: Identification/Commentary.lean, C.7a.
-/

import WeldAndArrow.Consequences.FoxCase
import WeldAndArrow.Doctrines.FourTruths

namespace WAA

namespace FoxCase

/-- "Each clenched reception is that life's dukkha": live mismatch is present,
    and its grade is definitionally the reception's share. -/
theorem fox_dukkha_per_life (n : Nat) :
    foxGrid.WaaMismatchLive (lifeReception (n + 1)) ∧
      foxGrid.WaaMismatchGrade (lifeReception (n + 1)) =
        foxGrid.share (lifeReception (n + 1)) :=
  ⟨fox_reception_clenched n, rfl⟩

end FoxCase

end WAA
