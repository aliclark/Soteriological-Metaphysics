/-
================================================================================
  WeldAndArrow.Meta.ReflexivityWitness
  One rung-indexed grid witnessing the ladder over its own labels
================================================================================

Jizang's fourfold two-truths are re-emptied here over their own rung labels.
This is a single legal grid instantiating the opaque `Being` parameter with
`Nat`; it is not a definition of `Being`, and it does not disturb the
boundary-freedom witnessed by `BeingNegative`.
-/

import WeldAndArrow.Meta.Nishitani

namespace WAA

namespace Grid
namespace DirectedConvention
namespace BeingConvention
namespace GridConvention

/-- A concrete grid whose being carrier is read as ladder-rung labels. This is
    one legal instantiation of the signature parameter, not a recovered being
    boundary or a claim that beings are numbers. -/
def ladderRungGrid : Grid Nat where
  Being      := Nat
  Call       := Unit
  Response   := Unit
  respondsTo _ _ := some ()
  grade b _ _ := b
  conditions _ _ := True

theorem ladderRungGrid_beings_sunyata :
    Nishitani.Sunyata (beingsRow ladderRungGrid) :=
  Nishitani.beings_sunyata ladderRungGrid

theorem ladderRungGrid_no_level_final :
    ∀ n, ¬ (beingsLadder ladderRungGrid n).Freeze :=
  beingsLadder_no_level_final ladderRungGrid

end GridConvention
end BeingConvention
end DirectedConvention
end Grid

end WAA
