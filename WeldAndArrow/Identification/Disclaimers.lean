/-
================================================================================
  WeldAndArrow.Identification.Disclaimers
  Disclaimer enumeration and number pins
================================================================================

Reading and motivation: Identification/Commentary.lean.
-/

import WeldAndArrow.Identification.Placements

namespace WAA

/- ==============================================================================
   §5  Disclaimers
============================================================================== -/

/-- The original moves plus the being-convention extension enumerated in
    `Paper/Proofs.md`. -/
inductive Disclaimer
  | tieringSeparateFuse
  | shoAgencyLent
  | forMeNessInWeld
  | receptionReachBack
  | threeRegisterSorting
  | linjiReading
  | shoVersusSatori
  | genjoArrivals
  | waaKarmaIdentification
  | weldTokenReflexivity
  | mmk17Decomposition
  | stoneOutsideEdge
  | generatedTaxonomy
  | twoErrorGrades
  | shareDropEvent
  | theoryStatus
  | rowTwoIndexPlacement
  | shareDetermination
  | dispositionActRetype
  | passiveSpent
  | clenchSelfShare
  | vacuityFromField
  | memoryPrudence
  | dukkhaFieldSide
  | asymmetricDomain
  | transposition
  | mirrorTerminus
  | threeKillings
  | officesSpine
  | contemporaryPlacement
  | hakuinReading
  | retypeOutcome
  | svakarmaDemotion
  | orthogonalityPrice
  | beingConvention
  | pilotGeneratedRows
  | beingTrichotomy
  | hareHornRegister
  | modalRealismFreeze
  | aptnessConditionality
  | sraddhaConditional
  | faithBothConjuncts
  | generatedTableStructure
  | poleAffirmingSemantics
  | proseRows
  | errorFreeReading
  | misFeedFence

namespace Disclaimer

/-- Preserve the paper's numbering without making the number itself carry
    doctrinal weight. -/
def number : Disclaimer → Nat
  | .tieringSeparateFuse => 1
  | .shoAgencyLent => 2
  | .forMeNessInWeld => 3
  | .receptionReachBack => 4
  | .threeRegisterSorting => 5
  | .linjiReading => 6
  | .shoVersusSatori => 7
  | .genjoArrivals => 8
  | .waaKarmaIdentification => 9
  | .weldTokenReflexivity => 10
  | .mmk17Decomposition => 11
  | .stoneOutsideEdge => 12
  | .generatedTaxonomy => 13
  | .twoErrorGrades => 14
  | .shareDropEvent => 15
  | .theoryStatus => 16
  | .rowTwoIndexPlacement => 17
  | .shareDetermination => 18
  | .dispositionActRetype => 19
  | .passiveSpent => 20
  | .clenchSelfShare => 21
  | .vacuityFromField => 22
  | .memoryPrudence => 23
  | .dukkhaFieldSide => 24
  | .asymmetricDomain => 25
  | .transposition => 26
  | .mirrorTerminus => 27
  | .threeKillings => 28
  | .officesSpine => 29
  | .contemporaryPlacement => 30
  | .hakuinReading => 31
  | .retypeOutcome => 32
  | .svakarmaDemotion => 33
  | .orthogonalityPrice => 34
  | .beingConvention => 35
  | .pilotGeneratedRows => 36
  | .beingTrichotomy => 37
  | .hareHornRegister => 38
  | .modalRealismFreeze => 39
  | .aptnessConditionality => 40
  | .sraddhaConditional => 41
  | .faithBothConjuncts => 42
  | .generatedTableStructure => 43
  | .poleAffirmingSemantics => 44
  | .proseRows => 45
  | .errorFreeReading => 46
  | .misFeedFence => 47

theorem waaKarmaIdentification_number :
    number Disclaimer.waaKarmaIdentification = 9 := rfl

theorem modalRealismFreeze_number :
    number Disclaimer.modalRealismFreeze = 39 := rfl

theorem aptnessConditionality_number :
    number Disclaimer.aptnessConditionality = 40 := rfl

theorem sraddhaConditional_number :
    number Disclaimer.sraddhaConditional = 41 := rfl

theorem faithBothConjuncts_number :
    number Disclaimer.faithBothConjuncts = 42 := rfl

theorem generatedTableStructure_number :
    number Disclaimer.generatedTableStructure = 43 := rfl

theorem poleAffirmingSemantics_number :
    number Disclaimer.poleAffirmingSemantics = 44 := rfl

theorem errorFreeReading_number :
    number Disclaimer.errorFreeReading = 46 := rfl

theorem misFeedFence_number :
    number Disclaimer.misFeedFence = 47 := rfl

end Disclaimer

end WAA