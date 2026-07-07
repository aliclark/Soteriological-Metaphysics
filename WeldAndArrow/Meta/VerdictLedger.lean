/-
================================================================================
  WeldAndArrow.Meta.VerdictLedger
  The verdict history as inspectable data
================================================================================

The theorem-file history paragraph is inductive testimony at the outer edge:
Lean cannot prove that the episodes happened, that the retypes were forced
rather than chosen, that they were recorded before later objections, or that a
future decline-and-retype rate will not shrink.

What this module can check is the office discipline around that testimony. The
ledger stores episode-grained entries, then derives the paragraph's aggregate
claims from the list: the number of retypes, the six displayed restraint kinds,
anchor cross-references, and the structural half of the falsifier. In
particular, the four retypes are four entries, not one entry carrying a
multiplicity field.
-/

import WeldAndArrow.Consequences.Taxonomy
import WeldAndArrow.Meta.InvarianceNegative
import WeldAndArrow.Identification.Residues

namespace WAA

/- ==============================================================================
   Verdict history data
============================================================================== -/

/-- The four public verdict-shapes named by the theorem-file generator
    paragraph, as a small ledger vocabulary. The semantic `GeneratorOutcome`
    over concrete distinctions remains in `Signature/Claims.lean`; this type is
    only the history paragraph's record code. -/
inductive Verdict
  | landed
  | newCell
  | declined
  | retype
deriving DecidableEq, Repr, BEq

/-- The cases listed in the verdict-history paragraph, in paragraph order. -/
inductive LedgerCaseName
  | zahavi
  | dispositionActCell
  | arrow
  | intraWeldArrow
  | terminusQuestion
  | foxQuestion
  | deafBlind
  | openDeliveryQuestions
  | seriesQuestions
deriving DecidableEq, Repr, BEq

/-- Outcomes recorded by the ledger. `noVerdict` and `ceded` are not generator
    verdicts; they are ledger postures for open delivery questions and ceded
    series questions. -/
inductive Outcome
  | verdict (v : Verdict)
  | noVerdict
  | ceded
deriving DecidableEq, Repr, BEq

/-- Prose anchors carried at episode grain. -/
inductive ProseAnchor
  | proofsZahavi
  | theoryAttainmentDispositionAct
  | theoryDeafBlindDecline
  | openDeliveryQuestions
  | seriesQuestions
deriving DecidableEq, Repr, BEq

/-- Lean anchors carried at episode grain. Separate examples below mention the
    declarations by name so ordinary renames break this module. -/
inductive LeanAnchor
  | directionNegative
  | interiorDirectionNegative
  | transpositionPair
  | foxLiveOffer
  | misFeedFenceGate
deriving DecidableEq, Repr, BEq

/-- The anchoring situation for one ledger episode. -/
inductive RecordAnchor
  | prose (anchor : ProseAnchor)
  | lean (anchor : LeanAnchor)
deriving DecidableEq, Repr, BEq

/-- One entry in the generator's self-ledger.

    The decomposition booleans are deliberately light data. They let the
    structural falsifier fail when a future mis-feed verdict is entered without
    its decomposition, but they do not prove that an author tagged the future
    case honestly. -/
structure RecordEntry where
  name : LedgerCaseName
  outcome : Outcome
  anchors : List RecordAnchor
  requiresDecomposition : Bool
  decompositionCarried : Bool
deriving DecidableEq, Repr, BEq

/-- The verdict-history paragraph as episode-grained data. -/
def generatorRecord : List RecordEntry := [
  { name := .zahavi
    outcome := .verdict .retype
    anchors := [.prose .proofsZahavi]
    requiresDecomposition := false
    decompositionCarried := false },
  { name := .dispositionActCell
    outcome := .verdict .retype
    anchors := [.prose .theoryAttainmentDispositionAct]
    requiresDecomposition := false
    decompositionCarried := false },
  { name := .arrow
    outcome := .verdict .retype
    anchors := [.lean .directionNegative]
    requiresDecomposition := false
    decompositionCarried := false },
  { name := .intraWeldArrow
    outcome := .verdict .retype
    anchors := [.lean .interiorDirectionNegative]
    requiresDecomposition := false
    decompositionCarried := false },
  { name := .terminusQuestion
    outcome := .verdict .landed
    anchors := [.lean .transpositionPair, .lean .misFeedFenceGate]
    requiresDecomposition := true
    decompositionCarried := true },
  { name := .foxQuestion
    outcome := .verdict .landed
    anchors := [.lean .foxLiveOffer]
    requiresDecomposition := true
    decompositionCarried := true },
  { name := .deafBlind
    outcome := .verdict .declined
    anchors := [.prose .theoryDeafBlindDecline]
    requiresDecomposition := false
    decompositionCarried := false },
  { name := .openDeliveryQuestions
    outcome := .noVerdict
    anchors := [.prose .openDeliveryQuestions]
    requiresDecomposition := false
    decompositionCarried := false },
  { name := .seriesQuestions
    outcome := .ceded
    anchors := [.prose .seriesQuestions]
    requiresDecomposition := false
    decompositionCarried := false }
]

example : generatorRecord.length = 9 := rfl

example :
    generatorRecord.map RecordEntry.name =
      [.zahavi, .dispositionActCell, .arrow, .intraWeldArrow,
        .terminusQuestion, .foxQuestion, .deafBlind, .openDeliveryQuestions,
        .seriesQuestions] := rfl

/-- The paragraph's "four retypes" claim is derived from the episode list. -/
theorem generatorRecord_retype_count :
    (generatorRecord.filter
      (fun e => e.outcome == Outcome.verdict Verdict.retype)).length = 4 := rfl

/-- No current episode forces a new row; the ledger adds no `RowTag`. -/
theorem generatorRecord_newCell_count :
    (generatorRecord.filter
      (fun e => e.outcome == Outcome.verdict Verdict.newCell)).length = 0 := rfl

/- ==============================================================================
   Restraint-kind projection
============================================================================== -/

/-- The six displayed kinds of restraint are a projection from entries, not the
    ledger's stored grain. -/
inductive RestraintKind
  | forcedRetype
  | answeredAtCheapDissolution
  | answeredAvyakataShaped
  | declinedNoError
  | standingNoVerdict
  | cededWholesale
deriving DecidableEq, Repr, BEq

/-- Coarsen an episode to the six-kind display view. -/
def restraintKind (e : RecordEntry) : RestraintKind :=
  match e.name with
  | .zahavi => .forcedRetype
  | .dispositionActCell => .forcedRetype
  | .arrow => .forcedRetype
  | .intraWeldArrow => .forcedRetype
  | .terminusQuestion => .answeredAtCheapDissolution
  | .foxQuestion => .answeredAvyakataShaped
  | .deafBlind => .declinedNoError
  | .openDeliveryQuestions => .standingNoVerdict
  | .seriesQuestions => .cededWholesale

/-- The universe of restraint-kind display labels. -/
def allRestraintKinds : List RestraintKind := [
  .forcedRetype,
  .answeredAtCheapDissolution,
  .answeredAvyakataShaped,
  .declinedNoError,
  .standingNoVerdict,
  .cededWholesale
]

/-- A display kind is seen when some episode projects to it. -/
def restraintKindSeen (k : RestraintKind) : Bool :=
  generatorRecord.any (fun e => restraintKind e == k)

example : allRestraintKinds.length = 6 := rfl

/-- The paragraph's "six kinds" is checked on the image of `generatorRecord`. -/
theorem generatorRecord_restraintKind_seen_count :
    (allRestraintKinds.filter restraintKindSeen).length = 6 := rfl

/-- Every restraint-kind constructor occurs as the image of some ledger entry. -/
theorem restraintKind_exhaustive_on_record :
    ∀ k : RestraintKind, restraintKindSeen k = true := by
  intro k
  cases k <;> rfl

/- ==============================================================================
   Anchor pins
============================================================================== -/

example := @DirectionNegative.no_direction_recovery_from_conditionsEither

example := @InteriorDirectionNegative.no_interior_direction_recovery

example :=
  @Grid.DirectedConvention.BeingConvention.GridConvention.exit_collapse_self_refuting

example :=
  @Grid.DirectedConvention.BeingConvention.GridConvention.transposition_erased_downward_collapse_self_refuting

example :=
  @Grid.DirectedConvention.BeingConvention.GridConvention.fox_utterance_misfits_live_offer

example := @MisFeedNegative.fence_and_gate

/- ==============================================================================
   Structural falsifier pin
============================================================================== -/

/-- One entry discharges the structural half of the falsifier exactly when it
    either is not a mis-feed verdict or carries the decomposition the prose says
    such verdicts owe. -/
def decompositionDutyDischarged (e : RecordEntry) : Bool :=
  (!e.requiresDecomposition) || e.decompositionCarried

/-- Checkable half of the falsifier: current mis-feed verdicts in the ledger
    carry their decompositions. The rate-trend half quantifies over future
    entries and remains prose. -/
theorem misFeed_entries_carry_decomposition :
    generatorRecord.all decompositionDutyDischarged = true := rfl

end WAA
