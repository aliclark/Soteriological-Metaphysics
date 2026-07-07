/-
================================================================================
  WeldAndArrow.Meta.Glossary
  Canonical glossary data and structural checks
================================================================================

The glossary is the single source for short definitions used by the paper-facing
markdown. Lean checks the office discipline around the prose: term uniqueness,
backward-only `seeAlso` references, and declaration-anchor resolvability. The
accuracy and aptness of the glosses remain prose obligations.
-/

import Lean
import WeldAndArrow.Consequences.Compounds
import WeldAndArrow.Doctrines
import WeldAndArrow.Identification
import WeldAndArrow.Meta.InvarianceNegative
import WeldAndArrow.Meta.Nishitani
import WeldAndArrow.Meta.ReflexivityWitness
import WeldAndArrow.Meta.VerdictLedger

namespace WAA

/- ==============================================================================
   Glossary data
============================================================================== -/

/-- The paper layer where a system term first does its work. -/
inductive SourceLayer
  | theory
  | theorems
  | identification
deriving DecidableEq, Repr, BEq

namespace SourceLayer

def label : SourceLayer -> String
  | .theory => "Theory"
  | .theorems => "Theorems"
  | .identification => "Identification"

end SourceLayer

/-- Provenance of a term in the merged glossary. -/
inductive TermKind
  | coinage (layer : SourceLayer)
  | canonical
  | leanConvention
deriving DecidableEq, Repr, BEq

namespace TermKind

def label : TermKind -> String
  | .coinage layer => layer.label
  | .canonical => "Canonical"
  | .leanConvention => "Lean convention"

end TermKind

/-- A glossary row. `anchors` name checked declarations; empty anchors are
    allowed for prose-only terms. `seeAlso` entries must point to earlier rows. -/
structure GlossaryEntry where
  term : String
  kind : TermKind
  gloss : String
  anchors : List Lean.Name := []
  seeAlso : List String := []
deriving Repr

/-- The glossary in pedagogical order. This order is the generated table order. -/
def glossary : List GlossaryEntry := [
  { term := "floor"
    kind := .coinage .theory
    gloss := "A floor is the place where no deeper support is being claimed. In this system it names the self-emptying limit at which every distinction is conventional, including the distinction between conventional and ultimate truth."
    anchors := [``Grid.Tier.floor] },
  { term := "genjō"
    kind := .canonical
    gloss := "Genjō means manifestation, the way something comes forward as this case. In this system it also names the pole-class face where no share is claimed."
    anchors := [``AtBot]
    seeAlso := ["floor"] },
  { term := "grid"
    kind := .coinage .theory
    gloss := "A grid is a deliberately small model of who responds to what and how those responses are connected. It supplies the apparatus for welds, grades, delivery, and diagnostics without pretending to be the whole doctrine."
    anchors := [``Grid]
    seeAlso := ["floor"] },
  { term := "act-grammar"
    kind := .coinage .theory
    gloss := "An act-grammar is a way to parse an occurrence into roles. In this system it is the three-row pattern that lets the grid discuss dependence, manifestation, resonance, practice, and causal carrying without storing a self."
    anchors := [``Grid.Tier, ``Grid.Distinction]
    seeAlso := ["grid"] },
  { term := "mujishō-sōe"
    kind := .canonical
    gloss := "Mujishō-sōe means mutual dependence without own-being. In this system it is the first-row dependence face of the act-grammar."
    seeAlso := ["act-grammar"] },
  { term := "kannō-sōe"
    kind := .canonical
    gloss := "Kannō-sōe means responsive resonance or mutual answering. In this system it is the second-row dependence face, where a call and a response are placed together."
    anchors := [``Grid.MountsAt]
    seeAlso := ["act-grammar"] },
  { term := "banpō susumite"
    kind := .canonical
    gloss := "Banpō susumite means the myriad dharmas advancing. In this system it is the second-row enactment face, where what arrives is answered by a concrete response."
    anchors := [``Grid.Actual]
    seeAlso := ["kannō-sōe"] },
  { term := "shō"
    kind := .canonical
    gloss := "Shō means realization. In this system it is read as the non-possessive face at the floor, not as a stored attainment."
    seeAlso := ["floor"] },
  { term := "shu"
    kind := .canonical
    gloss := "Shu means practice. In this system it names the enacted side of the occurrence, the doing that is spent as the occurrence happens."
    anchors := [``RawWeld]
    seeAlso := ["act-grammar"] },
  { term := "shushō-ittō"
    kind := .canonical
    gloss := "Shushō-ittō means practice and realization as non-dual. In this system it is read as one occurrence with two faces, not two events that later get joined."
    seeAlso := ["shō", "shu"] },
  { term := "shugenjō"
    kind := .coinage .theory
    gloss := "Shugenjō is the paper's compound for practice that manifests without a scaffold. It is treated as a proper subset of genjō, not as a synonym for all manifestation."
    seeAlso := ["genjō", "shu"] },
  { term := "genjōkōan"
    kind := .canonical
    gloss := "Genjōkōan is a manifest case, not an abstract principle floating free of use. In this system it names the first-row manifestation arriving in a second-row situation."
    seeAlso := ["genjō", "kannō-sōe"] },
  { term := "satori"
    kind := .canonical
    gloss := "Satori means awakening or realization in ordinary Buddhist usage. In this system it is a pole-typed dharmas-forward event and is kept distinct from shō and kenshō."
    seeAlso := ["genjō", "shō"] },
  { term := "call"
    kind := .coinage .theory
    gloss := "A call is something that arrives to be answered. In the grid it is the input slot of a weld, the thing a response addresses or fails to address."
    anchors := [``RawWeld.call, ``Grid.RecordedUtterance.answersCall]
    seeAlso := ["grid"] },
  { term := "response"
    kind := .coinage .theory
    gloss := "A response is what a being produces when it answers a call. In the grid it is the output slot of a weld and the visible side of function."
    anchors := [``RawWeld.response, ``Grid.MountsAt]
    seeAlso := ["call"] },
  { term := "field"
    kind := .coinage .theory
    gloss := "A field is the impersonal web of conditioning and delivery. In this system it carries connections through time without carrying an owner or self-index."
    anchors := [``Grid.conditions, ``Grid.ConditionsEither]
    seeAlso := ["grid"] },
  { term := "inga"
    kind := .canonical
    gloss := "Inga means cause and effect. In this system it is read as the field's conditioning structure, not as a stored moral account."
    anchors := [``Grid.conditions]
    seeAlso := ["field"] },
  { term := "delivery"
    kind := .coinage .theory
    gloss := "Delivery is the fact that one occurrence reaches another as part of the field. It is checked by a directed relation, but the act that receives it still has to be actual."
    anchors := [``Grid.DirectedConvention.DeliveredTo, ``Grid.DirectedConvention.LandsAt]
    seeAlso := ["field"] },
  { term := "delivery-regime"
    kind := .coinage .theory
    gloss := "A delivery-regime is the whole pattern of what reaches what. In this system it is ceded as a world-fact and is never something a single act commands."
    anchors := [``Grid.conditions]
    seeAlso := ["delivery", "field"] },
  { term := "weld"
    kind := .coinage .theory
    gloss := "A weld is one concrete occurrence of answering. In the grid it bundles agent, call, and response, so the act's index is made by the act rather than stored before it."
    anchors := [``RawWeld, ``Grid.Weld, ``Grid.index]
    seeAlso := ["call", "response"] },
  { term := "reach-back"
    kind := .coinage .theory
    gloss := "Reach-back is a reception reading what arrived as the return of some earlier deed. In the system it is full when delivery supplies the earlier deed and vacuous when it does not."
    anchors := [``Grid.DirectedConvention.WaaReachBackFull,
      ``Grid.DirectedConvention.deliveredTo_iff_waaReachBackFull]
    seeAlso := ["delivery", "weld"] },
  { term := "upādāna"
    kind := .canonical
    gloss := "Upādāna ordinarily means grasping or appropriation. In this system it is the traditional word closest to reach-back, with the technical decomposition handled by the grid."
    anchors := [``Grid.WaaAppropriates]
    seeAlso := ["reach-back"] },
  { term := "vacuity"
    kind := .coinage .theory
    gloss := "Vacuity is a place left unfilled rather than a false claim. In the system it names the reach-back shape where appropriation occurs but delivery supplies no deed to fill the second slot."
    anchors := [``Grid.DirectedConvention.NotDeliveredTo]
    seeAlso := ["reach-back", "delivery"] },
  { term := "share"
    kind := .coinage .theory
    gloss := "A share is the portion of an occurrence's drive that is claimed as self-maintaining. In the grid it is the contribution value projected from a weld."
    anchors := [``Grid.share, ``Grid.share_eq_grade_check]
    seeAlso := ["weld"] },
  { term := "grade"
    kind := .coinage .theory
    gloss := "A grade is an ordered display of how much share a concrete response carries. It is third-personal in form but indexical in content, because it reads this weld's placement."
    anchors := [``Grid.grade, ``Grid.WaaMismatchGrade, ``Grid.share_eq_grade_check]
    seeAlso := ["share", "weld"] },
  { term := "clench"
    kind := .coinage .theory
    gloss := "Clench is self-maintenance tightening around a response. In the grid it is read through live share rather than through a stored inner state."
    anchors := [``Grid.HasSelfPoleIndex, ``Grid.WaaAppropriates]
    seeAlso := ["share", "weld"] },
  { term := "arrogation"
    kind := .coinage .theory
    gloss := "Arrogation is a response claiming subjecthood for itself. In this system it is per call and per weld, never a standing rank possessed by a being."
    anchors := [``Grid.HasSelfPoleIndex]
    seeAlso := ["clench", "weld"] },
  { term := "self-forward"
    kind := .coinage .theory
    gloss := "Self-forward means carrying a self toward what is met. In this system it is the delusive direction of a live weld, not a permanent condition."
    seeAlso := ["arrogation", "weld"] },
  { term := "function"
    kind := .coinage .theory
    gloss := "Function is the ability to mount a response at all. The grid keeps it separate from share, so answering a call and claiming the answer are not the same fact."
    anchors := [``Grid.MountsAt, ``Grid.RespondsToEveryCall]
    seeAlso := ["response", "share"] },
  { term := "pole"
    kind := .coinage .theory
    gloss := "A pole is the zero-share class in the ordering. In the grid it is represented by `AtBot`, so the system can speak of no live self-index without choosing a numerical scale."
    anchors := [``AtBot, ``Grid.AtPoleClass]
    seeAlso := ["share", "genjō"] },
  { term := "stone"
    kind := .coinage .theory
    gloss := "A stone is the zero-function edge: no response is mounted. In this system it can sit at the pole only vacuously, because there is no answering act to grade."
    anchors := [``Grid.Stone, ``Grid.stone_is_terminus_vacuously]
    seeAlso := ["function", "pole"] },
  { term := "solipsist"
    kind := .coinage .theory
    gloss := "The solipsist is the opposite edge from the stone. It names the imagined case where response is all self-claim and the call has effectively vanished."
    seeAlso := ["function", "share"] },
  { term := "terminus"
    kind := .coinage .theory
    gloss := "A terminus is a responder whose mounted responses lie at the pole. It answers without live share, so the system treats it differently from a stone."
    anchors := [``Grid.Terminus, ``Grid.LiveTerminus, ``Grid.ResponsiveTerminus]
    seeAlso := ["function", "pole"] },
  { term := "tier"
    kind := .leanConvention
    gloss := "A tier is the level at which a claim is offered or tested. Lean uses tiers to distinguish the floor from an act-time weld."
    anchors := [``Grid.Tier, ``Grid.Tier.hasLiveShare]
    seeAlso := ["floor", "weld"] },
  { term := "Row 2"
    kind := .coinage .theory
    gloss := "Row 2 is the resonance row, where call and response are placed together. It is where the system states grade without turning grade into something possessed."
    anchors := [``Grid.Tier.hasLiveShare]
    seeAlso := ["kannō-sōe", "grade"] },
  { term := "determination clause"
    kind := .coinage .theory
    gloss := "The determination clause says the grade is fixed by what actually drove this response. It rejects a private glow or later outcome as the source of grading."
    anchors := [``Grid.share_eq_grade_check]
    seeAlso := ["grade", "response"] },
  { term := "probe"
    kind := .coinage .theory
    gloss := "A probe is a third-person way of varying calls to display a response pattern. It can show a placement, but it does not create the placement it shows."
    anchors := [``Grid.ProbeConstant]
    seeAlso := ["call", "grade"] },
  { term := "effectiveness"
    kind := .coinage .theory
    gloss := "Effectiveness is a landing rate within a delivery-regime. In this system it grades whether calls land; it does not type what a responder is."
    anchors := [``Grid.DirectedConvention.HasShareDropLanding,
      ``Grid.DirectedConvention.ShortfallClosedAt]
    seeAlso := ["delivery-regime", "grade"] },
  { term := "fixed/adaptive"
    kind := .coinage .theory
    gloss := "Fixed and adaptive describe how a responder's output relates to calls. The grid can model both without making adaptivity the ground of liberation."
    anchors := [``Grid.ResponseInvariant, ``Grid.ResponseVariesWithCall]
    seeAlso := ["call", "response", "effectiveness"] },
  { term := "orthogonality rule"
    kind := .coinage .theory
    gloss := "The orthogonality rule says two dimensions do not determine each other. Here function and share type the responder, while effectiveness grades landing."
    anchors := [``OrthogonalityNegative.waaFullyEnlightened_stronger_than_terminus]
    seeAlso := ["function", "share", "effectiveness"] },
  { term := "domain joint"
    kind := .coinage .theory
    gloss := "The domain joint is the question of what counts as responding at all. The grid answers it by drive-composition and accepts the resulting artifact cases openly."
    anchors := [``Grid.MountsAt]
    seeAlso := ["function", "response"] },
  { term := "aimed call"
    kind := .coinage .theory
    gloss := "An aimed call is a deed configured for a landing. In Lean this thin reading is just delivery from the deed to the reception, not a new intention primitive."
    anchors := [``Grid.DirectedConvention.WaaAimedAt]
    seeAlso := ["call", "delivery"] },
  { term := "re-pitch"
    kind := .coinage .theory
    gloss := "Re-pitch is what a reception hands forward as the next carried tendency. In the current signature it records the received weld's share and forgets the previous configuration."
    anchors := [``Grid.rePitch, ``Grid.rePitch_forgets]
    seeAlso := ["share", "weld"] },
  { term := "seed"
    kind := .coinage .theory
    gloss := "A seed is a carried tendency rather than a bearer. In Lean it is modeled by a configuration value with no stored owner, weld, or self-index."
    anchors := [``Config, ``Config.tendency]
    seeAlso := ["field", "re-pitch"] },
  { term := "standing/dated"
    kind := .coinage .theory
    gloss := "Standing means carried as a tendency; dated means enacted now. The system treats reading a dated occurrence directly from a standing tendency as a diagnostic error."
    anchors := [``Grid.DirectedConvention.BeingConvention.GridConvention.RowTag.standingDated,
      ``standing_does_not_determine_dated]
    seeAlso := ["seed", "weld"] },
  { term := "three registers"
    kind := .coinage .theory
    gloss := "The three registers are carried field facts, spent weld facts, and per-call grade statements. The split keeps the system from storing self-indexed ownership between acts."
    anchors := [``SortedFact.register]
    seeAlso := ["field", "weld", "grade"] },
  { term := "separate/fuse rule"
    kind := .coinage .theory
    gloss := "The separate/fuse rule says live act-time distinctions must be kept apart and floor-level distinctions must fuse. It is the grammar behind the taxonomy's collapse and freeze diagnoses."
    anchors := [``Grid.Distinction.ObeysSeparateFuse]
    seeAlso := ["floor", "tier"] },
  { term := "collapse/freeze"
    kind := .coinage .theory
    gloss := "Collapse fuses what should be separate; freeze holds separate what should fuse. These are the two basic ways the taxonomy catches a misuse of a distinction."
    anchors := [``Grid.Distinction.Collapse, ``Grid.Distinction.Freeze]
    seeAlso := ["separate/fuse rule"] },
  { term := "assert/display"
    kind := .leanConvention
    gloss := "Assert and display are two voices for a verdict. The grid asserts grammatical failures inside its lens and only displays value-laden or soteriological shortfall."
    anchors := [``Grid.VerdictVoice, ``Grid.ErrorGrade, ``Grid.ErrorGrade.voice]
    seeAlso := ["collapse/freeze"] },
  { term := "orange / eat this"
    kind := .coinage .theory
    gloss := "The orange is the paper's image for its own offering. It gives a thing to receive, while the phrase eat this marks the risk of turning a description into an injunction."
    seeAlso := ["assert/display", "call"] },
  { term := "object-axis/subject-axis"
    kind := .coinage .theory
    gloss := "Object-axis means being available as something received; subject-axis means mounting responses oneself. The grid keeps these axes apart, especially for stones and termini."
    anchors := [``Grid.DirectedConvention.ObjectAxisStanding, ``Grid.MountsAt]
    seeAlso := ["delivery", "function"] },
  { term := "index-question"
    kind := .coinage .theory
    gloss := "The index-question asks whose act or whose fruit is at issue. In this system the answer is enacted in a weld or stated by a grade, never stored in the field."
    anchors := [``Grid.index, ``Grid.HasSelfPoleIndex]
    seeAlso := ["weld", "field", "grade"] },
  { term := "mis-feed"
    kind := .coinage .identification
    gloss := "A mis-feed is an internal diagnostic where the wrong register is fed to a question. The checked fence covers index-free field answers being used where an index-bearing designation is required."
    anchors := [``MisFeedNegative.fence_and_gate]
    seeAlso := ["index-question", "field"] },
  { term := "dukkha"
    kind := .canonical
    gloss := "Dukkha ordinarily names suffering or unsatisfactoriness. In this system it is the mismatch of a live self-maintaining response with delivery that answers to no self."
    anchors := [``Grid.WaaMismatchGrade, ``Grid.WaaMismatchLive]
    seeAlso := ["share", "delivery", "clench"] },
  { term := "before/after"
    kind := .coinage .theory
    gloss := "Before and after are ordinary temporal words. In this system they are a reading over roles in the field, not extra furniture stored inside the field."
    anchors := [``Grid.DirectedConvention.TimeDirection]
    seeAlso := ["field", "delivery"] },
  { term := "arrow"
    kind := .coinage .theory
    gloss := "The arrow is direction read into conditioning. The retyped system treats direction as a display over field structure, not as a primitive property of that structure."
    anchors := [``Grid.DirectedConvention.TimeDirection,
      ``DirectionNegative.no_direction_recovery_from_conditionsEither]
    seeAlso := ["field", "before/after"] },
  { term := "ratchet"
    kind := .coinage .theory
    gloss := "A ratchet is a mechanism that reads a gradient as direction. In the paper it motivates why beings may read an arrow without making the arrow part of the field itself."
    seeAlso := ["arrow", "field"] },
  { term := "Waa marker"
    kind := .leanConvention
    gloss := "The Waa marker flags a system-point-of-view reading. It tells readers that a Lean name reports how the grid reads a concept, not what the tradition must mean by it."
    anchors := [``Grid.WaaAppropriates, ``Grid.WaaMismatchGrade,
      ``Grid.DirectedConvention.WaaReachBackFull]
    seeAlso := ["grid"] },
  { term := "DirectedConvention"
    kind := .leanConvention
    gloss := "DirectedConvention is the namespace for vocabulary that reads direction into the grid. It keeps directed delivery words separate from the direction-free signature beneath them."
    anchors := [``Grid.DirectedConvention.DeliveredTo]
    seeAlso := ["arrow", "delivery"] },
  { term := "being-convention"
    kind := .coinage .theory
    gloss := "A being-convention is a diagnosis-time way of reading fine tags as macro beings. It permits naming without claiming that the grid stores the true partition."
    anchors := [``Grid.DirectedConvention.BeingConvention.BeingCoarsening]
    seeAlso := ["grid", "DirectedConvention"] },
  { term := "coarsening"
    kind := .leanConvention
    gloss := "A coarsening maps fine tags to macro tags. Lean uses it to model a chosen being-reading while leaving the underlying grid unchanged."
    anchors := [``Grid.DirectedConvention.BeingConvention.BeingCoarsening,
      ``Grid.DirectedConvention.BeingConvention.BeingCoarsening.InFiber]
    seeAlso := ["being-convention"] },
  { term := "tag/fiber"
    kind := .coinage .theory
    gloss := "A tag is a fine identifier; a fiber is the set of fine tags read as one macro tag by a coarsening. Fiber-level predicates let the system discuss beings without storing beings as substances."
    anchors := [``Grid.DirectedConvention.BeingConvention.BeingCoarsening.InFiber,
      ``Grid.DirectedConvention.BeingConvention.BeingCoarsening.SameFiber]
    seeAlso := ["coarsening"] },
  { term := "tag-region/soma-reading"
    kind := .coinage .theory
    gloss := "A tag-region is a model-supplied class of fine tags. A soma-reading uses such a class to localize a cut to a region without making the region recoverable from grid data alone."
    anchors := [``Grid.SomaReading]
    seeAlso := ["tag/fiber"] },
  { term := "within-cut"
    kind := .coinage .theory
    gloss := "A within-cut is quietness inside a product of call-class and tag-region. It says enactment has ceased in that rectangle, not that a person owns an anti-fetter."
    anchors := [``Grid.FetterCutWithin]
    seeAlso := ["tag-region/soma-reading", "call"] },
  { term := "vāsanā"
    kind := .canonical
    gloss := "Vāsanā means residual habit or trace. In this system it is clench still enacted in an uncut region after another region has gone quiet."
    seeAlso := ["clench", "within-cut"] },
  { term := "sentient/insentient tag"
    kind := .coinage .theory
    gloss := "A sentient tag is one whose fiber mounts response somewhere; an insentient tag lacks that. The distinction is fiber-level and convention-relative."
    anchors := [``Grid.DirectedConvention.BeingConvention.BeingCoarsening.SentientTag,
      ``Grid.DirectedConvention.BeingConvention.BeingCoarsening.not_sentientTag_iff_fiber_all_stone]
    seeAlso := ["tag/fiber", "function"] },
  { term := "FiberAtPole / SelfAptTag / Patchy"
    kind := .leanConvention
    gloss := "These names describe a fiber spectrum: all actual welds at pole, all actual welds self-apt, or an irreducibly mixed case. They deliberately avoid defining an aggregate share for a fiber."
    anchors := [``Grid.DirectedConvention.BeingConvention.BeingCoarsening.FiberAtPole,
      ``Grid.DirectedConvention.BeingConvention.BeingCoarsening.SelfAptTag,
      ``Grid.DirectedConvention.BeingConvention.BeingCoarsening.Patchy]
    seeAlso := ["tag/fiber", "pole"] },
  { term := "coherence (grade)"
    kind := .coinage .theory
    gloss := "Coherence is a display grade over a coarsening. It can report how well a reading behaves, but it never licenses or forbids the naming of a being."
    seeAlso := ["coarsening", "grade"] },
  { term := "delegation"
    kind := .coinage .theory
    gloss := "Delegation reads macro agency through an actual fine weld in a fiber. The share remains the fine weld's share, so macro agency does not create a new stored subject."
    seeAlso := ["weld", "tag/fiber", "share"] },
  { term := "freedom witness"
    kind := .coinage .theory
    gloss := "A freedom witness is a countermodel showing that a supposed boundary is not forced by grid data. The being-boundary version permits both split and merge readings of the same fine grid."
    anchors := [``BeingNegative.no_partition_recovery]
    seeAlso := ["being-convention", "coarsening"] },
  { term := "kenshō"
    kind := .canonical
    gloss := "Kenshō ordinarily means seeing nature. In this system it is kept as a countable share-ceding event, not as a possession or stored attainment."
    anchors := [``Grid.IsShareDrop]
    seeAlso := ["share", "re-pitch"] },
  { term := "call/response"
    kind := .coinage .theory
    gloss := "Call/response is the smallest public shape of an occurrence: something arrives and something answers. In the grid this pair is carried by the weld and later inspected by the taxonomy."
    anchors := [``RawWeld.call, ``RawWeld.response, ``Grid.RecordedUtterance]
    seeAlso := ["call", "response", "weld"] },
  { term := "delivery-engineering"
    kind := .coinage .theorems
    gloss := "Delivery-engineering is legal work on what may arrive. Responder-side it finds calls that land; sowing-side it configures aimed calls without commanding the regime."
    anchors := [``Grid.DirectedConvention.WaaAimedAt,
      ``Grid.DirectedConvention.HasShareDropLanding]
    seeAlso := ["delivery", "aimed call"] },
  { term := "delivery-arrogation"
    kind := .coinage .theorems
    gloss := "Delivery-arrogation is claiming authority over what arrives next. The system treats that as grasping the one register no weld owns."
    anchors := [``DeliveryArrogationNegative.command_utterance_not_fits]
    seeAlso := ["delivery-regime", "arrogation"] },
  { term := "buddha-side shortfall"
    kind := .coinage .theorems
    gloss := "Buddha-side shortfall is failing to meet a not-yet-buddha's call where it is. It is the pole's live grade and is tracked by effectiveness rather than by terminus typing alone."
    anchors := [``Grid.DirectedConvention.ShortfallClosedAt,
      ``OrthogonalityNegative.waaFullyEnlightened_stronger_than_terminus]
    seeAlso := ["effectiveness", "terminus"] },
  { term := "backsliding theorem"
    kind := .coinage .theorems
    gloss := "The backsliding theorem says a share-drop event cannot be held as a stored attainment. Later live welds are possible because nothing self-indexed is carried between acts."
    anchors := [``backsliding_witness, ``backsliding_rePitchSequence_witness]
    seeAlso := ["kenshō", "re-pitch", "seed"] },
  { term := "memory theorem"
    kind := .coinage .theorems
    gloss := "The memory theorem reads a trace as a seed and remembering as a fresh reception. Felt mineness is predicted at recall-time without being stored before recall."
    anchors := [``Grid.DirectedConvention.MemoryWitness.memory_witness,
      ``Grid.DirectedConvention.WaaVacuousOwnershipFace,
      ``Grid.DirectedConvention.WaaDiachronicWhose]
    seeAlso := ["seed", "reach-back"] },
  { term := "retrospective soul"
    kind := .coinage .theorems
    gloss := "The retrospective soul is the error of freezing reach-back into a standing backward owner. It is the psychological version of treating fresh mineness as stored mineness."
    anchors := [``Grid.DirectedConvention.BeingConvention.GridConvention.sowingReapingRow_not_freeze,
      ``no_agent_recovery_of_field_collision]
    seeAlso := ["memory theorem", "reach-back", "standing/dated"] },
  { term := "prudence theorem"
    kind := .coinage .theorems
    gloss := "The prudence theorem says special authority for self-concern is not recoverable from the grid. The standing cross-gap whose that prudence would need is exactly what the typing declines."
    anchors := [``Grid.DirectedConvention.PrudentialPrivilegeNegative.not_prudentialPrivilege]
    seeAlso := ["index-question", "standing/dated"] },
  { term := "deliberator theorem"
    kind := .coinage .theorems
    gloss := "The deliberator theorem blocks a maximizer at three joints: supplied being-convention, absent accumulator, and failed command over delivery. It is a check on consequentialist reuse of the grid."
    anchors := [``ObjectiveNegative.no_grid_data_objective_for_my_drops,
      ``TransferNegative.adaptive_track_record_underdetermines_new_effect,
      ``DeliveryArrogationNegative.command_utterance_not_fits,
      ``Grid.ConsequentialistConvention.map_dropCount,
      ``Grid.ConsequentialistConvention.map_dropCountInFiber]
    seeAlso := ["being-convention", "re-pitch", "delivery-arrogation"] },
  { term := "covariation"
    kind := .coinage .theorems
    gloss := "Covariation means two quantities move together without being declared identical in every respect. The dukkha reading covaries with share, ordinally and per call."
    anchors := [``Grid.WaaMismatchGrade]
    seeAlso := ["dukkha", "share"] },
  { term := "proneness/occurrence"
    kind := .coinage .theorems
    gloss := "Proneness is a carried tendency; occurrence is the live event. The dukkha split uses this standing/dated distinction to avoid storing suffering as a bearer."
    seeAlso := ["dukkha", "seed", "standing/dated"] },
  { term := "transposition"
    kind := .coinage .theorems
    gloss := "Transposition is the answer to the terminus question: the self-pole index disappears, while reception-side activity for others can still run. Nothing travels from one pole to another."
    anchors := [``Grid.no_self_pole_index_of_atBot,
      ``Grid.DirectedConvention.BeingConvention.GridConvention.transposition_erased_downward_collapse_self_refuting]
    seeAlso := ["terminus", "pole", "object-axis/subject-axis"] },
  { term := "kiriya / ahosi"
    kind := .canonical
    gloss := "Kiriya and ahosi name action and lapsed fruit in Buddhist idiom around the arhat. In this system the point is derived from share-zero: fruit can land without a live index-question."
    seeAlso := ["share", "pole", "delivery"] },
  { term := "mirror"
    kind := .canonical
    gloss := "The mirror is the image of responsive output without possession. In this system it is function without share, legal as a display over a run."
    anchors := [``Grid.LiveTerminus]
    seeAlso := ["function", "share", "terminus"] },
  { term := "device / device-nature"
    kind := .coinage .theorems
    gloss := "A device is a compressed way to speak of pole-like responsiveness. It is legal as display and becomes a freeze when treated as a standing nature owned by a being."
    seeAlso := ["mirror", "terminus", "collapse/freeze"] },
  { term := "maximally adaptive call"
    kind := .coinage .theorems
    gloss := "The maximally adaptive call is the limiting case of call-fitting. The system deflates it from the ground of the terminus to the limit where buddha-side shortfall closes."
    seeAlso := ["fixed/adaptive", "buddha-side shortfall"] },
  { term := "generator"
    kind := .coinage .theorems
    gloss := "The generator is the taxonomy engine that makes rows from distinctions. Its discipline is that errors must land in existing cells, force a new cell, be declined, or force a retype."
    anchors := [``Grid.GeneratorOutcome,
      ``Grid.DirectedConvention.BeingConvention.GridConvention.tableOrder]
    seeAlso := ["collapse/freeze"] },
  { term := "four verdicts"
    kind := .coinage .theorems
    gloss := "The four verdicts are existing-cell, new-cell, declined, and retype. They are the public outcomes available when the generator meets a candidate error."
    anchors := [``Verdict, ``generatorRecord_newCell_count]
    seeAlso := ["generator"] },
  { term := "Sunyata"
    kind := .canonical
    gloss := "Sunyata means emptiness. In this system it is the no-final-freeze property of a distinction's re-emptying ladder."
    anchors := [``Grid.DirectedConvention.BeingConvention.GridConvention.Nishitani.Sunyata]
    seeAlso := ["collapse/freeze"] },
  { term := "direction-underdetermination witness"
    kind := .coinage .theorems
    gloss := "This witness shows that symmetric field residue does not determine direction. Two grids can agree on the undirected relation and disagree on the directed one."
    anchors := [``DirectionNegative.no_direction_recovery_from_conditionsEither]
    seeAlso := ["arrow", "field"] },
  { term := "being-boundary witness"
    kind := .coinage .theorems
    gloss := "This witness shows that grid data do not recover a unique being-boundary. Merge and split coarsenings can both be legal over the same fine grid."
    anchors := [``BeingNegative.no_partition_recovery]
    seeAlso := ["being-convention", "freedom witness"] },
  { term := "weld-boundary witness"
    kind := .coinage .theorems
    gloss := "Grid data do not recover a unique weld-segmentation. Merge and split readings of what counts as one call-response pairing are both legal over the same field."
    anchors := [``WeldNegative.no_weld_boundary_recovery]
    seeAlso := ["weld", "being-convention", "freedom witness"] },
  { term := "intra-weld arrow row"
    kind := .coinage .theorems
    gloss := "The intra-weld arrow row checks the call-to-response direction inside a weld as a convention layer. Its content form denies response-variation, and its witness says the unordered residue does not recover an interior arrow."
    anchors := [``Grid.DirectedConvention.BeingConvention.GridConvention.intraWeldArrowRow,
      ``Grid.DirectedConvention.BeingConvention.GridConvention.Nishitani.intraWeldArrow_sunyata,
      ``InteriorDirectionNegative.no_interior_direction_recovery]
    seeAlso := ["arrow", "weld", "weld-boundary witness"] },
  { term := "doer/deed row"
    kind := .coinage .theorems
    gloss := "The doer/deed row is the schema-only MMK 8 cell: a prior-doer reading is diagnosed without adding priority as a primitive field of the grid."
    anchors := [``Grid.DirectedConvention.BeingConvention.GridConvention.doerDeedRow,
      ``Grid.DirectedConvention.BeingConvention.GridConvention.Nishitani.doerDeed_sunyata,
      ``DoerDeedNegative.no_priority_recovery]
    seeAlso := ["weld", "collapse/freeze", "intra-weld arrow row"] },
  { term := "coming-to / going-from"
    kind := .coinage .theory
    gloss := "Coming-to and going-from are display labels for the two orientation readings of a weld's faces. Transposition reverses the labels; they are not tier names."
    anchors := [``InteriorDirectionNegative.transpose_swaps_readings,
      ``InteriorDirectionNegative.no_interior_direction_recovery]
    seeAlso := ["arrow", "weld", "intra-weld arrow row"] },
  { term := "reflexivity witness"
    kind := .coinage .theorems
    gloss := "The reflexivity witness instantiates a grid's being carrier with rung labels, showing that the beings ladder still has no final freeze when read over its own indices."
    anchors := [``Grid.DirectedConvention.BeingConvention.GridConvention.ladderRungGrid_beings_sunyata]
    seeAlso := ["being-convention", "Sunyata"] },
  { term := "weld row / weld śūnyatā"
    kind := .coinage .theorems
    gloss := "The weld row names the weld-grain distinction as a convention layer, and weld śūnyatā says its re-emptying ladder has no final frozen level."
    anchors := [``Grid.DirectedConvention.BeingConvention.GridConvention.weldRow,
      ``Grid.DirectedConvention.BeingConvention.GridConvention.Nishitani.weld_sunyata]
    seeAlso := ["collapse/freeze", "Sunyata"] },
  { term := "declined case"
    kind := .coinage .theorems
    gloss := "A declined case is a candidate that the taxonomy refuses to mark as error. The deaf-blind example matters because over-generating error would itself freeze the lens."
    anchors := [``InstructiveAbsence.declinedCase]
    seeAlso := ["four verdicts"] },
  { term := "Grade 1 / Grade 2"
    kind := .coinage .theorems
    gloss := "Grade 1 names grammatical errors assertable inside the lens; Grade 2 names shortfalls only displayable by the lens. The difference prevents the grid from issuing its own value command."
    anchors := [``Grid.ErrorGrade, ``Grid.ErrorGrade.voice]
    seeAlso := ["assert/display"] },
  { term := "clenched reception"
    kind := .coinage .theorems
    gloss := "A clenched reception is an arriving response taken tightly as mine. It is still graded as a fresh weld, not as evidence of a stored owner."
    seeAlso := ["clench", "reach-back", "weld"] },
  { term := "declining the orange"
    kind := .coinage .theorems
    gloss := "Declining the orange is a low-resonance reception of this offered call. It is not a global wrong and does not prove anything about a person."
    seeAlso := ["orange / eat this", "call"] },
  { term := "defiance"
    kind := .coinage .theorems
    gloss := "Defiance is arrogation hardened into policy. The fighting stance is a seed, but each fight remains a new act."
    seeAlso := ["arrogation", "seed", "weld"] },
  { term := "cetanā"
    kind := .canonical
    gloss := "Cetanā means intention or volition. In this system it is the traditional anchor for the claim that grading tracks the weld rather than the downstream event."
    anchors := [``Grid.grade_independent_of_conditions,
      ``Grid.share_independent_of_conditions]
    seeAlso := ["weld", "grade"] },
  { term := "cetanā theorem"
    kind := .coinage .theorems
    gloss := "The cetanā theorem is the derived version of intention as karma. It says the grading component follows the weld even where event-success and delivery diverge."
    anchors := [``Grid.grade_independent_of_conditions,
      ``Grid.share_independent_of_conditions,
      ``cetana_grading_tracks_weld_not_field_witness,
      ``cetana_live_share_without_object_standing_witness]
    seeAlso := ["cetanā", "weld", "field"] },
  { term := "futility theorem"
    kind := .coinage .theorems
    gloss := "The futility theorem says the deliberate attempt fails at target and downstream. The body can be staticized as a delivery loss without subtracting object-axis standing."
    anchors := [``Grid.staticized, ``Grid.futility_delivery_loss_real,
      ``Grid.futility_object_axis_subtraction_nil,
      ``Grid.DirectedConvention.staticized_objectAxisStanding_iff]
    seeAlso := ["delivery", "object-axis/subject-axis", "device / device-nature"] },
  { term := "victim-rank"
    kind := .coinage .theorems
    gloss := "Victim-rank is severity read from the victim's station. The system treats it as a freeze because rank is being smuggled into what should be per-weld grading."
    seeAlso := ["grade", "collapse/freeze"] },
  { term := "hell-typed"
    kind := .coinage .theorems
    gloss := "Hell-typed means a configuration receives no gentler call in the actual delivery-regime. The claim is regime-relative, not a statement about all possible calls."
    seeAlso := ["delivery-regime", "call"] },
  { term := "ledger"
    kind := .coinage .theorems
    gloss := "A ledger is a public register that prices what can be counted. In the Huichang case it names an economic modality and the errors produced by reading that modality as a being-sized truth."
    anchors := [``LedgerCase.decree_engineers_calls_not_receptions,
      ``LedgerCase.purge_loop_runs_on]
    seeAlso := ["delivery-regime", "Grade 1 / Grade 2"] },
  { term := "economic legibility"
    kind := .coinage .theorems
    gloss := "Economic legibility is a field-fact about which configurations a purge can reach. The system can assert that register while only displaying the worth of survival."
    anchors := [``Grid.DirectedConvention.landing_call_in_modality]
    seeAlso := ["ledger", "field"] },
  { term := "gradeability rule"
    kind := .coinage .theorems
    gloss := "The gradeability rule says a recorded utterance may be graded only where the record carries its call. Lean checks both the severed-transcript obstruction and the call-carrying positive form."
    anchors := [``GradeabilityNegative.no_grade_recovery_from_severed,
      ``GradeabilityNegative.gradeability_severed_underdetermination_witness,
      ``recordedUtterance_grade_determined]
    seeAlso := ["call", "grade", "weld"] },
  { term := "transcription"
    kind := .coinage .theorems
    gloss := "Transcription turns an adaptive event into a fixed record. In the system the transcript is a seed-like fixed call, not a stored fault in the words."
    seeAlso := ["fixed/adaptive", "seed", "call"] },
  { term := "per-call/global freeze"
    kind := .coinage .theorems
    gloss := "The per-call/global freeze turns a local grade into a global rank. It is the error behind treating stages, awakening, or census categories as stored altitude."
    anchors := [``Grid.DirectedConvention.BeingConvention.GridConvention.RowTag.perCallGlobal]
    seeAlso := ["grade", "collapse/freeze"] },
  { term := "subitism/gradualism"
    kind := .canonical
    gloss := "Subitism and gradualism name sudden and staged arrival patterns. The system permits both as run shapes while refusing to store a rate preference as attainment."
    anchors := [``Grid.WaaSuddenArrival, ``Grid.WaaGradualArrival,
      ``Grid.rate_invisible_to_config, ``SuddenGradualNegative.subitism_frequency_underdetermined]
    seeAlso := ["re-pitch", "per-call/global freeze"] },
  { term := "PathFactor"
    kind := .leanConvention
    gloss := "PathFactor names the factor-side regrouping of the existing fetter table. Rites, view, and resolve are active; speech and conduct are named but inert until the upper-pair question is settled."
    anchors := [``PathFactor, ``PathFactor.blockerClass]
    seeAlso := ["coarsening", "tag/fiber"] },
  { term := "FactorHeld"
    kind := .leanConvention
    gloss := "FactorHeld is a seen-run witness: an actual in-fiber weld in the factor blocker class carries a live self-pole index. It is not itself an error; it is factor-frame vocabulary, not freeze/collapse and not clench alone."
    anchors := [``Grid.FactorHeld]
    seeAlso := ["PathFactor", "clench", "weld"] },
  { term := "FactorReleased"
    kind := .leanConvention
    gloss := "FactorReleased is the release half of the factor pair: the fiber is at pole on the factor blocker class. One actual live weld in that class refutes it."
    anchors := [``Grid.FactorReleased, ``Grid.not_factorHeld_of_factorReleased]
    seeAlso := ["PathFactor", "FactorHeld", "pole"] },
  { term := "WaaStreamEnterer"
    kind := .leanConvention
    gloss := "WaaStreamEnterer is the path-position reading over the first pair: rites released, view held on the seen run. It deliberately separates path display from the fruit cut."
    anchors := [``Grid.WaaStreamEnterer]
    seeAlso := ["FactorHeld", "FactorReleased"] },
  { term := "WaaStreamWinner"
    kind := .leanConvention
    gloss := "WaaStreamWinner is the fruit-position reading for stream entry: rites and view are released, and Lean proves it coincides with the existing stream-entry cut class. The terminology is a checked departure from treating sotapanna as only one undivided label."
    anchors := [``Grid.WaaStreamWinner,
      ``Grid.waaStreamWinner_iff_streamEntry_cutClasses]
    seeAlso := ["WaaStreamEnterer", "FactorReleased"] },
  { term := "WaaOnceReturner"
    kind := .leanConvention
    gloss := "WaaOnceReturner keeps the stream-winning fruit and adds a witnessed resolve hold on the seen run. Its extra checked content is attenuation, not a new cut class."
    anchors := [``Grid.WaaOnceReturner]
    seeAlso := ["WaaStreamWinner", "FactorHeld"] },
  { term := "WaaNonReturner"
    kind := .leanConvention
    gloss := "WaaNonReturner is the fruit-position reading after resolve release. Lean proves it is exactly the non-return cut class, so the factor scheme remains a reading over the fetter lattice."
    anchors := [``Grid.WaaNonReturner,
      ``Grid.waaNonReturner_iff_nonReturn_cut]
    seeAlso := ["WaaOnceReturner", "FactorReleased"] },
  { term := "WaaResolveAttenuation"
    kind := .leanConvention
    gloss := "WaaResolveAttenuation gives once-return positive content: a strict resolve-class share-drop run whose final tendency has not reached the pole."
    anchors := [``Grid.WaaResolveAttenuation,
      ``Grid.waaOnceReturner_attenuation_witness,
      ``Grid.attenuation_not_release]
    seeAlso := ["WaaOnceReturner", "re-pitch"] },
  { term := "WaaSerialFactorRegime"
    kind := .leanConvention
    gloss := "WaaSerialFactorRegime is the conditional voice for factor order. If the supplied regime reads seen share-drops as rites before view before resolve, it promotes path readings to fruit readings; the grid never derives the regime or any frequency claim."
    anchors := [``Grid.WaaSerialFactorRegime,
      ``Grid.waaSerialFactorRegime_conditional,
      ``FactorsNegative.seen_run_underdetermines_factorOrder]
    seeAlso := ["WaaResolveAttenuation", "subitism/gradualism"] },
  { term := "śraddhā"
    kind := .canonical
    gloss := "Śraddhā means faith or trust. In this system it is modeled as an antecedent for testimony and path response, never as a field fact the grid can discharge by itself."
    anchors := [``Grid.DirectedConvention.WaaFaithPrinciple,
      ``Grid.DirectedConvention.waaFaithOught_conditional]
    seeAlso := ["buddha-side shortfall", "delivery"] },
  { term := "icchantika"
    kind := .canonical
    gloss := "Icchantika ordinarily names a being cut off from buddhahood. Here it is the terminus's inverse: non-stone, with a live self-pole index at every mounted response. It is reachable as a receiver and cannot be seated as an enlightened agent on its run. The permanent cannot-become-buddha verdict is declined, because foreclosure would be a stored rank the system forbids; defiance is a seed, not a rank."
    anchors := [``Icchantika, ``not_waaFullyEnlightened_of_icchantika,
      ``aversionContext_of_icchantika_reception,
      ``icchantika_release_not_foreclosed]
    seeAlso := ["defiance", "terminus", "backsliding theorem", "śraddhā"] },
  { term := "tariki / other-power"
    kind := .canonical
    gloss := "Tariki means other-power. In this system it is a delivery-regime reading, not a second act-grammar: the reception is still an ordinary weld."
    anchors := [``Grid.DirectedConvention.WaaTarikiLine,
      ``Grid.DirectedConvention.reception_typing_ignores_sower,
      ``TarikiCase.universal_fixed_call_lands_without_reading,
      ``OtherPowerNegative.regime_does_not_determine_share]
    seeAlso := ["delivery-regime", "weld"] },
  { term := "pariṇāmanā / dedication"
    kind := .canonical
    gloss := "Pariṇāmanā means dedication or turning over merit. In this system it is sowing-side share-cession whose routing is left to delivery rather than commanded by the act."
    anchors := [``Grid.DirectedConvention.BeingConvention.GridConvention.CompoundPosition.ledgerPicture,
      ``Grid.DirectedConvention.BeingConvention.GridConvention.CompoundPosition.ledgerPicture_decomposition,
      ``Grid.DirectedConvention.BeingConvention.GridConvention.CompoundPosition.ledgerPicture_contains_legal_causalSkeleton,
      ``Grid.DirectedConvention.SameAgentDelivery,
      ``Grid.DirectedConvention.CrossAgentDelivery,
      ``Grid.DirectedConvention.reception_typing_ignores_sower,
      ``OtherPowerNegative.regime_does_not_determine_share,
      ``OtherPowerNegative.share_does_not_determine_regime]
    seeAlso := ["share", "delivery-regime", "aimed call"] },
  { term := "instructive absences"
    kind := .coinage .theorems
    gloss := "Instructive absences are gaps the system keeps because they do diagnostic work. Lean mirrors them as data with status and numbering rather than treating them as forgotten cases."
    anchors := [``InstructiveAbsence, ``InstructiveAbsence.status,
      ``InstructiveAbsence.number]
    seeAlso := ["declined case", "generator"] },
  { term := "identification claim"
    kind := .coinage .identification
    gloss := "The identification claim says karma names the loop where the field carries diachronic relations and the weld enacts every index. It is a decomposition claim, not a stored-self claim."
    seeAlso := ["field", "weld", "index-question"] },
  { term := "state-designation vs. act-fixing"
    kind := .coinage .identification
    gloss := "State-designation names something over a standing base at a time; act-fixing makes the relevant index in the act itself. The contrast blocks a state-tool from ranging over karmic ownership."
    anchors := [``Grid.stateToolFits_iff_atBot]
    seeAlso := ["standing/dated", "weld"] },
  { term := "offices-spine"
    kind := .coinage .identification
    gloss := "The offices-spine is the list of traditional places where karmic ownership has work to do. The identification argues that each office discharges at act-time."
    anchors := [``WaaOwnershipOffice]
    seeAlso := ["identification claim", "weld"] },
  { term := "thin for-me-ness"
    kind := .coinage .identification
    gloss := "Thin for-me-ness is pre-reflective givenness without appropriation. The system keeps the token-reflexive light needed by the weld and removes standing ownership."
    seeAlso := ["weld", "arrogation"] },
  { term := "Sartrean occupant"
    kind := .coinage .identification
    gloss := "The Sartrean occupant is the remaining inhabitant of clench-as-structure after thin for-me-ness is pared back. It names anguish as a structure, not ownership as a stored thing."
    seeAlso := ["thin for-me-ness", "clench"] },
  { term := "sower-reaps split"
    kind := .coinage .identification
    gloss := "The sower-reaps split separates the report that a delivery line exists from the ownership face made at reception. It keeps true field reporting away from standing ownership."
    anchors := [``Grid.DirectedConvention.WaaReportFace,
      ``Grid.DirectedConvention.WaaOwnershipFace,
      ``Grid.DirectedConvention.WaaVacuousOwnershipFace]
    seeAlso := ["delivery", "reach-back"] },
  { term := "pole-typing corollary"
    kind := .coinage .identification
    gloss := "The pole-typing corollary says the state-tool fits exactly where live welding ceases. At share-zero there is no live self-pole index for the tool to miss."
    anchors := [``Grid.stateToolFits_iff_atBot,
      ``Grid.no_self_pole_index_of_atBot]
    seeAlso := ["pole", "index-question"] },
  { term := "soul-guard"
    kind := .coinage .identification
    gloss := "The soul-guard blocks storage by making the agent more empty, not more substantial. Both forward-facing and retrospective bearers are declined."
    anchors := [``no_agent_recovery_of_field_collision]
    seeAlso := ["field", "weld"] },
  { term := "being trichotomy"
    kind := .coinage .identification
    gloss := "The being trichotomy gives three readings: collapse deletes beings, freeze reifies a partition, and convention leaves naming free. It keeps designation useful without making it metaphysical."
    anchors := [``Disclaimer.beingTrichotomy]
    seeAlso := ["being-convention", "collapse/freeze"] },
  { term := "hare's horn"
    kind := .canonical
    gloss := "A hare's horn is the stock example of something nameable but unrealizable. In this system it shows that designation is constrained at use, not at the mere act of naming."
    anchors := [``Disclaimer.hareHornRegister]
    seeAlso := ["being-convention"] },
  { term := "Modal Realism"
    kind := .canonical
    gloss := "Modal Realism treats possible beings as fully real. In this system it is the beings-row freeze: plenitude moved into ontology rather than left as conventional designation."
    anchors := [``Disclaimer.modalRealismFreeze]
    seeAlso := ["being trichotomy", "collapse/freeze"] },
  { term := "disclaimers"
    kind := .coinage .identification
    gloss := "The disclaimers are the paper's explicit flags for original or non-canonical moves. They say which precision remains prose even when Lean checks anchors, numbering, and structural constraints."
    anchors := [``Disclaimer, ``Disclaimer.number]
    seeAlso := ["instructive absences"] }
]

/- ==============================================================================
   Structural checks
============================================================================== -/

def glossaryTerms : List String :=
  glossary.map (fun entry => entry.term)

/-- Every `seeAlso` target must have appeared earlier in the curated order. -/
def seeAlsoTargetsEarlierFrom (seen : List String) :
    List GlossaryEntry -> Bool
  | [] => true
  | entry :: rest =>
      entry.seeAlso.all (fun target => seen.contains target) &&
        seeAlsoTargetsEarlierFrom (entry.term :: seen) rest

def seeAlsoTargetsEarlier : Bool :=
  seeAlsoTargetsEarlierFrom [] glossary

example : glossary.length = 140 := rfl

example : glossaryTerms.Nodup := by
  native_decide

example : seeAlsoTargetsEarlier = true := by
  native_decide

/- ==============================================================================
   Anchor verifier
============================================================================== -/

open Lean Elab Command Meta

syntax (name := verifyGlossaryAnchors) "#verify_glossary_anchors" : command

unsafe def evalGlossaryEntries : Term.TermElabM (List GlossaryEntry) := do
  evalExpr (List GlossaryEntry)
    (mkApp (mkConst ``List [Level.zero]) (mkConst ``GlossaryEntry))
    (mkConst ``glossary)

@[command_elab verifyGlossaryAnchors] unsafe def elabVerifyGlossaryAnchors :
    CommandElab := fun _stx => do
  let entries <- liftTermElabM evalGlossaryEntries
  let env <- getEnv
  let mut missing : Array String := #[]
  for entry in entries do
    for anchor in entry.anchors do
      unless env.contains anchor do
        missing := missing.push s!"{entry.term}: {anchor}"
  unless missing.isEmpty do
    let details := missing.foldl (fun acc item => acc ++ "\n" ++ item) ""
    throwError m!"missing glossary anchors:{details}"

#verify_glossary_anchors

end WAA
