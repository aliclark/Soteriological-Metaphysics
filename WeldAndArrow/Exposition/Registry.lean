import WeldAndArrow.Exposition.Basic
import WeldAndArrow.Exposition.ResidueLedger

namespace WAA.Exposition

inductive DocProvenance
  | source
  | generated (generator : String)
deriving Repr, BEq

structure DocRef where
  id : DocId
  title : String
  output : String
  provenance : DocProvenance
  summary : String
deriving Repr

def preambleRef : DocRef :=
  { id := "preamble"
    title := "Preamble"
    output := "Exposition/Preamble.md"
    provenance := .source
    summary := "Jingqing's peck-and-tap exchange from the Blue Cliff Record, rendered from the Chinese" }

def indexRef : DocRef :=
  { id := "index"
    title := "Contents"
    output := "Exposition/index.md"
    provenance := .generated "lake exe exposition_gen"
    summary := "this table of contents, generated from the exposition registry; its reading order, numbering, links, and document inventory follow the registered document set" }

def theoryRef : DocRef :=
  { id := "theory"
    title := "Theory"
    output := "Exposition/Theory.md"
    provenance := .source
    summary := "the motivations and the rules: the floor, the act-grammar, the grade and its determination, the supplied sentience joint and orthogonality, the karma circuit and its three registers, the weld's two faces, the separate/fuse rule; the input-side assumption list at [Assumptions.md](Assumptions.md); one act run whole through the grid; [Glossary.md](Glossary.md)" }

def theoremsRef : DocRef :=
  { id := "theorems"
    title := "Theorems"
    output := "Exposition/Theorems.md"
    provenance := .source
    summary := "what falls out of the rules directly (backsliding, memory and prudence, dukkha, the transposition, the error-taxonomy) and the derivations that meet existing discourses (MMK 17, the three killings and AN 6.63, sudden and gradual, other-power, pariṇāmanā, transcription, the Ten Bulls, Five Ranks, and stage-schemes); with the instructive absences in both" }

def identificationRef : DocRef :=
  { id := "identification"
    title := "The Identification and Placements"
    output := "Exposition/Identification.md"
    provenance := .source
    summary := "the karma identification, the offices-spine that earns the name, the sower/reaper split, the contemporary placements, the pole-typing corollary, the taxonomy's internal mis-feeds, and the disclaimers, enumerated" }

def readingRef : DocRef :=
  { id := "reading"
    title := "Reading"
    output := "Exposition/Reading.md"
    provenance := .source
    summary := "a plain-English reading of the checked Lean surface: the reading conventions (the `Waa` system-POV marking, the directed-convention namespace layers as ontological ordering, rfl-transparency notes), the preorder and pole-class preliminaries, the signature and its convention layers, the layer-by-layer readings of `Consequences`, `Doctrines`, `Identification`, and `Meta` with the numbered pins, the śūnyatā wrappers and reflexivity witness, the invariance discipline and its sibling countermodels, the verdict ledger, and the axiom audit; with what remains prose-bound flagged throughout" }

def assumptionsRef : DocRef :=
  { id := "assumptions"
    title := "Assumptions"
    output := "Exposition/Assumptions.md"
    provenance := .generated "lake exe exposition_gen"
    summary := "the input side, enumerated: what the Signature asserts, what it deliberately declines, and its stand-ins; with checked anchors and the axiom audit" }

def glossaryRef : DocRef :=
  { id := "glossary"
    title := "Glossary"
    output := "Exposition/Glossary.md"
    provenance := .generated "lake exe exposition_gen"
    summary := "the generated glossary table from `WeldAndArrow/Exposition/Glossary.lean`: each term with its provenance kind (a Theory, Theorems, or Identification coinage; canonical; or Lean convention), a newcomer-facing gloss, checked Lean anchors, and backward-only see-also references; term uniqueness, reference ordering, table length, and anchor resolvability are Lean-checked, while gloss accuracy and canonical caveats remain prose obligations carried by the Disclaimers" }

/-- Reading order. List position is the Contents number. -/
def registry : List DocRef := [
  preambleRef,
  indexRef,
  theoryRef,
  theoremsRef,
  identificationRef,
  assumptionsRef,
  glossaryRef,
  readingRef
]

def registryIds : List DocId := registry.map (fun ref => ref.id)

def registryOutputs : List String := registry.map (fun ref => ref.output)

def DocRef.toDoc (ref : DocRef) : Doc :=
  { id := ref.id
    title := ref.title
    output := ref.output
    source := ref.output
    summary := ref.summary }

def allDocs : List Doc := registry.map DocRef.toDoc

example : registry.length = 8 := rfl

theorem registry_ids_nodup : registryIds.Nodup := by
  decide

theorem registry_outputs_nodup : registryOutputs.Nodup := by
  decide

theorem residue_loci_registered :
    residueLedger.all (fun entry => registryIds.contains entry.locus) = true := by
  decide

end WAA.Exposition
