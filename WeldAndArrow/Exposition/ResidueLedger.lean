import WeldAndArrow.Exposition.Basic
import WeldAndArrow.Doctrines.FoxCase
import WeldAndArrow.Doctrines.FactorsNegative

namespace WAA.Exposition

structure ResidueEntry where
  id : String
  locus : DocId
  reason : String
  anchors : List Lean.Name := []
deriving Repr

def residueLedger : List ResidueEntry := [
  { id := "glossary-accuracy"
    locus := "glossary"
    reason := "Gloss accuracy and canonical caveats remain prose obligations." },
  { id := "designation-universe-adequacy"
    locus := "identification"
    reason := "Adequacy of the modeled designation-universe to the avyākata questions remains a modeling claim." },
  { id := "an663-correlation"
    locus := "theorems"
    reason := "The AN 6.63 correlation, peaks reading, and comparative claim against event-typed theories remain prose-bound." },
  { id := "hakuin-epigram"
    locus := "theory"
    reason := "The Hakuin epigram pedigree is mixed and load-free for the checked mechanism." },
  { id := "kuoan-locus"
    locus := "theorems"
    reason := "The exact Kuòān verse locus for the Ten Bulls guard should be verified across translations." },
  { id := "historical-contra-dogen"
    locus := "theory"
    reason := "The Daishugyō/Jinshin inga contra has narrowed: both fascicles' core verdicts are checked with the same production and defiled-falsehood vocabulary, but whether the structurally unproduced floor face may be held remains historical interpretation, not a Lean result."
    anchors := [``FoxCase.daishugyo_floor_face_unproduced,
      ``FoxCase.oldMan_defiledFalsehood,
      ``FoxCase.jinshinInga_floor_voicing_defiled] },
  { id := "pilinda-response-form-vasana"
    locus := "theorems"
    reason := "Response-form vāsanā—an undefiled Pilinda-shaped habit at pole share—remains future work; the current theorem covers only live share in the body door."
    anchors := [``Grid.WaaVasana] },
  { id := "doubt-fetter-door-neutrality"
    locus := "theorems"
    reason := "The doubt fetter remains a supplied weld-class without a canonical door factorization."
    anchors := [``Grid.FetterReading] },
  { id := "conduct-factor-inert"
    locus := "theorems"
    reason := "The speech blocker is now the speech-door class, but the conduct factor remains intentionally inert pending body-door intimation content."
    anchors := [``PathFactor.blockerClass,
      ``FactorsNegative.conduct_class_inert] }
]

example : residueLedger.length = 9 := rfl

end WAA.Exposition
