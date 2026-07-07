import WeldAndArrow.Gen.AssumptionsLib
import WeldAndArrow.Gen.ExpositionLib

namespace WAA.Gen.FullExpositionGeneration

def outputRoot : String := ".lake/exposition-full"

def expositionDir : String := outputRoot ++ "/Exposition"

def expectedFiles : List String := [
  "Assumptions.md",
  "Formalization.md",
  "Glossary.md",
  "Identification.md",
  "Theorems.md",
  "Theory.md",
  "index.md"
]

def writeAssumptions : IO Unit := do
  IO.FS.createDirAll expositionDir
  IO.FS.writeFile (expositionDir ++ "/Assumptions.md") WAA.renderAssumptions

def checkNonempty (file : String) : IO Unit := do
  let path := expositionDir ++ "/" ++ file
  let content <- IO.FS.readFile path
  if content.isEmpty then
    throw (IO.userError s!"generated exposition file is empty: {path}")

def run : IO Unit := do
  WAA.Exposition.writeDocs outputRoot
  writeAssumptions
  for file in expectedFiles do
    checkNonempty file

end WAA.Gen.FullExpositionGeneration

def main : IO Unit := do
  WAA.Gen.FullExpositionGeneration.run
