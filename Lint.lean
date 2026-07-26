import Lint.ImportClosure
import Lake

open System

def lineWidth : Nat := 100

def commentWidth : Nat := lineWidth

def fileLineLimit : Nat := 1500

def rootLeanFiles : List FilePath :=
  ["GraphQL.lean", "Proofs.lean", "Lint.lean"]

def sourceDirs : List FilePath :=
  ["GraphQL", "Proofs", "Lint"]

def textFiles : List FilePath :=
  ["README.md"]

def isLeanFile (path : FilePath) : Bool :=
  path.extension == some "lean"

def allLeanFiles : IO (List FilePath) := do
  let mut files := rootLeanFiles
  for dir in sourceDirs do
    if (← dir.pathExists) && (← dir.isDir) then
      let entries ← dir.readDir
      for entry in entries do
        if isLeanFile entry.path then
          files := files ++ [entry.path]
  pure files

def allTextLintFiles : IO (List FilePath) := do
  pure ((← allLeanFiles) ++ textFiles)

def trimLeft (line : String) : String :=
  line.trimAsciiStart.toString

def dropTrailingCarriageReturn (line : String) : String :=
  line.dropEndWhile (fun char => char == '\r') |>.toString

def isBlockCommentStart (line : String) : Bool :=
  let trimmed := trimLeft line
  trimmed.startsWith "/-" && !trimmed.startsWith "-/"

def isBlockCommentEnd (line : String) : Bool :=
  (trimLeft line).startsWith "-/"

def isLineComment (line : String) : Bool :=
  (trimLeft line).startsWith "--"

def containsDollarSyntax (line : String) : Bool :=
  line.contains (String.singleton (Char.ofNat 36))

def containsLambdaSyntax (line : String) : Bool :=
  line.contains (String.singleton (Char.ofNat 955))

def containsDoubleUnderscore (line : String) : Bool :=
  line.contains (String.singleton '_' ++ String.singleton '_')

def hasUrl (line : String) : Bool :=
  line.contains "http://" || line.contains "https://"

def hasTrailingWhitespace (line : String) : Bool :=
  line.endsWith " " || line.endsWith "\t"

def hasTab (line : String) : Bool :=
  line.contains "\t"

def hasUnscopedSetOption (line : String) : Bool :=
  let trimmed := trimLeft line
  trimmed.startsWith "set_option"
  && (trimmed.contains "trace"
      || trimmed.contains "pp."
      || trimmed.contains "profiler"
      || trimmed.contains "maxHeartbeats")
  && !trimmed.contains " in "

def hasBareOpenClassical (line : String) : Bool :=
  let trimmed := trimLeft line
  trimmed == "open Classical" || trimmed == "open scoped Classical"

def declarationName? (line : String) : Option String :=
  match (trimLeft line).splitOn " " |>.filter (· != "") with
  | "def" :: name :: _ => some name
  | "theorem" :: name :: _ => some name
  | "lemma" :: name :: _ => some name
  | "abbrev" :: name :: _ => some name
  | "structure" :: name :: _ => some name
  | "inductive" :: name :: _ => some name
  | "class" :: name :: _ => some name
  | "instance" :: name :: _ => some name
  | _ => none

def hasBadDeclarationName (line : String) : Bool :=
  match declarationName? line with
  | none => false
  | some name => containsDoubleUnderscore name

def checkCommonStyleInFile (path : FilePath) : IO (List String) := do
  let content ← IO.FS.readFile path
  let lines := content.splitOn "\n"
  let mut failures := []
  let mut lineNumber := 1
  for rawLine in lines do
    let line := dropTrailingCarriageReturn rawLine
    if line.length > lineWidth && !hasUrl line then
      failures := failures ++ [s!"{path}:{lineNumber}: line has {line.length} columns"]
    if hasTrailingWhitespace line then
      failures := failures ++ [s!"{path}:{lineNumber}: trailing whitespace"]
    if hasTab line then
      failures := failures ++ [s!"{path}:{lineNumber}: tab character"]
    if containsLambdaSyntax line then
      failures :=
        failures ++ [s!"{path}:{lineNumber}: use `fun` instead of lambda syntax"]
    if containsDollarSyntax line then
      failures := failures ++ [s!"{path}:{lineNumber}: use `<|` instead of dollar syntax"]
    if hasUnscopedSetOption line then
      failures :=
        failures
        ++ [s!"{path}:{lineNumber}: avoid unscoped diagnostic/resource `set_option`"]
    if hasBareOpenClassical line then
      failures :=
        failures ++ [s!"{path}:{lineNumber}: scope `open Classical` to a declaration"]
    if hasBadDeclarationName line then
      failures :=
        failures ++ [s!"{path}:{lineNumber}: declaration name contains double underscore"]
    lineNumber := lineNumber + 1
  if lines.length > fileLineLimit then
    failures :=
      failures ++ [s!"{path}: file has {lines.length} lines; limit is {fileLineLimit}"]
  pure failures

def checkCommonStyle (files : List FilePath) : IO UInt32 := do
  let mut failures := []
  for file in files do
    if (← file.pathExists) then
      failures := failures ++ (← checkCommonStyleInFile file)
  if failures.isEmpty then
    IO.println "community-style: ok"
    pure 0
  else
    IO.eprintln s!"community-style: found {failures.length} issue(s)"
    for failure in failures do
      IO.eprintln failure
    pure 1

def checkCommentWidthInFile (path : FilePath) : IO (List String) := do
  let content ← IO.FS.readFile path
  let mut inBlockComment := false
  let mut lineNumber := 1
  let mut failures := []
  for line in content.splitOn "\n" do
    let line := dropTrailingCarriageReturn line
    let startsBlockComment := isBlockCommentStart line
    let isComment := inBlockComment || isLineComment line || startsBlockComment
    if isComment && line.length > commentWidth then
      failures :=
        failures ++ [s!"{path}:{lineNumber}: comment line has {line.length} columns"]
    if !inBlockComment && startsBlockComment && !line.contains "-/" then
      inBlockComment := true
    else if inBlockComment && isBlockCommentEnd line then
      inBlockComment := false
    lineNumber := lineNumber + 1
  pure failures

def checkCommentWidth (files : List FilePath) : IO UInt32 := do
  let mut failures := []
  for file in files do
    failures := failures ++ (← checkCommentWidthInFile file)
  if failures.isEmpty then
    IO.println s!"comment-width: ok (≤ {commentWidth})"
    pure 0
  else
    IO.eprintln s!"comment-width: found {failures.length} long comment line(s)"
    for failure in failures do
      IO.eprintln failure
    pure 1

def runLeanLintOnFile (path : FilePath) : IO UInt32 := do
  let output ←
    IO.Process.output
      {
        cmd := "lake",
        args :=
          #[
            "env",
            "lean",
            "-D",
            "linter.all=true",
            "-D",
            "linter.missingDocs=false",
            path.toString
          ]
      }
  if output.stdout != "" then
    IO.print output.stdout
  if output.stderr != "" then
    IO.eprint output.stderr
  if output.exitCode != 0 then
    pure output.exitCode
  else if output.stdout != "" || output.stderr != "" then
    pure 1
  else
    pure 0

def checkLeanLinters (files : List FilePath) : IO UInt32 := do
  let mut failures := 0
  for file in files do
    let exitCode ← runLeanLintOnFile file
    if exitCode != 0 then
      failures := failures + 1
  if failures == 0 then
    IO.println "lean-lint: ok"
    pure 0
  else
    IO.eprintln s!"lean-lint: {failures} file(s) failed"
    pure 1

def buildProject : IO UInt32 := do
  let output ← IO.Process.output { cmd := "lake", args := #["build"] }
  if output.stdout != "" then
    IO.print output.stdout
  if output.stderr != "" then
    IO.eprint output.stderr
  if output.exitCode == 0 then
    pure 0
  else
    IO.eprintln "build: failed before linting"
    pure output.exitCode

def checkLeanImportClosure : IO UInt32 := do
  Lint.ImportClosure.checkLeanImportClosure

def main (_args : List String) : IO UInt32 := do
  let files ← allLeanFiles
  let textFiles ← allTextLintFiles
  let buildExit ← buildProject
  let commentExit ← checkCommentWidth textFiles
  let styleExit ← checkCommonStyle textFiles
  let importClosureExit ← checkLeanImportClosure
  let leanExit ←
    if buildExit == 0 then
      checkLeanLinters files
    else
      pure 1
  pure
    (if buildExit == 0
        && commentExit == 0
        && styleExit == 0
        && importClosureExit == 0
        && leanExit == 0 then
        0
      else
        1)
