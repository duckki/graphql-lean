import Lake

open System

namespace Lint.ImportClosure

def defaultRoots : List String :=
  [
    "GraphQL",
    "Proofs",
    "Tests",
    "Benchmarks.QueryInclusion",
    "Lint",
    "Lint.ImportClosureMain"
  ]

def usage : String :=
  s!"Usage: lake exe import-closure [ROOT ...]\n\n"
  ++ "Checks that every existing tracked .lean file is reachable from the transitive\n"
  ++ "import closure of the root modules. Defaults to: "
  ++ ", ".intercalate defaultRoots

def runProcess (cmd : String) (args : Array String) (cwd : Option FilePath := none)
    : IO String := do
  let output ← IO.Process.output { cmd := cmd, args := args, cwd := cwd }
  if output.exitCode != 0 then
    let details :=
      "\n".intercalate ([output.stdout, output.stderr].filter (· != ""))
      |>.trimAscii
      |>.toString
    let message :=
      s!"{" ".intercalate (cmd :: args.toList)} failed"
      ++ if details == "" then "" else s!":\n{details}"
    throw (IO.userError message)
  pure output.stdout

def repositoryRoot : IO FilePath := do
  let stdout ← runProcess "git" #["rev-parse", "--show-toplevel"]
  pure (FilePath.mk stdout.trimAscii.toString)

def moduleNameForFile (file : String) : String :=
  (file.dropEnd ".lean".length |>.toString).replace "/" "."

def normalizeRoot (root : String) : String :=
  let trimmed := root.trimAscii.toString
  let root := if trimmed.startsWith "+" then (trimmed.drop 1).toString else trimmed
  if root.endsWith ".lean" then moduleNameForFile root else root

def parseRoots (args : List String) : Except String (Option (List String)) := do
  if args.any (fun arg => arg == "--help" || arg == "-h") then
    return none
  if let some arg := args.find? (fun arg => arg.startsWith "-") then
    throw s!"unknown option: {arg}"
  return some (if args.isEmpty then defaultRoots else args.map normalizeRoot)

def existingTrackedLeanFiles (repoRoot : FilePath) : IO (List String) := do
  let output ← runProcess "git" #["ls-files", "-z", "--", "*.lean"] (cwd := some repoRoot)
  let files := output.splitOn (String.singleton (Char.ofNat 0)) |>.filter (· != "")
  let mut existing := []
  for file in files do
    if (← (repoRoot / file).pathExists) then
      existing := existing ++ [file]
  pure existing

def parseStringArrayJson (source : String) : Except String (List String) := do
  let json ← Lean.Json.parse source
  let items ← json.getArr?
  items.toList.mapM (fun item => item.getStr?)

def transitiveImports (repoRoot : FilePath) (root : String) : IO (List String) := do
  let output ←
    runProcess "lake" #["query", s!"+{root}:transImports", "--json"]
      (cwd := some repoRoot)
  IO.ofExcept (parseStringArrayJson output.trimAscii.toString)

def reachableModules (repoRoot : FilePath) (roots : List String) : IO (List String) := do
  let mut reachable := []
  for root in roots do
    reachable := root :: reachable
    reachable := (← transitiveImports repoRoot root) ++ reachable
  pure reachable

def checkLeanImportClosure (roots : List String := defaultRoots) : IO UInt32 := do
  let repoRoot ← repositoryRoot
  let files ← existingTrackedLeanFiles repoRoot
  let reachable ← reachableModules repoRoot roots
  let unreachable :=
    files.filterMap
      fun file =>
        let moduleName := moduleNameForFile file
        if reachable.contains moduleName then
          none
        else
          some (file, moduleName)
  if unreachable.isEmpty then
    IO.println
      (s!"lean-import-closure: ok ({files.length} existing tracked Lean file(s), "
        ++ s!"roots: {", ".intercalate roots})")
    pure 0
  else
    IO.eprintln
      s!"lean-import-closure: found {unreachable.length} unreachable Lean file(s)"
    IO.eprintln s!"roots: {", ".intercalate roots}"
    for (file, moduleName) in unreachable do
      IO.eprintln s!"  {file} ({moduleName})"
    IO.eprintln
      "Import the module from a reachable root, pass it as a root, or delete it."
    pure 1

def main (args : List String) : IO UInt32 := do
  match parseRoots args with
  | .ok none =>
      IO.println usage
      pure 0
  | .ok (some roots) =>
      checkLeanImportClosure roots
  | .error message =>
      IO.eprintln s!"lean-import-closure: {message}"
      pure 1

end Lint.ImportClosure
