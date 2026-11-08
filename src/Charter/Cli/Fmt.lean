import Charter.Surface.Pretty

/-!
# Charter.Cli.Fmt — `charter fmt [--check] <file.charter ...>`

Formats `.charter` and `.eflint` source files canonically while preserving Leading `//!`
directives and verifying round-trip AST equality (`Pretty.formatAndVerify`) before any
file write (`AGENTS.md`: no silent fallbacks).
-/

namespace Charter.Cli

/-- Extract leading `//!` directive lines so test/exploration headers survive formatting. -/
def extractDirectiveHeader (src : String) : String :=
  let dirs := src.splitOn "\n" |>.filter (fun l => l.trim.startsWith "//!")
  if dirs.isEmpty then "" else "\n".intercalate dirs ++ "\n"

structure FmtOpts where
  checkOnly : Bool := false
  stdout    : Bool := false
  canonical : Bool := false
  files     : List String := []

def parseFmtArgs : List String → FmtOpts → Except String FmtOpts
  | [], o => .ok { o with files := o.files.reverse }
  | "--check" :: rest, o => parseFmtArgs rest { o with checkOnly := true }
  | "--stdout" :: rest, o => parseFmtArgs rest { o with stdout := true }
  | "--canonical" :: rest, o => parseFmtArgs rest { o with canonical := true }
  | a :: rest, o =>
    if a.startsWith "--" then .error s!"unknown flag {a}"
    else parseFmtArgs rest { o with files := a :: o.files }

/-- `charter fmt [--check] [--stdout] [--canonical] <file.charter ...>` -/
def fmtCommand (args : List String) : IO UInt32 := do
  let usage := "usage: charter fmt [--check] [--stdout] [--canonical] <file.charter> ..."
  match parseFmtArgs args {} with
  | .error e => IO.eprintln s!"charter fmt: {e}\n{usage}"; return 2
  | .ok o =>
    if o.files.isEmpty then IO.eprintln usage; return 2
    let mut status : UInt32 := 0
    for f in o.files do
      let p := System.FilePath.mk f
      if !(← p.pathExists) then
        IO.eprintln ((Diagnostic.error "CHR005" s!"cannot read {f}").withFile f).render
        status := 1
      else
        let src ← IO.FS.readFile p
        let fmtRes := if o.canonical then
          let hdr := extractDirectiveHeader src
          (hdr ++ ·) <$> Pretty.formatAndVerify src
        else
          Pretty.formatSourceAndVerify src
        match fmtRes with
        | .error d =>
          IO.eprintln (d.withFile f).render
          status := 1
        | .ok out =>
          if o.stdout then
            IO.print out
          else if o.checkOnly then
            if src != out then
              IO.eprintln s!"{f}: needs formatting (run `charter fmt {f}`)"
              status := 1
          else if src != out then
            IO.FS.writeFile p out
    return status

end Charter.Cli
