/-!
# Charter.Surface.Diagnostics — Diagnostics as data

Every error and warning the `charter` binary reports is a record (plan §3): a
code allocated in `docs/spec/diagnostics.md`, a severity, a hand-written message
naming the construct, and a position. The CLI renders them; nothing in a message
names the engine (Law 11).
-/

namespace Charter

/-- A line/column position in a source file (1-based; `0,0` when unknown). -/
structure Pos where
  line : Nat := 0
  col  : Nat := 0
  deriving Repr, DecidableEq, Inhabited

instance : ToString Pos := ⟨fun p => s!"{p.line}:{p.col}"⟩

inductive Severity
  | error
  | warning
  deriving Repr, DecidableEq, Inhabited

instance : ToString Severity := ⟨fun | .error => "error" | .warning => "warning"⟩

/-- A diagnostic record. `file` is filled in by the driver that knows the path. -/
structure Diagnostic where
  code     : String
  severity : Severity := .error
  message  : String
  file     : String := ""
  pos      : Pos := {}
  notes    : List String := []
  deriving Repr, Inhabited

namespace Diagnostic

def error (code : String) (message : String) (pos : Pos := {}) (notes : List String := []) : Diagnostic :=
  { code, severity := .error, message, pos, notes }

def warning (code : String) (message : String) (pos : Pos := {}) (notes : List String := []) : Diagnostic :=
  { code, severity := .warning, message, pos, notes }

def withFile (d : Diagnostic) (file : String) : Diagnostic :=
  if d.file.isEmpty then { d with file } else d

def withPos (d : Diagnostic) (pos : Pos) : Diagnostic :=
  if d.pos == {} then { d with pos } else d

def isError (d : Diagnostic) : Bool := d.severity == .error

/-- `file:line:col: error CHR003: message` followed by indented notes. -/
def render (d : Diagnostic) : String :=
  let loc := if d.file.isEmpty then "" else
    if d.pos == {} then s!"{d.file}: " else s!"{d.file}:{d.pos}: "
  let head := s!"{loc}{d.severity} {d.code}: {d.message}"
  (head :: d.notes.map (fun n => "  " ++ n)) |> String.intercalate "\n"

end Diagnostic

end Charter
