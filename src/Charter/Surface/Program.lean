import Lean
import Charter.Surface.Lower

/-!
# Charter.Surface.Program — `charter_program`: a `.charter` File as a Lean Term

    def myDoc : Charter.Dsl.Doc := charter_program "my-institution.charter"

reads the file (relative to the Lean source file, like `include_str`), parses and
validates it at elaboration time, and elaborates to the literal `Charter.Dsl.Doc` it
denotes. Lowering that term with `Charter.Dsl.lowerLaw` gives a `Charter.Law σ_dyn`
on which every kernel-checked statement of the language can be made by `decide`:
well-formedness, provenance coverage, approval status, scenario outcomes, and
equality with a hand-written Lean law.

The parser runs inside the elaborator, exactly as the `charter_*` macros run inside
the macro expander: the kernel only ever sees the resulting data, never the text.
Lake does not track the `.charter` file as a dependency of the Lean module, so after
editing the file, touch or rebuild the module that embeds it.
-/

namespace Charter.Dsl

open Lean Elab Term

syntax (name := charterProgramStx) "charter_program " str : term

@[term_elab charterProgramStx] def elabCharterProgram : TermElab
  | `(charter_program $path:str), _ => do
    let ctx ← readThe Core.Context
    let srcPath := System.FilePath.mk ctx.fileName
    let some srcDir := srcPath.parent
      | throwError "charter_program: cannot compute parent directory of `{srcPath}`"
    let full := srcDir / path.getString
    let txt ← IO.FS.readFile full
    match parseCharterText txt with
    | .error e => throwError "charter_program {path.getString}: {e}"
    | .ok doc =>
      match validate doc with
      | [] => return toExpr doc
      | errs => throwError "charter_program {path.getString}: {"\n".intercalate errs}"
  | _, _ => throwUnsupportedSyntax

end Charter.Dsl
