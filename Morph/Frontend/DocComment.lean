/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

/-!
# Documentation comments (loop 90)

The language spec (`spec/language/lexical_structure_syntax_spec.md` §1.3)
blesses `/// ...` as *semantic doc* lines. The lexer already skips them as
ordinary `//` comments, so documented files parse and run unchanged — this
module only *extracts* them: a maximal run of `///` lines documents the next
code line (blank and plain-`//` lines between the block and its statement are
tolerated; a block with no following statement is dropped). `morph doc`
renders the entries as Markdown via `renderMarkdown`.

Text-level by design (loop 90): statements carry no source spans, so pairing
by AST would need span tracking through the proved-total parser. The entry
shows the statement's first line; multi-line bodies are identified by it.
-/

namespace Morph.Frontend.DocComment

/-- One documented statement: the doc text and the statement's first line. -/
structure DocEntry where
  docs : String
  code : String
  deriving Repr, BEq, DecidableEq

/-- Strip the `///` prefix (one optional space after it) from a doc line. -/
def stripDocPrefix (line : String) : Option String :=
  let t := (line.dropWhile Char.isWhitespace).toString
  if t.startsWith "///" then
    let c := (t.drop 3).toString
    some (if c.startsWith " " then (c.drop 1).toString else c)
  else none

/-- A trimmed line is a plain (non-doc) comment. -/
def isPlainComment (trimmed : String) : Bool :=
  trimmed.startsWith "//"

/-- Extract the documented statements of a source file, in order. -/
def extract (src : String) : List DocEntry :=
  go (src.splitOn "\n") [] []
where go : List String → List String → List DocEntry → List DocEntry
  | [], _, acc => acc.reverse
  | line :: rest, pending, acc =>
    match stripDocPrefix line with
    | some d => go rest (pending ++ [d]) acc
    | none =>
      let t := line.trimAscii.toString
      if t == "" || isPlainComment t then go rest pending acc
      else
        match pending with
        | [] => go rest [] acc
        | ds => go rest [] ({ docs := "\n".intercalate ds, code := t } :: acc)

/-- Render entries as Markdown. Files without docs get the empty note. -/
def renderMarkdown : List DocEntry → String
  | [] => "# Documentation\n\nNo documentation comments found.\n"
  | entries =>
    "# Documentation\n" ++
      "".intercalate (entries.map fun e =>
        "\n## `" ++ e.code ++ "`\n" ++ e.docs ++ "\n")

/-! ## The extraction contract, pinned

The `///` convention the lexer already skips: one space stripped, plain
comments untouched, empty files extracting to nothing. -/

/-- One space after `///` is stripped. -/
theorem stripDocPrefix_doc : stripDocPrefix "/// hello" = some "hello" := by native_decide

/-- More leading space is kept past the first. -/
theorem stripDocPrefix_indented : stripDocPrefix "  ///  hi" = some " hi" := by native_decide

/-- Plain comments are not docs. -/
theorem stripDocPrefix_plain : stripDocPrefix "// x" = none := by native_decide

/-- Code lines are not docs. -/
theorem stripDocPrefix_code : stripDocPrefix "let y = 5;" = none := by native_decide

/-- Empty files extract to nothing. -/
theorem extract_empty : extract "" = [] := by native_decide

/-- Undocumented files extract to nothing. -/
theorem extract_undocumented : extract "let y = 5;\ny" = [] := by native_decide

/-- The empty rendering is the documented note. -/
theorem renderMarkdown_empty : renderMarkdown [] =
    "# Documentation\n\nNo documentation comments found.\n" := rfl

end Morph.Frontend.DocComment
