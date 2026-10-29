/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Driver

/-!
# Driver tests

End-to-end checks of the pipeline the `morph` executable runs: source text in,
`Outcome` out. Both pipeline stages are proved-total components (the parser,
loops 9/39; the evaluator, loop 38), so these tests only have to pin down the
*values*, which they do on the compiled evaluator (`native_decide`, the same
style as `Morph.Tests.Executable`).

The surface below is what `parseExpr` covers today: numeric/string/bool
literals, the binary operators, `if`/`let`. Unit and array literals and
lambda application are not yet parsed (the parsed `fn x -> e` also keeps its
parameter as an `fvar`, which the bvar-binding evaluator cannot see) — those
are the frontend gaps recorded in `docs/RESEARCH-LOOPS-70-79.md`.
-/

namespace Morph.Tests.Driver

open Morph.Driver

/-! ## Arithmetic and precedence -/

example : runSource "1 + 2 * 3" == .value "7" := by native_decide

example : runSource "(1 + 2) * 3" == .value "9" := by native_decide

example : runSource "10 / 3" == .value "3" := by native_decide

example : runSource "10 % 3" == .value "1" := by native_decide

example : runSource "2 - 5" == .value "-3" := by native_decide

/-! ## Comparisons and logic -/

example : runSource "2 < 3" == .value "true" := by native_decide

example : runSource "3 == 3" == .value "true" := by native_decide

example : runSource "true && false" == .value "false" := by native_decide

example : runSource "true || false" == .value "true" := by native_decide

example : runSource "if true then 1 else 2" == .value "1" := by native_decide

example : runSource "if 1 == 2 then 10 else 20" == .value "20" := by
  native_decide

/-! ## Strings -/

example : runSource "\"abc\" + \"def\"" == .value "abcdef" := by native_decide

example : runSource "\"hi\"" == .value "hi" := by native_decide

/-! ## Failure is a value, not a crash -/

-- A truncated expression fails to parse.
example : isParseFailed (runSource "1 +") := by
  native_decide

-- So does garbage.
example : isParseFailed (runSource "!!") := by
  native_decide

-- The empty program has no expression to parse.
example : isParseFailed (runSource "") := by
  native_decide

-- A type error at evaluation time is `stuck`, not a crash.
example : isStuck (runSource "1 && true") := by
  native_decide

-- An unbound name is `stuck` too.
example : isStuck (runSource "noSuchVariable + 1") := by
  native_decide

-- And `morph parse` reports the AST without evaluating.
example : isValue (parseSource "1 + 2") := by native_decide

end Morph.Tests.Driver
