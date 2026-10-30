/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Frontend.Lexer

/-!
# Executable min-to-hum projection (loop 79)

The translation table (`Morph.Specs.SyntaxTranslation`: `fix`→`match`,
`fn`→`function`, `ret`→`return`, `use`→`import`, `act`→`actor`) is specified
at the string level, but only one entry can reach the executable expression
parser: the module-level keywords (`function`/`import`/`actor` and their min
twins) never appear in an expression or statement, and the parser already
speaks a mixed surface (`fn` is min, `return` is hum). So the executable
projection maps exactly the entry the parser can observe — `fix` to `match` —
at the token level, where keywords are already classified and identifiers
(`prefix`), strings (`"fix"`), and comments can never be confused with them.

`Parser.matchHead` is the single-token version of this map, applied at the
`match`/`fix` dispatch sites so the hum parser below runs unchanged.
-/

namespace Morph.Frontend.Dialect

open Morph.Frontend

/-- Project one token from min to hum: `fix` becomes `match`, everything
else is untouched (identifiers, strings, and comments are already distinct
token kinds, so no naive-substring hazard like `prefix` → `prematch`).
The condition is propositional (`DecidableEq`, not `BEq`): `TokenKind` has no
`LawfulBEq` instance, so the `==` bridge is unprovable here — and the proofs
below case on the condition directly. -/
def projectToken (t : Token) : Token :=
  if t.kind = .keyword "fix" then { t with kind := .keyword "match" } else t

/-- Project a whole token stream from min to hum. -/
def projectMinToHum (toks : List Token) : List Token :=
  toks.map projectToken

/-- One token projects idempotently. -/
theorem projectToken_idem (t : Token) :
    projectToken (projectToken t) = projectToken t := by
  unfold projectToken
  split <;> simp_all

/-- Projecting twice is projecting once. -/
theorem projectMinToHum_idem (toks : List Token) :
    projectMinToHum (projectMinToHum toks) = projectMinToHum toks := by
  unfold projectMinToHum
  rw [List.map_map]
  have hcomp : (projectToken ∘ projectToken) = projectToken :=
    funext fun t => projectToken_idem t
  rw [hcomp]

/-- A hum stream (no `fix` keyword) projects to itself. -/
theorem projectMinToHum_hum (toks : List Token)
    (h : ∀ t ∈ toks, t.kind ≠ .keyword "fix") :
    projectMinToHum toks = toks := by
  simp only [projectMinToHum]
  induction toks with
  | nil => rfl
  | cons t rest ih =>
    simp only [List.map_cons]
    have ht : t.kind ≠ .keyword "fix" := h t (List.mem_cons_self ..)
    have hrest : ∀ t' ∈ rest, t'.kind ≠ .keyword "fix" :=
      fun t' hm => h t' (List.mem_cons_of_mem _ hm)
    have htok : projectToken t = t := by
      unfold projectToken
      simp_all
    rw [htok, ih hrest]

end Morph.Frontend.Dialect
