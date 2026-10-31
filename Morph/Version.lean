/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

/-!
# The Morph version (loop 92)

Semantic versioning for the language (LONGTERM_ROADMAP: adopt SemVer, publish
Morph 0.1 with a changelog and a stability policy for the core calculus).
`morph version` prints this; the policy it versions is `STABILITY.md`, the
history is `CHANGELOG.md`.
-/

namespace Morph

/-- The current release. Bumped by the release process with a `CHANGELOG.md`
entry (see `STABILITY.md` for what a bump is allowed to change). -/
def versionString : String := "0.1.0"

end Morph
