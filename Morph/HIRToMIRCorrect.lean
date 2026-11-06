/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.HIRToMIRCore
import Morph.HIRToMIRTotal

/-!
# Straight-line `compile_correct` bridge (loops 139-142)

Umbrella module. The bridge is split so that work on the totality section
(`Morph/HIRToMIRTotal.lean`, the small file) does not re-elaborate the
forward proofs (`Morph/HIRToMIRCore.lean`). Import this module, not the
parts.
-/
