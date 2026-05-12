/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Specs.BackendTiling.Spec

namespace Morph.Specs.BackendTiling

/-!
## Examples

Concrete examples demonstrating the BackendTiling specification.
-/

def tile1 : Tile := { offset := 0, size := 4, stride := 1 }

def tile2 : Tile := { offset := 4, size := 4, stride := 1 }

def tiles : List Tile := generateTiles 10 4

example : expectedCacheHits tile1 2 = 2 := rfl

example : expectedCacheHits tile1 10 = 4 := rfl

example : cacheHitRatio 0 0 = 1.0 := rfl

example : getTileForIndex [] 0 = none := by
  unfold getTileForIndex; simp

example : defaultTile.offset = 0 := rfl

example : defaultTile.size = 0 := rfl

example : defaultTilingStrategy = TilingStrategy.block 1 := rfl

theorem tile_size_nonneg (t : Tile) : t.size ≥ 0 := Nat.zero_le t.size

theorem tile_offset_nonneg (t : Tile) : t.offset ≥ 0 := Nat.zero_le t.offset

end Morph.Specs.BackendTiling
