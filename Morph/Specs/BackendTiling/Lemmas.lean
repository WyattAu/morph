/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Specs.BackendTiling.Spec

namespace Morph.Specs.BackendTiling

/-!
## Lemmas

Lemmas and auxiliary results for the BackendTiling specification.
-/

theorem generateTiles_empty_tileSize (arraySize : Nat) :
  generateTiles arraySize 0 = [] := rfl

theorem expectedCacheHits_le_tileSize (tile : Tile) (cacheSize : Nat) :
  expectedCacheHits tile cacheSize ≤ tile.size := Nat.min_le_left tile.size cacheSize

theorem expectedCacheHits_le_cacheSize (tile : Tile) (cacheSize : Nat) :
  expectedCacheHits tile cacheSize ≤ cacheSize := Nat.min_le_right tile.size cacheSize

theorem defaultTile_eq : defaultTile = { offset := 0, size := 0, stride := 0 } := rfl

theorem defaultTilingStrategy_eq : defaultTilingStrategy = TilingStrategy.block 1 := rfl

theorem tile_size_nonneg (t : Tile) : t.size ≥ 0 := Nat.zero_le t.size

theorem tile_offset_nonneg (t : Tile) : t.offset ≥ 0 := Nat.zero_le t.offset

theorem tilingStrategy_cases (s : TilingStrategy) :
  match s with
  | .block _ => True
  | .strip _ => True
  | .cyclic _ => True := by cases s <;> simp

end Morph.Specs.BackendTiling
