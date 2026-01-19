/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0

import Morph.Specs.GLOSSARY
import Morph.Specs.GLOSSARY.Spec

/-!
# Backend Tiling Lemmas

This module provides additional mathematical lemmas for backend tiling theory.

## Overview

The Backend Tiling Lemmas module formalizes:
- Additional tiling properties
- Tile scheduling algorithms
- Tile graph construction
- Dependency resolution strategies

## Key Concepts

- Tile: Represents a backend code generation unit
- TileKind: Represents type of tile (function, data, control)
- TileEdge: Represents a dependency between tiles
- TileGraph: Represents a complete tiling structure
- TileSchedule: Represents a valid tiling schedule

-!
namespace Morph.Specs.BackendTiling

/-! BT-LEM-001: Tile graph well-formedness implies topological sort exists -/
theorem wellFormedImpliesTopologicalSort :
    forall (graph : TileGraph),
      isWellFormed graph ->
        exists (schedule : TileSchedule),
          isValidTileSchedule schedule graph /
          schedule.isTopological := by
  intro graph hwf
  let schedule : TileSchedule :=
    { tiles := graph.tiles, isTopological := true, isMinimal := false }
  constructor
  · exact hwf
  · intro hvalid
  unfold isValidTileSchedule at hvalid
  constructor
  · rfl
  · intro hdeps
  intro tile edge hidx
  cases hidx
  case some => intro _ => rfl
  case none => intro hnone
    unfold dependenciesSatisfied at hnone
    intro htile
    unfold dependenciesSatisfied
    intro htile2
    have hcont : graph.tiles.contains htile := by
      unfold isWellFormed at hwf
      cases hwf
      case false => intro _ => contradiction hwf
      case true =>
        intro hnodes
        unfold isWellFormed at hnodes
        cases hnodes
        case false => intro _ => contradiction hnodes
        case true =>
          intro hall
          exact hall
    have hcont2 : graph.tiles.contains htile2 := by
      unfold isWellFormed at hwf
      cases hwf
      case false => intro _ => contradiction hwf
      case true =>
        intro hnodes2
        unfold isWellFormed at hnodes2
        cases hnodes2
        case false => intro _ => contradiction hnodes2
        case true =>
          intro hall2
          exact hall2
    constructor
  · exact hcont
  · exact hcont2
end Morph.Specs.BackendTiling
