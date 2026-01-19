-- Copyright 2024-2025 The Morph Project Authors
-- SPDX-License-Identifier: Apache-2.0

import Morph.Core
import Morph.Syntax
import Morph.Memory
import Morph.Specs.GLOSSARY.Lemmas

-- Directed graph type 
abbrev DirectedGraph (α : Type) := α → α → Prop

-- Path type from GLOSSARY 
abbrev Path {α : Type} (G : DirectedGraph α) := α → α → Prop

-- Ordering type 
inductive Ordering where
  | lt : Ordering
  | eq : Ordering
  | gt : Ordering
  deriving Repr

/-
-/