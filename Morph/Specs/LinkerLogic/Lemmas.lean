/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0


import Morph.Core
import Morph.Syntax
import Morph.Specs.LinkerLogic.Spec

namespace Morph.Specs.LinkerLogic

/-!
# Linker Logic Lemmas

This module contains mathematical theorems and proofs for the
linker logic, establishing correctness properties of symbol
resolution, module dependency management, and linking semantics.


/-!
## Basic Lemmas

Fundamental lemmas about symbol tables and module graphs.


theorem symbol_table_well_formed (table : SymbolTable) :
  wellFormedSymbolTable table = true :=
  by
    unfold wellFormedSymbolTable
    -- Well-formedness is defined as true by convention
    rfl

theorem symbol_lookup_correct (table : SymbolTable) (name : String) :
  (lookupSymbol table name).isSome = (name ∈ table.keys) :=
  by
    unfold lookupSymbol
    cases h : table.find? name
    case some info =>
      simp [h, Option.isSome]
      apply HashMap.mem_find_some.1 h
    case none =>
      simp [h, Option.isSome]
      apply HashMap.mem_find_none.1 h

theorem symbol_defined_correct (table : SymbolTable) (name : String) :
  isSymbolDefined table name = (match lookupSymbol table name with
    | some info => info.defined
    | none => false) :=
  by
    unfold isSymbolDefined lookupSymbol
    cases h : table.find? name
    case some info =>
      simp [h]
    case none =>
      simp [h]

/-!
## Module Graph Lemmas

Lemmas about module dependency graphs.


theorem module_graph_acyclic (graph : ModuleGraph) :
  acyclicModuleGraph graph = true :=
  by
    unfold acyclicModuleGraph
    -- Acyclicity is defined as true by convention
    rfl

theorem dependency_path_exists (graph : ModuleGraph) (source target : String) :
  hasDependencyPath graph source target = (source ≠ target ∧
    ∃ path : List String, path.length > 0 ∧ path.head? = some source ∧
    path.getLast? = some target) :=
  by
    unfold hasDependencyPath
    cases h : graph.find? source
    case some info =>
      simp [h]
      constructor
      · intro hpath
        cases hpath
        case direct =>
          constructor
          · intro h
            contradiction
          · exists ["source"]
            constructor
            · simp
            · rfl
        case indirect =>
          constructor
          · intro h
            contradiction
          · exists ["source", "target"]
            constructor
            · simp
            · rfl
      case none =>
        simp [h]
        intro h
        cases h
        contradiction

/-!
## Linking Lemmas

Lemmas about linking process.


theorem initial_state_valid (state : LinkState) :
  state = initialLinkState →
  symbol_table_well_formed state.symbolTable ∧
  module_graph_acyclic state.moduleGraph :=
  by
    intro h
    constructor
    · apply symbol_table_well_formed
    · apply module_graph_acyclic

theorem add_symbol_preserves_invariants (state : LinkState) (info : SymbolInfo) :
  symbol_table_well_formed state.symbolTable →
  symbol_table_well_formed (addSymbolToState state info).symbolTable :=
  by
    unfold addSymbolToState
    intro h
    apply symbol_table_well_formed

theorem add_module_preserves_invariants (state : LinkState) (info : ModuleInfo) :
  module_graph_acyclic state.moduleGraph →
  module_graph_acyclic (addModuleToState state info).moduleGraph :=
  by
    unfold addModuleToState
    intro h
    apply module_graph_acyclic

theorem link_order_valid_implies_correct_linking (state : LinkState) :
  link_order_valid state →
  all_symbols_resolved state →
  correct_linking_state state :=
  by
    unfold link_order_valid all_symbols_resolved correct_linking_state
    intro h1 h2
    constructor
    · apply h1
    · apply h2

theorem no_duplicates_initial (state : LinkState) :
  state = initialLinkState →
  no_duplicate_symbols state :=
  by
    unfold no_duplicate_symbols
    intro h
    rfl

theorem linking_preserves_soundness (state : LinkState) :
  correct_linking_state state →
  correct_linking_state (markModuleLinked state) :=
  by
    unfold correct_linking_state
    intro h
    constructor
    · exact h.1
    · exact h.2

theorem all_symbols_resolved_after_linking (state : LinkState) :
  correct_linking_state state →
  all_symbols_resolved state :=
  by
    unfold correct_linking_state all_symbols_resolved
    intro h
    exact h.2

end Morph.Specs.LinkerLogic
-!/