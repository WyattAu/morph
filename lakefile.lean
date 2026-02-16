import Lake
open Lake DSL

package morph {
  -- Package configuration for Morph verification project
  -- Follows ADR-010: Lean 4 Version and Lake Package Management
  moreLeanArgs := #["-DcheckBinderAnnotations=false"]
}

-- Main Morph library
lean_lib Morph {
  globs := #[.submodules `Morph]
}

-- Morph.Tests library for test infrastructure
lean_lib Morph.Tests {
  globs := #[.submodules `Morph.Tests]
}

-- Test executable - main test driver
-- Follows ADR-009: Testing Infrastructure
lean_exe morph_test {
  root := `Morph.Tests.Main
}

-- Test targets by domain for selective testing
lean_exe morph_test_basic {
  root := `Morph.Tests.Basic
}

lean_exe morph_test_core {
  root := `Morph.Tests.Core
}

lean_exe morph_test_executable {
  root := `Morph.Tests.Executable
}

lean_exe morph_test_memory {
  root := `Morph.Tests.Memory
}

lean_exe morph_test_semantics {
  root := `Morph.Tests.Semantics
}

lean_exe morph_test_typing {
  root := `Morph.Tests.Typing
}

lean_exe morph_test_ast {
  root := `Morph.Tests.AST
}

-- Dependencies - using v4.10.0-compatible versions
require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "a719ba5c3115d47b68bf0497a9dd1bcbb21ea663"
require batteries from git "https://github.com/leanprover-community/batteries" @ "0f3e143dffdc3a591662f3401ce1d7a3405227c0"
require aesop from git "https://github.com/JLimperg/aesop" @ "209712c78b16c795453b6da7f7adbda4589a8f21"
require importGraph from git "https://github.com/leanprover-community/import-graph" @ "543725b3bfed792097fc134adca628406f6145f5"
