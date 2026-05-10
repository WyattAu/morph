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

-- Dependencies - using v4.27.0-compatible versions
require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "a3a10db0e9d66acbebf76c5e6a135066525ac900"
require batteries from git "https://github.com/leanprover-community/batteries" @ "b25b36a7caf8e237e7d1e6121543078a06777c8a"
require aesop from git "https://github.com/JLimperg/aesop" @ "cb837cc26236ada03c81837bebe0acd9c70ced7d"
require importGraph from git "https://github.com/leanprover-community/import-graph" @ "8f497d55985a189cea8020d9dc51260af1e41ad2"
