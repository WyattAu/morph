# Differential testing: Lean `morph` vs Rust `morph`

Two `morph` implementations live in this repo: the verified Lean pipeline
(`Morph/`, total parser + evaluator) and the Rust compiler (`cli/` +
`compiler/` + `runtime/`). This harness locks their *accept/reject behavior*
to a manifest so divergence is visible and intentional.

## What it checks today: verdicts, not values

Two facts force verdict-only comparison for now:

1. **Disjoint top levels.** Lean programs are statements/expressions
   (`let`, `while`, `if`, `match`/`fix`, bare expressions); Rust files are
   items (`fn` with type signatures, `type`, `const`, `actor`, ...). The
   file-level intersect is empty.
2. **The Rust `run` does not execute.** It reports "MorphVM interpreter not
   yet integrated" on successful compilation, so there are no Rust values
   to compare against Lean's.

Each manifest row records the expected verdict per side (`ok` = exit 0).
If a case ever becomes ok/ok (shared surface + Rust interpreter), extend
`diff.sh` with value normalization instead of exit codes.

## The divergence map (verified 2026-10-30)

| Construct | Lean | Rust | Notes |
|---|---|---|---|
| `fn name(args: ty) -> ty { }` | reject | accept | Rust items; Lean has untyped `fn x -> e` lambdas only |
| `fix n { 0 => .., _ => .. }` (no `case`, no parens) | reject | accept | Rust match shape; Lean needs `case` + parens (expr) or bare scrutinee + `{ }` arms (stmt) |
| `fix (s) { case .. }` / `match s { case .. => { .. } }` | accept | reject | Lean shapes; Rust wants `fix` without `case` |
| `type` / `actor` / `const` / `use` | reject | accept | Rust-only items |
| `let`/`while`/`if`-statements, `for` exprs, `??`, `\|>`, unary `-` | accept | reject (at file level) | Lean-only surface (the operators exist *inside* Rust expressions but files must be items) |

## Running

```bash
cargo build -p morph        # Rust binary -> ./target/debug/morph
lake build morph            # Lean binary  -> .lake/build/bin/morph
tests/differential/diff.sh [lean_bin] [rust_bin]
```

## Adding cases

1. Add the `.morph` file under `corpus/`.
2. Append one manifest row: `path lean_cmd lean_want rust_cmd rust_want`.
3. Run `diff.sh`. A mismatch fails the run — update the manifest only if the
   behavior change is intended (e.g. surface convergence), and say why in
   the commit message.

Note: the `../../cli/tests/fixtures/` rows reference the Rust suite directly
on purpose — if upstream fixtures change shape, the harness fails loudly and
forces a manifest review instead of going silently stale.
