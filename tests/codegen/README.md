# Stage B codegen corpus

Fixtures for the Cranelift path (`morph build --codegen=cranelift`, stage B item
B6) and the input contract for the native driver (item B7) and its value
differential (item B8). Everything here is checked against the **Lean** binary
today; nothing needs `cargo`.

```bash
lake build morph                          # .lake/build/bin/morph
tests/codegen/check.sh [morph_bin]
```

## What the harness checks

For every row of `manifest.tsv`:

1. `morph run <file>` exits 0 and prints the recorded value — this is the value a
   native run of the artifact must reproduce (B8's oracle is Lean, not the Rust
   pipeline, so the recorded column *is* the expectation);
2. `morph build --codegen=cranelift <file>` exits 0 and writes `<stem>.clif`
   next to the input;
3. the artifact never contains `return %v0`. Register 0 is the unit prologue's
   destination and is never defined in the text, so a return of `%v0` is not
   CLIF (loop 151).

For every row of `rejects.tsv`, `morph build` exits 1, prints exactly the
recorded message on stderr, and writes no artifact.

## Why these programs are in the accepted set

They exercise the whole encodable operator set on integers: literals, `+`, `-`,
`*`, nested calls and parenthesization, a negative result, a result above 32
bits (1e9, so a truncating backend shows up), and a longer binding chain where
register numbers grow. Values were measured from `morph run` and pasted, not
predicted.

## Why the rejects are rejects

Each row is a different gate, and the messages differ on purpose:

| case | gate | why |
| --- | --- | --- |
| `unit_value.hum`, `empty.hum` | emitter | value is unit; the function is `-> i64` and CLIF has no unit |
| `boolean_value.hum` | emitter | value is a bool; `icmp` produces i8 and there is no widening in the modelled subset |
| `division.hum` | encoder | `div`/`mod` semantics (truncation, division by zero) have no agreement lemma yet |
| `unary_minus.hum` | MIR fragment | the surface parses and evaluates it, but lowering does not produce the straight-line fragment |
| `control_flow.hum` | HIR fragment | `match` with arms is outside stage A's straight-line fragment |
| `parse_error.hum` | parser | ordinary syntax error, reported by the parser |

The boolean case is the conservative end of a deliberate choice: the emitter
refuses *any* body containing a truth-valued instruction, so `let c = a < b; 42`
is refused even though its value is an integer. The alternative — a per-register
type pass — is what would make that program printable; until then the refusal is
sound and the corpus records it as such.

## Adding cases

1. Add the file under `corpus/` or `rejects/`.
2. Measure the expectation (`morph run`, or the exact `build` stderr) rather than
   guessing it.
3. Add the row. A mismatch fails the run; if a behavior change is intended, say
   why in the commit message.
