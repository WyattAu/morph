# C8 call ABI: options memo for D-7

Status: options memo (S2). Decides nothing. D-7 is due end of S3; if
unanswered, the roadmap register's default holds: the refusal pins
stand, D-work proceeds unaffected (C8 is a leaf, not a spine).

## What D-7 must fix

The encoder refuses every call-bearing program (`instrEncode_call` in
`Morph/ClifLower.lean`, `encodeBlock_hasCall` / `encodeFunc_hasCall` in
`Morph/ClifCfgEncode.lean`, pins in `Morph/Tests/ClifCall.lean`), while
the models already execute single-level calls (`MIR.execFuncCall`,
`ClifTarget.runCallee`, `Proofs/Call/Evidence.lean`). To emit a real
CLIF `call`, the project must fix three things, and only these three:

1. **The value→CLIF-type mapping.** What a Morph `Typ` becomes in a
   declared signature: `intType`, `boolType`, `stringType`,
   `pointerType`, `unitType` (`Morph/Core.lean`, `Typ`).
2. **Who assigns locations.** Whether Morph pins registers/stack slots
   or declares signatures and lets Cranelift's isa assign them.
3. **The bool/unit representation at call boundaries.** Today the
   printed world is monomorphic `-> i64`: `allI64` refuses bodies with
   comparisons or boolean ops, and unit/bool-valued programs are refused
   (`Morph/ClifEmit.lean`). A call ABI must say what crosses when the
   value is not an integer.

Recursion is explicitly out of scope: `runCallee` runs callees through
the call-free `runInstrs`, so nested calls stall to `none` by fragment
design. Lifting that is a fragment extension, a separate decision.

## What the tree already commits to

- `Morph/Runtime.lean` (`marshal`, ~line 181) already publishes a
  value↔native table: int→i64, bool→i8 (0/1), string→NUL-terminated
  pointer, pointer→raw, unit→void. Any ABI that contradicts this table
  creates a second story the FFI layer must then bridge.
- `Morph/Runtime.lean` also carries `CallingConvention`
  (cdecl | stdcall | fastcall): x86-32 legacy names, meaningless for
  x86-64 SystemV or anything Cranelift lowers. Whatever D-7 decides,
  that enum needs revisiting; no option below keeps it as is.
- `Morph/ClifTarget.lean` (`Sig`, `bindCArgs`) binds by arity only;
  types are unchecked. The bridge lemma
  (`bindCallArgs_bindCArgs_agree`) proves the MIR and CLIF binders agree
  when formals name the signature. A typed ABI upgrades this lemma; an
  untyped ABI reuses it unchanged.
- The 22/22 codegen corpus passes under the `-> i64` world: the corpus
  is integer-only in practice, so no corpus case today forces the
  bool/unit question. The first bool-returning call will force it.

## Options

### A. Monomorphic i64

Every value crosses calls as `i64` (bool 0/1 widened, unit 0 or absent,
strings/pointers boxed later). Proof delta: near zero — the untyped
`Sig` and the bridge lemma are reused unchanged; only `call` emission
with an i64 signature is new. Cost: bakes a representation into the
ABI that contradicts the Runtime i8-bool story, and guarantees an ABI
break the day a string crosses a call. Fallback if S3 review finds the
proof cost of B too high for the quarter.

### B. Typed signatures from `Typ` (adopt the marshal table)

Each `Typ` maps to a CLIF type per the Runtime table
(int→i64, bool→i8/boolean, string→pointer, unit→void/absent result).
`Sig` becomes arity + types, `bindCArgs` checks both, the bridge lemma
upgrades to typed agreement, and the `allI64` conservative gate is
replaced by the type pass `ClifEmit.lean` already anticipates
("`lastDef` + a type per instruction"). Cost: the largest proof delta
of the viable options, but it unifies the C8 story with the already
committed FFI story instead of writing a second one. Recommended.

### C. Declare signatures, let Cranelift assign (combines with A or B)

Orthogonal to the type mapping: Morph declares per-function signatures
and emits plain `call`; register/stack assignment stays with
Cranelift's isa. Pinning locations Morph-side would duplicate the
backend's job and its proofs. Whichever of A/B wins, assignment is
delegated. Recommended in combination, not standalone.

### D. Morph-managed calling (stack/tags)

All arguments as tagged words on a Morph-managed stack; maximal control
for a future GC/closure representation. Cost: the largest proof burden
by far, and it breaks the additive small-step pattern (C1/C8 hedge)
that got calls modelled without moving anything proved. Revisit only
if a GC design arrives (Year 3+); not a Y1 option.

## Recommendation

**B + C**: typed signatures per the Runtime marshal table, declared
(signatures authored Morph-side, locations assigned Cranelift-side),
with the `CallingConvention` enum replaced by the actual target
convention. Fallback **A + C** if S3 review prices B out of the
quarter. The memo's test for either: the first bool-returning call in
the corpus must encode, run, and agree — that case is today's
`allI64`-refused shape, so it exercises exactly what D-7 adds.
