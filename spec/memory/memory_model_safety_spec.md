# Memory Model Safety Specification

* File:* `memory/memory_model_safety_spec.md`
* Version:* 1.0.0
* Context:* Runtime — memory model
* Formalism:* Block allocation, bounds-checked access
* Status:* Active
* Machine-checked in:* `Morph/Specs/MemoryModel/`

---

## 1. Purpose and Scope

This specification replaces the MemoryModel module's **seven** vacuous
advertisements with real statements, and proves them.

## 2. What was there

| Name | Was | Now |
|---|---|---|
| `isMemorySafe` | `True` — vacuous for every memory | every block's data has exactly the size it claims |
| `spec_memory_allocation` | `True` | allocation returns a fresh id, bumps the counter, and yields a well-formed block |
| `spec_memory_deallocation` | `True` | deallocation removes the block |
| `spec_memory_access` | `True` | access is bounds-checked: a read past the end yields nothing; a write past the end leaves the memory alone |
| `memory_safety_invariant` | `True` | still `True` — recorded as vacuous, not claimed |
| `allocation_preserves_safety` | `True` | still `True` — recorded as vacuous, not claimed |
| `deallocation_preserves_safety` | `True` | still `True` — recorded as vacuous, not claimed |
| `empty_memory_well_formed` | `True` | still `True` — recorded as vacuous, not claimed |

And the one theorem that *looked* like a real property was a tautology:

```lean
theorem read_preserves_memory (mem : Memory) (id : Core.BlockId) (offset : Nat) :
    readByte mem id offset = readByte mem id offset := by rfl
```

## 3. Requirements discharged

| Theorem | Statement |
|---|---|
| `allocation_spec` | allocation is fresh, bumps the id counter, and produces a well-formed block |
| `deallocation_spec` | deallocation removes the block |
| `readByte_out_of_bounds` | a read past the end of a block yields `none` |
| `writeByte_out_of_bounds` | a write past the end of a block leaves the memory alone |
| `access_spec` | the specification's `spec_memory_access`, in both halves |

## 4. A core-level finding: `BlockId`'s `BEq` was not lawful

Proving the deallocation property needed `BlockId`'s equality to be *decidable
and sound*. It was neither: `Morph/Core.lean` derived `BEq` for `BlockId`
**without** a `LawfulBEq` instance, so every `==` on a block id in the compiler
was unprovably sound — the same defect loop 12 found for `Typ`, but at the level
of the core type.

Fixed by deriving `DecidableEq` for `BlockId` and by comparing ids with
`decide` in the memory model, so the properties above are provable *and* the
comparisons are lawful. The same treatment is still owed for the other `BEq`
types in `Morph/Core.lean` that lack a `LawfulBEq` instance.

## 5. Scope: explicit non-claims

1. **Four stubs remain `True`** (`memory_safety_invariant`,
   `allocation_preserves_safety`, `deallocation_preserves_safety`,
   `empty_memory_well_formed`). They are recorded here as vacuous rather than
   silently left in place; two of them are proved in their honest form in
   `Lemmas.lean` (`empty_memory_well_formed'`, `allocation_preserves_safety'`).
2. **No refcount semantics.** `incrementRefCount`/`decrementRefCount` are
   unproved; the reference-counting discipline is `Morph/Specs/MemoryBounds`
   (loop 2), which works at the affine-type level rather than this level.
3. **No aliasing or use-after-free reasoning.** The properties here are
   bounds checks, not lifetime safety.
4. **Not connected to `Morph/Memory.lean`** — the runtime memory module is a
   separate implementation, and this specification is about the *model*.

## 6. Traceability

| Artifact | Location |
|---|---|
| Corrected properties | `Morph/Specs/MemoryModel/Spec.lean` |
| The proofs | `Morph/Specs/MemoryModel/Lemmas.lean` |
| The vacuity, now visible | `Morph/Specs/MemoryModel/Examples.lean` |
| Decidable equality for `BlockId` | `Morph/Core.lean` |
