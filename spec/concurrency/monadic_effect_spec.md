# Monadic Effect Specification

- `File:* concurrency/monadic_effect_spec.md
- `Version:* 1.0.0
- `Context:* Layer 2 (Semantics) & Layer 4 (Infrastructure)
- `Formalism:* Monads, Kleisli Categories

## 1. The Effect Monad ($\mathcal{M}$)

The Effect System is formalized as a Monad $(M, \eta, \mu)$ handling side effects.

### 1.1 Definition

- **Type Constructor:* $M_E: \text{Type} \rightarrow \text{Type}$ where $E$ is the Effect Set `{IO, Net, ...}`.
- **Unit ($\eta$):* $\eta: A \rightarrow M_{\emptyset} A$
  - Lifts a pure value into a pure effect context.
- **Bind ($>>=$):* $M_{E1} A \rightarrow (A \rightarrow M_{E2} B) \rightarrow M_{E1 \cup E2} B$
  - Sequences two effectful computations, accumulating the Effect Set (Union).

## 2. Effect Linearization (The "Do" Notation)

Morph's block syntax `{ s1; s2; }` is syntactic sugar for Monadic Binding.

$$ \{ x := \text{expr1}; \text{expr2} \} \equiv \text{expr1} >>= (\lambda x \rightarrow \text{expr2}) $$

### 2.1 Reordering Constraints

Given two statements $S_1 :: M_{E1}()$ and $S_2 :: M_{E2}()$:

- If $E1 \neq \emptyset$ and $E2 \neq \emptyset$ (both are impure), the Compiler **MUST NOT** reorder them.
- Mathematically, the Kleisli composition is non-commutative:
  $$ f \diamond g \neq g \diamond f $$

## 3. The `Result` Monad (Error Handling)

The `Result<T, E>` type acts as the standard Error Monad.

### 3.1 The Propagation Operator (`?`)

The `?` operator is the **Bind** operation restricted to the Failure path.

- Formal definition of `x?`:
  $$ \text{match } x \ \{ \ Ok(v) \rightarrow v, \ Err(e) \rightarrow \text{return } Err(e) \ \} $$
- This satisfies the Monad Laws (Left Identity, Right Identity, Associativity), ensuring that error handling logic is mathematically consistent and optimizable.

- -

### Implementation Note

By defining these structures, we enable the **Auto-Fuzzer** and **LLM** to reason as follows:

- "This function returns `M_IO`. I cannot call it from a function returning `M_Pure` because there is no geometric morphism from the Monad back to the Identity (Unsafe Extraction is banned)."
- "I need to refactor this AST. Since $G_{AST}$ is a Merkle DAG, if I change this leaf, I must update the hash of the root."

These files should be added to the repository immediately.
