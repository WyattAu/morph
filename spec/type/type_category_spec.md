# Category Theoretic Type Specification

- `File:* type/type_category_spec.md
- `Version:* 1.0.0
- `Context:* Layer 2 (Type Checker)
- `Formalism:* Category Theory

## 1. The Category of Types ($\mathcal{C}_{Morph}$)

Morph types form a Category where:

- **Objects ($Obj$):* Concrete Types (`i32`, `User`, `List<u8>`).
- **Morphisms ($Hom$):* Pure Functions $f: A \rightarrow B$.
- **Composition:* The Pipe Operator `|>` is the composition operator $\circ$.
  $$ (f \circ g)(x) \equiv x \ |> \ g \ |> \ f $$

### 1.1 The Unit Object

The type `void` is the terminal object $1$.

- For any object $A$, there exists a unique morphism $!_A: A \rightarrow 1$ (Discard).

### 1.2 Product Objects (Structs)

A `type` struct $T = \{a: A, b: B\}$ is the Categorical Product $A \times B$.

- Projections: $\pi_1: T \rightarrow A$ and $\pi_2: T \rightarrow B$ correspond to field accessors.

### 1.3 Coproduct Objects (Enums)

A `type` enum $E = A \ | \ B$ is the Categorical Coproduct $A + B$.

- Injections: $in_1: A \rightarrow E$ and $in_2: B \rightarrow E$ correspond to variant constructors.

## 2. Functors and Generics

Generic types are **Endofunctors** $F: \mathcal{C} \rightarrow \mathcal{C}$.

### 2.1 The `List` Functor

- Maps Object $A$ to Object $List<A>$.
- Maps Morphism $f: A \rightarrow B$ to $map(f): List<A> \rightarrow List<B>$.

### 2.2 The `Option` Functor

- Maps Object $A$ to Object $A?$.
- **Natural Transformation:* There exists a natural transformation $\eta: Id \rightarrow Option$ defined by `Some(x)`. This formalizes "Null Safety" as lifting a value into the Functor context.

## 3. Subcategories of Capabilities

To model memory safety, we partition $\mathcal{C}_{Morph}$ into subcategories based on Capabilities.

- $\mathcal{C}_{val}$: The subcategory of Immutable, Shareable types.
- $\mathcal{C}_{iso}$: The subcategory of Unique, Linear types.
- **Linearity Constraint:* In $\mathcal{C}_{iso}$, morphisms consume their domain.
  $$ f: A\_{iso} \rightarrow B \implies A \text{ is moved} $$
