# Morph Lexical Structure & Syntax Specification (LS3)

- `System:* Morph Programming Language
- `Version:* 1.0.0
- `Context:* Layer 2 (Compilation Phase)
- `Formalism:* EBNF (Extended Backus-Naur Form)

- -

## 1. Source Representation

### 1.1 Character Encoding

- **Standard:* Source files MUST be encoded in **UTF-8**.
- **Normalization:* All identifiers are normalized to **NFC** (Normalization Form C) prior to hashing.
- **Case Sensitivity:* The language is **Case-Sensitive**.

### 1.2 Whitespace & Delimiters

- **Structure:* Morph uses explicit delimiters (`{`, `}`, `;`) for scoping.
- **Ignored Whitespace:* Spaces, tabs, and newlines are insignificant except when separating alphanumeric tokens.
- **Minification:* The `min` dialect strips all non-functional whitespace.
  - _Example:_ `fn main(){x:=1;ret x;}`

### 1.3 Comments

- **Line:* `// ...` (Terminated by newline).
- **Block:* `/* ... */` (Nestable).
- **Semantic Doc:* `/// ...`
  - **Behavior:* Extracted by the compiler for Vector Embedding (RAG).

- -

## 2. Keywords & Identifiers

### 2.1 Optimized Keyword Set

To maximize Information Density per Token, Morph reserves a compressed set of **22 Keywords**. All other tokens are identifiers.

| Keyword          | Context     | Semantic Meaning                 |
| :--------------- | :---------- | :------------------------------- |
| `fn`             | Declaration | Function definition.             |
| `ret`            | Control     | Return value.                    |
| `use`            | Module      | Import dependency.               |
| `pub`            | Visibility  | Public export.                   |
| `mut`            | Storage     | Mutable binding.                 |
| `type`           | Data        | ADT / Struct / Enum definition.  |
| `act`            | Concurrency | Actor (`logic`) definition.      |
| `state`          | Actor       | Internal mutable state.          |
| `event`          | Actor       | Public message interface.        |
| `on`             | Actor       | Event handler.                   |
| `spawn`          | Concurrency | Task creation.                   |
| `async`          | Concurrency | Dataflow modifier.               |
| `fix`            | Control     | Pattern matching (Match/Fixate). |
| `if`, `else`     | Control     | Conditional branching.           |
| `loop`           | Control     | General iteration.               |
| `defer`          | Resource    | Scope-exit cleanup.              |
| `const`          | Constant    | Compile-time constant.           |
| `void`           | Type        | Unit type.                       |
| `in`, `is`, `as` | Operators   | Membership, Type Check, Cast.    |

### 2.2 Capability Sigils

Single-character prefixes used to denote Memory Capabilities (Ownership).

| Sigil | Name    | Meaning                     | Usage          |
| :---- | :------ | :-------------------------- | :------------- |
| `^`   | **Iso** | Isolated (Unique/Move-Only) | `img: ^Image`  |
| `#`   | **Val** | Value (Shared/Immutable)    | `cfg: #Config` |
| `&`   | **Ref** | Reference (Local/Mutable)   | `buf: &Buffer` |
| `?`   | **Opt** | Optional (Nullable)         | `user: User?`  |

- -

## 3. Literals & Constants

### 3.1 Numeric Literals

- **Integers:* `123`, `0xFF` (Hex), `0b101` (Binary).
- **Floats:* `1.0`, `1e-10`.
- **Optimization Hole:* `??`
  - **Semantics:* Represents a value to be determined by Compiler's Search Engine.
  - **Usage:* `const UNROLL = ??;`

### 3.2 String Literals

#### 3.2.1 Standard String (`"..."`)

- **Syntax:* Double-quoted sequence.
- **Escapes:* Supports `\n`, `\t`, `\"`, `\u{...}`.
- **Usage:* UI labels, simple identifiers.

#### 3.2.2 Fenced Code String (` ``` `)

- **Syntax:* Markdown-style fenced blocks.
- **Delimiter:* A sequence of 3 or more backticks.
- **Termination:* The string ends **only** when a matching sequence of backticks is encountered.
- **Tag:* An optional identifier immediately following the opening fence is treated as a Semantic Hint (e.g., `json`, `sql`) for Compiler/IDE but ignored at runtime.
- **Behavior:* All content inside is Raw (No escapes).
- **Rationale:* Aligns perfectly with LLM training data (Markdown). Explicit and robust against internal quote hallucination.

- `Example:*

`````rust
// Agent code
val query := ```sql
    SELECT * FROM "Users" WHERE id = '5'
```;

val complex := ````text
    This string contains triple backticks: ```
    but it doesn't close yet.
````;
`````

- -

## 4. Operators & Expressions

### 4.1 The Walrus Operator (`:=`)

- **Purpose:* Inferred Type Declaration. Replaces `let`.
- **Syntax:* `x := 10;`
- **Semantics:* Declares `x`, infers type `int`, assigns `10`.

### 4.2 The Pipe Operator (`|>`)

- **Purpose:* Linear Data Transformation.
- **Syntax:* `x |> f(y)` desugars to `f(x, y)`.
- **Semantics:* Enforces left-to-right token generation flow.

### 4.3 Operator Precedence

| Level | Operators         | Description                    |
| :---- | :---------------- | :----------------------------- | -------- |
| 1     | `.` `()` `[]` `?` | Access, Call, Index, Propagate |
| 2     | `^` `!`           | Bitwise/Logical Not            |
| 3     | `*` `/` `%`       | Multiplicative                 |
| 4     | `+` `-`           | Additive                       |
| 5     | `                 | >`                             | Pipeline |
| 6     | `==` `!=` `<`     | Relational                     |
| 7     | `:=` `=`          | Declaration / Assignment       |

- -

## 5. Formal Grammar (EBNF)

### 5.1 Compilation Unit

```ebnf
CompilationUnit ::= { UseDecl } { TopLevelDecl }
UseDecl         ::= 'use' Identifier [ 'as' Identifier ] ';'
TopLevelDecl    ::= FuncDecl | TypeDecl | ActDecl | ConstDecl
```

### 5.2 Declarations

```ebnf
/* Declaration of Constants and Variables */
ConstDecl   ::= 'const' Identifier '=' ( Expr | '??' ) ';'
VarDecl     ::= Identifier ':=' Expr ';'              (* Inferred *)
              | Identifier ':' Type '=' Expr ';'      (* Explicit *)

/* Function Definition */
FuncDecl    ::= 'fn' Identifier [Generics] Params [ '->' Type ] Block

/* Type (ADT) Definition */
TypeDecl    ::= 'type' Identifier [Generics] '=' TypeBody ';'
TypeBody    ::= '{' FieldList '}'                     (* Product/Struct *)
              | Variant { '|' Variant }               (* Sum/Enum *)
```

### 5.3 Actor (Logic) Definition

```ebnf
ActDecl     ::= 'act' Identifier '{' { StateBlock | EventDecl | HandlerDecl } '}'
StateBlock  ::= 'state' '{' { Identifier ':' Type [ '=' Expr ] ';' } '}'
EventDecl   ::= 'event' Identifier Params ';'
HandlerDecl ::= 'on' Identifier Params Block
```

### 5.4 Control Flow

```ebnf
Statement   ::= VarDecl
              | 'async' 'let' Identifier '=' Expr ';' (* Dataflow *)
              | 'ret' [Expr] ';'
              | 'fix' Expr '{' { MatchArm } '}'       (* Pattern Match *)
              | 'if' Expr Block [ 'else' Block ]
              | 'loop' Block
              | 'defer' Block
              | Expr ';'
```

### 5.5 Literals

````ebnf
Literal     ::= Integer | Float | String | FencedString | '??'

/* Fenced String Logic */
FencedString ::= Backticks [Tag] Newline AnyChar* Newline Backticks
Backticks    ::= '```' { '`' }
````

- -

## 6. Ambiguity Resolution

### 6.1 The "Function vs. Struct" Disambiguation

- **Ambiguity:* `Name { ... }` could be a block or a struct init.
- **Resolution:*
  - In an `Expr` position, `Name { ... }` is a **Struct Initialization**.
  - In a `Statement` position, `Name { ... }` is invalid (Morph does not support labeled blocks).
  - Blocks are only valid as children of Control Flow keywords (`if`, `loop`, `fn`).

### 6.2 The "Dangling Else"

- **Resolution:* Impossible. Morph requires braces `{ ... }` for all `if` bodies.
  - _Invalid:_ `if (x) ret;`
  - _Valid:_ `if (x) { ret; }`

### 6.3 The "Walrus" Scope

- **Rule:* `:=` introduces a new variable in the current scope.
- **Shadowing:* Shadowing is **Allowed** but triggers a compiler warning in `hum` mode.
  ```rust
  x := 1;
  {
      x := 2; // Valid, new 'x'
  }
  ```

- -

## 7. Examples

### 7.1 Agent-Optimized Syntax (`min`)

```rust
use net;use std;
fn fetch(u:str)->^Data{
  req:=net.get(u);
  res:=req.send()?;
  ret res.body;
}
act Downloader{
  state{cache:Map<str,^Data>;}
  on Get(u:str){
    d:=fetch(u);
    cache.insert(u,d);
  }
}
```

### 7.2 Human-Projected View (`hum`)

_Generated by IDE, not stored._

```rust
use net;
use std;

fn fetch(u: str) -> ^Data {
    req := net.get(u);
    res := req.send()?;
    ret res.body;
}

act Downloader {
    state {
        cache: Map<str, ^Data>;
    }

    on Get(u: str) {
        d := fetch(u);
        cache.insert(u, d);
    }
}
```
