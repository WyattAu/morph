# Diagnostic & Remediation Protocol (DRP)

**System:** Morph Ecosystem
**Version:** 1.0.0
**Context:** Layer 2 (Compiler) $\rightarrow$ Layer 5 (Agent Interface)

## 1. Philosophy: Errors as Data

In Morph, a compilation error is not a string to be printed to `stderr`. It is a **Structured Object** to be queried by the Agent. The Compiler acts as a **Static Analysis Server**.

## 2. The Diagnostic Schema

Every error or warning emitted by the MCP Server MUST adhere to this JSON schema.

```json
{
  "diagnostic_id": "UUID-v4",
  "code": "E0402",
  "severity": "Error", // Error, Warning, Hint
  "message": "Type Mismatch in Assignment",

  // 1. Precise Location (Canonical)
  "location": {
    "module_hash": "sha256:...",
    "node_id": "AST-1024",
    "span": { "start": 50, "end": 58 }
  },

  // 2. The Semantic Context (What the Agent needs to know)
  "context": {
    "expected_type": "morph.std.collections.List<i32>",
    "actual_type": "morph.std.primitives.i32",
    "enclosing_function": "process_data"
  },

  // 3. Related Information (Why this happened)
  "related": [
    {
      "node_id": "AST-900",
      "message": "Variable 'list' defined here as List<i32>"
    }
  ],

  // 4. Deterministic Remediation (The Fix)
  "suggested_fixes": [
    {
      "confidence": 0.95,
      "description": "Wrap the integer in a List constructor",
      "mutation": {
        "operation": "WRAP",
        "target_node": "AST-1024",
        "wrapper": "List::from([$NODE])"
      }
    }
  ]
}
```

## 3. Error Categories & Recovery

### 3.1 Syntax Errors (Parsing)

- **Behavior:** The parser attempts **Resilient Parsing**. It does not stop at the first error. It inserts "Error Nodes" into the AST so the Agent can see the rest of the file structure.
- **Agent View:** "I understood 99% of your file, but Node #55 is malformed. Here is the partial AST."

### 3.2 Semantic Errors (Type/Contract)

- **Behavior:** Occurs after AST generation.
- **DbC Integration:** If a `requires` contract fails (statically), the error points to the **Call Site**, but the `related` field points to the **Contract Definition**.
- **RAG Integration:** The `context` field includes a simplified signature of the expected type, fetched from the Vector DB.

### 3.3 Topology Errors (Build)

- **Behavior:** Circular dependencies or missing packages.
- **Remediation:** The `suggested_fixes` will include `"action": "install_package", "package": "std.net"`.

## 4. The `fix_it` Protocol

The MCP exposes a specific endpoint to apply these fixes.

### 4.1 `apply_fix(diagnostic_id, fix_index)`

- **Input:** The ID of the error and the index of the suggestion.
- **Process:**
  1.  Compiler retrieves the AST mutation strategy.
  2.  Compiler applies the patch to the In-Memory AST.
  3.  Compiler re-runs Semantic Analysis on the affected subgraph.
  4.  **Result:** Returns `success: true` or a new set of Diagnostics.
- **Why:** This allows the Agent to perform **"Blind Repair"**. It doesn't need to re-write the code text; it just approves the compiler's suggestion.

## 5. Requirements Traceability

| Feature               | Rationale                                                   | Requirement |
| :-------------------- | :---------------------------------------------------------- | :---------- |
| **Structured JSON**   | Agents parse JSON better than text logs.                    | REQ-MCP-02  |
| **AST Node IDs**      | Deterministic reference points (vs line numbers).           | REQ-3.1.2   |
| **Suggested Fixes**   | Turns debugging into a selection task, not a creative task. | REQ-7.2     |
| **Resilient Parsing** | Maximizes context even in broken code.                      | REQ-7.2     |

