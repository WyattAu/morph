# Licensing & Compliance Specification (LCS)

**System:** Morph Ecosystem
**Version:** 1.0.0
**Context:** Layer 1 (Infrastructure) & Layer 5 (Agent Interface)

## 1. Metadata Standards

### 1.1 SPDX Identifiers

- **REQ-LIC-01:** Every `morph.pkg` manifest MUST contain a `license` field using a valid **SPDX Identifier** (e.g., `"MIT"`, `"Apache-2.0"`, `"UNLICENSED"`).
- **REQ-LIC-02:** The Registry SHALL reject package publications with invalid or ambiguous SPDX identifiers.
- **REQ-LIC-03:** For multi-licensed packages, complex expressions are supported (e.g., `"MIT OR Apache-2.0"`).

## 2. Policy Enforcement (The Firewall)

### 2.1 The License Policy Configuration

The `morph.workspace` or root `morph.pkg` supports a compliance configuration block.

```toml
[compliance]
# Strategy: "allowlist" (Default for Enterprise) or "open"
strategy = "allowlist"

# Allowed Licenses (Permissive Stack)
allow = ["MIT", "Apache-2.0", "BSD-3-Clause", "ISC"]

# Explicitly Denied (Copyleft Stack)
deny = ["GPL-*", "AGPL-*", "WTFPL"]

# Action on Violation: "error" (Build Fails) or "warn"
on_violation = "error"
```

### 2.2 Build-Time Validation

- **REQ-LIC-04:** During the **Graph Resolution Phase**, the MBS MUST walk the dependency tree.
- **REQ-LIC-05:** If a dependency's license violates the root policy, the build SHALL fail immediately with a **Compliance Error**: _"Package 'super-algo' (GPL-3.0) violates policy 'allowlist'. Implementation rejected."_

## 3. Agent-Side Filtering (MCP)

### 3.1 Context-Aware Discovery

- **REQ-LIC-06:** When the Agent queries the Registry (`query_symbol` or `search_packages`), the MCP server MUST cross-reference the results against the project's `[compliance]` policy.
- **REQ-LIC-07:** Incompatible packages MUST be filtered out of the search results or clearly marked as `[PROHIBITED]`.
- **Reasoning:** Prevents the Agent from hallucinating that it can use a library, only to be blocked by the compiler later.

## 4. The `morph audit` Command

### 4.1 Bill of Materials (SBOM) Generation

- **REQ-LIC-08:** The toolchain SHALL support `morph audit --sbom`.
- **Output:** Generates a standard SBOM (Software Bill of Materials) in JSON/SPDX format, listing every dependency, its version, hash, and license.
- **Usage:** Critical for enterprise adoption (supply chain security).

### 4.2 Legal Notice Generation

- **REQ-LIC-09:** The toolchain SHALL support `morph audit --credits`.
- **Output:** Generates a `CREDITS.txt` file aggregating the license texts of all statically linked dependencies (required by Apache-2.0/MIT attribution clauses).

---

### Summary of the "Best Practice" Approach

| Feature        | Your Proposal (Display)         | **Morph Solution (Enforce)**                        |
| :------------- | :------------------------------ | :-------------------------------------------------- |
| **Visibility** | "Show me the licenses."         | **SBOM Generation** (Standardized).                 |
| **Prevention** | Developer checks list manually. | **Policy Engine** (Auto-Fail build).                |
| **AI Safety**  | Agent imports blindly.          | **MCP Filtering** (Agent can't see forbidden libs). |
| **Scope**      | Just the package list.          | **Viral Graph Analysis** (GPL propagation).         |

This turns Licensing from a "Legal Afterthought" into a "Compile-Time Constraint," effectively solving the risk of AI-generated IP contamination.
