## 1. Philosophy: The "Textual Viewport"

An Agent cannot see pixels. If an Agent builds a UI, it needs a way to verify:

1.  **Topology:** Is "Submit" inside the "Form"?
2.  **Geometry:** Is the "Cancel" button overlapping the "OK" button?
3.  **State:** Did clicking "Login" actually change the screen to the Dashboard?

The SAP provides a **Computed Semantic Tree**—a snapshot of the UI _after_ layout calculation and rendering, serialized into a token-efficient JSON format.

## 2. The Semantic Node Schema

Every UI element (Widget) is serialized into a `SemanticNode` object.

```json
{
  "id": 102,
  "role": "button",        // ARIA-compatible roles (button, text, slider, container)
  "label": "Submit",       // The screen-reader text
  "value": null,           // Current value (for inputs)

  // 1. Computed Geometry (The Agent's "Eyes")
  "rect": { "x": 100, "y": 500, "w": 200, "h": 50 },
  "z_index": 5,

  // 2. Interaction State
  "flags": [
    "visible",             // Is it rendered?
    "clickable",           // Is there an onClick handler?
    "focused",             // Does it have keyboard focus?
    "occluded"             // Is it covered by another window?
  ],

  // 3. Hierarchy
  "children": [ ... ]
}
```

### 2.1 Role Taxonomy

Morph normalizes native widgets into generic roles to simplify Agent reasoning.

- `container`: Generic grouping (Row, Column, Div).
- `static_text`: Non-interactive labels.
- `interactive`: Buttons, links.
- `input`: Text fields, sliders, checkboxes.
- `modal`: Popups, dialogs (implies high Z-index).

---

## 3. The Protocol Interactions (MCP)

The Agent interacts with the SAP via specific MCP endpoints.

### 3.1 `get_ui_snapshot(scope_id)`

- **Request:** Agent asks for the current state of a Window or Component.
- **Process:**
  1.  Runtime forces a Layout Pass.
  2.  Runtime builds the Accessibility Tree.
  3.  Runtime performs **Occlusion Culling** (calculating if Node A covers Node B).
  4.  Runtime serializes to JSON.
- **Response:**
  ```json
  {
    "root": {
      "role": "window", "label": "Login Page",
      "children": [
        { "role": "input", "label": "Username", "rect": { ... } },
        { "role": "button", "label": "Log In", "flags": ["disabled"] }
      ]
    }
  }
  ```

### 3.2 `simulate_interaction(node_id, action, params)`

- **Purpose:** Allows the Agent to run End-to-End (E2E) tests on its own UI.
- **Actions:**
  - `tap`: Simulates a click/touch at the center of the node's `rect`.
  - `type`: Injects text into an `input` node.
  - `scroll`: Scrolls a `container`.
- **Safety:** The Runtime rejects the action if the node is `occluded` or `invisible`, returning an error: _"Cannot click Node #102: Covered by Node #99 (Modal)"_. This forces the Agent to fix z-index bugs.

---

## 4. Visual Verification Logic

The Agent is trained to perform "Spatial Unit Tests" using the SAP data.

### 4.1 Overlap Detection

- **Logic:** Agent checks if `Rect A` intersects `Rect B`.
- **Use Case:** "Verify that the 'Delete' button is not touching the 'Save' button."

### 4.2 Contrast & Visibility

- **Logic:** Agent checks the `flags` array.
- **Use Case:** "I set the button to hidden. Verify `flags` does NOT contain 'visible'."

### 4.3 Responsive Design Verification

- **Logic:** Agent requests snapshots at different viewport sizes.
- **Scenario:**
  1.  `set_viewport(1920, 1080)` $\rightarrow$ `get_ui_snapshot()` $\rightarrow$ Verify Sidebar is visible.
  2.  `set_viewport(400, 800)` $\rightarrow$ `get_ui_snapshot()` $\rightarrow$ Verify Sidebar is hidden (Hamburger menu).

---

## 5. Requirements Traceability

| Feature                    | Rationale                                            | Requirement |
| :------------------------- | :--------------------------------------------------- | :---------- |
| **Computed Geometry**      | Allows Agent to debug CSS/Layout logic without eyes. | REQ-6.1.3   |
| **Occlusion Detection**    | Prevents "Z-Fighting" and overlay bugs.              | REQ-6.1.3   |
| **Interaction Simulation** | Enables self-testing (Agent writes/runs E2E tests).  | REQ-7.2.2   |
| **Role Normalization**     | Abstracts platform differences (DOM vs Native).      | REQ-6.1.1   |

