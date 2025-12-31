### 1. The Architectural Choice: "Embedder Isolation"

Instead of the Agent's code asking the OS for events, the OS **injects** events into the Morph Runtime. This inversion of control is critical for determinism.

- **Rejected:** GLFW/GLAD (Too limited; no mobile/audio support).
- **Rejected:** SDL2 Raw (Too messy; exposes C-structs and platform quirks).
- **Accepted:** **The "Packetized" Event Stream** (inspired by Flutter's Embedder API).
  - The OS Layer (SDL3/Web/TUI) captures raw input.
  - It converts it instantly into a **Morph Canonical Input Event (MCIE)**.
  - It pushes this packet into a thread-safe **Input Ring Buffer**.
  - The `logic` block reads from the buffer.

### 2. The Canonical Input Event (MCIE) Schema

This is the **ONLY** data structure the Agent (and the Semantic Tree) ever sees. It abstracts the physical hardware completely.

**Structure (in Morph Data Syntax):**

```rust
data InputPacket {
    timestamp: u64, // Microseconds since app start (Deterministic Clock)
    device_id: u32, // Unique ID for the hardware device

    // Sum Type for all possible inputs
    event: InputType =
      | Pointer {
           x: f32, y: f32,        // Normalized Coordinates (0.0 to 1.0 or Logical Pixels)
           phase: Phase,          // Down, Move, Up, Cancel
           signal: SignalKind     // MouseLeft, TouchContact, PenPressure
        }
      | Keyboard {
           key: KeyCode,          // Physical Location (QWERTY "W")
           scan: ScanCode,        // Hardware ID
           state: KeyState        // Pressed, Released, Repeat
        }
      | Axis {
           axis: AxisCode,        // Gamepad LeftStickX, MouseWheelY
           value: f32             // -1.0 to 1.0
        }
      | System {
           kind: SysKind          // WindowResize, LowMemory, ClipboardPaste
        }
}
```

### 3. The Backend Implementation (The "Drivers")

To support your specific targets (x86, ARM, Web, TUI), the Morph Runtime includes specific **Embedders** that produce these MCIE packets.

| Target Platform             | Host Driver (Implementation) | Normalization Strategy                                                                                                                         |
| :-------------------------- | :--------------------------- | :--------------------------------------------------------------------------------------------------------------------------------------------- |
| **Windows / Linux / macOS** | **SDL3 (Static)**            | SDL3 is chosen over SDL2 for its thread-safety and better High-DPI support. It handles the raw windowing and OpenGL/Vulkan context creation.   |
| **Android / iOS**           | **SDL3 (Static)**            | SDL3 handles the Java/Obj-C interop (JNI) and forwards Touch events.                                                                           |
| **Web (Wasm)**              | **HTML5 JS Bridge**          | JS `addEventListener` captures DOM events. A small JS shim serializes them to linear memory. Morph Wasm reads memory and deserializes to MCIE. |
| **Terminal (TUI)**          | **Built-in ANSI Parser**     | Captures `stdin`. Decodes escape sequences (e.g., `\x1b[M` for Mouse). Maps Grid Cells $(Col, Row)$ to Coordinate $(x, y)$.                    |

### 4. Resolving the TUI Ambiguity

You asked how TUI works with this.

- **The Trick:** The TUI Driver "lies" to the runtime.
- **Mouse:** Modern terminals support `SGR 1006` mouse tracking. When you click at Column 10, Row 5, the TUI Driver emits a `Pointer { x: 100.0, y: 50.0, phase: Down }` (assuming a 10x10 cell size).
- **Result:** The Agent's Button Logic **does not change**. It checks `if pointer.x > button.x`. This works for both 4K Monitors and Terminal Screens.

### 5. Deterministic Replay (The "Agent Verification")

Because all inputs are normalized into the **Input Ring Buffer** (MCIE packets) _before_ reaching the logic:

1.  **Recording:** You can save the stream of MCIE packets to a file.
2.  **Replay:** You can feed those packets back into the runtime.
3.  **Guarantee:** Because the logic is deterministic (no threads sharing memory), replaying the inputs guarantees the **exact same application state** (Time Travel Debugging).

---

### Updated BSAD Section: Input Architecture

Add this to your technical documentation to finalize the design.

#### L4.4 - Input Normalizer Architecture

- **REQ-INP-01 (Embedder Isolation):** The Morph Runtime SHALL NOT expose host windowing handles (HWND, NSWindow) or raw driver events (SDL_Event) to the logic layer.
- **REQ-INP-02 (Canonicalization):** All inputs must be converted to **Morph Canonical Input Events (MCIE)** at the system boundary.
- **REQ-INP-03 (Coordinate Normalization):** Pointer coordinates must be normalized to **Logical Pixels** (DPI-aware).
  - **TUI:** 1 Cell = 10x20 Logical Pixels (virtual).
  - **High-DPI Mobile:** Hardware pixels / Device Pixel Ratio.
- **REQ-INP-04 (Input Ring Buffer):** All MCIEs must pass through a fixed-size Ring Buffer stamped with a deterministic timestamp, serving as the synchronization point for the "Time Travel Debugger."

### Summary

- **Use SDL3** (hidden implementation detail) for the heavy lifting on Native/Mobile.
- **Use Custom Parsers** for Web/TUI.
- **Expose Only MCIE** to the Agent.

This architecture ensures that when the Agent writes code for a "Click," it works on a Mouse, a Touchscreen, and a Terminal via SSH, with zero code changes.
