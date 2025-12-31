### 1. The UI Compilation Pipeline

The UI process follows a 4-stage pipeline. The Agent interacts with Stage 1. The Compiler handles Stage 2 & 3. The Runtime handles Stage 4.

| Stage | Name                    | Representation                     | Responsibility                                                      |
| :---- | :---------------------- | :--------------------------------- | :------------------------------------------------------------------ |
| **1** | **Declarative Phase**   | **Widget Tree** (High-Level)       | Agent defines logic (`Column`, `Button`).                           |
| **2** | **Layout Phase**        | **Layout Tree** (Solved Geometry)  | Compiler/Runtime calculates X, Y, Width, Height using Constraints.  |
| **3** | **Paint Phase**         | **Render Command Buffer** (MUI-IR) | A linear list of drawing instructions (`DrawRect`, `DrawTextBlob`). |
| **4** | **Rasterization Phase** | **GPU/DOM/ANSI** (Backend)         | Executing instructions on the specific hardware.                    |

---

### 2. The Core Technology: Morph UI IR (MUI-IR)

The **MUI-IR** is a platform-agnostic, binary protocol for describing visual primitives. It is **not** pixels; it is vector instructions.

**Structure of a MUI-IR Frame:**

```rust
// Simplified binary representation
Frame #102:
  [0x01] SaveLayer
  [0x02] ClipRect (0, 0, 800, 600)
  [0x03] DrawRect (x=10, y=10, w=100, h=50, color=#FF0000)
  [0x04] DrawText (x=15, y=25, font_id=1, string_hash=0xA1B2)
  [0x05] RestoreLayer
```

This list is what gets distributed or generated. It is mathematically pure.

---

### 3. Backend Implementation (Target Specifics)

This is how the MUI-IR translates to your specific requested targets. The Compiler uses **Traits** to select the correct "Rasterizer Driver."

#### A. Target: Native Desktop/Mobile (x86, ARM, Android, macOS)

**Driver:** `Morph::GpuDriver` (based on WebGPU/WGPU logic).

- **Windowing:** Uses a lightweight shell (like SDL or GLFW) to create a raw OS Window.
- **Compilation:**
  - MUI-IR `DrawRect` $\rightarrow$ Generates Vertex Buffer (2 triangles).
  - MUI-IR `DrawText` $\rightarrow$ Uses a **Texture Atlas** (font glyphs cached in GPU memory).
  - **Shaders:** Morph includes pre-compiled SPIR-V shaders for drawing primitives.
- **Android/iOS Specifics:**
  - Hooks into the `SurfaceView` (Android) or `CAMetalLayer` (iOS).
  - Touch events are normalized into generic `PointerEvents` before reaching the Agent's logic.

#### B. Target: WebAssembly (Wasm)

**Driver:** `Morph::CanvasDriver` or `Morph::WebGLDriver`.

- **Strategy 1 (Performance):** Uses **WebGL2/WebGPU**.
  - MUI-IR commands are fed directly to the GPU via Wasm. This is pixel-identical to the Native Desktop target.
- **Strategy 2 (Compatibility):** Uses **HTML5 Canvas 2D Context**.
  - MUI-IR `DrawRect` $\rightarrow$ JS `ctx.fillRect()`.
  - MUI-IR `DrawText` $\rightarrow$ JS `ctx.fillText()`.
- **Accessibility:** Since Canvas is invisible to screen readers, the Runtime maintains a parallel, invisible **DOM Tree** with ARIA tags that matches the Semantics Tree.

#### C. Target: Terminal (TUI)

**Driver:** `Morph::AnsiDriver`.

- **The "Cell Buffer":** Instead of pixels, the screen is a Grid of Cells (Character + FG Color + BG Color + Attributes).
- **Rasterization:**
  - MUI-IR `DrawRect` $\rightarrow$ Iterates over the grid cells intersecting the rect. Sets their BG Color to the rect color.
  - MUI-IR `DrawText` $\rightarrow$ Writes characters into the cells.
  - **High-Res Trick:** Uses **Braille Patterns** or **Block Elements** (e.g., `▀`, `▄`) to simulate "sub-pixel" rendering in the terminal.
- **Output:** The diff of the Cell Buffer is flushed to `stdout` using ANSI Escape Codes.

---

### 4. Layout Engine (The "Solver")

Before we can Draw (Stage 3), we must Layout (Stage 2).
Native UI frameworks (Constraints) are complex. The Web (Flexbox) is complex.

**Morph Decision:** The Layout Engine is a **Single-Pass Flexbox Implementation** written in core Morph.

- **Why?** Flexbox is expressive enough for 99% of UI.
- **Mechanism:**
  1.  The Agent writes `Row { ChildA, ChildB }`.
  2.  The Runtime receives the Layout Tree.
  3.  It calculates constraints: `ParentWidth` is known. `ChildA` wants 50px. `ChildB` takes the rest.
  4.  **Result:** Concrete `(x, y, w, h)` coordinates for every node.
- **Optimization:** When compiling to Native Code, the Layout Engine is compiled to highly optimized SIMD instructions (via OIR), making layout calculation nearly instant (sub-millisecond).

---

### 5. Handling Fonts (The Hardest Part)

Fonts are the biggest source of "it looks different on my machine."

**Morph Solution:** **Client-Side Rendering via SDF**.

- **Packaging:** The `.mpx` binary embeds the fonts (or downloads them). It does _not_ rely on System Fonts (Arial, San Francisco) by default to ensure Determinism.
- **Technique:** Uses **Signed Distance Fields (SDF)**.
  - The font is converted into a specialized texture.
  - This allows the GPU to render crisp text at any size without re-rasterizing CPU-side.
  - This works identically on High-DPI screens, Low-DPI screens, and WebGL.

---

### 6. Architectural Addendum (GUI Specifications)

Add this section to the **LAD (Layering Architecture Document)** under Layer 4 to formalize this.

#### L4.1.A - The Universal Renderer (MUI-IR)

- **Definition:** A platform-independent command buffer for 2D graphics.
- **Primitives:**
  - `DrawGeometry` (Rects, RRects, Circles, Paths).
  - `DrawImage` (Bitmaps, SVG Vectors).
  - `DrawText` (Shaped Glyphs).
  - `PushClip` / `PopClip` (Masking).
  - `PushTransform` / `PopTransform` (Matrix operations).

#### L4.1.B - The Backend Adapters (Drivers)

- **`GPU_Backend`:**
  - **API:** Vulkan (Linux/Android), Metal (macOS/iOS), DX12 (Windows), WebGPU (Web).
  - **Shader:** Unified SPIR-V shader pipeline.
- **`TUI_Backend`:**
  - **API:** ANSI / ncurses emulation.
  - **Mapping:** Maps geometric primitives to nearest-neighbor character blocks.

#### L4.1.C - The Input Normalizer

- **Role:** Abstraction of hardware events.
- **Mapping:**
  - Mouse Click $\rightarrow$ `PointerDown(x,y, primary)`.
  - Touch Tap $\rightarrow$ `PointerDown(x,y, primary)`.
  - Keyboard `A` $\rightarrow$ `KeyDown(Keycode::A)`.
  - Gamepad `X` $\rightarrow$ `KeyDown(Keycode::GameButtonX)`.

### Summary for the User

To answer your question directly: The "GUI IR" is a linear list of **Vector Drawing Commands**.

- On **x86/Windows**, the runtime reads this list and makes DirectX calls.
- On **Android/ARM**, the runtime reads _the exact same list_ and makes Vulkan calls.
- On **Terminal**, the runtime reads _the exact same list_ and calculates which text characters represent those shapes.

This separation means the Agent writes the UI once, and the **Morph Runtime** acts as the translator to the physical hardware pixels.
