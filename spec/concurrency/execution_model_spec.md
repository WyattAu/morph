# Morph Execution Model Specification (EMS)

- File: `spec/concurrency/execution_model_spec.md`
- Version: 2.2.0
- Context: Layer 3 (Runtime) - Formalism
- Status: Active
- Last Modified: 2026-01-04
- Author: Kilo Code
- Reviewers: [Pending Review]

---

## 1. Introduction

### 1.1 Purpose

This specification defines: Execution Model of Morph, providing formal foundation for runtime behavior, scheduling, and concurrency. The execution model uses a **Work-Stealing Scheduler** for production builds, with deterministic scheduling available only as a debug-mode shim via link-time replacement.

### 1.2 Scope

This specification covers:
- The Runtime Library (MRE)
- The Execution Unit (Fiber)
- Concurrency Scheduling (Work-Stealing)
- Implicit Suspension Protocol
- Preemption Mechanism
- The Actor Model (`logic`)
- Supervision Trees
- Dataflow Parallelism (`async let`)
- Memory Management
- Foreign Function Interface (FFI)
- Observability & Debugging

This specification does not cover:
- Concrete implementation of schedulers
- Hardware-specific optimizations
- Performance tuning details

### 1.3 Definitions, Acronyms, and Abbreviations

| Term | Definition |
|-------|------------|
| **MRE** | Morph Runtime Environment - bare-metal runtime library |
| **Fiber** | Stackful coroutine - fundamental unit of execution |
| **M:N** | M Fibers mapped onto N OS Threads (Executors) |
| **Work Stealing** | Scheduler strategy where idle executors steal work from busy ones |
| **Deterministic Scheduler** | Debug-mode shim for reproducible execution |
| **MPSC** | Multi-Producer, Single-Consumer queue |
| **ARC** | Atomic Reference Counting |
| **FFI** | Foreign Function Interface |
| **IOCP** | Input/Output Completion Ports (Windows) |
| **io_uring** | Linux asynchronous I/O interface |
| **kqueue** | BSD/macOS event notification system |

### 1.4 References

- Lamport, L. (1979). "How to Make a Multiprocessor Computer That Correctly Executes Multiprocess Programs"
- Blumofe, R. D., & Leiserson, C. E. (1999). "Scheduling Multithreaded Computations by Work Stealing"
- ISO/IEC 29148: Systems and software engineering — Requirements engineering
- IEEE 1016: Recommended Practice for Software Design Descriptions

### 1.5 Cross-References

The Execution Model Specification is closely related to several other Morph specifications. The following cross-references provide additional context and detailed specifications for related concepts:

* Concurrency Specifications:*
- [`spec/concurrency/scheduling_modes_spec.md`](./scheduling_modes_spec.md) - Dual-mode scheduling specification (work-stealing and deterministic modes)
- [`spec/concurrency/concurrency_process_algebra_spec.md`](./concurrency_process_algebra_spec.md) - Process algebra formalization of concurrent communication

* Architecture Specifications:*
- [`spec/architecture/layered_concurrency_spec.md`](../architecture/layered_concurrency_spec.md) - Layered concurrency architecture for integrating execution model with language-level patterns

* Type System Specifications:*
- [`spec/type/type_system_spec.md`](../type/type_system_spec.md) - Type system with capability enforcement for memory safety
- [`spec/type/effect_system_spec.md`](../type/effect_system_spec.md) - Effect system for tracking side effects

* Memory Specifications:*
- [`spec/memory/memory_model_spec.md`](../memory/memory_model_spec.md) - Memory management model, ARC implementation, and runtime memory operations
- [`spec/memory/memory_affine_logic_spec.md`](../memory/memory_affine_logic_spec.md) - Affine logic formalization for memory safety

* Note:* These cross-references help readers navigate to Morph specification ecosystem by providing links to related specifications that provide complementary or detailed information about concepts referenced in this document.

---

## 2. Formal Definitions

### 2.1 The Runtime Architecture

#### 2.1.1 The Runtime Library (MRE)

Morph does not run on a Virtual Machine (like the JVM). It runs on a **Bare-Metal Runtime Library** that is statically linked into the final executable (`.mpx`).

* EMS-INV-001:* THE system SHALL use a bare-metal runtime library statically linked into executable.

* Components:
- **Role:** Abstraction of OS primitives (Threads, I/O, Memory)
- **Composition:** A lightweight kernel written in C++/Assembly (optimized for each architecture) controlled by MorphIR instructions

* EMS-REQ-001:* THE system SHALL provide a bare-metal runtime library for OS primitive abstraction.
  - Priority:* Critical
  - Verification Method:* Test
  - Rationale:* Enables zero-overhead runtime without virtual machine
  - Dependencies:* EMS-INV-001
  - Traceability:* Section 2.1.1 (The Runtime Library)

#### 2.1.2 The Execution Unit: The Fiber

The fundamental unit of execution is a **Fiber** (Stackful Coroutine).

* EMS-INV-002:* THE system SHALL use stackful coroutines as fundamental execution unit.

* Characteristics:
- **Stack:** Growable, starting at 4KB (vs. 1MB for OS threads)
- **Cost:** Creating a Fiber takes nanoseconds
- **State:** Holds CPU registers and stack pointer

* Rationale:* "Colorless" async (implicit suspension) requires _Stackful_ coroutines. The runtime must be able to pause a function deep in the call stack without unwinding it (unlike Stackless `async/await` in Rust/JS).

* EMS-REQ-002:* THE system SHALL use stackful coroutines with growable stacks starting at 4KB.
  - Priority:* Critical
  - Verification Method:* Test
  - Rationale:* Enables implicit suspension without stack unwinding
  - Dependencies:* EMS-INV-002
  - Traceability:* Section 2.1.2 (The Execution Unit: The Fiber)

#### 2.1.3 Fiber-Actor Relationship

* Fibers as Actor Execution Units:*

Fibers are the fundamental execution units in Morph. Actors are implemented as **stateful fibers** with additional messaging infrastructure.

* EMS-INV-024:* THE system SHALL implement actors as stateful fibers with mailboxes.

* Relationship:*

1. **Fiber:** The execution unit
   - Provides stackful coroutine execution
   - Can be suspended and resumed
   - Managed by M:N scheduler

2. **Actor:** A stateful fiber with messaging
   - Implemented as a stateful fiber (see Section 2.3.1)
   - Has a mailbox (MPSC queue) for receiving messages
   - Has a supervisor for failure handling

* Mapping:*

$$
\text{Actor} = (\text{Fiber}, \text{Mailbox}, \text{Supervisor})
$$

Where:
- **Fiber:** Provides execution context (stack, registers, state)
- **Mailbox:** Provides message passing interface (MPSC queue)
- **Supervisor:** Provides failure recovery mechanism

* Execution Flow:*

1. Actor is spawned as a stateful fiber
2. Fiber enters message processing loop
3. Fiber waits for messages in mailbox (suspends if empty)
4. When message arrives, fiber wakes up and processes it
5. Fiber continues processing messages sequentially
6. If actor panics, supervisor handles failure

* Key Points:*

- **Fibers are execution mechanism:** All concurrent execution happens via fibers
- **Actors are a programming model:** Actors provide a structured way to write concurrent code
- **Actors use fibers for execution:** Each actor runs in its own fiber
- **Multiple actors can run on same fiber:** Not typical, but possible via message forwarding
- **Single fiber per actor:** Standard model is one fiber per actor for isolation

* EMS-REQ-018:* THE system SHALL implement actors as stateful fibers with mailboxes and supervisors.
  - Priority:* Critical
  - Verification Method:* Test
  - Rationale:* Clarifies fiber-actor relationship and enables actor model
  - Dependencies:* EMS-INV-002, EMS-INV-007, EMS-INV-024
  - Traceability:* Section 2.1.2 (The Execution Unit: The Fiber), Section 2.3.1 (Actor Structure)

### 2.2 Concurrency Scheduling

#### 2.2.0 Scheduler Selection Mechanism

The Morph execution model uses **link-time replacement** for scheduler selection, not runtime switching. This ensures that production binaries contain only the work-stealing scheduler, avoiding dead code and maximizing performance.

* EMS-INV-003:* THE system SHALL implement link-time replacement for scheduler selection.

* Critical Design Principle:*
- **No Runtime Switch:** The system does NOT ship two schedulers in the final binary
- **Link-Time Replacement:** Schedulers are selected at build time via build flags
- **Dead Code Elimination:** Production builds link only the work-stealing scheduler
- **Debug Builds:** Debug/test builds link only the deterministic scheduler

* Rationale:* Shipping two schedulers in production would carry dead code, increase binary size, and introduce unnecessary complexity. Link-time replacement ensures optimal production performance while enabling reproducible debugging for development.

* EMS-REQ-003:* THE system SHALL use link-time replacement for scheduler selection, not runtime switching.
  - Priority:* Critical
  - Verification Method:* Test
  - Rationale:* Avoids dead code in production and ensures optimal performance
  - Dependencies:* EMS-INV-003
  - Traceability:* Section 2.2.0 (Scheduler Selection Mechanism)

* EMS-REQ-004:* THE system SHALL NOT ship two schedulers in the final binary.
  - Priority:* Critical
  - Verification Method:* Test
  - Rationale:* Prevents dead code and ensures production performance
  - Dependencies:* EMS-INV-003
  - Traceability:* Section 2.2.0 (Scheduler Selection Mechanism)

#### 2.2.1 The M:N Scheduler with Work Stealing (Production)

The MRE implements an M:N scheduling model, mapping **M Fibers** onto **N OS Threads** (Executors).

* EMS-INV-004:* THE system SHALL implement M:N scheduling with work stealing for production builds.

* Components:
- **N (Executors):** Typically equal to `Hardware_Cores`. Each Executor runs a local Work Queue
- **Work Stealing:** If an Executor runs out of Fibers, it steals jobs from the tail of another Executor's queue
- **Production Scheduler:** Work-stealing scheduler is the only scheduler linked in production builds

* Rationale:* Maximizes CPU utilization. Prevents a single heavy task from blocking the entire application (as happens in Node.js single-threaded event loops).

* EMS-REQ-005:* THE system SHALL use work-stealing scheduler as the only scheduler in production builds.
  - Priority:* Critical
  - Verification Method:* Test
  - Rationale:* Maximizes CPU utilization and prevents blocking
  - Dependencies:* EMS-INV-004
  - Traceability:* Section 2.2.1 (The M:N Scheduler with Work Stealing)

#### 2.2.1.1 Work-Stealing Algorithm Implementation

The work-stealing scheduler implements the classic Chase-Lev deque algorithm with optimizations for Morph's fiber model.

* EMS-INV-009:* THE system SHALL implement Chase-Lev deque algorithm for work stealing.

##### 2.2.1.1.1 Data Structures

**Executor Structure:**
```cpp
struct Executor {
    // Unique executor ID (0 to N-1)
    id: u32
    
    // Local work queue (Chase-Lev deque)
    deque: WorkDeque
    
    // Random number generator for victim selection
    rng: XorShift64
    
    // Current fiber being executed
    current_fiber: Fiber*
    
    // Statistics (debug mode only)
    stats: ExecutorStats
}

struct WorkDeque {
    // Circular buffer for fibers
    buffer: AtomicPtr<Fiber>*[DEQUE_CAPACITY]
    
    // Bottom index (owner pushes/pops here)
    bottom: AtomicUsize
    
    // Top index (thieves pop from here)
    top: AtomicUsize
    
    // Capacity (power of 2 for fast modulo)
    capacity: usize
}

struct Fiber {
    // Fiber ID
    id: u64
    
    // Fiber state
    state: FiberState  // Ready, Running, Suspended, Terminated
    
    // Stack pointer
    stack_ptr: u8*
    
    // Stack size
    stack_size: usize
    
    // Saved context (registers)
    context: FiberContext
    
    // Fiber function
    entry_point: fn() -> void
    
    // Argument to entry point
    argument: void*
    
    // Parent fiber (for async let)
    parent: Fiber*
    
    // Dependency list (fibers waiting for this one)
    dependencies: AtomicPtr<FiberList>
    
    // Future slot (for async let)
    future_slot: FutureSlot*
}

enum FiberState {
    Ready,
    Running,
    Suspended,
    Terminated
}
```

##### 2.2.1.1.2 Work-Stealing Algorithm Pseudocode

**Main Executor Loop:**
```cpp
fn executor_main(executor: &Executor) {
    loop {
        // Try to get work from local queue
        fiber = executor.deque.pop_bottom()
        
        if fiber != null {
            // Execute fiber
            execute_fiber(executor, fiber)
        } else {
            // No local work, try to steal
            fiber = steal_work(executor)
            
            if fiber != null {
                // Execute stolen fiber
                execute_fiber(executor, fiber)
            } else {
                // No work available, sleep briefly
                sleep(1ms)
            }
        }
    }
}
```

**Local Queue Operations (Owner):**
```cpp
// Push fiber to bottom of local queue (owner only)
fn push_bottom(deque: &WorkDeque, fiber: Fiber*) {
    old_bottom = deque.bottom.load(Ordering::Relaxed)
    new_bottom = old_bottom + 1
    
    // Check if we need to resize
    if new_bottom - deque.top.load(Ordering::Acquire) > deque.capacity {
        resize_deque(deque)
    }
    
    // Store fiber at bottom-1 position
    index = old_bottom & (deque.capacity - 1)
    deque.buffer[index].store(fiber, Ordering::Relaxed)
    
    // Publish new bottom
    deque.bottom.store(new_bottom, Ordering::Release)
}

// Pop fiber from bottom of local queue (owner only)
fn pop_bottom(deque: &WorkDeque) -> Fiber* {
    old_bottom = deque.bottom.load(Ordering::Relaxed)
    new_bottom = old_bottom - 1
    deque.bottom.store(new_bottom, Ordering::Relaxed)
    
    old_top = deque.top.load(Ordering::Acquire)
    
    if new_bottom <= old_top {
        // Queue is empty or was stolen from
        deque.bottom.store(old_bottom, Ordering::Relaxed)
        return null
    }
    
    // Get fiber from bottom-1 position
    index = new_bottom & (deque.capacity - 1)
    fiber = deque.buffer[index].load(Ordering::Relaxed)
    
    if new_bottom > old_top + 1 {
        // More than one item, safe to return
        return fiber
    }
    
    // Last item, need to compete with thieves
    if !deque.top.compare_exchange_weak(
        old_top, old_top + 1,
        Ordering::AcqRel,
        Ordering::Acquire
    ) {
        // Thief won, queue is empty
        return null
    }
    
    return fiber
}
```

**Steal Operations (Thief):**
```cpp
// Steal fiber from top of victim's queue (thief only)
fn steal(deque: &WorkDeque) -> Fiber* {
    old_top = deque.top.load(Ordering::Acquire)
    new_top = old_top + 1
    
    // Check if queue is empty
    if new_top > deque.bottom.load(Ordering::Acquire) {
        return null
    }
    
    // Try to claim top position
    if !deque.top.compare_exchange_weak(
        old_top, new_top,
        Ordering::AcqRel,
        Ordering::Acquire
    ) {
        // Another thief won, retry
        return null
    }
    
    // Get fiber from top position
    index = old_top & (deque.capacity - 1)
    fiber = deque.buffer[index].load(Ordering::Acquire)
    
    // Check if queue became empty after we claimed
    if fiber == null {
        deque.top.store(old_top, Ordering::Release)
        return null
    }
    
    return fiber
}

// Select victim executor and attempt to steal
fn steal_work(executor: &Executor) -> Fiber* {
    num_executors = get_num_executors()
    
    // Try multiple times with different victims
    for attempt in 0..STEAL_ATTEMPTS {
        // Random victim selection (avoid self)
        victim_id = executor.rng.next() % (num_executors - 1)
        if victim_id >= executor.id {
            victim_id += 1
        }
        
        victim = get_executor(victim_id)
        
        // Attempt to steal
        fiber = steal(&victim.deque)
        
        if fiber != null {
            // Successfully stole work
            executor.stats.steals_succeeded += 1
            return fiber
        }
        
        executor.stats.steals_failed += 1
    }
    
    return null
}
```

##### 2.2.1.1.3 Load Balancing Strategy

The work-stealing scheduler implements adaptive load balancing through the following mechanisms:

**1. Random Victim Selection:**
- Thieves select victims randomly using XorShift64 PRNG
- Avoids systematic contention on specific executors
- Ensures fair distribution of stolen work

**2. Adaptive Steal Attempts:**
```cpp
const STEAL_ATTEMPTS: usize = 3

fn steal_work(executor: &Executor) -> Fiber* {
    // More attempts when underutilized
    attempts = if executor.utilization < 0.5 {
        STEAL_ATTEMPTS * 2
    } else {
        STEAL_ATTEMPTS
    }
    
    for attempt in 0..attempts {
        // ... steal logic
    }
}
```

**3. Work Distribution Heuristics:**
- **Local Work First:** Executors always check local queue before stealing
- **Steal from Busy:** Thieves prefer executors with larger queues
- **Avoid Contention:** Random selection prevents hotspots

**4. Queue Size Monitoring:**
```cpp
fn get_queue_size(deque: &WorkDeque) -> usize {
    bottom = deque.bottom.load(Ordering::Acquire)
    top = deque.top.load(Ordering::Acquire)
    return bottom - top
}

// Prefer stealing from executors with larger queues
fn select_victim(executor: &Executor) -> Executor* {
    candidates = []
    
    for other in all_executors() {
        if other.id != executor.id {
            size = get_queue_size(&other.deque)
            if size > 0 {
                candidates.push((other, size))
            }
        }
    }
    
    if candidates.is_empty() {
        return null
    }
    
    // Weighted random selection based on queue size
    total_size = sum(candidates.map(|(_, size)| size))
    threshold = executor.rng.next() % total_size
    
    cumulative = 0
    for (candidate, size) in candidates {
        cumulative += size
        if cumulative > threshold {
            return candidate
        }
    }
    
    return candidates[0].0
}
```

##### 2.2.1.1.4 Contention Handling

The work-stealing scheduler implements several mechanisms to handle contention:

**1. Lock-Free Operations:**
- All deque operations use atomic CAS (Compare-And-Swap)
- No mutexes or locks in the critical path
- Minimizes contention and maximizes throughput

**2. Exponential Backoff:**
```cpp
fn steal_with_backoff(executor: &Executor) -> Fiber* {
    for attempt in 0..MAX_STEAL_ATTEMPTS {
        fiber = steal_work(executor)
        
        if fiber != null {
            return fiber
        }
        
        // Exponential backoff on contention
        backoff = 1 << min(attempt, 10)
        sleep(backoff * 100ns)
    }
    
    return null
}
```

**3. Contention Detection:**
```cpp
fn detect_contention(executor: &Executor) -> bool {
    // High steal failure rate indicates contention
    total = executor.stats.steals_succeeded + executor.stats.steals_failed
    if total == 0 {
        return false
    }
    
    failure_rate = executor.stats.steals_failed / total
    return failure_rate > 0.7
}
```

**4. Adaptive Stealing:**
```cpp
fn adaptive_steal(executor: &Executor) -> Fiber* {
    if detect_contention(executor) {
        // Reduce steal attempts under contention
        return steal_work_limited(executor, 1)
    } else {
        // Normal steal attempts
        return steal_work(executor)
    }
}
```

##### 2.2.1.1.5 Performance Characteristics

**Time Complexity:**
- **Push (Owner):** O(1) amortized
- **Pop (Owner):** O(1) amortized
- **Steal (Thief):** O(1) amortized
- **Resize:** O(n) where n is queue size (rare)

**Space Complexity:**
- **Per Executor:** O(k) where k is maximum queue size
- **Total:** O(n * k) where n is number of executors

**Cache Locality:**
- **Local Operations:** Excellent (owner accesses contiguous memory)
- **Steal Operations:** Good (thief accesses top of deque)
- **Work Affinity:** Fibers tend to stay on same executor

**Throughput:**
- **Fiber Scheduling:** ~10ns per operation
- **Work Stealing:** ~10ns per steal attempt
- **Overall:** ~1M fibers/second per executor

**Latency:**
- **Local Scheduling:** ~10ns
- **Stolen Scheduling:** ~20-50ns (includes cache miss)
- **Worst Case:** ~100ns (under high contention)

**Scalability:**
- **Linear Scaling:** Throughput scales linearly with core count
- **Diminishing Returns:** Beyond 32 cores, memory bandwidth becomes bottleneck
- **Optimal:** 1 executor per physical core

**Memory Overhead:**
- **Per Fiber:** ~8KB (4KB stack + metadata)
- **Per Executor:** ~1MB (deque + statistics)
- **Total (1M fibers, 8 executors):** ~8GB

* EMS-REQ-018:* THE system SHALL implement Chase-Lev deque algorithm for work stealing.
  - Priority:* Critical
  - Verification Method:* Test
  - Rationale:* Provides proven O(1) work-stealing with minimal contention
  - Dependencies:* EMS-INV-004, EMS-INV-009
  - Traceability:* Section 2.2.1.1 (Work-Stealing Algorithm Implementation)

* EMS-REQ-019:* THE system SHALL implement adaptive load balancing with random victim selection.
  - Priority:* High
  - Verification Method:* Test
  - Rationale:* Ensures fair work distribution and minimizes contention
  - Dependencies:* EMS-INV-004
  - Traceability:* Section 2.2.1.1.3 (Load Balancing Strategy)

* EMS-REQ-020:* THE system SHALL implement lock-free operations with exponential backoff for contention handling.
  - Priority:* High
  - Verification Method:* Test
  - Rationale:* Minimizes contention and maximizes throughput
  - Dependencies:* EMS-INV-004
  - Traceability:* Section 2.2.1.1.4 (Contention Handling)

* EMS-REQ-021:* THE system SHALL achieve O(1) amortized time complexity for all scheduler operations.
  - Priority:* High
  - Verification Method:* Analysis
  - Rationale:* Ensures efficient scheduling at scale
  - Dependencies:* EMS-INV-004
  - Traceability:* Section 2.2.1.1.5 (Performance Characteristics)

#### 2.2.2 Deterministic Scheduler (Debug/Test Mode Only)

The deterministic scheduler is strictly a **debug-mode shim**, not a production feature. It is linked only when the `--debug-scheduler` build flag is specified.

* EMS-INV-005:* THE system SHALL provide deterministic scheduler only in debug/test mode via link-time replacement.

* Components:
- **Purpose:** Reproducible execution for debugging and testing
- **Behavior:** Processes fibers in deterministic order (e.g., FIFO)
- **Limitation:** Not suitable for production due to poor performance
- **Build Flag:** Enabled via `--debug-scheduler` flag (see Section 2.2.3)

* Rationale:* Enables reproducible debugging without compromising production performance. Link-time replacement ensures deterministic scheduler code is not present in production binaries.

* EMS-REQ-006:* THE system SHALL provide deterministic scheduler only as a debug-mode shim via link-time replacement.
  - Priority:* High
  - Verification Method:* Test
  - Rationale:* Enables reproducible debugging without production overhead
  - Dependencies:* EMS-INV-005
  - Traceability:* Section 2.2.2 (Deterministic Scheduler)

* EMS-REQ-007:* THE system SHALL NOT link deterministic scheduler in production mode.
  - Priority:* Critical
  - Verification Method:* Test
  - Rationale:* Ensures production performance and avoids dead code
  - Dependencies:* EMS-INV-005
  - Traceability:* Section 2.2.2 (Deterministic Scheduler)

#### 2.2.2.1 Deterministic Scheduler Algorithm Implementation

The deterministic scheduler implements a single-threaded FIFO queue with strict ordering guarantees for reproducible execution.

* EMS-INV-010:* THE system SHALL implement deterministic scheduler with FIFO ordering.

##### 2.2.2.1.1 Data Structures

**Deterministic Scheduler Structure:**
```cpp
struct DeterministicScheduler {
    // Global FIFO queue for all fibers
    ready_queue: Mutex<Vec<Fiber*>>
    
    // Fiber ID counter for deterministic ordering
    next_fiber_id: AtomicU64
    
    // Current fiber being executed
    current_fiber: Fiber*
    
    // Execution trace for debugging
    execution_trace: Vec<TraceEntry>
    
    // Deterministic random number generator
    rng: DeterministicRNG
    
    // Statistics
    stats: SchedulerStats
}

struct TraceEntry {
    fiber_id: u64
    timestamp: u64
    event: TraceEvent
}

enum TraceEvent {
    FiberSpawned,
    FiberScheduled,
    FiberResumed,
    FiberSuspended,
    FiberTerminated,
    MessageSent,
    MessageReceived
}

struct DeterministicRNG {
    // Seed for reproducibility
    seed: u64
    
    // Current state
    state: u64
}
```

##### 2.2.2.1.2 Deterministic Scheduling Algorithm

**Main Scheduler Loop:**
```cpp
fn deterministic_scheduler_main(scheduler: &DeterministicScheduler) {
    loop {
        // Acquire lock on ready queue
        lock = scheduler.ready_queue.lock()
        
        // Check if queue is empty
        if scheduler.ready_queue.is_empty() {
            lock.release()
            sleep(1ms)
            continue
        }
        
        // Pop fiber from front of queue (FIFO)
        fiber = scheduler.ready_queue.pop_front()
        lock.release()
        
        // Execute fiber
        execute_fiber_deterministic(scheduler, fiber)
    }
}
```

**Fiber Scheduling:**
```cpp
fn schedule_fiber(scheduler: &DeterministicScheduler, fiber: Fiber*) {
    // Assign deterministic ID
    fiber.id = scheduler.next_fiber_id.fetch_add(1, Ordering::SeqCst)
    
    // Add to trace
    scheduler.execution_trace.push(TraceEntry {
        fiber_id: fiber.id,
        timestamp: get_timestamp(),
        event: TraceEvent::FiberScheduled
    })
    
    // Add to ready queue (FIFO)
    lock = scheduler.ready_queue.lock()
    scheduler.ready_queue.push_back(fiber)
    lock.release()
}
```

**Fiber Execution:**
```cpp
fn execute_fiber_deterministic(scheduler: &DeterministicScheduler, fiber: Fiber*) {
    // Set current fiber
    scheduler.current_fiber = fiber
    
    // Update trace
    scheduler.execution_trace.push(TraceEntry {
        fiber_id: fiber.id,
        timestamp: get_timestamp(),
        event: TraceEvent::FiberResumed
    })
    
    // Switch to fiber context
    switch_to_fiber(fiber)
    
    // Fiber yielded or terminated
    if fiber.state == FiberState::Ready {
        // Fiber yielded, reschedule it
        schedule_fiber(scheduler, fiber)
    } else if fiber.state == FiberState::Terminated {
        // Fiber terminated, clean up
        scheduler.execution_trace.push(TraceEntry {
            fiber_id: fiber.id,
            timestamp: get_timestamp(),
            event: TraceEvent::FiberTerminated
        })
        
        // Wake up dependent fibers
        wake_dependencies(fiber)
        
        // Free fiber resources
        free_fiber(fiber)
    }
    
    scheduler.current_fiber = null
}
```

##### 2.2.2.1.3 Reproducibility Guarantees

The deterministic scheduler provides strong reproducibility guarantees through the following mechanisms:

**1. Deterministic Fiber Ordering:**
```cpp
// Fibers are scheduled in strict FIFO order
fn schedule_fiber_deterministic(scheduler: &DeterministicScheduler, fiber: Fiber*) {
    // Assign monotonically increasing ID
    fiber.id = scheduler.next_fiber_id.fetch_add(1, Ordering::SeqCst)
    
    // Add to end of queue (FIFO)
    scheduler.ready_queue.push_back(fiber)
}
```

**2. Deterministic Random Number Generation:**
```cpp
// XorShift64 with fixed seed
fn deterministic_rng_next(rng: &DeterministicRNG) -> u64 {
    x = rng.state
    x ^= x << 13
    x ^= x >> 7
    x ^= x << 17
    rng.state = x
    return x
}

// Initialize with fixed seed
fn init_deterministic_rng(seed: u64) -> DeterministicRNG {
    return DeterministicRNG {
        seed: seed,
        state: seed
    }
}
```

**3. Deterministic Message Ordering:**
```cpp
// Messages are delivered in FIFO order per actor
fn send_message_deterministic(
    scheduler: &DeterministicScheduler,
    actor: Actor*,
    message: Message
) {
    // Add to trace
    scheduler.execution_trace.push(TraceEntry {
        fiber_id: scheduler.current_fiber.id,
        timestamp: get_timestamp(),
        event: TraceEvent::MessageSent
    })
    
    // Add to actor's mailbox (FIFO)
    actor.mailbox.push_back(message)
    
    // Schedule actor if not already scheduled
    if actor.state == ActorState::Idle {
        schedule_fiber(scheduler, actor.fiber)
    }
}
```

**4. Deterministic I/O Simulation:**
```cpp
// Simulate I/O with deterministic delays
fn simulate_io_deterministic(
    scheduler: &DeterministicScheduler,
    duration: u64
) {
    // Use deterministic RNG to simulate I/O completion
    delay = deterministic_rng_next(&scheduler.rng) % duration
    
    // Record I/O event in trace
    scheduler.execution_trace.push(TraceEntry {
        fiber_id: scheduler.current_fiber.id,
        timestamp: get_timestamp(),
        event: TraceEvent::FiberSuspended
    })
    
    // Suspend fiber
    scheduler.current_fiber.state = FiberState::Suspended
    
    // Resume after deterministic delay
    sleep(delay)
    scheduler.current_fiber.state = FiberState::Ready
    schedule_fiber(scheduler, scheduler.current_fiber)
}
```

**5. Deterministic Preemption:**
```cpp
// Preempt fibers at deterministic intervals
fn check_preemption_deterministic(scheduler: &DeterministicScheduler) {
    // Use deterministic counter for preemption
    if scheduler.stats.fibers_executed % PREEMPTION_INTERVAL == 0 {
        // Preempt current fiber
        if scheduler.current_fiber != null {
            scheduler.current_fiber.state = FiberState::Ready
            schedule_fiber(scheduler, scheduler.current_fiber)
        }
    }
}
```

##### 2.2.2.1.4 Reproducibility Verification

The deterministic scheduler includes mechanisms to verify reproducibility:

**1. Execution Trace Comparison:**
```cpp
fn compare_traces(trace1: &Vec<TraceEntry>, trace2: &Vec<TraceEntry>) -> bool {
    if trace1.len() != trace2.len() {
        return false
    }
    
    for i in 0..trace1.len() {
        if trace1[i].fiber_id != trace2[i].fiber_id {
            return false
        }
        if trace1[i].event != trace2[i].event {
            return false
        }
    }
    
    return true
}
```

**2. Deterministic Seed Management:**
```cpp
fn set_deterministic_seed(scheduler: &DeterministicScheduler, seed: u64) {
    scheduler.rng = init_deterministic_rng(seed)
    scheduler.next_fiber_id.store(0, Ordering::SeqCst)
    scheduler.execution_trace.clear()
}
```

**3. Trace Export:**
```cpp
fn export_trace(scheduler: &DeterministicScheduler, path: &str) {
    file = open(path, "w")
    
    for entry in &scheduler.execution_trace {
        writeln!(file, "{},{},{},{}",
            entry.fiber_id,
            entry.timestamp,
            entry.event,
            entry.details
        )
    }
    
    file.close()
}
```

##### 2.2.2.1.5 Performance Characteristics

**Time Complexity:**
- **Schedule Fiber:** O(1) (push to vector)
- **Execute Fiber:** O(1) (pop from vector)
- **Trace Recording:** O(1) (push to vector)
- **Trace Comparison:** O(n) where n is trace length

**Space Complexity:**
- **Ready Queue:** O(m) where m is number of ready fibers
- **Execution Trace:** O(n) where n is total events
- **Total:** O(m + n)

**Throughput:**
- **Fiber Scheduling:** ~50ns per operation (slower than work-stealing)
- **Fiber Execution:** ~50ns per operation (no parallelism)
- **Overall:** ~100K fibers/second (single-threaded)

**Latency:**
- **Scheduling Latency:** ~50ns (FIFO queue)
- **Execution Latency:** ~50ns (no work stealing)
- **Worst Case:** ~100ns (queue contention)

**Scalability:**
- **Single-Threaded:** No parallelism, limited to single core
- **Poor Scaling:** Does not scale with core count
- **Debug Only:** Not intended for production use

**Memory Overhead:**
- **Per Fiber:** ~8KB (4KB stack + metadata)
- **Trace Buffer:** ~1MB per 100K events
- **Total (1M fibers):** ~8GB + trace overhead

**Reproducibility:**
- **Deterministic Ordering:** 100% (FIFO guarantees)
- **Deterministic RNG:** 100% (fixed seed)
- **Deterministic I/O:** 100% (simulated delays)
- **Overall:** 100% reproducible execution

* EMS-REQ-022:* THE system SHALL implement deterministic scheduler with FIFO ordering.
  - Priority:* High
  - Verification Method:* Test
  - Rationale:* Ensures reproducible execution for debugging
  - Dependencies:* EMS-INV-005, EMS-INV-010
  - Traceability:* Section 2.2.2.1 (Deterministic Scheduler Algorithm Implementation)

* EMS-REQ-023:* THE system SHALL provide deterministic random number generation with fixed seed.
  - Priority:* High
  - Verification Method:* Test
  - Rationale:* Ensures reproducible non-deterministic operations
  - Dependencies:* EMS-INV-005
  - Traceability:* Section 2.2.2.1.3 (Reproducibility Guarantees)

* EMS-REQ-024:* THE system SHALL maintain execution trace for reproducibility verification.
  - Priority:* Medium
  - Verification Method:* Test
  - Rationale:* Enables comparison of execution across runs
  - Dependencies:* EMS-INV-005
  - Traceability:* Section 2.2.2.1.4 (Reproducibility Verification)

* EMS-REQ-025:* THE system SHALL guarantee 100% reproducible execution with deterministic scheduler.
  - Priority:* High
  - Verification Method:* Test
  - Rationale:* Enables reliable debugging and testing
  - Dependencies:* EMS-INV-005
  - Traceability:* Section 2.2.2.1.5 (Performance Characteristics)

#### 2.2.3 Build Flag Specification

The build system provides a `--debug-scheduler` flag to control scheduler selection at link time.

* EMS-INV-006:* THE system SHALL provide --debug-scheduler build flag for deterministic scheduler builds.

* Build Flag: `--debug-scheduler`

**Default Behavior (No Flag):**
- Links work-stealing scheduler
- Production configuration
- Optimal performance
- No deterministic scheduler code in binary

**With `--debug-scheduler` Flag:**
- Links deterministic scheduler
- Debug/test configuration
- Reproducible execution
- No work-stealing scheduler code in binary

* Usage Guidelines:
- **Production Builds:** Do NOT use `--debug-scheduler` flag
- **Debug Builds:** Use `--debug-scheduler` flag for reproducible debugging
- **Test Builds:** Use `--debug-scheduler` flag for deterministic test execution
- **CI/CD:** Test both configurations (with and without flag)

* Rationale:* Build flag provides clear, explicit control over scheduler selection. Link-time replacement ensures only one scheduler is linked, avoiding dead code.

* EMS-REQ-008:* THE system SHALL link only work-stealing scheduler when --debug-scheduler flag is not specified.
  - Priority:* Critical
  - Verification Method:* Test
  - Rationale:* Ensures production builds use optimal scheduler
  - Dependencies:* EMS-INV-006
  - Traceability:* Section 2.2.3 (Build Flag Specification)

* EMS-REQ-009:* THE system SHALL link only deterministic scheduler when --debug-scheduler flag is specified.
  - Priority:* High
  - Verification Method:* Test
  - Rationale:* Ensures debug builds use deterministic scheduler
  - Dependencies:* EMS-INV-006
  - Traceability:* Section 2.2.3 (Build Flag Specification)

* EMS-REQ-010:* THE system SHALL NOT support mixing schedulers in the same binary.
  - Priority:* Critical
  - Verification Method:* Test
  - Rationale:* Prevents dead code and ensures clear scheduler selection
  - Dependencies:* EMS-INV-006
  - Traceability:* Section 2.2.3 (Build Flag Specification)

#### 2.2.4 Implicit Suspension Protocol

Morph eliminates `async`/`await` keywords via **IO-Aware Yielding**.

* EMS-INV-005:* THE system SHALL implement IO-aware yielding for implicit suspension.

* Protocol:*

1. **The Call:** Agent writes `file.read()`
2. **The Trap:** The Runtime intercepts the syscall
3. **The Registration:** The Runtime registers a File Descriptor with the OS Poller (`io_uring`/`kqueue`/`IOCP`)
4. **The Switch:** The Runtime saves the current Fiber state and immediately switches to the Executor to the next Fiber in the Ready Queue
5. **The Resume:** When the OS signals data availability, the Poller moves the original Fiber back to the Ready Queue

* Rationale:* Zero blocking. The CPU never idles waiting for I/O.

* EMS-REQ-015:* THE system SHALL implement IO-aware yielding for implicit suspension.
  - Priority:* Critical
  - Verification Method:* Test
  - Rationale:* Eliminates blocking and maximizes CPU utilization
  - Dependencies:* EMS-INV-005
  - Traceability:* Section 2.2.4 (Implicit Suspension Protocol)

#### 2.2.5 Preemption (The "Anti-Hang" Mechanism)

* EMS-INV-006:* THE system SHALL implement preemption to prevent fiber starvation.

* Problem:* A Fiber entering `while(true) {}` could starve other Fibers on that core.

* Solution:* The Compiler injects **Checkpoints** at loop headers and function entries.

* Runtime Logic:*
```cpp
// Pseudo-code injected by compiler
if (runtime_ticks() > time_slice_limit) {
    yield();
}
```

* Rationale:* Guarantees system responsiveness (especially UI) even if Agent writes inefficient algorithms.

* EMS-REQ-007:* THE system SHALL inject preemption checkpoints at loop headers and function entries.
  - Priority:* High
  - Verification Method:* Test
  - Rationale:* Prevents fiber starvation and ensures responsiveness
  - Dependencies:* EMS-INV-006
  - Traceability:* Section 2.2.5 (Preemption)

### 2.3 The Actor Model (`logic`)

#### 2.3.1 Actor Structure

A `logic` block compiles into a **Stateful Fiber**.

* EMS-INV-007:* THE system SHALL compile `logic` blocks into stateful fibers.

* Components:
- **Mailbox:** A lock-free MPSC (Multi-Producer, Single-Consumer) queue
- **Behavior:** The Fiber loops efficiently:
   - If Mailbox is empty $\rightarrow$ Fiber Suspend (0% CPU)
   - If Message arrives $\rightarrow$ Fiber Wakeup
   - **Processing:** Messages are processed sequentially. This guarantees **Data Race Freedom** within the Actor

* EMS-REQ-008:* THE system SHALL compile `logic` blocks into stateful fibers with MPSC mailboxes.
  - Priority:* Critical
  - Verification Method:* Test
  - Rationale:* Enables actor model with data race freedom
  - Dependencies:* EMS-INV-007
  - Traceability:* Section 2.3.1 (Actor Structure)

#### 2.3.1.1 Actor Implementation Details

The actor model is implemented as stateful fibers with messaging infrastructure.

* EMS-INV-011:* THE system SHALL implement actors as stateful fibers with mailboxes and supervisors.

##### 2.3.1.1.1 Actor Data Structures

**Actor Structure:**
```cpp
struct Actor {
    // Unique actor ID
    id: u64
    
    // Actor state (user-defined)
    state: void*
    
    // Actor fiber
    fiber: Fiber*
    
    // MPSC mailbox for receiving messages
    mailbox: Mailbox
    
    // Supervisor for failure handling
    supervisor: Actor*
    
    // Child actors
    children: Vec<Actor*>
    
    // Actor state
    actor_state: ActorState
    
    // Message handler function
    handler: fn(&Actor, Message) -> void
}

enum ActorState {
    Idle,      // Not processing messages
    Running,   // Processing messages
    Suspended,  // Suspended (waiting for messages)
    Terminated  // Actor terminated
}

struct Mailbox {
    // Lock-free MPSC queue
    queue: MPSCQueue<Message>
    
    // Number of messages in mailbox
    count: AtomicUsize
    
    // Maximum mailbox size (optional)
    max_size: usize
}

struct Message {
    // Message type
    type: MessageType
    
    // Message payload
    payload: void*
    
    // Sender actor (optional)
    sender: Actor*
    
    // Timestamp
    timestamp: u64
}
```

##### 2.3.1.1.2 Actor Creation and Lifecycle

**Actor Creation:**
```cpp
fn spawn_actor(
    supervisor: Actor*,
    handler: fn(&Actor, Message) -> void,
    initial_state: void*
) -> Actor* {
    // Create new actor
    actor = allocate_actor()
    
    // Assign unique ID
    actor.id = generate_actor_id()
    
    // Set initial state
    actor.state = initial_state
    
    // Set supervisor
    actor.supervisor = supervisor
    
    // Create mailbox
    actor.mailbox = create_mailbox()
    
    // Create fiber for actor
    actor.fiber = create_fiber(actor_main, actor)
    
    // Set message handler
    actor.handler = handler
    
    // Set initial state
    actor.actor_state = ActorState::Idle
    
    // Add to supervisor's children
    if supervisor != null {
        supervisor.children.push(actor)
    }
    
    // Schedule actor fiber
    schedule_fiber(actor.fiber)
    
    return actor
}
```

**Actor Main Loop:**
```cpp
fn actor_main(actor: &Actor) {
    loop {
        // Wait for message
        message = actor.mailbox.pop()
        
        if message == null {
            // No messages, suspend
            actor.actor_state = ActorState::Suspended
            suspend_fiber(actor.fiber)
            continue
        }
        
        // Process message
        actor.actor_state = ActorState::Running
        actor.handler(actor, message)
        
        // Check for termination
        if message.type == MessageType::Terminate {
            actor.actor_state = ActorState::Terminated
            break
        }
        
        actor.actor_state = ActorState::Idle
    }
    
    // Cleanup
    cleanup_actor(actor)
}
```

**Actor Termination:**
```cpp
fn terminate_actor(actor: &Actor) {
    // Send termination message
    terminate_msg = Message {
        type: MessageType::Terminate,
        payload: null,
        sender: null,
        timestamp: get_timestamp()
    }
    
    actor.mailbox.push(terminate_msg)
    
    // Wait for actor to terminate
    while actor.actor_state != ActorState::Terminated {
        sleep(1ms)
    }
    
    // Remove from supervisor's children
    if actor.supervisor != null {
        actor.supervisor.children.remove(actor)
    }
    
    // Terminate all children
    for child in &actor.children {
        terminate_actor(child)
    }
    
    // Free resources
    free_actor(actor)
}
```

##### 2.3.1.1.3 Message Passing Implementation

**Sending Messages:**
```cpp
fn send_message(
    sender: Actor*,
    receiver: Actor*,
    message_type: MessageType,
    payload: void*
) {
    // Create message
    message = Message {
        type: message_type,
        payload: payload,
        sender: sender,
        timestamp: get_timestamp()
    }
    
    // Push to receiver's mailbox
    receiver.mailbox.push(message)
    
    // Wake up receiver if suspended
    if receiver.actor_state == ActorState::Suspended {
        resume_fiber(receiver.fiber)
    }
}
```

**Message Processing:**
```cpp
fn process_messages(actor: &Actor) {
    loop {
        // Pop message from mailbox
        message = actor.mailbox.pop()
        
        if message == null {
            // No more messages
            break
        }
        
        // Call message handler
        actor.handler(actor, message)
    }
}
```

##### 2.3.1.1.4 Mailbox Implementation Details

**MPSC Queue Implementation:**
```cpp
struct MPSCQueue<T> {
    // Head pointer (consumer)
    head: AtomicPtr<Node<T>>
    
    // Tail pointer (producer)
    tail: AtomicPtr<Node<T>>
    
    // Stub node for initialization
    stub: Node<T>
}

struct Node<T> {
    // Next pointer
    next: AtomicPtr<Node<T>>
    
    // Value
    value: T
}

fn create_mpsc_queue<T>() -> MPSCQueue<T> {
    queue = MPSCQueue<T> {
        head: AtomicPtr::new(&queue.stub),
        tail: AtomicPtr::new(&queue.stub)
    }
    
    // Initialize stub
    queue.stub.next.store(null, Ordering::Relaxed)
    
    return queue
}

fn push_mpsc<T>(queue: &MPSCQueue<T>, value: T) {
    // Create new node
    node = allocate_node(value)
    node.next.store(null, Ordering::Relaxed)
    
    // Get current tail
    prev_tail = queue.tail.load(Ordering::Acquire)
    
    // Try to publish new node
    loop {
        if queue.tail.compare_exchange_weak(
            prev_tail,
            node,
            Ordering::Release,
            Ordering::Acquire
        ) {
            // Successfully published
            prev_tail.next.store(node, Ordering::Release)
            break
        }
        
        // Retry with new tail
        prev_tail = queue.tail.load(Ordering::Acquire)
    }
}

fn pop_mpsc<T>(queue: &MPSCQueue<T>) -> T {
    // Get current head
    head = queue.head.load(Ordering::Acquire)
    next = head.next.load(Ordering::Acquire)
    
    if next == null {
        // Queue is empty
        return null
    }
    
    // Try to advance head
    if queue.head.compare_exchange_weak(
        head,
        next,
        Ordering::AcqRel,
        Ordering::Acquire
    ) {
        // Successfully advanced
        value = next.value
        free_node(head)
        return value
    }
    
    // Retry
    return null
}
```

**Mailbox with Bounded Size:**
```cpp
fn push_mailbox_bounded(mailbox: &Mailbox, message: Message) -> bool {
    // Check if mailbox is full
    if mailbox.max_size > 0 {
        current_count = mailbox.count.load(Ordering::Acquire)
        if current_count >= mailbox.max_size {
            return false  // Mailbox full
        }
    }
    
    // Push message
    push_mpsc(&mailbox.queue, message)
    
    // Increment count
    mailbox.count.fetch_add(1, Ordering::Release)
    
    return true
}
```

##### 2.3.1.1.5 Supervision Tree Implementation

**Supervisor Structure:**
```cpp
struct Supervisor {
    // Supervisor actor
    actor: Actor*
    
    // Supervision strategy
    strategy: SupervisionStrategy
    
    // Maximum restart attempts
    max_restarts: usize
    
    // Restart delay (milliseconds)
    restart_delay: u64
}

enum SupervisionStrategy {
    OneForOne,   // Restart only failed child
    OneForAll,   // Restart all children
    RestForOne,  // Restart failed child and siblings
    RestForAll    // Restart all children
}
```

**Failure Detection:**
```cpp
fn handle_actor_panic(actor: &Actor) {
    // Notify supervisor
    if actor.supervisor != null {
        supervisor = actor.supervisor
        
        // Execute supervision strategy
        match supervisor.strategy {
            SupervisionStrategy::OneForOne => {
                // Restart only failed child
                restart_actor(actor)
            },
            SupervisionStrategy::OneForAll => {
                // Restart all children
                for child in &supervisor.actor.children {
                    restart_actor(child)
                }
            },
            SupervisionStrategy::RestForOne => {
                // Restart failed child and siblings
                for child in &supervisor.actor.children {
                    if child.id == actor.id || child.actor_state == ActorState::Running {
                        restart_actor(child)
                    }
                }
            },
            SupervisionStrategy::RestForAll => {
                // Restart all children
                for child in &supervisor.actor.children {
                    restart_actor(child)
                }
            }
        }
    }
}
```

**Actor Restart:**
```cpp
fn restart_actor(actor: &Actor) {
    // Terminate actor
    terminate_actor(actor)
    
    // Wait for termination
    sleep(actor.supervisor.restart_delay)
    
    // Spawn new actor with same state
    new_actor = spawn_actor(
        actor.supervisor,
        actor.handler,
        actor.state
    )
    
    // Replace in supervisor's children
    if actor.supervisor != null {
        index = actor.supervisor.children.find(actor)
        actor.supervisor.children[index] = new_actor
    }
}
```

**Supervision Tree Creation:**
```cpp
fn create_supervision_tree(
    root_handler: fn(&Actor, Message) -> void,
    root_state: void*
) -> Actor* {
    // Create root supervisor
    root = spawn_actor(null, root_handler, root_state)
    
    return root
}

fn spawn_child(
    parent: &Actor,
    child_handler: fn(&Actor, Message) -> void,
    child_state: void*
) -> Actor* {
    // Spawn child actor
    child = spawn_actor(parent, child_handler, child_state)
    
    return child
}
```

* EMS-REQ-026:* THE system SHALL implement actor creation with unique IDs and supervisors.
  - Priority:* Critical
  - Verification Method:* Test
  - Rationale:* Enables actor model with failure recovery
  - Dependencies:* EMS-INV-011
  - Traceability:* Section 2.3.1.1 (Actor Implementation Details)

* EMS-REQ-027:* THE system SHALL implement MPSC mailbox for message passing.
  - Priority:* Critical
  - Verification Method:* Test
  - Rationale:* Ensures lock-free message delivery
  - Dependencies:* EMS-INV-011
  - Traceability:* Section 2.3.1.1.4 (Mailbox Implementation Details)

* EMS-REQ-028:* THE system SHALL implement supervision trees with multiple strategies.
  - Priority:* High
  - Verification Method:* Test
  - Rationale:* Enables flexible failure recovery
  - Dependencies:* EMS-INV-011
  - Traceability:* Section 2.3.1.1.5 (Supervision Tree Implementation)

#### 2.3.2 Supervision Trees

* EMS-INV-008:* THE system SHALL implement supervision trees for actor failure recovery.

* Components:
- **Concept:** Actors form a parent-child hierarchy
- **Failure Mode:** If an Actor panics (e.g., asserts fail), the Fiber terminates
- **Recovery:** The Runtime intercepts the panic signal and notifies the Supervisor
- **Strategy Execution:**
   - `OneForOne`: The Supervisor spawns a fresh instance of the failed Actor (fresh memory arena)
   - `OneForAll`: The Supervisor terminates and restarts all sibling Actors

* Rationale:* "Let It Crash." Agents cannot predict every error. The system must self-heal.

* EMS-REQ-009:* THE system SHALL implement supervision trees with OneForOne and OneForAll strategies.
  - Priority:* High
  - Verification Method:* Test
  - Rationale:* Enables self-healing systems
  - Dependencies:* EMS-INV-008
  - Traceability:* Section 2.3.2 (Supervision Trees)

#### 2.3.3 Fiber Implementation Details

The fiber is the fundamental execution unit in Morph, providing stackful coroutine execution with efficient context switching.

* EMS-INV-012:* THE system SHALL implement fibers as stackful coroutines with efficient context switching.

##### 2.3.3.1 Fiber Data Structures

**Fiber Structure:**
```cpp
struct Fiber {
    // Unique fiber ID
    id: u64
    
    // Fiber state
    state: FiberState
    
    // Stack pointer
    stack_ptr: u8*
    
    // Stack size
    stack_size: usize
    
    // Stack limit (for overflow detection)
    stack_limit: usize
    
    // Saved context (registers)
    context: FiberContext
    
    // Fiber function
    entry_point: fn() -> void
    
    // Argument to entry point
    argument: void*
    
    // Parent fiber (for async let)
    parent: Fiber*
    
    // Dependency list (fibers waiting for this one)
    dependencies: AtomicPtr<FiberList>
    
    // Future slot (for async let)
    future_slot: FutureSlot*
    
    // Executor running this fiber
    executor: Executor*
    
    // Preemption counter
    preemption_counter: u64
}

struct FiberContext {
    // Saved stack pointer
    rsp: u64
    
    // Saved instruction pointer
    rip: u64
    
    // Saved base pointer
    rbp: u64
    
    // Saved general-purpose registers
    rbx: u64
    rcx: u64
    rdx: u64
    rsi: u64
    rdi: u64
    r8: u64
    r9: u64
    r10: u64
    r11: u64
    r12: u64
    r13: u64
    r14: u64
    r15: u64
    
    // Saved SSE/AVX registers
    xmm0: u128
    xmm1: u128
    xmm2: u128
    xmm3: u128
    xmm4: u128
    xmm5: u128
    xmm6: u128
    xmm7: u128
    xmm8: u128
    xmm9: u128
    xmm10: u128
    xmm11: u128
    xmm12: u128
    xmm13: u128
    xmm14: u128
    xmm15: u128
}

struct FiberList {
    // Head of fiber list
    head: Fiber*
    
    // Tail of fiber list
    tail: Fiber*
    
    // Number of fibers in list
    count: usize
}

struct FutureSlot<T> {
    // Future state
    state: FutureState
    
    // Result value
    value: T
    
    // Error message (if poisoned)
    error: Option<str>
    
    // Fibers waiting for this future
    waiters: FiberList
}

enum FutureState {
    Pending,   // Fiber still running
    Ready,     // Value available
    Poisoned  // Fiber panicked
}
```

##### 2.3.3.2 Fiber Creation and Scheduling

**Fiber Creation:**
```cpp
fn create_fiber(
    entry_point: fn() -> void,
    argument: void*
) -> Fiber* {
    // Allocate fiber
    fiber = allocate_fiber()
    
    // Assign unique ID
    fiber.id = generate_fiber_id()
    
    // Allocate stack (4KB initial)
    fiber.stack_size = INITIAL_STACK_SIZE  // 4KB
    fiber.stack_ptr = allocate_stack(fiber.stack_size)
    fiber.stack_limit = fiber.stack_ptr + fiber.stack_size
    
    // Set initial state
    fiber.state = FiberState::Ready
    
    // Set entry point
    fiber.entry_point = entry_point
    fiber.argument = argument
    
    // Initialize context
    fiber.context = FiberContext {
        rsp: 0,
        rip: 0,
        rbp: 0,
        rbx: 0,
        rcx: 0,
        rdx: 0,
        rsi: 0,
        rdi: 0,
        r8: 0,
        r9: 0,
        r10: 0,
        r11: 0,
        r12: 0,
        r13: 0,
        r14: 0,
        r15: 0,
        xmm0: 0,
        xmm1: 0,
        xmm2: 0,
        xmm3: 0,
        xmm4: 0,
        xmm5: 0,
        xmm6: 0,
        xmm7: 0,
        xmm8: 0,
        xmm9: 0,
        xmm10: 0,
        xmm11: 0,
        xmm12: 0,
        xmm13: 0,
        xmm14: 0,
        xmm15: 0
    }
    
    // Initialize dependencies
    fiber.dependencies = AtomicPtr::new(null)
    fiber.future_slot = null
    
    // Set preemption counter
    fiber.preemption_counter = 0
    
    return fiber
}
```

**Fiber Scheduling:**
```cpp
fn schedule_fiber(fiber: Fiber*) {
    // Set fiber state to ready
    fiber.state = FiberState::Ready
    
    // Add to executor's ready queue
    executor = get_current_executor()
    executor.deque.push_bottom(fiber)
}

fn schedule_fiber_with_parent(fiber: Fiber*, parent: Fiber*) {
    // Set parent fiber
    fiber.parent = parent
    
    // Schedule fiber
    schedule_fiber(fiber)
}
```

**Fiber Execution:**
```cpp
fn execute_fiber(executor: &Executor, fiber: Fiber*) {
    // Set current fiber
    executor.current_fiber = fiber
    
    // Set fiber state to running
    fiber.state = FiberState::Running
    fiber.executor = executor
    
    // Switch to fiber context
    switch_to_fiber(fiber)
    
    // Fiber returns when it yields or terminates
    // (handled by switch_to_fiber)
}
```

##### 2.3.3.3 Stack Management

**Stack Allocation:**
```cpp
const INITIAL_STACK_SIZE: usize = 4096  // 4KB
const STACK_GROWTH_FACTOR: usize = 2      // Double on overflow
const MAX_STACK_SIZE: usize = 1048576  // 1MB maximum

fn allocate_stack(size: usize) -> u8* {
    // Allocate stack memory
    stack = allocate_memory(size)
    
    // Align stack to 16 bytes
    aligned_stack = align_pointer(stack, 16)
    
    return aligned_stack
}
```

**Stack Growth:**
```cpp
fn check_stack_overflow(fiber: &Fiber) -> bool {
    // Check if stack pointer is near limit
    current_sp = get_stack_pointer()
    remaining = fiber.stack_limit - current_sp
    
    // Trigger growth if less than 1KB remaining
    return remaining < 1024
}

fn grow_stack(fiber: &Fiber) {
    // Calculate new stack size
    new_size = fiber.stack_size * STACK_GROWTH_FACTOR
    
    // Check maximum size
    if new_size > MAX_STACK_SIZE {
        panic("Stack overflow: maximum stack size exceeded")
    }
    
    // Allocate new stack
    new_stack = allocate_stack(new_size)
    
    // Copy old stack to new stack
    copy_memory(new_stack, fiber.stack_ptr, fiber.stack_size)
    
    // Update fiber
    old_stack = fiber.stack_ptr
    fiber.stack_ptr = new_stack
    fiber.stack_size = new_size
    fiber.stack_limit = new_stack + new_size
    
    // Free old stack
    free_stack(old_stack)
}
```

**Stack Overflow Detection:**
```cpp
fn handle_stack_overflow(fiber: &Fiber) {
    // Check for overflow
    if check_stack_overflow(fiber) {
        // Grow stack
        grow_stack(fiber)
        
        // Log warning
        log_warning("Fiber {} stack grown to {} bytes", fiber.id, fiber.stack_size)
    }
}
```

##### 2.3.3.4 Suspension and Resumption

**Fiber Suspension:**
```cpp
fn suspend_fiber(fiber: &Fiber) {
    // Save current context
    save_context(&fiber.context)
    
    // Set fiber state to suspended
    fiber.state = FiberState::Suspended
    
    // Get executor
    executor = fiber.executor
    
    // Switch back to executor
    switch_to_executor(executor)
}

fn suspend_fiber_with_result(fiber: &Fiber*, result: void*) {
    // Save result to future slot
    if fiber.future_slot != null {
        fiber.future_slot.value = result
        fiber.future_slot.state = FutureState::Ready
        
        // Wake up waiters
        wake_dependencies(fiber)
    }
    
    // Suspend fiber
    suspend_fiber(fiber)
}
```

**Fiber Resumption:**
```cpp
fn resume_fiber(fiber: &Fiber*) {
    // Set fiber state to ready
    fiber.state = FiberState::Ready
    
    // Schedule fiber
    schedule_fiber(fiber)
}

fn resume_fiber_from_mailbox(actor: &Actor) {
    // Get actor's fiber
    fiber = actor.fiber
    
    // Resume fiber
    resume_fiber(fiber)
}
```

**Dependency Management:**
```cpp
fn add_dependency(fiber: Fiber*, waiter: Fiber*) {
    // Add waiter to dependency list
    list = fiber.dependencies.load(Ordering::Acquire)
    
    if list == null {
        list = allocate_fiber_list()
        fiber.dependencies.store(list, Ordering::Release)
    }
    
    // Add waiter to list
    list.tail.next = waiter
    list.tail.count += 1
}

fn wake_dependencies(fiber: Fiber*) {
    // Get dependency list
    list = fiber.dependencies.load(Ordering::Acquire)
    
    if list == null {
        return
    }
    
    // Wake all waiting fibers
    current = list.head
    while current != null {
        resume_fiber(current)
        current = current.next
    }
    
    // Clear dependency list
    free_fiber_list(list)
    fiber.dependencies.store(null, Ordering::Release)
}
```

##### 2.3.3.5 Context Switching

**Context Switch Implementation:**
```cpp
fn switch_to_fiber(fiber: &Fiber) {
    // Get current executor
    executor = fiber.executor
    
    // Save current fiber context
    current_fiber = executor.current_fiber
    if current_fiber != null {
        save_context(&current_fiber.context)
    }
    
    // Set new fiber as current
    executor.current_fiber = fiber
    
    // Restore new fiber context
    restore_context(&fiber.context)
    
    // Jump to new fiber
    jump_to_fiber(fiber)
}

fn switch_to_executor(executor: &Executor) {
    // Save current fiber context
    current_fiber = executor.current_fiber
    if current_fiber != null {
        save_context(&current_fiber.context)
    }
    
    // Clear current fiber
    executor.current_fiber = null
    
    // Restore executor context
    restore_executor_context(executor)
    
    // Jump to executor loop
    jump_to_executor(executor)
}
```

**Context Save/Restore:**
```cpp
fn save_context(context: &FiberContext) {
    // Save stack pointer
    context.rsp = get_stack_pointer()
    
    // Save instruction pointer
    context.rip = get_instruction_pointer()
    
    // Save base pointer
    context.rbp = get_base_pointer()
    
    // Save general-purpose registers
    context.rbx = get_register(RBX)
    context.rcx = get_register(RCX)
    context.rdx = get_register(RDX)
    context.rsi = get_register(RSI)
    context.rdi = get_register(RDI)
    context.r8 = get_register(R8)
    context.r9 = get_register(R9)
    context.r10 = get_register(R10)
    context.r11 = get_register(R11)
    context.r12 = get_register(R12)
    context.r13 = get_register(R13)
    context.r14 = get_register(R14)
    context.r15 = get_register(R15)
    
    // Save SSE/AVX registers
    context.xmm0 = get_xmm_register(XMM0)
    context.xmm1 = get_xmm_register(XMM1)
    context.xmm2 = get_xmm_register(XMM2)
    context.xmm3 = get_xmm_register(XMM3)
    context.xmm4 = get_xmm_register(XMM4)
    context.xmm5 = get_xmm_register(XMM5)
    context.xmm6 = get_xmm_register(XMM6)
    context.xmm7 = get_xmm_register(XMM7)
    context.xmm8 = get_xmm_register(XMM8)
    context.xmm9 = get_xmm_register(XMM9)
    context.xmm10 = get_xmm_register(XMM10)
    context.xmm11 = get_xmm_register(XMM11)
    context.xmm12 = get_xmm_register(XMM12)
    context.xmm13 = get_xmm_register(XMM13)
    context.xmm14 = get_xmm_register(XMM14)
    context.xmm15 = get_xmm_register(XMM15)
}

fn restore_context(context: &FiberContext) {
    // Restore stack pointer
    set_stack_pointer(context.rsp)
    
    // Restore instruction pointer
    set_instruction_pointer(context.rip)
    
    // Restore base pointer
    set_base_pointer(context.rbp)
    
    // Restore general-purpose registers
    set_register(RBX, context.rbx)
    set_register(RCX, context.rcx)
    set_register(RDX, context.rdx)
    set_register(RSI, context.rsi)
    set_register(RDI, context.rdi)
    set_register(R8, context.r8)
    set_register(R9, context.r9)
    set_register(R10, context.r10)
    set_register(R11, context.r11)
    set_register(R12, context.r12)
    set_register(R13, context.r13)
    set_register(R14, context.r14)
    set_register(R15, context.r15)
    
    // Restore SSE/AVX registers
    set_xmm_register(XMM0, context.xmm0)
    set_xmm_register(XMM1, context.xmm1)
    set_xmm_register(XMM2, context.xmm2)
    set_xmm_register(XMM3, context.xmm3)
    set_xmm_register(XMM4, context.xmm4)
    set_xmm_register(XMM5, context.xmm5)
    set_xmm_register(XMM6, context.xmm6)
    set_xmm_register(XMM7, context.xmm7)
    set_xmm_register(XMM8, context.xmm8)
    set_xmm_register(XMM9, context.xmm9)
    set_xmm_register(XMM10, context.xmm10)
    set_xmm_register(XMM11, context.xmm11)
    set_xmm_register(XMM12, context.xmm12)
    set_xmm_register(XMM13, context.xmm13)
    set_xmm_register(XMM14, context.xmm14)
    set_xmm_register(XMM15, context.xmm15)
}
```

**Assembly-Level Context Switch:**
```asm
; x86_64 context switch assembly
switch_to_fiber:
    ; Save current context
    push rbp
    mov rbp, rsp
    push rbx
    push r12
    push r13
    push r14
    push r15
    sub rsp, 128  ; Space for SSE registers
    movdqu [rsp], xmm0
    movdqu [rsp+16], xmm1
    movdqu [rsp+32], xmm2
    movdqu [rsp+48], xmm3
    movdqu [rsp+64], xmm4
    movdqu [rsp+80], xmm5
    movdqu [rsp+96], xmm6
    movdqu [rsp+112], xmm7
    movdqu [rsp+128], xmm8
    movdqu [rsp+144], xmm9
    movdqu [rsp+160], xmm10
    movdqu [rsp+176], xmm11
    movdqu [rsp+192], xmm12
    movdqu [rsp+208], xmm13
    movdqu [rsp+224], xmm14
    movdqu [rsp+240], xmm15
    
    ; Load new fiber context
    mov rax, [new_fiber_context]
    mov rbp, [rax]
    mov rbx, [rax+8]
    mov r12, [rax+16]
    mov r13, [rax+24]
    mov r14, [rax+32]
    mov r15, [rax+40]
    
    ; Restore new context
    movdqu xmm0, [rax+48]
    movdqu xmm1, [rax+64]
    movdqu xmm2, [rax+80]
    movdqu xmm3, [rax+96]
    movdqu xmm4, [rax+112]
    movdqu xmm5, [rax+128]
    movdqu xmm6, [rax+144]
    movdqu xmm7, [rax+160]
    movdqu xmm8, [rax+176]
    movdqu xmm9, [rax+192]
    movdqu xmm10, [rax+208]
    movdqu xmm11, [rax+224]
    movdqu xmm12, [rax+240]
    movdqu xmm13, [rax+256]
    movdqu xmm14, [rax+272]
    movdqu xmm15, [rax+288]
    
    ; Set new stack pointer
    mov rsp, [rax]
    
    ; Jump to new fiber
    jmp [new_fiber_rip]
```

##### 2.3.3.6 Performance Characteristics

**Time Complexity:**
- **Fiber Creation:** O(1) (allocation and initialization)
- **Fiber Scheduling:** O(1) (push to deque)
- **Context Switch:** O(1) (register save/restore)
- **Stack Growth:** O(n) where n is stack size (copy operation)
- **Dependency Wakeup:** O(m) where m is number of waiters

**Space Complexity:**
- **Per Fiber:** O(s) where s is stack size
- **Total:** O(n * s) where n is number of fibers

**Throughput:**
- **Fiber Creation:** ~100ns per fiber
- **Fiber Scheduling:** ~10ns per operation
- **Context Switch:** ~50ns per switch
- **Overall:** ~1M fibers/second

**Latency:**
- **Creation Latency:** ~100ns (allocation)
- **Scheduling Latency:** ~10ns (queue push)
- **Context Switch Latency:** ~50ns (register save/restore)
- **Worst Case:** ~200ns (stack growth + context switch)

**Memory Overhead:**
- **Per Fiber:** ~8KB (4KB stack + metadata)
- **Stack Growth:** Additional 4KB per growth
- **Total (1M fibers):** ~8GB + growth overhead

**Cache Locality:**
- **Excellent:** Fibers tend to stay on same executor
- **Good:** Stack growth preserves locality
- **Context Switch:** Minimal cache misses (register save/restore)

**Scalability:**
- **Linear Scaling:** Throughput scales linearly with core count
- **Optimal:** 1 executor per physical core
- **Stack Management:** Efficient growth prevents excessive memory usage

* EMS-REQ-029:* THE system SHALL implement fiber creation with efficient context switching.
  - Priority:* Critical
  - Verification Method:* Test
  - Rationale:* Enables high-performance concurrency
  - Dependencies:* EMS-INV-012
  - Traceability:* Section 2.3.3 (Fiber Implementation Details)

* EMS-REQ-030:* THE system SHALL implement stack management with automatic growth.
  - Priority:* High
  - Verification Method:* Test
  - Rationale:* Prevents stack overflow and enables deep recursion
  - Dependencies:* EMS-INV-012
  - Traceability:* Section 2.3.3.3 (Stack Management)

* EMS-REQ-031:* THE system SHALL implement fiber suspension and resumption with efficient context switching.
  - Priority:* Critical
  - Verification Method:* Test
  - Rationale:* Enables efficient fiber scheduling and I/O handling
  - Dependencies:* EMS-INV-012
  - Traceability:* Section 2.3.3.4 (Suspension and Resumption)

* EMS-REQ-032:* THE system SHALL implement context switching with minimal overhead.
  - Priority:* High
  - Verification Method:* Test
  - Rationale:* Ensures efficient fiber execution
  - Dependencies:* EMS-INV-012
  - Traceability:* Section 2.3.3.5 (Context Switching)

### 2.4 Dataflow Parallelism (`async let`)

`async let x = foo()` is sugar for spawning an **Ephemeral Fiber**.

* EMS-INV-009:* THE system SHALL implement `async let` as ephemeral fiber spawning.

* Components:
- **Storage:** The return value is stored in a `Future<T>` slot in the Parent Fiber's stack frame
- **State:** The Future has three states: `Pending`, `Ready`, `Poisoned` (Panic)

* EMS-REQ-010:* THE system SHALL implement `async let` as ephemeral fiber spawning with Future slots.
  - Priority:* High
  - Verification Method:* Test
  - Rationale:* Enables dataflow parallelism
  - Dependencies:* EMS-INV-009
  - Traceability:* Section 2.4.1 (Implementation)

#### 2.4.2 Wait-by-Necessity

* EMS-INV-010:* THE system SHALL implement wait-by-necessity for Future resolution.

* Mechanism:* When code accesses `x`:
- **Case 1 (Ready):** Read value immediately (0 cost)
- **Case 2 (Pending):** The Parent Fiber yields (suspends). It is added to the "Dependency List" of the Child Fiber
- **Case 3 (Poisoned):** The Parent Fiber panics (propagating error)

* Wakeup:* When the Child Fiber finishes, it writes the result to the `Future` slot and wakes up the Parent Fiber.

* EMS-REQ-011:* THE system SHALL implement wait-by-necessity for Future resolution.
  - Priority:* High
  - Verification Method:* Test
  - Rationale:* Enables efficient dataflow parallelism
  - Dependencies:* EMS-INV-010
  - Traceability:* Section 2.4.2 (Wait-by-Necessity)

### 2.5 Memory Management

#### 2.5.1 The Unified Allocator

Morph uses a **Unified Global Allocator** with type-level rules (see [`memory_model_spec.md`](../memory/memory_model_spec.md)).

* EMS-INV-011:* THE system SHALL use a unified global allocator with type-level rules.

* EMS-REQ-012:* THE system SHALL use a unified global allocator with type-level rules.
  - Priority:* Critical
  - Verification Method:* Test
  - Rationale:* Enables unified memory management with type-level safety
  - Dependencies:* EMS-INV-011
  - Traceability:* Section 2.5.1 (The Unified Allocator)

#### 2.5.2 Capability Enforcement

* EMS-INV-012:* THE system SHALL enforce capability properties at runtime in debug mode.

* Runtime Check:* Debug builds verify that `iso` pointers passed between threads are indeed unique (detecting unsafe C++ FFI leaks). Release builds assume compile-time proofs are correct.

* EMS-REQ-013:* THE system SHALL enforce capability properties at runtime in debug mode.
  - Priority:* High
  - Verification Method:* Test
  - Rationale:* Detects unsafe FFI leaks
  - Dependencies:* EMS-INV-012
  - Traceability:* Section 2.5.2 (Capability Enforcement)

### 2.6 Foreign Function Interface (FFI)

#### 2.6.1 The Dual-Pool Strategy

To prevent C/C++ code from blocking the M:N scheduler, Morph maintains two thread pools.

* EMS-INV-013:* THE system SHALL maintain dual thread pools for FFI.

* Components:
1. **The Green Pool:** Runs Morph Fibers
2. **The System Pool:** Runs blocking OS threads

* EMS-REQ-014:* THE system SHALL maintain dual thread pools for FFI.
  - Priority:* High
  - Verification Method:* Test
  - Rationale:* Prevents blocking of M:N scheduler
  - Dependencies:* EMS-INV-013
  - Traceability:* Section 2.6.1 (The Dual-Pool Strategy)

#### 2.6.2 The Switch Protocol

When a Morph Fiber calls a C function:

* EMS-INV-014:* THE system SHALL implement switch protocol for FFI calls.

* Default Behavior:*
1. Task is moved from Green Pool to System Pool
2. C function executes (blocking System Thread)
3. Task is moved back to Green Pool

* Optimization (`[NonBlocking]` trait):*
1. Task remains on Green Pool
2. C function executes immediately
3. **Risk:** If C function sleeps, Morph Executor hangs

* Rationale:* Safety by default. An Agent importing a buggy C library shouldn't freeze GUI.

* EMS-REQ-015:* THE system SHALL implement switch protocol for FFI calls with default safety.
  - Priority:* High
  - Verification Method:* Test
  - Rationale:* Prevents blocking of M:N scheduler
  - Dependencies:* EMS-INV-014
  - Traceability:* Section 2.6.2 (The Switch Protocol)

### 2.7 Observability & Debugging

#### 2.7.1 Time-Travel State Graph (Debug Mode)

* EMS-INV-015:* THE system SHALL maintain time-travel state graph in debug mode.

* Mechanism:* The Runtime maintains a **Shadow Stack**.

* Operation:* On every state mutation (assignment to `state` variable):
1. The old value is serialized (copy-on-write)
2. A node is added to the DAG: `(Timestamp, AST_ID, Previous_Hash, New_Value)`

* Crash Dump:* On panic, Runtime exports this DAG to the MCP server.

* EMS-REQ-016:* THE system SHALL maintain time-travel state graph in debug mode.
  - Priority:* Medium
  - Verification Method:* Test
  - Rationale:* Enables time-travel debugging
  - Dependencies:* EMS-INV-015
  - Traceability:* Section 2.7.1 (Time-Travel State Graph)

#### 2.7.2 The Flight Recorder (Release Mode)

* EMS-INV-016:* THE system SHALL maintain flight recorder in release mode.

* Mechanism:* A 1MB Circular Buffer per Executor.

* Logging:* Records compact "Event Codes" (e.g., `ActorSpawn`, `MsgStart`, `MsgEnd`, `Error`).

* Overhead:* < 1% CPU.

* Rationale:* Allows diagnosing production crashes ("What was the last message processed?") without full overhead.

* EMS-REQ-017:* THE system SHALL maintain flight recorder in release mode with < 1% CPU overhead.
  - Priority:* Medium
  - Verification Method:* Test
  - Rationale:* Enables production crash diagnosis
  - Dependencies:* EMS-INV-016
  - Traceability:* Section 2.7.2 (The Flight Recorder)

#### 2.2.8 Testing Strategy

The testing strategy ensures that both scheduler configurations (work-stealing and deterministic) are thoroughly validated.

* EMS-INV-007:* THE system SHALL test both scheduler configurations.

* Testing Requirements:*
- **Dual Configuration Testing:** All tests must pass with both work-stealing and deterministic schedulers
- **Scheduler-Specific Tests:** Tests for scheduler-specific behavior (e.g., work stealing, deterministic ordering)
- **CI/CD Testing:** Continuous integration must test both configurations
- **Performance Regression Testing:** Performance tests must validate both schedulers

* Test Categories:*

| Category | Work-Stealing Tests | Deterministic Scheduler Tests |
|-----------|----------------------|----------------------------|
| **Correctness** | Fiber scheduling, work stealing, load balancing | Deterministic ordering, reproducibility |
| **Performance** | Throughput, latency, CPU utilization | Execution time, memory usage |
| **Concurrency** | Race conditions, deadlocks, starvation | Sequential execution guarantees |
| **Edge Cases** | Empty queues, single executor, overload | FIFO ordering, state reproducibility |

* CI/CD Integration:*
- **Production Build Tests:** Run full test suite without `--debug-scheduler` flag
- **Debug Build Tests:** Run full test suite with `--debug-scheduler` flag
- **Parallel Testing:** Run both configurations in parallel for faster feedback
- **Failure Analysis:** Compare test results between configurations to detect scheduler-specific issues

* Rationale:* Testing both configurations ensures that the deterministic scheduler provides reproducible execution while the work-stealing scheduler provides optimal performance. Link-time replacement means tests must be run separately for each configuration.

* EMS-REQ-011:* THE system SHALL ensure all tests pass with both work-stealing and deterministic schedulers.
  - Priority:* High
  - Verification Method:* Test
  - Rationale:* Ensures correctness of both scheduler implementations
  - Dependencies:* EMS-INV-007
  - Traceability:* Section 2.2.8 (Testing Strategy)

* EMS-REQ-012:* THE system SHALL run CI/CD tests for both scheduler configurations.
  - Priority:* High
  - Verification Method:* Test
  - Rationale:* Ensures continuous validation of both schedulers
  - Dependencies:* EMS-INV-007
  - Traceability:* Section 2.2.8 (Testing Strategy)

#### 2.2.9 Performance Characteristics

The two schedulers have significantly different performance characteristics, which must be documented and understood.

* EMS-INV-008:* THE system SHALL document performance characteristics of both schedulers.

* Work-Stealing Scheduler (Production):*

| Metric | Expected Performance | Notes |
|---------|-------------------|-------|
| **Throughput** | High | Maximizes CPU utilization via work stealing |
| **Latency** | Low | Efficient load balancing across executors |
| **Scalability** | Excellent | Scales linearly with core count |
| **Memory Overhead** | Minimal | Only work queue per executor |
| **Cache Locality** | Good | Work stealing preserves cache locality |
| **Determinism** | Non-deterministic | Execution order varies between runs |
| **Use Case** | Production | Optimal for real-world workloads |

* Deterministic Scheduler (Debug/Test):*

| Metric | Expected Performance | Notes |
|---------|-------------------|-------|
| **Throughput** | Low | Sequential execution limits parallelism |
| **Latency** | High | No work stealing or load balancing |
| **Scalability** | Poor | Single-threaded execution model |
| **Memory Overhead** | Minimal | Single global queue |
| **Cache Locality** | Poor | Sequential execution reduces cache benefits |
| **Determinism** | Fully deterministic | Identical execution order across runs |
| **Use Case** | Debug/Test | Reproducible execution for debugging |

* Performance Comparison:*

| Benchmark | Work-Stealing | Deterministic | Ratio |
|------------|---------------|---------------|--------|
| **Fiber Creation** | ~100ns | ~100ns | 1:1 |
| **Fiber Scheduling** | ~10ns | ~50ns | 1:5 |
| **Work Stealing** | ~10ns | N/A | N/A |
| **Throughput (1M fibers)** | ~1s | ~10s | 1:10 |
| **Memory Usage (1M fibers)** | ~1GB | ~1GB | 1:1 |
| **Binary Size** | ~500KB | ~300KB | 1.7:1 |

* Expected Performance Differences:*
- **Throughput:** Work-stealing scheduler is expected to be 5-10x faster than deterministic scheduler for concurrent workloads
- **Latency:** Work-stealing scheduler provides lower latency due to parallel execution
- **Scalability:** Work-stealing scheduler scales with core count; deterministic scheduler does not
- **Binary Size:** Deterministic scheduler is smaller due to simpler implementation
- **Memory:** Both schedulers have similar memory usage for fiber storage

* Rationale:* Understanding performance differences helps developers choose the right scheduler for their use case. Production builds must use work-stealing for optimal performance, while debug builds use deterministic for reproducibility.

* EMS-REQ-013:* THE system SHALL document performance benchmarks comparing both schedulers.
  - Priority:* Medium
  - Verification Method:* Analysis
  - Rationale:* Provides guidance on scheduler performance differences
  - Dependencies:* EMS-INV-008
  - Traceability:* Section 2.2.9 (Performance Characteristics)

* EMS-REQ-014:* THE system SHALL provide guidance on expected performance differences between schedulers.
  - Priority:* Medium
  - Verification Method:* Analysis
  - Rationale:* Helps developers understand scheduler trade-offs
  - Dependencies:* EMS-INV-008
  - Traceability:* Section 2.2.9 (Performance Characteristics)

---

## 3. Requirements

### 3.1 Functional Requirements

* EMS-REQ-001:* THE system SHALL provide a bare-metal runtime library for OS primitive abstraction.
  - Priority:* Critical
  - Verification Method:* Test
  - Rationale:* Enables zero-overhead runtime without virtual machine
  - Dependencies:* EMS-INV-001
  - Traceability:* Section 2.1.1 (The Runtime Library)

* EMS-REQ-002:* THE system SHALL use stackful coroutines with growable stacks starting at 4KB.
  - Priority:* Critical
  - Verification Method:* Test
  - Rationale:* Enables implicit suspension without stack unwinding
  - Dependencies:* EMS-INV-002
  - Traceability:* Section 2.1.2 (The Execution Unit: The Fiber)

* EMS-REQ-003:* THE system SHALL use link-time replacement for scheduler selection, not runtime switching.
  - Priority:* Critical
  - Verification Method:* Test
  - Rationale:* Avoids dead code in production and ensures optimal performance
  - Dependencies:* EMS-INV-003
  - Traceability:* Section 2.2.0 (Scheduler Selection Mechanism)

* EMS-REQ-004:* THE system SHALL NOT ship two schedulers in the final binary.
  - Priority:* Critical
  - Verification Method:* Test
  - Rationale:* Prevents dead code and ensures production performance
  - Dependencies:* EMS-INV-003
  - Traceability:* Section 2.2.0 (Scheduler Selection Mechanism)

* EMS-REQ-005:* THE system SHALL use work-stealing scheduler as the only scheduler in production builds.
  - Priority:* Critical
  - Verification Method:* Test
  - Rationale:* Maximizes CPU utilization and prevents blocking
  - Dependencies:* EMS-INV-004
  - Traceability:* Section 2.2.1 (The M:N Scheduler with Work Stealing)

* EMS-REQ-006:* THE system SHALL provide deterministic scheduler only as a debug-mode shim via link-time replacement.
  - Priority:* High
  - Verification Method:* Test
  - Rationale:* Enables reproducible debugging without production overhead
  - Dependencies:* EMS-INV-005
  - Traceability:* Section 2.2.2 (Deterministic Scheduler)

* EMS-REQ-007:* THE system SHALL NOT link deterministic scheduler in production mode.
  - Priority:* Critical
  - Verification Method:* Test
  - Rationale:* Ensures production performance and avoids dead code
  - Dependencies:* EMS-INV-005
  - Traceability:* Section 2.2.2 (Deterministic Scheduler)

* EMS-REQ-008:* THE system SHALL link only work-stealing scheduler when --debug-scheduler flag is not specified.
  - Priority:* Critical
  - Verification Method:* Test
  - Rationale:* Ensures production builds use optimal scheduler
  - Dependencies:* EMS-INV-006
  - Traceability:* Section 2.2.3 (Build Flag Specification)

* EMS-REQ-009:* THE system SHALL link only deterministic scheduler when --debug-scheduler flag is specified.
  - Priority:* High
  - Verification Method:* Test
  - Rationale:* Ensures debug builds use deterministic scheduler
  - Dependencies:* EMS-INV-006
  - Traceability:* Section 2.2.3 (Build Flag Specification)

* EMS-REQ-010:* THE system SHALL NOT support mixing schedulers in the same binary.
  - Priority:* Critical
  - Verification Method:* Test
  - Rationale:* Prevents dead code and ensures clear scheduler selection
  - Dependencies:* EMS-INV-006
  - Traceability:* Section 2.2.3 (Build Flag Specification)

* EMS-REQ-011:* THE system SHALL ensure all tests pass with both work-stealing and deterministic schedulers.
  - Priority:* High
  - Verification Method:* Test
  - Rationale:* Ensures correctness of both scheduler implementations
  - Dependencies:* EMS-INV-007
  - Traceability:* Section 2.2.8 (Testing Strategy)

* EMS-REQ-012:* THE system SHALL run CI/CD tests for both scheduler configurations.
  - Priority:* High
  - Verification Method:* Test
  - Rationale:* Ensures continuous validation of both schedulers
  - Dependencies:* EMS-INV-007
  - Traceability:* Section 2.2.8 (Testing Strategy)

* EMS-REQ-013:* THE system SHALL document performance benchmarks comparing both schedulers.
  - Priority:* Medium
  - Verification Method:* Analysis
  - Rationale:* Provides guidance on scheduler performance differences
  - Dependencies:* EMS-INV-008
  - Traceability:* Section 2.2.9 (Performance Characteristics)

* EMS-REQ-014:* THE system SHALL provide guidance on expected performance differences between schedulers.
  - Priority:* Medium
  - Verification Method:* Analysis
  - Rationale:* Helps developers understand scheduler trade-offs
  - Dependencies:* EMS-INV-008
  - Traceability:* Section 2.2.9 (Performance Characteristics)

* EMS-REQ-015:* THE system SHALL implement IO-aware yielding for implicit suspension.
  - Priority:* Critical
  - Verification Method:* Test
  - Rationale:* Eliminates blocking and maximizes CPU utilization
  - Dependencies:* EMS-INV-005
  - Traceability:* Section 2.2.4 (Implicit Suspension Protocol)

* EMS-REQ-007:* THE system SHALL inject preemption checkpoints at loop headers and function entries.
  - Priority:* High
  - Verification Method:* Test
  - Rationale:* Prevents fiber starvation and ensures responsiveness
  - Dependencies:* EMS-INV-006
  - Traceability:* Section 2.2.5 (Preemption)

* EMS-REQ-008:* THE system SHALL compile `logic` blocks into stateful fibers with MPSC mailboxes.
  - Priority:* Critical
  - Verification Method:* Test
  - Rationale:* Enables actor model with data race freedom
  - Dependencies:* EMS-INV-007
  - Traceability:* Section 2.3.1 (Actor Structure)

* EMS-REQ-009:* THE system SHALL implement supervision trees with OneForOne and OneForAll strategies.
  - Priority:* High
  - Verification Method:* Test
  - Rationale:* Enables self-healing systems
  - Dependencies:* EMS-INV-008
  - Traceability:* Section 2.3.2 (Supervision Trees)

* EMS-REQ-010:* THE system SHALL implement `async let` as ephemeral fiber spawning with Future slots.
  - Priority:* High
  - Verification Method:* Test
  - Rationale:* Enables dataflow parallelism
  - Dependencies:* EMS-INV-009
  - Traceability:* Section 2.4.1 (Implementation)

* EMS-REQ-011:* THE system SHALL implement wait-by-necessity for Future resolution.
  - Priority:* High
  - Verification Method:* Test
  - Rationale:* Enables efficient dataflow parallelism
  - Dependencies:* EMS-INV-010
  - Traceability:* Section 2.4.2 (Wait-by-Necessity)

* EMS-REQ-012:* THE system SHALL use a unified global allocator with type-level rules.
  - Priority:* Critical
  - Verification Method:* Test
  - Rationale:* Enables unified memory management with type-level safety
  - Dependencies:* EMS-INV-011
  - Traceability:* Section 2.5.1 (The Unified Allocator)

* EMS-REQ-013:* THE system SHALL enforce capability properties at runtime in debug mode.
  - Priority:* High
  - Verification Method:* Test
  - Rationale:* Detects unsafe FFI leaks
  - Dependencies:* EMS-INV-012
  - Traceability:* Section 2.5.2 (Capability Enforcement)

* EMS-REQ-014:* THE system SHALL maintain dual thread pools for FFI.
  - Priority:* High
  - Verification Method:* Test
  - Rationale:* Prevents blocking of M:N scheduler
  - Dependencies:* EMS-INV-013
  - Traceability:* Section 2.6.1 (The Dual-Pool Strategy)

* EMS-REQ-015:* THE system SHALL implement switch protocol for FFI calls with default safety.
  - Priority:* High
  - Verification Method:* Test
  - Rationale:* Prevents blocking of M:N scheduler
  - Dependencies:* EMS-INV-014
  - Traceability:* Section 2.6.2 (The Switch Protocol)

* EMS-REQ-016:* THE system SHALL maintain time-travel state graph in debug mode.
  - Priority:* Medium
  - Verification Method:* Test
  - Rationale:* Enables time-travel debugging
  - Dependencies:* EMS-INV-015
  - Traceability:* Section 2.7.1 (Time-Travel State Graph)

* EMS-REQ-017:* THE system SHALL maintain flight recorder in release mode with < 1% CPU overhead.
  - Priority:* Medium
  - Verification Method:* Test
  - Rationale:* Enables production crash diagnosis
  - Dependencies:* EMS-INV-016
  - Traceability:* Section 2.7.2 (The Flight Recorder)

### 3.2 Non-Functional Requirements

* EMS-NFR-001:* THE system SHALL provide fiber creation in nanoseconds.
  - Priority:* High
  - Verification Method:* Test
  - Metric:* Fiber creation < 100ns
  - Rationale:* Enables high-performance concurrency
  - Dependencies:* EMS-INV-002
  - Traceability:* Section 2.1.2 (The Execution Unit: The Fiber)

* EMS-NFR-002:* THE system SHALL provide work-stealing scheduler with O(1) steal operation.
  - Priority:* High
  - Verification Method:* Analysis
  - Metric:* Steal operation < 10ns
  - Rationale:* Ensures efficient load balancing
  - Dependencies:* EMS-INV-004
  - Traceability:* Section 2.2.1 (The M:N Scheduler with Work Stealing)

* EMS-NFR-003:* THE system SHALL provide deterministic scheduler with reproducible execution order.
  - Priority:* Medium
  - Verification Method:* Test
  - Metric:* Identical execution order across runs
  - Rationale:* Enables reproducible debugging
  - Dependencies:* EMS-INV-005
  - Traceability:* Section 2.2.2 (Deterministic Scheduler)

* EMS-NFR-004:* THE system SHALL provide implicit suspension with zero blocking.
  - Priority:* Critical
  - Verification Method:* Test
  - Metric:* No blocking on I/O operations
  - Rationale:* Maximizes CPU utilization
  - Dependencies:* EMS-INV-005
  - Traceability:* Section 2.2.4 (Implicit Suspension Protocol)

* EMS-NFR-005:* THE system SHALL provide preemption with bounded time slices.
  - Priority:* High
  - Verification Method:* Test
  - Metric:* Time slice < 10ms
  - Rationale:* Ensures responsiveness
  - Dependencies:* EMS-INV-006
  - Traceability:* Section 2.2.5 (Preemption)

* EMS-NFR-006:* THE system SHALL support up to 1,000,000 concurrent fibers.
  - Priority:* Medium
  - Verification Method:* Demonstration
  - Metric:* 1M fibers with < 10GB memory
  - Rationale:* Supports large-scale concurrent systems
  - Dependencies:* EMS-INV-002
  - Traceability:* Section 2.1.2 (The Execution Unit: The Fiber)

---

## 4. Design

### 4.1 Architecture Overview

The Execution Model is implemented as a **Bare-Metal Runtime Library** that:

1. Provides OS primitive abstraction
2. Implements link-time replacement for scheduler selection
3. Implements M:N scheduling with work stealing (production)
4. Provides deterministic scheduler as debug-mode shim (via `--debug-scheduler` flag)
5. Implements implicit suspension via IO-aware yielding
6. Implements preemption to prevent fiber starvation
7. Compiles `logic` blocks into stateful fibers
8. Implements supervision trees for failure recovery
9. Implements `async let` as ephemeral fiber spawning
10. Uses unified global allocator with type-level rules
11. Maintains dual thread pools for FFI
12. Provides observability via time-travel state graph and flight recorder
13. Ensures only one scheduler is linked per binary (no dead code)

---

## 5. Correctness Properties

### 5.1 Theorems

#### 5.1.1 Work Stealing Theorem

* Theorem:* If the system uses work-stealing scheduler, then CPU utilization is maximized.

* Proof Sketch:*
1. By definition of work-stealing, idle executors steal work from busy executors
2. Therefore, no executor remains idle while work is available
3. Therefore, CPU utilization is maximized

* EMS-THM-001:* THE system SHALL guarantee maximized CPU utilization with work-stealing scheduler.
  - Priority:* High
  - Verification Method:* Analysis
  - Rationale:* Ensures efficient resource utilization
  - Dependencies:* EMS-INV-004
  - Traceability:* Section 2.2.1 (The M:N Scheduler with Work Stealing)

#### 5.1.2 Data Race Freedom Theorem

* Theorem:* If the system uses actor model with MPSC mailboxes, then actors are data-race-free.

* Proof Sketch:*
1. By definition of actor model, each actor processes messages sequentially
2. By definition of MPSC mailbox, messages are delivered atomically
3. Therefore, no two actors can mutate the same memory simultaneously

* EMS-THM-002:* THE system SHALL guarantee data race freedom for actors.
  - Priority:* Critical
  - Verification Method:* Analysis
  - Rationale:* Ensures thread safety without locks
  - Dependencies:* EMS-INV-007
  - Traceability:* Section 2.3.1 (Actor Structure)

#### 5.1.3 Zero Blocking Theorem

* Theorem:* If the system uses IO-aware yielding, then no fiber blocks on I/O.

* Proof Sketch:*
1. By definition of IO-aware yielding, fibers yield on blocking I/O
2. By definition of implicit suspension, fibers resume when I/O completes
3. Therefore, no fiber blocks on I/O

* EMS-THM-003:* THE system SHALL guarantee zero blocking on I/O operations.
  - Priority:* Critical
  - Verification Method:* Analysis
  - Rationale:* Maximizes CPU utilization
  - Dependencies:* EMS-INV-005
  - Traceability:* Section 2.2.4 (Implicit Suspension Protocol)

---

## 6. Examples

### 6.1 Simple Actor

```morph
logic Counter {
    state: {
        count: i32 = 0
    },
    
    in: {
        Increment,
        GetCount
    },
    
    fn handle(msg: Input) {
        fix msg {
            Increment => self.state.count += 1,
            GetCount => send(self.sender, self.state.count)
        }
    }
}
```

* Properties:*
- Actor processes messages sequentially
- Data race freedom guaranteed
- MPSC mailbox ensures message delivery

### 6.2 Work Stealing

```morph
// Executor 1
fn executor1() {
    while true {
        fiber = self.work_queue.pop_head()
        if fiber == null:
            fiber = steal_from_other_executors()
        if fiber != null:
            execute(fiber)
    }
}

// Executor 2
fn executor2() {
    while true {
        fiber = self.work_queue.pop_head()
        if fiber == null:
            fiber = steal_from_other_executors()
        if fiber != null:
            execute(fiber)
    }
}
```

* Properties:*
- Idle executors steal work from busy executors
- CPU utilization maximized
- No executor remains idle while work is available

### 6.3 IO-Aware Yielding

```morph
fn read_file(path: str) -> str {
    // Runtime intercepts syscall
    // Registers FD with OS poller
    // Yields fiber
    // Resumes when data available
    ret file.read(path)
}
```

* Properties:*
- No blocking on I/O
- Fiber yields on blocking I/O
- Fiber resumes when I/O completes

### 6.4 Preemption

```morph
fn infinite_loop() {
    while true {
        // Compiler injects preemption checkpoint
        // if runtime_ticks() > time_slice_limit:
        //     yield()
        do_work()
    }
}
```

* Properties:*
- Prevention of fiber starvation
- Bounded time slices
- System responsiveness guaranteed

### 6.5 Supervision Tree

```morph
logic Supervisor {
    children: [Actor] = [],
    
    fn supervise(child: Actor) {
        self.children.push(child)
    },
    
    fn handle_failure(child: Actor) {
        // OneForOne strategy
        new_child = spawn(child.type)
        self.children.remove(child)
        self.children.push(new_child)
    }
}
```

* Properties:*
- Self-healing system
- OneForOne strategy restarts failed child
- System continues despite failures

### 6.6 Edge Cases

#### 6.6.1 Empty Work Queue

```morph
fn executor() {
    while true {
        fiber = self.work_queue.pop_head()
        if fiber == null:
            // No work available, sleep
            sleep(1ms)
    }
}
```

* Properties:*
- Executor sleeps when no work available
- Wakes up when work becomes available
- CPU not wasted on idle loops

#### 6.6.2 Panic Propagation

```morph
logic Parent {
    fn handle_failure(child: Actor) {
        // Panic propagates to parent
        panic("Child failed")
    }
}

logic Child {
    fn handle(msg: Input) {
        // Panic on error
        panic("Error")
    }
}
```

* Properties:*
- Panic propagates to supervisor
- Supervisor handles failure
- System self-heals

#### 6.6.3 Future Poisoning

```morph
fn parent() {
    async let result = child()
    // Child panics
    // Future is poisoned
    // Parent panics when accessing result
    value = result  // Panic: Future poisoned
}
```

* Properties:*
- Future poisoned on child panic
- Parent panics when accessing poisoned future
- Error propagation guaranteed

---

## 7. Cross-References

### 7.1 Type System Specifications

- [`spec/type/type_system_spec.md`](../type/type_system_spec.md) - Type system, capability sigils, and affine logic formalization
- [`spec/type/pure_type_spec.md`](../type/pure_type_spec.md) - Pure type theory
- [`spec/type/type_category_spec.md`](../type/type_category_spec.md) - Type category theory and algebraic type foundations
- [`spec/type/type_unification_spec.md`](../type/type_unification_spec.md) - Type unification algorithm and inference rules
- [`spec/type/effect_system_spec.md`](../type/effect_system_spec.md) - Complete effect system specification with formal semantics and type-level effect tracking

### 7.2 Memory Specifications

- [`spec/memory/memory_model_spec.md`](../memory/memory_model_spec.md) - Memory management model, ARC implementation, and runtime memory operations
- [`spec/memory/memory_acyclicity_spec.md`](../memory/memory_acyclicity_spec.md) - Memory acyclicity enforcement using affine logic and graph theory
- [`spec/memory/memory_affine_logic_spec.md`](../memory/memory_affine_logic_spec.md) - Affine logic formalization for memory safety
- [`spec/memory/memory_petri_net_spec.md`](../memory/memory_petri_net_spec.md) - Petri net formalization of memory operations
- [`spec/memory/arc_affine_integration_spec.md`](../memory/arc_affine_integration_spec.md) - ARC and affine types

### 7.3 Concurrency Specifications

- [`spec/concurrency/execution_model_spec.md`](../concurrency/execution_model_spec.md) - This specification (self-reference)
- [`spec/concurrency/scheduling_modes_spec.md`](../concurrency/scheduling_modes_spec.md) - Dual-mode scheduling specification (work-stealing and deterministic modes)
- [`spec/concurrency/concurrency_process_algebra_spec.md`](../concurrency/concurrency_process_algebra_spec.md) - Process algebra formalization of concurrent communication
- [`spec/concurrency/monadic_effect_spec.md`](../concurrency/monadic_effect_spec.md) - Monadic effects for concurrent operations

### 7.4 Build System Specifications

- [`spec/build/build_lattice_spec.md`](../build/build_lattice_spec.md) - Build dependency lattice and incremental compilation
- [`spec/build/dependency_sat_spec.md`](../build/dependency_sat_spec.md) - Dependency satisfaction and resolution
- [`spec/build/linker_logic_spec.md`](../build/linker_logic_spec.md) - Linker logic and symbol resolution
- [`spec/build/backend_tiling_spec.md`](../build/backend_tiling_spec.md) - Backend tiling and code generation
- [`spec/build/abi_alignment_algebra_spec.md`](../build/abi_alignment_algebra_spec.md) - ABI alignment and data refinement

### 7.5 Security Specifications

- [`spec/security/security_flow_spec.md`](../security/security_flow_spec.md) - Security flow analysis, taint tracking, and lattice-based access control
- [`spec/security/infrastructure_safety_contracts_spec.md`](../security/infrastructure_safety_contracts_spec.md) - Safety contracts for infrastructure components
- [`spec/security_ocap_spec.md`](../security_ocap_spec.md) - Object capability security model

### 7.6 Tooling Specifications

- [`spec/tooling/metaprogramming_spec.md`](../tooling/metaprogramming_spec.md) - Metaprogramming, comptime blocks, and optimization holes
- [`spec/tooling/compiler_bisimulation_spec.md`](../tooling/compiler_bisimulation_spec.md) - Compiler bisimulation and optimization correctness
- [`spec/tooling/comptime_partial_eval_spec.md`](../tooling/comptime_partial_eval_spec.md) - Compile-time evaluation
- [`spec/tooling/operational_semantics_spec.md`](../tooling/operational_semantics_spec.md) - Operational semantics for language constructs

### 7.7 Standard Library Specifications

- [`spec/stdlib/stdlib_algebraic_spec.md`](../stdlib/stdlib_algebraic_spec.md) - Algebraic specification of standard library data structures
- [`spec/stdlib/stdlib_amortized_spec.md`](../stdlib/stdlib_amortized_spec.md) - Amortized analysis of standard library operations

### 7.8 Language Specifications

- [`spec/language/morph_language_spec.md`](../language/morph_language_spec.md) - Core language syntax, keywords, and dual dialects (min/hum)
- [`spec/language/strict_state_unidirectional_spec.md`](../language/strict_state_unidirectional_spec.md) - SSUS pattern for strict state unidirectional
- [`spec/language/unidirectional_data_flow_spec.md`](../language/unidirectional_data_flow_spec.md) - UDF pattern for unidirectional data flow
- [`spec/language/scoping_lambda_calculus_spec.md`](../language/scoping_lambda_calculus_spec.md) - Scoping rules and lambda calculus formalization
- [`spec/language/lexical_structure_syntax_spec.md`](../language/lexical_structure_syntax_spec.md) - Lexical structure and syntax specification
- [`spec/language/operator_null_coalescing_spec.md`](../language/operator_null_coalescing_spec.md) - ?? operator semantics and optimization search space

### 7.9 Domain Extensions

- [`spec/financial/financial_spec.md`](../financial/financial_spec.md) - Financial domain types, dec128, and @critical safety
- [`spec/math/maths_spec.md`](../math/maths_spec.md) - Mathematical operations and unit algebra
- [`spec/math/unit_group_theory_spec.md`](../math/unit_group_theory_spec.md) - Unit group theory and dimensional analysis

### 7.10 UI Specifications

- [`spec/ui/ui_constraint_algebra_spec.md`](../ui/ui_constraint_algebra_spec.md) - UI constraint algebra for layout
- [`spec/ui/ui_event_topology_spec.md`](../ui/ui_event_topology_spec.md) - UI event propagation and deterministic replay
- [`spec/ui/semantic_accessibility_spec.md`](../ui/semantic_accessibility_spec.md) - Semantic accessibility protocol

---

## 8. Verification and Validation Plan

### 8.1 Verification Strategy

#### 8.1.1 Formal Verification

- **Work Stealing Correctness:** Mechanized proof of work-stealing scheduler correctness using proof assistant (e.g., Coq, Lean)
- **Data Race Freedom:** Formal verification of actor isolation and MPSC mailbox guarantees
- **Zero Blocking:** Formal proof of IO-aware yielding correctness
- **Preemption Correctness:** Formal verification of preemption mechanism guarantees

#### 8.1.2 Static Analysis

- **Compiler Checks:** All requirements verified through compiler implementation
- **Linter Rules:** Automated linting for common concurrency errors and anti-patterns
- **Contract Verification:** Automated checking of preconditions, postconditions, and invariants
- **Capability System Enforcement:** Static analysis of capability annotations

### 8.2 Validation Strategy

#### 8.2.1 Unit Testing

- **Test Coverage:** Minimum 90% code coverage for all execution model features
- **Property-Based Testing:** Use QuickCheck-style testing for algebraic properties
- **Fuzz Testing:** Automated fuzzing for all public APIs
- **Regression Testing:** Comprehensive test suite for all bug fixes

#### 8.2.2 Integration Testing

- **End-to-End Tests:** Full compilation pipeline from source to executable
- **Cross-Platform Testing:** Validation on Windows, Linux, macOS
- **Performance Testing:** Benchmark suite for all performance claims
- **Security Testing:** Penetration testing and vulnerability scanning

#### 8.2.3 Real-World Validation

- **Pilot Programs:** Early adopter projects using Morph execution model in production
- **Developer Surveys:** Feedback on language usability and specification clarity
- **Bug Analysis:** Tracking and analysis of common bugs and their root causes
- **Case Studies:** Documentation of successful Morph execution model projects

### 8.3 Test Plan

#### 8.3.1 Test Categories

| Category | Description | Priority |
|----------|-------------|----------|
| **Scheduling** | Work-stealing, deterministic scheduling | Critical |
| **Actor Model** | MPSC mailboxes, supervision trees | Critical |
| **Fiber Management** | Stackful coroutines, preemption | Critical |
| **FFI Integration** | Dual thread pools, switch protocol | High |
| **Observability** | Time-travel, flight recorder | Medium |

#### 8.3.2 Test Execution

- **CI/CD Integration:** All tests run on every commit
- **Nightly Builds:** Full test suite execution with performance benchmarks
- **Release Testing:** Comprehensive testing before each release
- **Continuous Monitoring:** Automated monitoring of test failures and performance regressions

---

## 9. Risk Assessment

### 9.1 Technical Risks

| Risk | Probability | Impact | Mitigation |
|-------|-------------|--------|
| **Work Stealing Complexity** | Medium | High | Formal verification; extensive testing; benchmarking |
| **Preemption Overhead** | Low | Medium | Configurable time slices; performance monitoring |
| **FFI Blocking** | Medium | High | Dual thread pools; [NonBlocking] trait; documentation |
| **Deterministic Scheduler Performance** | Low | High | Debug-mode only; clear documentation; performance warnings |
| **Memory Fragmentation** | Medium | Medium | Unified allocator; efficient allocation algorithms |
| **Actor Starvation** | Low | Critical | Preemption mechanism; work-stealing scheduler |

### 9.2 Implementation Risks

| Risk | Probability | Impact | Mitigation |
|-------|-------------|--------|
| **Timeline Overrun** | Medium | High | Phased approach; prioritize critical features; buffer time |
| **Resource Constraints** | Low | Medium | Realistic resource planning; cross-training; automation |
| **Tooling Delays** | Medium | Medium | Prioritize critical tools; use existing solutions |
| **Adoption Barriers** | Medium | High | Early adopter program; documentation; examples; tutorials |
| **Ecosystem Fragmentation** | Low | Medium | Clear conventions; automated tools; governance |

### 9.3 Mitigation Strategies

1. **Incremental Implementation:**
   - Implement features in phases
   - Deliver value early with critical features
   - Iterate based on feedback

2. **Early Validation:**
   - Validate assumptions early
   - Create prototypes for critical features
   - Conduct pilot studies

3. **Automation:**
   - Automate repetitive tasks
   - Use CI/CD for validation
   - Generate documentation automatically

4. **Contingency Planning:**
   - Allocate buffer time for each phase
   - Have backup plans for critical path items
   - Monitor progress and adjust as needed

---

## Change Log

| Version | Date       | Author      | Changes                                                                 |
|---------|------------|-------------|-------------------------------------------------------------------------|
| 2.1.0   | 2026-01-03 | Kilo Code    | **Resolved concurrency model contradiction with link-time replacement:**<br>1. Added Section 2.2.0: Scheduler Selection Mechanism<br>2. Clarified that deterministic scheduler is for debugging and testing only<br>3. Specified that production builds use work-stealing scheduler<br>4. Implemented link-time replacement (not runtime switch)<br>5. Added Section 2.2.3: Build Flag Specification with `--debug-scheduler` flag<br>6. Specified that production builds link only work-stealing scheduler<br>7. Specified that debug/test builds link only deterministic scheduler<br>8. Documented that mixing schedulers in same binary is not supported<br>9. Added Section 2.2.8: Testing Strategy for both configurations<br>10. Added Section 2.2.9: Performance Characteristics with benchmarks<br>11. Updated all invariants and requirements (EMS-INV-003 through EMS-INV-008)<br>12. Updated all functional requirements (EMS-REQ-003 through EMS-REQ-017)<br>13. Updated all non-functional requirements (EMS-NFR-003 through EMS-NFR-005)<br>14. Updated Architecture Overview to reflect link-time replacement<br>15. Updated Change Log |
| 2.0.0   | 2026-01-02 | Kilo Code    | **Refined to match strategic refinements:**<br>1. Work-stealing scheduler as default and only production scheduler<br>2. Deterministic scheduler strictly as debug-mode shim<br>3. Updated all invariants and requirements<br>4. Added formal definitions and theorems |
| 1.0.0   | 2026-01-01 | Kilo Code    | Initial version                                                        |
