# SPDX-License-Identifier: PMPL-1.0-or-later
# Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>

# Phronesis — System Specifications

Phronesis is a language that compiles to and runs on the Elixir/BEAM platform,
inheriting the runtime characteristics of the Erlang virtual machine.

## Memory Model

Phronesis uses the BEAM virtual machine's memory model:

- **Process heaps**: Each BEAM process has its own private heap. No shared mutable
  state exists between processes, eliminating data races at the memory level.
- **Immutable data**: All values are immutable once created. "Mutation" produces new
  values; the old value remains unchanged until garbage collected.
- **Per-process GC**: Garbage collection is per-process and generational. A GC pause
  in one process does not affect any other process. Short-lived processes that
  terminate before triggering GC have their entire heap reclaimed at once.
- **Binary heap**: Large binaries (>64 bytes) are reference-counted on a shared
  binary heap. Small binaries are copied into process heaps.
- **ETS tables**: Erlang Term Storage provides mutable shared-memory tables outside
  the process model. Data is copied in and out, preserving isolation semantics.
- **No manual memory management**: Developers never allocate or free memory directly.
- **Atoms**: Atoms are interned strings stored in a global atom table. They are never
  garbage collected. The atom table has a default limit of 1,048,576 entries.

## Concurrency Model

Phronesis inherits the BEAM actor model:

- **Processes**: Lightweight BEAM processes (not OS threads). Millions can run
  concurrently with ~2KB initial heap each.
- **Message passing**: Processes communicate exclusively via asynchronous message
  passing. Each process has a mailbox; messages are pattern-matched with `receive`.
- **OTP supervisors**: Fault tolerance through supervision trees. Supervisors monitor
  child processes and restart them according to configurable strategies (one-for-one,
  one-for-all, rest-for-one).
- **Preemptive scheduling**: The BEAM scheduler preempts processes after a reduction
  count, ensuring fair scheduling without cooperative yielding.
- **Distribution**: Processes can send messages transparently across nodes in a
  cluster. Location transparency is a first-class property.
- **No shared state**: Concurrency bugs related to locks, mutexes, and shared memory
  are structurally impossible in the standard process model.
- **Links and monitors**: Processes can be linked (bidirectional failure propagation)
  or monitored (unidirectional notification on exit). These primitives underpin OTP
  supervisor behaviour.
- **Task module**: For structured concurrency, the `Task` module provides
  `async`/`await` semantics built on top of processes, with automatic linking to
  the caller.

## Effect System

Phronesis uses a pure functional approach to effects:

- **Pure by default**: Functions are pure unless they explicitly perform IO or send
  messages. The type system tracks purity at the function level.
- **Explicit IO**: Side effects (file IO, network, database) are performed through
  dedicated modules that make the effectful nature visible in the API.
- **Process effects**: Spawning processes, sending messages, and receiving messages
  are the primary effect channels. These are explicit in the function signatures.
- **With-blocks**: Resource acquisition and release follow the `with` pattern,
  ensuring cleanup even when processes crash.
- **Telemetry integration**: Observable effects (metrics, traces) use the standard
  BEAM telemetry library for instrumentation without coupling.

## Module System

Phronesis uses the Elixir module system:

- **Modules**: Defined with `defmodule`. Each module is a namespace containing
  functions, macros, structs, and type specifications.
- **`use`**: Injects code from another module via the `__using__/1` macro callback.
  Commonly used for behaviours and DSLs.
- **`import`**: Brings functions from another module into the current scope,
  allowing them to be called without the module prefix.
- **`alias`**: Creates a short name for a module (e.g., `alias MyApp.Accounts.User`
  allows referring to `User` directly).
- **`require`**: Ensures a module is compiled before the current one, necessary
  when using macros from that module.
- **Behaviours**: Define callback contracts that implementing modules must fulfil.
  Compile-time warnings for missing callbacks.
- **Protocols**: Ad-hoc polymorphism. Protocols define a set of functions that can
  be implemented for any data type without modifying the type itself.
- **Package manager**: Mix for build tooling and task running; Hex for package
  registry and dependency resolution. Dependencies declared in `mix.exs`.
