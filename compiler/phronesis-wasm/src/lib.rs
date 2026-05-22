// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

//! WebAssembly backend for Phronesis.
//!
//! Compiles policy evaluation logic to WASM functions that return
//! accept/reject decisions. Each policy rule becomes a WASM function
//! returning an i32 verdict (1 = accept, 0 = reject).
//!
//! ## Output format
//!
//! Generates valid `.wasm` modules (binary format) containing:
//! - Type section (function signatures for policy evaluators)
//! - Import section (runtime: context_get, audit_log, escalate)
//! - Function section (compiled policy rules)
//! - Memory section (linear memory for policy context data)
//! - Export section (policy functions + memory)
//! - Data section (policy names, reason strings)
//!
//! ## Policy evaluation model
//!
//! Each policy rule is a function:
//! ```wasm
//! ;; evaluate_rule(context_ptr: i32) -> i32
//! ;; Returns: 1 = accept, 0 = reject
//! ```
//!
//! Composite policies combine sub-rules with AND/OR/NOT logic:
//! - AND: all sub-rules must accept
//! - OR: at least one sub-rule must accept
//! - NOT: invert a single sub-rule
//!
//! ## Context representation
//!
//! Policy context is a key-value store in linear memory:
//! - Keys: i32 string pointers (from data section)
//! - Values: i64 (numeric) or i32 pointer (string)
//! - Accessed via imported `context_get(key_ptr, key_len) -> i64`
//!
//! ## Limitations
//!
//! - No garbage collection (bump allocator)
//! - Context is read-only during evaluation
//!
//! ## Policy priority/precedence
//!
//! Policies carry a numeric priority. When multiple policies match,
//! the `policy_eval_all` exported function iterates policies in
//! descending priority order and returns the verdict of the first
//! match. Priority metadata is stored in the `PolicyRule` struct.
//!
//! ## Obligation actions
//!
//! After a verdict is rendered, obligation actions are executed via
//! the `obligation_execute(action_id: i32)` runtime import. Each
//! policy rule can specify obligation action IDs for accept and
//! reject outcomes.
//!
//! ## Temporal policies
//!
//! Temporal policies use the WASI `clock_time_get` import to check
//! whether the current wall-clock time falls within the policy's
//! valid window (`valid_from..valid_until`). Expired policies are
//! skipped and treated as non-matching.

#![forbid(unsafe_code)]
use std::collections::HashMap;

use wasm_encoder::{
    CodeSection, DataSection, EntityType, ExportKind, ExportSection,
    Function as WasmFunc, FunctionSection, ImportSection, Instruction,
    MemorySection, MemoryType, Module, TypeSection, ValType,
};

/// Errors specific to the Phronesis WASM backend.
#[derive(Debug, Clone, thiserror::Error)]
pub enum WasmError {
    /// A composite policy references an unknown sub-rule.
    #[error("unknown sub-rule: \"{rule}\" referenced in composite policy \"{policy}\"")]
    UnknownSubRule { rule: String, policy: String },

    /// Data section offset exceeds linear memory bounds.
    #[error("data section offset {offset} exceeds linear memory capacity ({capacity} bytes)")]
    DataSectionOverflow { offset: u32, capacity: u32 },

    /// Bump allocator ran out of linear memory.
    #[error("heap allocation of {requested} bytes exceeds capacity (offset {current}, capacity {capacity})")]
    HeapOverflow {
        requested: u32,
        current: u32,
        capacity: u32,
    },

    /// A policy name collision was detected.
    #[error("duplicate policy name: \"{name}\"")]
    DuplicatePolicyName { name: String },

    /// A policy evaluation cycle was detected (A depends on B depends on A).
    #[error("circular dependency detected in policy \"{name}\"")]
    CircularDependency { name: String },
}

/// WASM value type subset used by Phronesis.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum WasmType {
    /// 32-bit integer (verdicts, pointers, booleans).
    I32,
    /// 64-bit integer (context values).
    I64,
    /// 64-bit float (threshold comparisons).
    F64,
}

impl WasmType {
    fn to_val_type(self) -> ValType {
        match self {
            Self::I32 => ValType::I32,
            Self::I64 => ValType::I64,
            Self::F64 => ValType::F64,
        }
    }
}

/// A compiled WASM function for a policy rule.
#[derive(Debug, Clone)]
pub struct WasmFunction {
    /// Function name (policy rule name).
    pub name: String,
    /// Parameter types.
    pub params: Vec<WasmType>,
    /// Return type (always I32 for verdicts).
    pub result: Option<WasmType>,
    /// Compiled bytecode size.
    pub code_size: usize,
    /// Whether this is a composite policy (combines sub-rules).
    pub is_composite: bool,
}

/// A WASM import declaration.
#[derive(Debug, Clone)]
pub struct WasmImport {
    /// Module name (e.g., "phronesis_rt").
    pub module: String,
    /// Function name.
    pub name: String,
    /// Parameter types.
    pub params: Vec<WasmType>,
    /// Return type (None = void).
    pub result: Option<WasmType>,
}

/// Output of the Phronesis WASM backend.
#[derive(Debug, Clone)]
pub struct WasmModule {
    /// Compiled functions.
    pub functions: Vec<WasmFunction>,
    /// Required imports.
    pub imports: Vec<WasmImport>,
    /// Initial memory pages (64KB each).
    pub initial_memory_pages: u32,
    /// Maximum memory pages.
    pub max_memory_pages: u32,
    /// The WASM binary module bytes.
    binary: Vec<u8>,
}

impl WasmModule {
    /// Get the WASM binary bytes.
    pub fn to_bytes(&self) -> &[u8] {
        &self.binary
    }

    /// Consume and return the WASM binary bytes.
    pub fn into_bytes(self) -> Vec<u8> {
        self.binary
    }
}

/// Bump allocator for WASM linear memory.
struct BumpAllocator {
    next_offset: u32,
    capacity: u32,
}

impl BumpAllocator {
    fn new(initial_offset: u32, initial_pages: u32) -> Self {
        Self {
            next_offset: initial_offset,
            capacity: initial_pages.saturating_mul(65536),
        }
    }

    fn alloc(&mut self, size: u32) -> Result<u32, WasmError> {
        let aligned = (self.next_offset + 7) & !7;
        let new_offset = aligned.checked_add(size).ok_or(WasmError::HeapOverflow {
            requested: size,
            current: self.next_offset,
            capacity: self.capacity,
        })?;
        if new_offset > self.capacity {
            return Err(WasmError::HeapOverflow {
                requested: size,
                current: self.next_offset,
                capacity: self.capacity,
            });
        }
        self.next_offset = new_offset;
        Ok(aligned)
    }
}

/// How a policy rule evaluates its verdict.
#[derive(Debug, Clone)]
pub enum PolicyBody {
    /// Always accept.
    Accept,
    /// Always reject.
    Reject,
    /// Check if a context value exceeds a threshold.
    /// context_get(key) > threshold => accept, else reject.
    ThresholdCheck {
        context_key: String,
        threshold: i64,
    },
    /// AND-combine multiple sub-rules (all must accept).
    And(Vec<String>),
    /// OR-combine multiple sub-rules (at least one must accept).
    Or(Vec<String>),
    /// Invert a single sub-rule.
    Not(String),
}

/// A policy rule to compile.
#[derive(Debug, Clone)]
pub struct PolicyRule {
    /// Policy name (becomes the WASM function name).
    pub name: String,
    /// Evaluation body.
    pub body: PolicyBody,
    /// Priority for precedence ordering (higher = evaluated first).
    /// When `policy_eval_all` is emitted, rules are tried in
    /// descending priority order.
    pub priority: i32,
    /// Obligation action ID to execute on accept (None = no obligation).
    pub on_accept_obligation: Option<i32>,
    /// Obligation action ID to execute on reject (None = no obligation).
    pub on_reject_obligation: Option<i32>,
    /// Temporal validity: earliest valid time (UNIX timestamp in
    /// nanoseconds). `None` means no lower bound.
    pub valid_from: Option<i64>,
    /// Temporal validity: latest valid time (UNIX timestamp in
    /// nanoseconds). `None` means no upper bound.
    pub valid_until: Option<i64>,
}

impl Default for PolicyRule {
    fn default() -> Self {
        Self {
            name: String::new(),
            body: PolicyBody::Reject,
            priority: 0,
            on_accept_obligation: None,
            on_reject_obligation: None,
            valid_from: None,
            valid_until: None,
        }
    }
}

/// Input to the Phronesis WASM backend.
#[derive(Debug, Clone)]
pub struct PhronesisProgram {
    /// Policy rules.
    pub rules: Vec<PolicyRule>,
    /// String constants (context keys, policy names, reason messages).
    pub string_constants: Vec<String>,
}

/// WASM backend for Phronesis.
pub struct WasmBackend {
    initial_memory_pages: u32,
    max_memory_pages: u32,
    warnings: Vec<String>,
}

impl WasmBackend {
    /// Create a new WASM backend with default memory settings.
    pub fn new() -> Self {
        Self {
            initial_memory_pages: 4,
            max_memory_pages: 64,
            warnings: Vec::new(),
        }
    }

    /// Retrieve any warnings generated during the last `generate()` call.
    pub fn warnings(&self) -> &[String] {
        &self.warnings
    }

    /// Set initial memory pages.
    pub fn with_initial_memory(mut self, pages: u32) -> Self {
        self.initial_memory_pages = pages;
        self
    }

    /// Set maximum memory pages.
    pub fn with_max_memory(mut self, pages: u32) -> Self {
        self.max_memory_pages = pages;
        self
    }

    /// Generate a WASM module from a Phronesis program.
    ///
    /// Each policy rule compiles to a WASM function returning i32
    /// (1 = accept, 0 = reject). Composite policies (AND/OR/NOT) call
    /// their sub-rule functions and combine results.
    pub fn generate(&mut self, program: &PhronesisProgram) -> Result<WasmModule, WasmError> {
        self.warnings.clear();

        // Check for duplicate policy names
        let mut seen_names: HashMap<&str, bool> = HashMap::new();
        for rule in &program.rules {
            if seen_names.contains_key(rule.name.as_str()) {
                return Err(WasmError::DuplicatePolicyName {
                    name: rule.name.clone(),
                });
            }
            seen_names.insert(&rule.name, true);
        }

        // Build rule name to index map (for composite policies to call sub-rules)
        let rule_index: HashMap<&str, u32> = program
            .rules
            .iter()
            .enumerate()
            .map(|(i, r)| (r.name.as_str(), i as u32))
            .collect();

        // Validate composite policy references
        for rule in &program.rules {
            let sub_rules: Vec<&str> = match &rule.body {
                PolicyBody::And(refs) | PolicyBody::Or(refs) => {
                    refs.iter().map(|s| s.as_str()).collect()
                }
                PolicyBody::Not(r) => vec![r.as_str()],
                _ => vec![],
            };
            for sub in sub_rules {
                if !rule_index.contains_key(sub) {
                    return Err(WasmError::UnknownSubRule {
                        rule: sub.to_string(),
                        policy: rule.name.clone(),
                    });
                }
            }
        }

        // Collect string constants
        let string_offsets = self.collect_strings(&program.string_constants)?;

        // Build imports
        let imports = vec![
            WasmImport {
                module: "phronesis_rt".into(),
                name: "context_get".into(),
                params: vec![WasmType::I32, WasmType::I32], // key_ptr, key_len
                result: Some(WasmType::I64),                // context value
            },
            WasmImport {
                module: "phronesis_rt".into(),
                name: "audit_log".into(),
                params: vec![WasmType::I32, WasmType::I32, WasmType::I32], // policy_ptr, len, verdict
                result: None,
            },
            WasmImport {
                module: "phronesis_rt".into(),
                name: "escalate".into(),
                params: vec![WasmType::I32, WasmType::I32], // policy_ptr, len
                result: Some(WasmType::I32),                // escalated verdict
            },
            WasmImport {
                module: "phronesis_rt".into(),
                name: "obligation_execute".into(),
                params: vec![WasmType::I32], // action_id
                result: None,
            },
            WasmImport {
                module: "wasi_snapshot_preview1".into(),
                name: "clock_time_get".into(),
                params: vec![WasmType::I32, WasmType::I64, WasmType::I32], // clock_id, precision, result_ptr
                result: Some(WasmType::I32), // errno
            },
            WasmImport {
                module: "phronesis_rt".into(),
                name: "warn_missing_key".into(),
                params: vec![WasmType::I32, WasmType::I32], // key_ptr, key_len
                result: None,
            },
        ];
        let import_count = imports.len() as u32;

        // Compile policy rules
        let mut compiled_funcs: Vec<(Vec<WasmType>, Option<WasmType>, WasmFunc)> = Vec::new();
        let mut wasm_functions: Vec<WasmFunction> = Vec::new();

        for rule in &program.rules {
            let is_composite = matches!(
                rule.body,
                PolicyBody::And(_) | PolicyBody::Or(_) | PolicyBody::Not(_)
            );

            // Temporal policies need a local for the timestamp result.
            // Import indices: context_get=0, audit_log=1, escalate=2,
            //   obligation_execute=3, clock_time_get=4, warn_missing_key=5
            let has_temporal = rule.valid_from.is_some() || rule.valid_until.is_some();
            let has_obligations =
                rule.on_accept_obligation.is_some() || rule.on_reject_obligation.is_some();

            // Extra locals: local 1 = verdict (i32), local 2 = timestamp scratch (i64)
            let extra_locals = if has_temporal {
                vec![(1, ValType::I32), (1, ValType::I64)]
            } else if has_obligations {
                vec![(1, ValType::I32)]
            } else {
                vec![]
            };
            let mut func_body = WasmFunc::new(extra_locals);

            // === Temporal gate: check valid_from / valid_until ===
            if has_temporal {
                // Call clock_time_get(clock_id=0 (realtime), precision=1000, result_ptr=0)
                // Result is written to linear memory at offset 0 (8 bytes).
                func_body.instruction(&Instruction::I32Const(0)); // clock_id: realtime
                func_body.instruction(&Instruction::I64Const(1000)); // precision: 1us
                func_body.instruction(&Instruction::I32Const(0)); // result_ptr
                func_body.instruction(&Instruction::Call(4)); // clock_time_get
                func_body.instruction(&Instruction::Drop); // drop errno

                // Load timestamp from memory[0] as i64
                func_body.instruction(&Instruction::I32Const(0));
                func_body.instruction(&Instruction::I64Load(wasm_encoder::MemArg {
                    offset: 0,
                    align: 3,
                    memory_index: 0,
                }));
                func_body.instruction(&Instruction::LocalSet(2)); // timestamp

                // Check valid_from: if now < valid_from, skip (return 0)
                if let Some(from_ns) = rule.valid_from {
                    func_body.instruction(&Instruction::LocalGet(2));
                    func_body.instruction(&Instruction::I64Const(from_ns));
                    func_body.instruction(&Instruction::I64LtS);
                    func_body.instruction(&Instruction::If(wasm_encoder::BlockType::Empty));
                    func_body.instruction(&Instruction::I32Const(0));
                    func_body.instruction(&Instruction::Return);
                    func_body.instruction(&Instruction::End);
                }

                // Check valid_until: if now > valid_until, skip (return 0)
                if let Some(until_ns) = rule.valid_until {
                    func_body.instruction(&Instruction::LocalGet(2));
                    func_body.instruction(&Instruction::I64Const(until_ns));
                    func_body.instruction(&Instruction::I64GtS);
                    func_body.instruction(&Instruction::If(wasm_encoder::BlockType::Empty));
                    func_body.instruction(&Instruction::I32Const(0));
                    func_body.instruction(&Instruction::Return);
                    func_body.instruction(&Instruction::End);
                }
            }

            // === Policy body evaluation ===
            match &rule.body {
                PolicyBody::Accept => {
                    func_body.instruction(&Instruction::I32Const(1));
                }

                PolicyBody::Reject => {
                    func_body.instruction(&Instruction::I32Const(0));
                }

                PolicyBody::ThresholdCheck {
                    context_key,
                    threshold,
                } => {
                    // Look up context key in string offsets
                    let key_offset = string_offsets
                        .iter()
                        .find(|(s, _)| s == context_key)
                        .map(|(_, off)| *off);

                    if let Some(offset) = key_offset {
                        // context_get(key_ptr, key_len)
                        func_body.instruction(&Instruction::I32Const(offset as i32));
                        func_body
                            .instruction(&Instruction::I32Const(context_key.len() as i32));
                        func_body.instruction(&Instruction::Call(0)); // context_get

                        // Compare: result > threshold
                        func_body.instruction(&Instruction::I64Const(*threshold));
                        func_body.instruction(&Instruction::I64GtS);
                    } else {
                        // Key not in string constants — warn via runtime import, then
                        // default to reject.
                        func_body.instruction(&Instruction::I32Const(0)); // key_ptr (unavailable)
                        func_body.instruction(&Instruction::I32Const(context_key.len() as i32));
                        func_body.instruction(&Instruction::Call(5)); // warn_missing_key
                        func_body.instruction(&Instruction::I32Const(0)); // default reject
                    }
                }

                PolicyBody::And(sub_rules) => {
                    // Start with 1 (accept), AND each sub-rule result
                    func_body.instruction(&Instruction::I32Const(1));
                    for sub in sub_rules {
                        if let Some(&idx) = rule_index.get(sub.as_str()) {
                            // Call sub-rule with the same context pointer
                            func_body.instruction(&Instruction::LocalGet(0));
                            func_body.instruction(&Instruction::Call(import_count + idx));
                            func_body.instruction(&Instruction::I32And);
                        }
                    }
                }

                PolicyBody::Or(sub_rules) => {
                    // Start with 0 (reject), OR each sub-rule result
                    func_body.instruction(&Instruction::I32Const(0));
                    for sub in sub_rules {
                        if let Some(&idx) = rule_index.get(sub.as_str()) {
                            func_body.instruction(&Instruction::LocalGet(0));
                            func_body.instruction(&Instruction::Call(import_count + idx));
                            func_body.instruction(&Instruction::I32Or);
                        }
                    }
                }

                PolicyBody::Not(sub) => {
                    if let Some(&idx) = rule_index.get(sub.as_str()) {
                        func_body.instruction(&Instruction::LocalGet(0));
                        func_body.instruction(&Instruction::Call(import_count + idx));
                        func_body.instruction(&Instruction::I32Eqz); // invert: 0->1, nonzero->0
                    } else {
                        func_body.instruction(&Instruction::I32Const(0));
                    }
                }
            }

            // === Obligation actions ===
            // At this point the verdict (i32) is on the stack.
            if has_obligations {
                // Store verdict in local 1
                func_body.instruction(&Instruction::LocalSet(1));

                // Execute accept obligation if verdict == 1
                if let Some(accept_action) = rule.on_accept_obligation {
                    func_body.instruction(&Instruction::LocalGet(1));
                    func_body.instruction(&Instruction::If(wasm_encoder::BlockType::Empty));
                    func_body.instruction(&Instruction::I32Const(accept_action));
                    func_body.instruction(&Instruction::Call(3)); // obligation_execute
                    func_body.instruction(&Instruction::End);
                }

                // Execute reject obligation if verdict == 0
                if let Some(reject_action) = rule.on_reject_obligation {
                    func_body.instruction(&Instruction::LocalGet(1));
                    func_body.instruction(&Instruction::I32Eqz);
                    func_body.instruction(&Instruction::If(wasm_encoder::BlockType::Empty));
                    func_body.instruction(&Instruction::I32Const(reject_action));
                    func_body.instruction(&Instruction::Call(3)); // obligation_execute
                    func_body.instruction(&Instruction::End);
                }

                // Push verdict back on stack for return
                func_body.instruction(&Instruction::LocalGet(1));
            }

            func_body.instruction(&Instruction::End);

            // All policy functions: (context_ptr: i32) -> i32 verdict
            compiled_funcs.push((vec![WasmType::I32], Some(WasmType::I32), func_body));
            wasm_functions.push(WasmFunction {
                name: rule.name.clone(),
                params: vec![WasmType::I32],
                result: Some(WasmType::I32),
                code_size: 5, // approximate
                is_composite,
            });
        }

        // === policy_eval_all: iterate rules in priority order ===
        // Emits a function that calls each policy in descending priority
        // order and returns the verdict of the first accepting policy.
        // If none accept, returns 0 (reject).
        // Signature: (context_ptr: i32) -> i32
        if !program.rules.is_empty() {
            let mut sorted_indices: Vec<(usize, i32)> = program
                .rules
                .iter()
                .enumerate()
                .map(|(i, r)| (i, r.priority))
                .collect();
            sorted_indices.sort_by(|a, b| b.1.cmp(&a.1)); // descending priority

            let mut func_body = WasmFunc::new(vec![
                (1, ValType::I32), // local 1: verdict scratch
            ]);

            for (rule_idx, _priority) in &sorted_indices {
                // Call rule function with context_ptr
                func_body.instruction(&Instruction::LocalGet(0)); // context_ptr
                func_body.instruction(&Instruction::Call(import_count + *rule_idx as u32));
                func_body.instruction(&Instruction::LocalSet(1)); // store verdict

                // If verdict == 1 (accept), return immediately
                func_body.instruction(&Instruction::LocalGet(1));
                func_body.instruction(&Instruction::If(wasm_encoder::BlockType::Empty));
                func_body.instruction(&Instruction::LocalGet(1));
                func_body.instruction(&Instruction::Return);
                func_body.instruction(&Instruction::End);
            }

            // No rule accepted — return 0
            func_body.instruction(&Instruction::I32Const(0));
            func_body.instruction(&Instruction::End);

            compiled_funcs.push((vec![WasmType::I32], Some(WasmType::I32), func_body));
            wasm_functions.push(WasmFunction {
                name: "policy_eval_all".into(),
                params: vec![WasmType::I32],
                result: Some(WasmType::I32),
                code_size: 5 + program.rules.len() * 5,
                is_composite: true,
            });
        }

        // Build WASM binary
        let binary = self.build_module(&imports, &compiled_funcs, &string_offsets, &wasm_functions);

        Ok(WasmModule {
            functions: wasm_functions,
            imports,
            initial_memory_pages: self.initial_memory_pages,
            max_memory_pages: self.max_memory_pages,
            binary,
        })
    }

    /// Collect string constants and assign data section offsets.
    fn collect_strings(&mut self, strings: &[String]) -> Result<Vec<(String, u32)>, WasmError> {
        let mut result = Vec::new();
        let mut offset: u32 = 0;
        let capacity = self.initial_memory_pages.saturating_mul(65536);

        for s in strings {
            let entry_size = s.len() as u32 + 1;
            let new_offset = offset.checked_add(entry_size).ok_or(
                WasmError::DataSectionOverflow { offset, capacity },
            )?;
            if new_offset > capacity {
                return Err(WasmError::DataSectionOverflow {
                    offset: new_offset,
                    capacity,
                });
            }
            result.push((s.clone(), offset));
            offset = new_offset;
        }

        if capacity > 0 && offset > capacity * 3 / 4 {
            self.warnings.push(format!(
                "data section uses {offset}/{capacity} bytes ({:.0}% of initial memory)",
                offset as f64 / capacity as f64 * 100.0
            ));
        }

        Ok(result)
    }

    /// Build the complete WASM binary module.
    fn build_module(
        &self,
        imports: &[WasmImport],
        compiled_funcs: &[(Vec<WasmType>, Option<WasmType>, WasmFunc)],
        string_data: &[(String, u32)],
        wasm_functions: &[WasmFunction],
    ) -> Vec<u8> {
        let mut module = Module::new();
        let import_count = imports.len() as u32;

        // === Type section ===
        let mut types = TypeSection::new();
        for imp in imports {
            let params: Vec<ValType> = imp.params.iter().map(|t| t.to_val_type()).collect();
            let results: Vec<ValType> = imp.result.iter().map(|t| t.to_val_type()).collect();
            types.ty().function(params, results);
        }
        for (params, result, _) in compiled_funcs {
            let wasm_params: Vec<ValType> = params.iter().map(|t| t.to_val_type()).collect();
            let wasm_results: Vec<ValType> = result.iter().map(|t| t.to_val_type()).collect();
            types.ty().function(wasm_params, wasm_results);
        }
        module.section(&types);

        // === Import section ===
        if !imports.is_empty() {
            let mut import_section = ImportSection::new();
            for (i, imp) in imports.iter().enumerate() {
                import_section.import(
                    &imp.module,
                    &imp.name,
                    EntityType::Function(i as u32),
                );
            }
            module.section(&import_section);
        }

        // === Function section ===
        let mut func_section = FunctionSection::new();
        for i in 0..compiled_funcs.len() {
            func_section.function(import_count + i as u32);
        }
        module.section(&func_section);

        // === Memory section ===
        let mut memory_section = MemorySection::new();
        memory_section.memory(MemoryType {
            minimum: self.initial_memory_pages as u64,
            maximum: Some(self.max_memory_pages as u64),
            memory64: false,
            shared: false,
            page_size_log2: None,
        });
        module.section(&memory_section);

        // === Export section ===
        let mut export_section = ExportSection::new();
        for (i, func) in wasm_functions.iter().enumerate() {
            export_section.export(
                &func.name,
                ExportKind::Func,
                import_count + i as u32,
            );
        }
        export_section.export("memory", ExportKind::Memory, 0);
        module.section(&export_section);

        // === Code section ===
        let mut code_section = CodeSection::new();
        for (_, _, func_body) in compiled_funcs {
            code_section.function(func_body);
        }
        module.section(&code_section);

        // === Data section ===
        if !string_data.is_empty() {
            let mut data_section = DataSection::new();
            for (s, offset) in string_data {
                let mut bytes = s.as_bytes().to_vec();
                bytes.push(0);
                data_section.active(
                    0,
                    &wasm_encoder::ConstExpr::i32_const(*offset as i32),
                    bytes,
                );
            }
            module.section(&data_section);
        }

        module.finish()
    }
}

impl Default for WasmBackend {
    fn default() -> Self {
        Self::new()
    }
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    /// Helper: create an empty Phronesis program.
    fn empty_program() -> PhronesisProgram {
        PhronesisProgram {
            rules: vec![],
            string_constants: vec![],
        }
    }

    /// Helper: create a simple program with accept/reject rules.
    fn simple_program() -> PhronesisProgram {
        PhronesisProgram {
            rules: vec![
                PolicyRule {
                    name: "allow_all".into(),
                    body: PolicyBody::Accept,
                    ..Default::default()
                },
                PolicyRule {
                    name: "deny_all".into(),
                    body: PolicyBody::Reject,
                },
            ],
            string_constants: vec![],
        }
    }

    #[test]
    fn test_empty_program_generates_valid_wasm() {
        let mut backend = WasmBackend::new();
        let module = backend.generate(&empty_program()).expect("TODO: handle error");
        let bytes = module.to_bytes();
        assert_eq!(&bytes[0..4], b"\0asm");
        assert_eq!(bytes[4], 1);
        assert!(module.functions.is_empty());
    }

    #[test]
    fn test_simple_accept_reject_rules() {
        let mut backend = WasmBackend::new();
        let module = backend.generate(&simple_program()).expect("TODO: handle error");
        assert_eq!(module.functions.len(), 2);
        assert_eq!(module.functions[0].name, "allow_all");
        assert_eq!(module.functions[1].name, "deny_all");
        // Both return i32 verdicts
        assert_eq!(module.functions[0].result, Some(WasmType::I32));
        assert_eq!(module.functions[1].result, Some(WasmType::I32));
        let bytes = module.to_bytes();
        assert_eq!(&bytes[0..4], b"\0asm");
    }

    #[test]
    fn test_composite_and_policy() {
        let program = PhronesisProgram {
            rules: vec![
                PolicyRule {
                    name: "rule_a".into(),
                    body: PolicyBody::Accept,
                    ..Default::default()
                },
                PolicyRule {
                    name: "rule_b".into(),
                    body: PolicyBody::Accept,
                    ..Default::default()
                },
                PolicyRule {
                    name: "both_must_accept".into(),
                    body: PolicyBody::And(vec!["rule_a".into(), "rule_b".into()]),
                },
            ],
            string_constants: vec![],
        };

        let mut backend = WasmBackend::new();
        let module = backend.generate(&program).expect("TODO: handle error");
        assert_eq!(module.functions.len(), 3);
        assert!(module.functions[2].is_composite);
        assert_eq!(module.functions[2].name, "both_must_accept");
    }

    #[test]
    fn test_composite_not_policy() {
        let program = PhronesisProgram {
            rules: vec![
                PolicyRule {
                    name: "base_rule".into(),
                    body: PolicyBody::Reject,
                },
                PolicyRule {
                    name: "inverted".into(),
                    body: PolicyBody::Not("base_rule".into()),
                },
            ],
            string_constants: vec![],
        };

        let mut backend = WasmBackend::new();
        let module = backend.generate(&program).expect("TODO: handle error");
        assert_eq!(module.functions.len(), 2);
        assert!(module.functions[1].is_composite);
    }

    #[test]
    fn test_unknown_sub_rule_errors() {
        let program = PhronesisProgram {
            rules: vec![PolicyRule {
                name: "bad_composite".into(),
                body: PolicyBody::And(vec!["nonexistent".into()]),
            }],
            string_constants: vec![],
        };

        let mut backend = WasmBackend::new();
        let result = backend.generate(&program);
        assert!(result.is_err());
        match result.unwrap_err() {
            WasmError::UnknownSubRule { rule, policy } => {
                assert_eq!(rule, "nonexistent");
                assert_eq!(policy, "bad_composite");
            }
            other => panic!("Expected UnknownSubRule, got: {other}"),
        }
    }

    #[test]
    fn test_duplicate_policy_name_errors() {
        let program = PhronesisProgram {
            rules: vec![
                PolicyRule {
                    name: "rule".into(),
                    body: PolicyBody::Accept,
                    ..Default::default()
                },
                PolicyRule {
                    name: "rule".into(),
                    body: PolicyBody::Reject,
                },
            ],
            string_constants: vec![],
        };

        let mut backend = WasmBackend::new();
        let result = backend.generate(&program);
        assert!(result.is_err());
        match result.unwrap_err() {
            WasmError::DuplicatePolicyName { name } => assert_eq!(name, "rule"),
            other => panic!("Expected DuplicatePolicyName, got: {other}"),
        }
    }

    #[test]
    fn test_binary_output_is_deterministic() {
        let program = simple_program();
        let mut b1 = WasmBackend::new();
        let mut b2 = WasmBackend::new();
        let m1 = b1.generate(&program).expect("TODO: handle error");
        let m2 = b2.generate(&program).expect("TODO: handle error");
        assert_eq!(m1.to_bytes(), m2.to_bytes());
    }

    #[test]
    fn test_module_has_runtime_imports() {
        let mut backend = WasmBackend::new();
        let module = backend.generate(&simple_program()).expect("TODO: handle error");
        assert_eq!(module.imports.len(), 3);
        assert_eq!(module.imports[0].name, "context_get");
        assert_eq!(module.imports[1].name, "audit_log");
        assert_eq!(module.imports[2].name, "escalate");
    }

    #[test]
    fn test_threshold_check_with_context() {
        let program = PhronesisProgram {
            rules: vec![PolicyRule {
                name: "age_check".into(),
                body: PolicyBody::ThresholdCheck {
                    context_key: "age".into(),
                    threshold: 18,
                },
            }],
            string_constants: vec!["age".into()],
        };

        let mut backend = WasmBackend::new();
        let module = backend.generate(&program).expect("TODO: handle error");
        assert_eq!(module.functions.len(), 1);
        assert_eq!(module.functions[0].name, "age_check");
        assert!(!module.functions[0].is_composite);
        let bytes = module.to_bytes();
        assert_eq!(&bytes[0..4], b"\0asm");
    }

    #[test]
    fn test_error_display_messages() {
        let err = WasmError::UnknownSubRule {
            rule: "missing".into(),
            policy: "composite".into(),
        };
        let msg = err.to_string();
        assert!(msg.contains("missing") && msg.contains("composite"));

        let err = WasmError::CircularDependency {
            name: "loop_rule".into(),
        };
        assert!(err.to_string().contains("loop_rule"));

        let err = WasmError::HeapOverflow {
            requested: 128,
            current: 65400,
            capacity: 65536,
        };
        assert!(err.to_string().contains("128"));
    }

    #[test]
    fn test_bump_allocator_bounds_check() {
        let mut alloc = BumpAllocator::new(65530, 1);
        let result = alloc.alloc(16);
        assert!(result.is_err());
        match result.unwrap_err() {
            WasmError::HeapOverflow { requested, .. } => assert_eq!(requested, 16),
            other => panic!("Expected HeapOverflow, got: {other}"),
        }
    }

    #[test]
    fn test_or_composite_policy() {
        let program = PhronesisProgram {
            rules: vec![
                PolicyRule {
                    name: "fast_path".into(),
                    body: PolicyBody::Accept,
                    ..Default::default()
                },
                PolicyRule {
                    name: "slow_path".into(),
                    body: PolicyBody::Reject,
                },
                PolicyRule {
                    name: "either_ok".into(),
                    body: PolicyBody::Or(vec!["fast_path".into(), "slow_path".into()]),
                },
            ],
            string_constants: vec![],
        };

        let mut backend = WasmBackend::new();
        let module = backend.generate(&program).expect("TODO: handle error");
        assert_eq!(module.functions.len(), 3);
        assert!(module.functions[2].is_composite);
    }

    #[test]
    fn test_string_constants_in_data_section() {
        let program = PhronesisProgram {
            rules: vec![],
            string_constants: vec!["policy_name".into(), "reason_denied".into()],
        };

        let mut backend = WasmBackend::new();
        let module = backend.generate(&program).expect("TODO: handle error");
        let bytes = module.to_bytes();
        assert_eq!(&bytes[0..4], b"\0asm");
        assert!(bytes.len() > 20);
    }
}
