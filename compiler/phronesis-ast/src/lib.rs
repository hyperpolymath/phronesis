// SPDX-License-Identifier: MPL-2.0
// Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

#![forbid(unsafe_code)]

//! Abstract syntax tree definitions for the Phronesis policy language.
//!
//! Phronesis is a provably-terminating policy DSL for ethical/agentic reasoning.
//! Its programs consist of policy declarations with conditions, actions, and
//! metadata (priority, expiry, authorship). The AST defined here faithfully
//! represents the grammar in `spec/grammar.ebnf` and the core semantics in
//! `spec/SPEC.core.scm`.
//!
//! ## Design decisions
//!
//! - Every AST node that can appear in source carries a [`Span`] for
//!   diagnostics and IDE tooling (LSP, error messages, code actions).
//! - An [`Expr::Error`] variant enables error-recovery parsing: the parser
//!   can insert a sentinel node and continue, collecting multiple diagnostics
//!   in a single pass.
//! - `serde` support is behind a feature flag (`serde`) so downstream crates
//!   that do not need serialisation avoid the dependency.
//! - Types derive `Debug`, `Clone`, `PartialEq` uniformly to support both
//!   testing (assertion equality) and tree transformations (clone + modify).

// ---------------------------------------------------------------------------
// 1. Span — source location tracking
// ---------------------------------------------------------------------------

/// A half-open byte range `[start, end)` in the source text.
///
/// Byte offsets are `u32` because Phronesis policy files are expected to be
/// well under 4 GiB. The `synthetic` constructor produces a zero-length span
/// for compiler-generated nodes that have no corresponding source text.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Span {
    /// Inclusive start byte offset.
    pub start: u32,
    /// Exclusive end byte offset.
    pub end: u32,
}

impl Span {
    /// Create a span covering `[start, end)`.
    #[inline]
    pub fn new(start: u32, end: u32) -> Self {
        Self { start, end }
    }

    /// Create a zero-length synthetic span (no source location).
    ///
    /// Used for compiler-generated or desugared nodes.
    #[inline]
    pub fn synthetic() -> Self {
        Self { start: 0, end: 0 }
    }

    /// Returns `true` when this span was created by [`Span::synthetic`].
    #[inline]
    pub fn is_synthetic(&self) -> bool {
        self.start == 0 && self.end == 0
    }

    /// Merge two spans into one that covers both.
    #[inline]
    pub fn merge(self, other: Self) -> Self {
        Self {
            start: self.start.min(other.start),
            end: self.end.max(other.end),
        }
    }

    /// Byte length of the span.
    #[inline]
    pub fn len(&self) -> u32 {
        self.end.saturating_sub(self.start)
    }

    /// Returns `true` when the span covers zero bytes.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.start >= self.end
    }
}

// ---------------------------------------------------------------------------
// 2. Program — top-level container
// ---------------------------------------------------------------------------

/// A complete Phronesis source file.
///
/// ```text
/// program = { declaration } ;
/// ```
#[derive(Debug, Clone, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Program {
    /// Top-level declarations in source order.
    pub declarations: Vec<Declaration>,
    /// Span covering the entire file.
    pub span: Span,
}

// ---------------------------------------------------------------------------
// 3. Declarations / Items
// ---------------------------------------------------------------------------

/// A top-level declaration.
///
/// ```text
/// declaration = policy_decl | import_decl | const_decl ;
/// ```
#[derive(Debug, Clone, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Declaration {
    pub kind: DeclarationKind,
    pub span: Span,
}

/// The different kinds of top-level declaration.
#[derive(Debug, Clone, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum DeclarationKind {
    /// A policy rule declaration.
    ///
    /// ```text
    /// POLICY <name>: <condition> THEN <action> <metadata>
    /// ```
    Policy(PolicyDecl),

    /// An import declaration.
    ///
    /// ```text
    /// IMPORT <module_path> [ AS <alias> ]
    /// ```
    Import(ImportDecl),

    /// A constant binding.
    ///
    /// ```text
    /// CONST <name> = <expr>
    /// ```
    Const(ConstDecl),

    /// A chain declaration (groups policies for ordered evaluation).
    ///
    /// ```text
    /// CHAIN <name>: <policy_refs>
    /// ```
    Chain(ChainDecl),

    /// An error placeholder produced by recovery parsing.
    Error {
        /// Diagnostic message explaining the parse failure.
        message: String,
    },
}

/// A policy declaration — the central construct of Phronesis.
///
/// Models the 5-tuple `(name, condition, action, priority, metadata)` from
/// `SPEC.core.scm`.
#[derive(Debug, Clone, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct PolicyDecl {
    /// Policy name (identifier after `POLICY`).
    pub name: Identifier,
    /// The condition expression that gates the action.
    pub condition: Expr,
    /// The action to execute when the condition is true.
    pub action: Action,
    /// Policy metadata: priority, expiry, creator.
    pub metadata: PolicyMetadata,
}

/// Policy metadata fields.
#[derive(Debug, Clone, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct PolicyMetadata {
    /// Numeric priority (higher = evaluated first).
    pub priority: Expr,
    /// Optional expiry value (`"never"` or a datetime literal).
    pub expires: Option<Expr>,
    /// Optional creator identifier.
    pub created_by: Option<Identifier>,
    /// Span covering all metadata fields.
    pub span: Span,
}

/// An import declaration.
#[derive(Debug, Clone, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct ImportDecl {
    /// Dot-separated module path (e.g., `Std.RPKI`).
    pub path: ModulePath,
    /// Optional alias (`AS <name>`).
    pub alias: Option<Identifier>,
}

/// A dot-separated module path.
#[derive(Debug, Clone, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct ModulePath {
    /// Path segments (e.g., `["Std", "RPKI"]`).
    pub segments: Vec<Identifier>,
    pub span: Span,
}

/// A constant binding.
#[derive(Debug, Clone, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct ConstDecl {
    /// The constant name.
    pub name: Identifier,
    /// The value expression.
    pub value: Expr,
}

/// A chain declaration groups policies for ordered evaluation.
#[derive(Debug, Clone, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct ChainDecl {
    /// Chain name.
    pub name: Identifier,
    /// References to policy names in evaluation order.
    pub policies: Vec<Identifier>,
}

// ---------------------------------------------------------------------------
// 4. Expressions
// ---------------------------------------------------------------------------

/// An expression with source location.
#[derive(Debug, Clone, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Expr {
    pub kind: ExprKind,
    pub span: Span,
}

/// Expression variants.
///
/// Covers literals, variables, binary/unary operations, function calls,
/// comparisons, field access, actions, and error recovery.
#[derive(Debug, Clone, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum ExprKind {
    // -- Literals ---------------------------------------------------------

    /// Integer literal (decimal, hex `0x`, binary `0b`, or octal `0o`).
    IntLiteral(i64),

    /// Floating-point literal.
    FloatLiteral(f64),

    /// String literal (regular, raw, or multiline).
    StringLiteral(String),

    /// Interpolated string with embedded `${expr}` segments.
    InterpolatedString(Vec<StringSegment>),

    /// Boolean literal (`true` / `false`).
    BoolLiteral(bool),

    /// Null literal.
    NullLiteral,

    /// IPv4 address, optionally with CIDR prefix length.
    ///
    /// Stored as the raw string (e.g., `"192.168.1.0/24"`) because
    /// semantic analysis is responsible for parsing and validating the
    /// address.
    Ipv4Address(String),

    /// IPv6 address, optionally with CIDR prefix length.
    ///
    /// Stored as the raw string (e.g., `"2001:db8::/32"`).
    Ipv6Address(String),

    /// ISO 8601 datetime literal.
    DateTimeLiteral(String),

    /// List literal (e.g., `[64496, 64497, 64498]`).
    ListLiteral(Vec<Expr>),

    // -- Names and access -------------------------------------------------

    /// A variable reference.
    Variable(Identifier),

    /// Field access: `expr.field`.
    FieldAccess {
        object: Box<Expr>,
        field: Identifier,
    },

    /// Optional chaining: `expr?.field`.
    OptionalChain {
        object: Box<Expr>,
        field: Identifier,
    },

    // -- Operations -------------------------------------------------------

    /// Binary operation: `lhs <op> rhs`.
    BinaryOp {
        lhs: Box<Expr>,
        op: BinaryOp,
        rhs: Box<Expr>,
    },

    /// Unary operation: `<op> operand`.
    UnaryOp {
        op: UnaryOp,
        operand: Box<Expr>,
    },

    /// Comparison: `lhs <relop> rhs`.
    ///
    /// Separated from `BinaryOp` because comparisons produce boolean
    /// values and are the primary building block of policy conditions.
    Comparison {
        lhs: Box<Expr>,
        op: ComparisonOp,
        rhs: Box<Expr>,
    },

    /// Logical connective: `lhs AND rhs` or `lhs OR rhs`.
    Logical {
        lhs: Box<Expr>,
        op: LogicalOp,
        rhs: Box<Expr>,
    },

    /// Logical NOT: `NOT expr`.
    LogicalNot(Box<Expr>),

    // -- Calls ------------------------------------------------------------

    /// Function or module call: `callee(args)`.
    ///
    /// The callee may be a dotted path (e.g., `Std.RPKI.validate`).
    FunctionCall {
        callee: Box<Expr>,
        arguments: Vec<Argument>,
    },

    // -- Actions (as expressions) -----------------------------------------

    /// An action expression (EXECUTE, REJECT, ACCEPT, REPORT, etc.).
    Action(Action),

    // -- Priority ---------------------------------------------------------

    /// A priority expression (wraps the numeric priority value).
    Priority(Box<Expr>),

    // -- Assignment -------------------------------------------------------

    /// Local assignment within a policy body: `name = expr`.
    Assignment {
        name: Identifier,
        value: Box<Expr>,
    },

    // -- Conditional expression -------------------------------------------

    /// `IF <cond> THEN <then_expr> [ ELSE <else_expr> ]`
    If {
        condition: Box<Expr>,
        then_branch: Box<Expr>,
        else_branch: Option<Box<Expr>>,
    },

    /// A block of expressions: `BEGIN ... END`.
    Block(Vec<Expr>),

    // -- Grouping ---------------------------------------------------------

    /// Parenthesised expression `(expr)`.
    Grouped(Box<Expr>),

    // -- Error recovery ---------------------------------------------------

    /// Placeholder for a malformed expression.
    ///
    /// Allows the parser to continue after encountering a syntax error,
    /// collecting multiple diagnostics in a single pass.
    Error {
        message: String,
    },
}

/// A segment within an interpolated string.
#[derive(Debug, Clone, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum StringSegment {
    /// Literal text portion.
    Literal(String),
    /// Embedded expression: `${expr}`.
    Interpolation(Expr),
}

/// A function call argument, which may be positional or named.
#[derive(Debug, Clone, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Argument {
    /// `Some(name)` for named arguments (`name: value`), `None` for positional.
    pub name: Option<Identifier>,
    /// The argument value expression.
    pub value: Expr,
    pub span: Span,
}

// ---------------------------------------------------------------------------
// 5. Operators
// ---------------------------------------------------------------------------

/// Arithmetic binary operators.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum BinaryOp {
    /// `+`
    Add,
    /// `-`
    Sub,
    /// `*`
    Mul,
    /// `/`
    Div,
}

/// Unary operators.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum UnaryOp {
    /// Arithmetic negation: `-expr`.
    Neg,
}

/// Comparison / relational operators.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum ComparisonOp {
    /// `==`
    Eq,
    /// `!=`
    NotEq,
    /// `>`
    Gt,
    /// `>=`
    GtEq,
    /// `<`
    Lt,
    /// `<=`
    LtEq,
    /// `IN` (membership test).
    In,
}

/// Logical connectives.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum LogicalOp {
    /// `AND`
    And,
    /// `OR`
    Or,
}

// ---------------------------------------------------------------------------
// 6. Actions
// ---------------------------------------------------------------------------

/// An action that a policy may trigger.
///
/// Actions correspond to the `action` production in the grammar and the
/// `<action>` record type in `SPEC.core.scm`.
#[derive(Debug, Clone, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Action {
    pub kind: ActionKind,
    pub span: Span,
}

/// Action variants.
#[derive(Debug, Clone, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum ActionKind {
    /// `EXECUTE(function, args...)` — invoke an external function.
    ///
    /// Carries the IO effect in the TypeLL bridge.
    Execute {
        function: Identifier,
        arguments: Vec<Argument>,
    },

    /// `REJECT(reason)` — reject with an optional reason.
    ///
    /// Carries the Except("PolicyReject") effect in the TypeLL bridge.
    Reject {
        reason: Option<Box<Expr>>,
    },

    /// `ACCEPT(reason)` — accept with an optional reason.
    Accept {
        reason: Option<Box<Expr>>,
    },

    /// `REPORT(message)` — emit an audit/diagnostic message.
    ///
    /// Carries the IO effect in the TypeLL bridge.
    Report {
        message: Box<Expr>,
    },

    /// `LOG(message)` — write to the decision trace.
    Log {
        message: Box<Expr>,
    },

    /// `DROP` — silently discard (no response, used in firewall contexts).
    Drop,

    /// `BEGIN ... END` — a block of sequential actions.
    Block {
        actions: Vec<Action>,
    },

    /// `IF <cond> THEN <action> [ELSE <action>]` — conditional action.
    Conditional {
        condition: Box<Expr>,
        then_action: Box<Action>,
        else_action: Option<Box<Action>>,
    },
}

// ---------------------------------------------------------------------------
// 7. Conditions
// ---------------------------------------------------------------------------

/// A structured condition for policy matching.
///
/// While conditions can be represented as general [`Expr`] nodes, this enum
/// provides a higher-level, domain-specific view used by analysis passes
/// and the WASM backend.
#[derive(Debug, Clone, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Condition {
    pub kind: ConditionKind,
    pub span: Span,
}

/// Condition variants.
#[derive(Debug, Clone, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum ConditionKind {
    /// Source IP matches a network/CIDR.
    ///
    /// ```text
    /// source_ip IN 192.168.0.0/16
    /// ```
    SourceIpMatch {
        network: Expr,
    },

    /// Destination IP matches a network/CIDR.
    ///
    /// ```text
    /// dest_ip IN 10.0.0.0/8
    /// ```
    DestIpMatch {
        network: Expr,
    },

    /// Port match (source or destination).
    ///
    /// ```text
    /// dest_port == 443
    /// dest_port IN [80, 443, 8080]
    /// ```
    PortMatch {
        direction: PortDirection,
        value: Expr,
    },

    /// Protocol match.
    ///
    /// ```text
    /// protocol == "TCP"
    /// ```
    ProtocolMatch {
        protocol: Expr,
    },

    /// Compound condition: `lhs AND rhs` or `lhs OR rhs`.
    Compound {
        lhs: Box<Condition>,
        op: LogicalOp,
        rhs: Box<Condition>,
    },

    /// Negated condition: `NOT <cond>`.
    Not(Box<Condition>),

    /// A general expression used as a condition (fallback).
    ///
    /// Any boolean-valued expression that does not match a more specific
    /// variant above.
    Expression(Expr),
}

/// Whether a port condition refers to source or destination.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum PortDirection {
    Source,
    Destination,
}

// ---------------------------------------------------------------------------
// 8. Statements
// ---------------------------------------------------------------------------

/// A statement within a policy body or block.
#[derive(Debug, Clone, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Statement {
    pub kind: StatementKind,
    pub span: Span,
}

/// Statement variants.
#[derive(Debug, Clone, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum StatementKind {
    /// An expression evaluated for its side effect.
    Expr(Expr),

    /// A local variable binding: `name = expr`.
    Let {
        name: Identifier,
        value: Expr,
    },

    /// An action statement.
    Action(Action),

    /// A conditional statement.
    If {
        condition: Expr,
        then_branch: Vec<Statement>,
        else_branch: Option<Vec<Statement>>,
    },

    /// An error placeholder for recovery parsing.
    Error {
        message: String,
    },
}

// ---------------------------------------------------------------------------
// 9. Type expressions
// ---------------------------------------------------------------------------

/// A type expression, used in annotations and type-checking.
///
/// Phronesis is not a general-purpose language, so its type system is
/// domain-specific: IP addresses, port ranges, protocol identifiers, and
/// policy-level types.
#[derive(Debug, Clone, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct TypeExpr {
    pub kind: TypeExprKind,
    pub span: Span,
}

/// Type expression variants.
#[derive(Debug, Clone, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum TypeExprKind {
    /// Primitive integer type.
    Integer,

    /// Primitive floating-point type.
    Float,

    /// Primitive string type.
    String,

    /// Primitive boolean type.
    Boolean,

    /// IPv4 address type.
    Ipv4Address,

    /// IPv6 address type.
    Ipv6Address,

    /// Generic IP address type (v4 or v6).
    IpAddress,

    /// CIDR range type (address + prefix length).
    CidrRange,

    /// Port number type (0..65535).
    Port,

    /// Port range type (e.g., `1024..65535`).
    PortRange,

    /// Protocol identifier type (TCP, UDP, ICMP, etc.).
    Protocol,

    /// DateTime type (ISO 8601).
    DateTime,

    /// List type with element type.
    List(Box<TypeExpr>),

    /// A named/user-defined type.
    Named(String),

    /// The type of a policy (carries priority metadata).
    Policy {
        priority_type: Box<TypeExpr>,
    },

    /// The type of an action result.
    ActionResult,

    /// Error recovery placeholder.
    Error,
}

// ---------------------------------------------------------------------------
// 10. Patterns
// ---------------------------------------------------------------------------

/// A pattern for matching values.
///
/// Currently minimal since Phronesis v0.2 does not have full pattern
/// matching, but the AST is designed for forward compatibility.
#[derive(Debug, Clone, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Pattern {
    pub kind: PatternKind,
    pub span: Span,
}

/// Pattern variants.
#[derive(Debug, Clone, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum PatternKind {
    /// Wildcard: matches anything, binds nothing.
    Wildcard,

    /// Bind a name: `x`.
    Binding(Identifier),

    /// Match a literal value.
    Literal(Expr),

    /// Match a CIDR network: `192.168.0.0/16`.
    CidrPattern(String),

    /// Match a port range: `1024..65535`.
    PortRange {
        low: u16,
        high: u16,
    },

    /// Match a protocol name: `:TCP`, `:UDP`, etc.
    Protocol(String),

    /// Match a list of patterns: `[p1, p2, ...]`.
    List(Vec<Pattern>),

    /// Error recovery placeholder.
    Error,
}

// ---------------------------------------------------------------------------
// 11. Shared types
// ---------------------------------------------------------------------------

/// An identifier with source location.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Identifier {
    /// The identifier text.
    pub name: String,
    pub span: Span,
}

impl Identifier {
    /// Create a new identifier with the given name and span.
    pub fn new(name: impl Into<String>, span: Span) -> Self {
        Self {
            name: name.into(),
            span,
        }
    }

    /// Create a synthetic identifier (no source location).
    pub fn synthetic(name: impl Into<String>) -> Self {
        Self {
            name: name.into(),
            span: Span::synthetic(),
        }
    }
}

// ---------------------------------------------------------------------------
// 12. Convenience constructors for Expr
// ---------------------------------------------------------------------------

impl Expr {
    /// Create an integer literal expression.
    pub fn int(value: i64, span: Span) -> Self {
        Self {
            kind: ExprKind::IntLiteral(value),
            span,
        }
    }

    /// Create a float literal expression.
    pub fn float(value: f64, span: Span) -> Self {
        Self {
            kind: ExprKind::FloatLiteral(value),
            span,
        }
    }

    /// Create a string literal expression.
    pub fn string(value: impl Into<String>, span: Span) -> Self {
        Self {
            kind: ExprKind::StringLiteral(value.into()),
            span,
        }
    }

    /// Create a boolean literal expression.
    pub fn boolean(value: bool, span: Span) -> Self {
        Self {
            kind: ExprKind::BoolLiteral(value),
            span,
        }
    }

    /// Create an IPv4 address literal expression.
    pub fn ipv4(addr: impl Into<String>, span: Span) -> Self {
        Self {
            kind: ExprKind::Ipv4Address(addr.into()),
            span,
        }
    }

    /// Create an IPv6 address literal expression.
    pub fn ipv6(addr: impl Into<String>, span: Span) -> Self {
        Self {
            kind: ExprKind::Ipv6Address(addr.into()),
            span,
        }
    }

    /// Create a variable reference expression.
    pub fn var(name: impl Into<String>, span: Span) -> Self {
        Self {
            kind: ExprKind::Variable(Identifier::new(name, span)),
            span,
        }
    }

    /// Create an error recovery expression.
    pub fn error(message: impl Into<String>, span: Span) -> Self {
        Self {
            kind: ExprKind::Error {
                message: message.into(),
            },
            span,
        }
    }

    /// Create a comparison expression.
    pub fn comparison(lhs: Expr, op: ComparisonOp, rhs: Expr) -> Self {
        let span = lhs.span.merge(rhs.span);
        Self {
            kind: ExprKind::Comparison {
                lhs: Box::new(lhs),
                op,
                rhs: Box::new(rhs),
            },
            span,
        }
    }

    /// Create a logical AND/OR expression.
    pub fn logical(lhs: Expr, op: LogicalOp, rhs: Expr) -> Self {
        let span = lhs.span.merge(rhs.span);
        Self {
            kind: ExprKind::Logical {
                lhs: Box::new(lhs),
                op,
                rhs: Box::new(rhs),
            },
            span,
        }
    }

    /// Create a binary arithmetic expression.
    pub fn binary(lhs: Expr, op: BinaryOp, rhs: Expr) -> Self {
        let span = lhs.span.merge(rhs.span);
        Self {
            kind: ExprKind::BinaryOp {
                lhs: Box::new(lhs),
                op,
                rhs: Box::new(rhs),
            },
            span,
        }
    }
}

// ---------------------------------------------------------------------------
// 13. Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_span_new() {
        let s = Span::new(10, 20);
        assert_eq!(s.start, 10);
        assert_eq!(s.end, 20);
        assert_eq!(s.len(), 10);
        assert!(!s.is_empty());
        assert!(!s.is_synthetic());
    }

    #[test]
    fn test_span_synthetic() {
        let s = Span::synthetic();
        assert!(s.is_synthetic());
        assert!(s.is_empty());
        assert_eq!(s.len(), 0);
    }

    #[test]
    fn test_span_merge() {
        let a = Span::new(5, 15);
        let b = Span::new(10, 25);
        let merged = a.merge(b);
        assert_eq!(merged.start, 5);
        assert_eq!(merged.end, 25);
    }

    #[test]
    fn test_expr_int_literal() {
        let e = Expr::int(42, Span::new(0, 2));
        assert_eq!(e.kind, ExprKind::IntLiteral(42));
        assert_eq!(e.span, Span::new(0, 2));
    }

    #[test]
    fn test_expr_ipv4() {
        let e = Expr::ipv4("192.168.1.0/24", Span::new(0, 18));
        match &e.kind {
            ExprKind::Ipv4Address(addr) => assert_eq!(addr, "192.168.1.0/24"),
            other => panic!("expected Ipv4Address, got {:?}", other),
        }
    }

    #[test]
    fn test_expr_ipv6() {
        let e = Expr::ipv6("2001:db8::/32", Span::new(0, 13));
        match &e.kind {
            ExprKind::Ipv6Address(addr) => assert_eq!(addr, "2001:db8::/32"),
            other => panic!("expected Ipv6Address, got {:?}", other),
        }
    }

    #[test]
    fn test_expr_comparison() {
        let lhs = Expr::var("risk_level", Span::new(0, 10));
        let rhs = Expr::int(75, Span::new(13, 15));
        let cmp = Expr::comparison(lhs, ComparisonOp::Gt, rhs);
        assert_eq!(cmp.span, Span::new(0, 15));
        match &cmp.kind {
            ExprKind::Comparison { op, .. } => assert_eq!(*op, ComparisonOp::Gt),
            other => panic!("expected Comparison, got {:?}", other),
        }
    }

    #[test]
    fn test_expr_logical() {
        let a = Expr::boolean(true, Span::new(0, 4));
        let b = Expr::boolean(false, Span::new(9, 14));
        let logical = Expr::logical(a, LogicalOp::And, b);
        assert_eq!(logical.span, Span::new(0, 14));
    }

    #[test]
    fn test_expr_error_recovery() {
        let e = Expr::error("unexpected token ']'", Span::new(42, 43));
        match &e.kind {
            ExprKind::Error { message } => assert!(message.contains("unexpected")),
            other => panic!("expected Error, got {:?}", other),
        }
    }

    #[test]
    fn test_identifier_synthetic() {
        let id = Identifier::synthetic("generated_name");
        assert_eq!(id.name, "generated_name");
        assert!(id.span.is_synthetic());
    }

    #[test]
    fn test_action_reject_with_reason() {
        let reason = Expr::string("Risk level too high", Span::new(20, 41));
        let action = Action {
            kind: ActionKind::Reject {
                reason: Some(Box::new(reason)),
            },
            span: Span::new(14, 42),
        };
        match &action.kind {
            ActionKind::Reject { reason: Some(r) } => {
                assert_eq!(r.kind, ExprKind::StringLiteral("Risk level too high".into()));
            }
            other => panic!("expected Reject with reason, got {:?}", other),
        }
    }

    #[test]
    fn test_action_drop() {
        let action = Action {
            kind: ActionKind::Drop,
            span: Span::new(0, 4),
        };
        assert_eq!(action.kind, ActionKind::Drop);
    }

    #[test]
    fn test_condition_source_ip_match() {
        let network = Expr::ipv4("10.0.0.0/8", Span::new(15, 25));
        let cond = Condition {
            kind: ConditionKind::SourceIpMatch { network },
            span: Span::new(0, 25),
        };
        match &cond.kind {
            ConditionKind::SourceIpMatch { network } => {
                assert_eq!(network.kind, ExprKind::Ipv4Address("10.0.0.0/8".into()));
            }
            other => panic!("expected SourceIpMatch, got {:?}", other),
        }
    }

    #[test]
    fn test_condition_compound() {
        let left = Condition {
            kind: ConditionKind::ProtocolMatch {
                protocol: Expr::string("TCP", Span::new(0, 3)),
            },
            span: Span::new(0, 20),
        };
        let right = Condition {
            kind: ConditionKind::PortMatch {
                direction: PortDirection::Destination,
                value: Expr::int(443, Span::new(30, 33)),
            },
            span: Span::new(25, 33),
        };
        let compound = Condition {
            kind: ConditionKind::Compound {
                lhs: Box::new(left),
                op: LogicalOp::And,
                rhs: Box::new(right),
            },
            span: Span::new(0, 33),
        };
        match &compound.kind {
            ConditionKind::Compound { op, .. } => assert_eq!(*op, LogicalOp::And),
            other => panic!("expected Compound, got {:?}", other),
        }
    }

    #[test]
    fn test_policy_decl_construction() {
        let policy = PolicyDecl {
            name: Identifier::new("security_check", Span::new(7, 21)),
            condition: Expr::comparison(
                Expr::var("risk_level", Span::new(24, 34)),
                ComparisonOp::Gt,
                Expr::var("threshold", Span::new(37, 46)),
            ),
            action: Action {
                kind: ActionKind::Reject {
                    reason: Some(Box::new(Expr::string(
                        "Risk level too high",
                        Span::new(60, 81),
                    ))),
                },
                span: Span::new(52, 82),
            },
            metadata: PolicyMetadata {
                priority: Expr::int(100, Span::new(95, 98)),
                expires: Some(Expr::string("never", Span::new(110, 115))),
                created_by: Some(Identifier::new("security_team", Span::new(130, 143))),
                span: Span::new(85, 143),
            },
        };
        assert_eq!(policy.name.name, "security_check");
    }

    #[test]
    fn test_type_expr_ip_types() {
        let ipv4_ty = TypeExpr {
            kind: TypeExprKind::Ipv4Address,
            span: Span::synthetic(),
        };
        let ipv6_ty = TypeExpr {
            kind: TypeExprKind::Ipv6Address,
            span: Span::synthetic(),
        };
        let cidr_ty = TypeExpr {
            kind: TypeExprKind::CidrRange,
            span: Span::synthetic(),
        };
        assert_ne!(ipv4_ty.kind, ipv6_ty.kind);
        assert_ne!(ipv4_ty.kind, cidr_ty.kind);
    }

    #[test]
    fn test_pattern_port_range() {
        let pat = Pattern {
            kind: PatternKind::PortRange {
                low: 1024,
                high: 65535,
            },
            span: Span::new(0, 14),
        };
        match &pat.kind {
            PatternKind::PortRange { low, high } => {
                assert_eq!(*low, 1024);
                assert_eq!(*high, 65535);
            }
            other => panic!("expected PortRange, got {:?}", other),
        }
    }

    #[test]
    fn test_full_program_construction() {
        let program = Program {
            declarations: vec![
                Declaration {
                    kind: DeclarationKind::Import(ImportDecl {
                        path: ModulePath {
                            segments: vec![
                                Identifier::new("Std", Span::new(7, 10)),
                                Identifier::new("RPKI", Span::new(11, 15)),
                            ],
                            span: Span::new(7, 15),
                        },
                        alias: None,
                    }),
                    span: Span::new(0, 15),
                },
                Declaration {
                    kind: DeclarationKind::Const(ConstDecl {
                        name: Identifier::new("threshold", Span::new(22, 31)),
                        value: Expr::int(75, Span::new(34, 36)),
                    }),
                    span: Span::new(16, 36),
                },
            ],
            span: Span::new(0, 36),
        };
        assert_eq!(program.declarations.len(), 2);
    }

    #[test]
    fn test_chain_decl() {
        let chain = ChainDecl {
            name: Identifier::new("input_chain", Span::new(6, 17)),
            policies: vec![
                Identifier::new("security_check", Span::new(20, 34)),
                Identifier::new("rate_limit", Span::new(36, 46)),
            ],
        };
        assert_eq!(chain.policies.len(), 2);
    }

    #[test]
    fn test_declaration_error_variant() {
        let decl = Declaration {
            kind: DeclarationKind::Error {
                message: "expected POLICY, IMPORT, or CONST".into(),
            },
            span: Span::new(0, 5),
        };
        match &decl.kind {
            DeclarationKind::Error { message } => assert!(message.contains("POLICY")),
            other => panic!("expected Error, got {:?}", other),
        }
    }

    #[test]
    fn test_statement_let() {
        let stmt = Statement {
            kind: StatementKind::Let {
                name: Identifier::new("rpki_result", Span::new(2, 13)),
                value: Expr::var("Std.RPKI.validate", Span::new(16, 33)),
            },
            span: Span::new(2, 33),
        };
        match &stmt.kind {
            StatementKind::Let { name, .. } => assert_eq!(name.name, "rpki_result"),
            other => panic!("expected Let, got {:?}", other),
        }
    }
}
