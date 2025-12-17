# Syntax Reference

Complete syntax reference for the Phronesis policy language.

---

## Notation

This document uses Extended Backus-Naur Form (EBNF):

| Notation | Meaning |
|----------|---------|
| `=` | Definition |
| `;` | End of rule |
| `\|` | Alternative |
| `[ ]` | Optional (0 or 1) |
| `{ }` | Repetition (0 or more) |
| `( )` | Grouping |
| `" "` | Terminal string |
| `'a'..'z'` | Character range |

---

## Complete Grammar

```ebnf
(* Program Structure *)
program        = { declaration } ;

declaration    = policy_decl
               | const_decl
               | import_decl ;

(* Policy Declaration *)
policy_decl    = "POLICY" identifier ":"
                 condition
                 "THEN" action_block
                 [ "ELSE" action_block ]
                 "PRIORITY:" integer ;

(* Constant Declaration *)
const_decl     = "CONST" identifier "=" expression ;

(* Import Declaration *)
import_decl    = "IMPORT" module_path [ "AS" identifier ] ;

module_path    = identifier { "." identifier } ;

(* Conditions *)
condition      = logical_expr ;

logical_expr   = comparison_expr { ("AND" | "OR") comparison_expr } ;

comparison_expr = [ "NOT" ] (
                    arith_expr [ comp_op arith_expr ]
                  | arith_expr "IN" arith_expr
                  | "(" logical_expr ")" ) ;

comp_op        = "==" | "!=" | "<" | ">" | "<=" | ">=" ;

(* Arithmetic Expressions *)
arith_expr     = term { ("+" | "-") term } ;

term           = factor { ("*" | "/" | "%") factor } ;

factor         = literal
               | identifier
               | field_access
               | module_call
               | "(" arith_expr ")" ;

field_access   = identifier { "." identifier } ;

module_call    = module_path "(" [ args ] ")" ;

args           = expression { "," expression } ;

(* Actions *)
action_block   = action
               | "IF" condition "THEN" action_block [ "ELSE" action_block ] ;

action         = accept_action
               | reject_action
               | report_action
               | execute_action ;

accept_action  = "ACCEPT" "(" [ expression ] ")" ;
reject_action  = "REJECT" "(" [ expression ] ")" ;
report_action  = "REPORT" "(" expression ")" ;
execute_action = "EXECUTE" "(" identifier "," args ")" ;

(* Expressions *)
expression     = logical_expr ;

(* Literals *)
literal        = integer
               | float
               | string
               | boolean
               | ip_address
               | datetime
               | list
               | record
               | null ;

integer        = [ "-" ] digit { digit } ;
float          = [ "-" ] digit { digit } "." digit { digit } ;
string         = '"' { string_char } '"' ;
boolean        = "true" | "false" ;
null           = "null" ;

ip_address     = ipv4_address | ipv4_cidr | ipv6_address ;
ipv4_address   = octet "." octet "." octet "." octet ;
ipv4_cidr      = ipv4_address "/" prefix_length ;
octet          = digit | digit digit | digit digit digit ;
prefix_length  = digit | digit digit | digit digit digit ;

datetime       = date "T" time [ timezone ] ;
date           = year "-" month "-" day ;
time           = hour ":" minute ":" second ;
timezone       = "Z" | ("+" | "-") hour ":" minute ;

list           = "[" [ expression { "," expression } ] "]" ;
record         = "{" [ field { "," field } ] "}" ;
field          = identifier ":" expression ;

(* Lexical Elements *)
identifier     = letter { letter | digit | "_" } ;
letter         = 'a'..'z' | 'A'..'Z' | "_" ;
digit          = '0'..'9' ;
string_char    = ? any character except '"' or '\' ?
               | escape_sequence ;
escape_sequence = "\\" | '\"' | "\n" | "\t" | "\r" ;

(* Comments *)
comment        = "#" { ? any character except newline ? } ;

(* Whitespace *)
whitespace     = " " | "\t" | "\n" | "\r" ;
```

---

## Lexical Structure

### Identifiers

Identifiers name constants, policies, and modules:

```
identifier = letter { letter | digit | "_" }
letter     = 'a'..'z' | 'A'..'Z' | "_"
digit      = '0'..'9'
```

Valid identifiers:
```
x
myPolicy
my_policy
_private
route123
MAX_LENGTH
```

Invalid identifiers:
```
123abc      # Cannot start with digit
my-policy   # Hyphens not allowed
my policy   # Spaces not allowed
```

### Keywords

These 15 words are reserved and cannot be used as identifiers:

```
POLICY  CONST  IMPORT  AS  THEN  IF  ELSE  PRIORITY
AND  OR  NOT  ACCEPT  REJECT  REPORT  EXECUTE
```

Keywords are case-sensitive (must be uppercase).

### Comments

Single-line comments start with `#`:

```phronesis
# This is a comment
CONST x = 10  # Inline comment
```

### Whitespace

Whitespace (spaces, tabs, newlines) separates tokens but is otherwise ignored:

```phronesis
# These are equivalent:
CONST x=10
CONST x = 10
CONST
  x
  =
  10
```

---

## Literals

### Integer Literals

```
integer = [ "-" ] digit { digit }
```

Examples:
```phronesis
0
42
-17
1000000
```

Range: Arbitrary precision (limited by memory).

### Float Literals

```
float = [ "-" ] digit { digit } "." digit { digit }
```

Examples:
```phronesis
0.0
3.14159
-0.5
1.0
123.456
```

Precision: IEEE 754 double (64-bit).

### String Literals

```
string = '"' { string_char } '"'
```

Examples:
```phronesis
""
"hello"
"hello world"
"line1\nline2"
"quote: \"text\""
"path: C:\\Users"
```

Escape sequences:
| Sequence | Character |
|----------|-----------|
| `\\` | Backslash |
| `\"` | Double quote |
| `\n` | Newline |
| `\t` | Tab |
| `\r` | Carriage return |

### Boolean Literals

```
boolean = "true" | "false"
```

Examples:
```phronesis
true
false
```

### Null Literal

```
null = "null"
```

Example:
```phronesis
null
```

### IP Address Literals

```
ip_address   = ipv4_address | ipv4_cidr
ipv4_address = octet "." octet "." octet "." octet
ipv4_cidr    = ipv4_address "/" prefix_length
```

Examples:
```phronesis
192.0.2.1
10.0.0.0
10.0.0.0/8
192.168.1.0/24
0.0.0.0/0
```

### DateTime Literals

```
datetime = date "T" time [ timezone ]
date     = year "-" month "-" day
time     = hour ":" minute ":" second
timezone = "Z" | ("+" | "-") hour ":" minute
```

Examples:
```phronesis
2025-01-15T10:30:00Z
2025-12-31T23:59:59Z
2025-06-15T14:30:00+02:00
```

### List Literals

```
list = "[" [ expression { "," expression } ] "]"
```

Examples:
```phronesis
[]
[1, 2, 3]
["a", "b", "c"]
[1, "mixed", true, null]
[[1, 2], [3, 4]]
```

### Record Literals

```
record = "{" [ field { "," field } ] "}"
field  = identifier ":" expression
```

Examples:
```phronesis
{}
{name: "test"}
{x: 1, y: 2}
{prefix: "10.0.0.0/8", origin_as: 65001}
{nested: {a: 1, b: 2}}
```

---

## Declarations

### Policy Declaration

```
policy_decl = "POLICY" identifier ":"
              condition
              "THEN" action_block
              [ "ELSE" action_block ]
              "PRIORITY:" integer
```

Examples:

```phronesis
# Minimal policy
POLICY accept_all:
  true
  THEN ACCEPT(route)
  PRIORITY: 1

# With ELSE clause
POLICY validate:
  is_valid(route)
  THEN ACCEPT(route)
  ELSE REJECT("Invalid")
  PRIORITY: 100

# Complex condition
POLICY complex:
  route.prefix_length <= 24
  AND route.origin_as IN trusted_asns
  AND NOT route.prefix IN bogon_list
  THEN ACCEPT(route)
  PRIORITY: 150
```

### Constant Declaration

```
const_decl = "CONST" identifier "=" expression
```

Examples:

```phronesis
CONST max_len = 24
CONST trusted = [13335, 15169]
CONST config = {timeout: 5000, retries: 3}
CONST greeting = "Hello, World!"
```

### Import Declaration

```
import_decl = "IMPORT" module_path [ "AS" identifier ]
module_path = identifier { "." identifier }
```

Examples:

```phronesis
IMPORT Std.RPKI
IMPORT Std.BGP
IMPORT Std.BGP AS bgp
IMPORT Std.Consensus
IMPORT Std.Temporal AS time
```

---

## Expressions

### Arithmetic Expressions

```
arith_expr = term { ("+" | "-") term }
term       = factor { ("*" | "/" | "%") factor }
factor     = literal | identifier | "(" arith_expr ")"
```

Examples:

```phronesis
1 + 2           # 3
10 - 3          # 7
4 * 5           # 20
10 / 3          # 3.333...
10 % 3          # 1
(1 + 2) * 3     # 9
2 + 3 * 4       # 14 (not 20)
```

### Comparison Expressions

```
comparison_expr = arith_expr comp_op arith_expr
comp_op         = "==" | "!=" | "<" | ">" | "<=" | ">="
```

Examples:

```phronesis
1 == 1          # true
1 != 2          # true
1 < 2           # true
2 > 1           # true
1 <= 1          # true
2 >= 2          # true
"a" == "a"      # true
```

### Logical Expressions

```
logical_expr    = comparison_expr { ("AND" | "OR") comparison_expr }
comparison_expr = [ "NOT" ] ...
```

Examples:

```phronesis
true AND false        # false
true OR false         # true
NOT true              # false
NOT false             # true

a AND b OR c          # a AND (b OR c) - see precedence
(a AND b) OR c        # explicit grouping
NOT a AND b           # (NOT a) AND b
```

### Membership Expression

```
membership = arith_expr "IN" arith_expr
```

Examples:

```phronesis
1 IN [1, 2, 3]              # true
"x" IN ["a", "b"]           # false
route.prefix IN bogon_list  # list membership
65001 IN route.as_path      # AS in path
```

### Field Access

```
field_access = identifier { "." identifier }
```

Examples:

```phronesis
route.prefix
route.origin_as
route.as_path
config.timeout
nested.deeply.nested.field
```

### Module Calls

```
module_call = module_path "(" [ args ] ")"
args        = expression { "," expression }
```

Examples:

```phronesis
Std.RPKI.validate(route)
Std.BGP.extract_as_path(route)
Std.Consensus.require_votes(action, threshold: 0.67)
Std.Temporal.now()
```

---

## Actions

### ACCEPT Action

```
accept_action = "ACCEPT" "(" [ expression ] ")"
```

Examples:

```phronesis
ACCEPT(route)
ACCEPT(route WITH {local_pref: 100})
ACCEPT("approved")
ACCEPT()
```

### REJECT Action

```
reject_action = "REJECT" "(" [ expression ] ")"
```

Examples:

```phronesis
REJECT("Invalid route")
REJECT("RPKI validation failed")
REJECT({reason: "bogon", prefix: route.prefix})
```

### REPORT Action

```
report_action = "REPORT" "(" expression ")"
```

Examples:

```phronesis
REPORT("Route accepted")
REPORT({event: "accept", route: route})
REPORT("Alert: unusual AS path detected")
```

### EXECUTE Action

```
execute_action = "EXECUTE" "(" identifier "," args ")"
```

Examples:

```phronesis
EXECUTE(send_alert, "admin@example.com", "Hijack detected")
EXECUTE(update_counter, "rejected_routes", 1)
EXECUTE(log_event, {type: "policy_match", policy: "rpki_check"})
```

### Conditional Action

```
action_block = action
             | "IF" condition "THEN" action_block [ "ELSE" action_block ]
```

Examples:

```phronesis
# Simple
ACCEPT(route)

# Conditional
IF route.origin_as IN trusted_asns
THEN ACCEPT(route)
ELSE REJECT("Untrusted origin")

# Nested
IF condition1
THEN IF condition2
     THEN ACCEPT(route)
     ELSE REPORT("Condition 2 failed")
ELSE REJECT("Condition 1 failed")
```

---

## Operator Precedence

From highest (binds tightest) to lowest:

| Level | Operators | Associativity | Example |
|-------|-----------|---------------|---------|
| 1 | `NOT` | Right | `NOT x` |
| 2 | `*` `/` `%` | Left | `a * b` |
| 3 | `+` `-` | Left | `a + b` |
| 4 | `<` `>` `<=` `>=` | Left | `a < b` |
| 5 | `==` `!=` `IN` | Left | `a == b` |
| 6 | `AND` | Left | `a AND b` |
| 7 | `OR` | Left | `a OR b` |

Examples:

```phronesis
# Arithmetic before comparison
1 + 2 < 4           # (1 + 2) < 4 = true

# Comparison before logical
a < b AND c < d     # (a < b) AND (c < d)

# AND before OR
a OR b AND c        # a OR (b AND c)

# NOT has highest precedence
NOT a AND b         # (NOT a) AND b

# Use parentheses for clarity
(a OR b) AND c      # explicit grouping
```

---

## Complete Example

```phronesis
# BGP Security Policy
# Implements comprehensive route filtering

IMPORT Std.RPKI
IMPORT Std.BGP
IMPORT Std.Temporal

# Constants
CONST bogon_prefixes = [
  "0.0.0.0/8",
  "10.0.0.0/8",
  "127.0.0.0/8",
  "169.254.0.0/16",
  "172.16.0.0/12",
  "192.168.0.0/16",
  "224.0.0.0/4"
]

CONST max_prefix_len_v4 = 24
CONST max_as_path_len = 50
CONST trusted_asns = [13335, 15169, 32934]

# RPKI Validation (highest priority)
POLICY rpki_invalid:
  Std.RPKI.validate(route) == "invalid"
  THEN REJECT("RPKI validation failed: invalid origin AS")
  PRIORITY: 200

# Bogon Filter
POLICY bogon_filter:
  route.prefix IN bogon_prefixes
  THEN REJECT("Bogon prefix not allowed")
  PRIORITY: 190

# Prefix Length Filter
POLICY prefix_length:
  route.prefix_length > max_prefix_len_v4
  THEN REJECT("Prefix too specific")
  PRIORITY: 180

# AS Path Length Filter
POLICY as_path_length:
  Std.BGP.as_path_length(route) > max_as_path_len
  THEN REJECT("AS path too long")
  PRIORITY: 170

# Trusted Networks (with logging)
POLICY trusted_networks:
  route.origin_as IN trusted_asns
  THEN IF Std.Temporal.within_window("00:00", "06:00")
       THEN ACCEPT(route)
       ELSE REPORT("Trusted route outside maintenance window")
  PRIORITY: 100

# Default Accept
POLICY default_accept:
  true
  THEN ACCEPT(route)
  PRIORITY: 1
```

---

## See Also

- [Language Overview](Language-Overview.md) - Conceptual introduction
- [Types](Types.md) - Type system details
- [Operators](Operators.md) - Operator reference
- [Reference-Grammar](Reference-Grammar.md) - Formal grammar
