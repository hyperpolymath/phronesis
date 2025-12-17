# Grammar Reference

Complete formal grammar for the Phronesis policy language in EBNF.

---

## EBNF Notation

| Symbol | Meaning |
|--------|---------|
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
(* ================================================
   Phronesis Grammar v0.1
   A consensus-gated policy language for networks
   ================================================ *)

(* Program Structure *)
program        = { declaration } ;

declaration    = policy_decl
               | const_decl
               | import_decl ;

(* ================================================
   Declarations
   ================================================ *)

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

(* ================================================
   Expressions
   ================================================ *)

(* Condition (alias for logical expression) *)
condition      = logical_expr ;

(* Logical Expression *)
logical_expr   = comparison_expr { ("AND" | "OR") comparison_expr } ;

(* Comparison Expression *)
comparison_expr = [ "NOT" ] (
                    arith_expr [ comp_op arith_expr ]
                  | arith_expr "IN" arith_expr
                  | "(" logical_expr ")" ) ;

comp_op        = "==" | "!=" | "<" | ">" | "<=" | ">=" ;

(* Arithmetic Expression *)
arith_expr     = term { ("+" | "-") term } ;

term           = factor { ("*" | "/" | "%") factor } ;

factor         = literal
               | identifier
               | field_access
               | module_call
               | "(" arith_expr ")" ;

(* Field Access *)
field_access   = identifier { "." identifier } ;

(* Module Call *)
module_call    = module_path "(" [ args ] ")" ;

args           = expression { "," expression } ;

expression     = logical_expr ;

(* ================================================
   Actions
   ================================================ *)

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

(* ================================================
   Literals
   ================================================ *)

literal        = integer
               | float
               | string
               | boolean
               | ip_address
               | datetime
               | list
               | record
               | null ;

(* Numeric Literals *)
integer        = [ "-" ] digit { digit } ;
float          = [ "-" ] digit { digit } "." digit { digit } ;

(* String Literal *)
string         = '"' { string_char } '"' ;
string_char    = ? any character except '"' or '\' ?
               | escape_sequence ;
escape_sequence = "\\" | '\"' | "\n" | "\t" | "\r" ;

(* Boolean Literal *)
boolean        = "true" | "false" ;

(* Null Literal *)
null           = "null" ;

(* IP Address Literal *)
ip_address     = ipv4_address | ipv4_cidr ;
ipv4_address   = octet "." octet "." octet "." octet ;
ipv4_cidr      = ipv4_address "/" prefix_length ;
octet          = digit [ digit [ digit ] ] ;
prefix_length  = digit [ digit ] ;

(* DateTime Literal *)
datetime       = date "T" time [ timezone ] ;
date           = year "-" month "-" day ;
year           = digit digit digit digit ;
month          = digit digit ;
day            = digit digit ;
time           = hour ":" minute ":" second ;
hour           = digit digit ;
minute         = digit digit ;
second         = digit digit ;
timezone       = "Z" | ( "+" | "-" ) hour ":" minute ;

(* Collection Literals *)
list           = "[" [ expression { "," expression } ] "]" ;
record         = "{" [ field { "," field } ] "}" ;
field          = identifier ":" expression ;

(* ================================================
   Lexical Elements
   ================================================ *)

identifier     = ( letter | "_" ) { letter | digit | "_" } ;
letter         = 'a'..'z' | 'A'..'Z' ;
digit          = '0'..'9' ;

(* ================================================
   Comments and Whitespace
   ================================================ *)

comment        = "#" { ? any character except newline ? } newline ;
whitespace     = " " | "\t" | "\n" | "\r" ;
```

---

## Keywords

The 15 reserved keywords:

```
POLICY   CONST   IMPORT   AS   THEN
IF       ELSE    PRIORITY AND  OR
NOT      ACCEPT  REJECT   REPORT  EXECUTE
```

Additionally reserved:
```
IN       true    false    null
```

---

## Operator Precedence

From highest (tightest binding) to lowest:

| Level | Operators | Associativity |
|-------|-----------|---------------|
| 1 | `NOT` | Right |
| 2 | `*` `/` `%` | Left |
| 3 | `+` `-` | Left |
| 4 | `<` `>` `<=` `>=` | Left |
| 5 | `==` `!=` `IN` | Left |
| 6 | `AND` | Left |
| 7 | `OR` | Left |

---

## Grammar Properties

### LL(1)

The grammar is LL(1), meaning:
- No left recursion
- Deterministic with 1 token lookahead
- Suitable for recursive descent parsing

### FIRST Sets (Selected)

```
FIRST(declaration) = { POLICY, CONST, IMPORT }
FIRST(action) = { ACCEPT, REJECT, REPORT, EXECUTE }
FIRST(literal) = { integer, float, string, true, false, null, ip_address, datetime, [, { }
FIRST(factor) = FIRST(literal) ∪ { identifier, ( }
```

### FOLLOW Sets (Selected)

```
FOLLOW(declaration) = { POLICY, CONST, IMPORT, EOF }
FOLLOW(action_block) = { ELSE, PRIORITY }
FOLLOW(expression) = { ), ,, ], }, THEN, ELSE, PRIORITY, AND, OR }
```

---

## Grammar Statistics

| Metric | Value |
|--------|-------|
| Non-terminals | 32 |
| Terminals | 48 |
| Productions | 45 |
| Keywords | 15 |
| Lines of EBNF | ~40 |

---

## Railroad Diagrams

### Policy Declaration

```
           ┌─────────────────────────────────────────────────────┐
           │                                                     │
──POLICY──►│identifier│──:──►│condition│──THEN──►│action_block│──┼──►
           │          │      │         │         │            │  │
           └──────────┘      └─────────┘         └────────────┘  │
                                                                 │
       ┌─────────────────────────────────────────────────────────┘
       │
       ▼
  ┌────────────────────────────────────────────┐
  │                                            │
──┼──►──ELSE──►│action_block│──┼──PRIORITY:──►│integer│──►
  │            │            │  │              │       │
  │            └────────────┘  │              └───────┘
  │                            │
  └────────────────────────────┘
```

### Logical Expression

```
                    ┌─────────────────────┐
                    │                     │
──►│comparison_expr│──┼──►│AND│──►│comparison_expr│──┼──►
   │               │  │   │OR │   │               │  │
   └───────────────┘  │   └───┘   └───────────────┘  │
                      │                              │
                      └──────────────────────────────┘
```

### Arithmetic Expression

```
              ┌─────────────────────┐
              │                     │
──►│term│──┬──┼──►│+│──►│term│──┬───┼──►
   │    │  │  │   │-│   │    │  │   │
   └────┘  │  │   └─┘   └────┘  │   │
           │  │                 │   │
           │  └─────────────────┘   │
           │                        │
           └────────────────────────┘
```

---

## See Also

- [Syntax Reference](Syntax-Reference.md) - Syntax guide
- [Language Overview](Language-Overview.md) - Language concepts
- [Architecture-Parser](Architecture-Parser.md) - Parser implementation
