# Litex Syntax Cheat Sheet

## Table of Contents
1. [Basic Concepts](#basic-concepts)
2. [Object Declaration](#object-declaration)
3. [Propositions and Facts](#propositions-and-facts)
4. [Functions](#functions)
5. [Logical Operators](#logical-operators)
6. [Proof Strategies](#proof-strategies)
7. [Inline Syntax](#inline-syntax)
8. [Common Errors and Prevention](#common-errors-and-prevention)
9. [Built-in Sets and Operations](#built-in-sets-and-operations)
10. [Package Management](#package-management)
11. [Comments](#comments)
12. [Keywords in Litex](#keywords-in-litex)
13. [Best Practices](#best-practices)

---

## Basic Concepts

### Statement Outcomes
Every statement has three possible outcomes:
- **true**: Statement is proven to be true
- **unknown**: Insufficient information to determine truth value
- **error**: Syntax error or invalid operation

### Core Mechanism: Match and Substitution
Litex verifies statements through two methods:
1. **Special to Special**: Direct matching of known facts
2. **General to Special**: Deriving specific instances from general rules

---
## Comments

Single-line comment:
```litex
# single line comment
```

Multi-line comment:
```litex
"
multi-line comment
multi-line comment
"
```

You can write as many `"` as you want.
```
"""
Three " is allowed.
"""
```

`""` can be translated to LaTeX style comment in display; One or any number of `"` except two can be translated to markdown style comment in display.

## Object Declaration

### `have` - Safe Declaration
Use `have` to declare an object with checking its existence.

Basic usage:
```litex
have a N, b Q, c R
```

From existential propositions:
```litex
exist_prop x R st larger_than(y R): 
    x > y
exist 2 st $larger_than(1)  # a $in R, a > 1
    
have a st $larger_than(1)  # a $in R, a > 1
```

Finite set enumeration:
```litex
have set one_to_five := {1,2,3,4,5}
```

Subset definition:
```litex
prop P(x R)

have set s := {x R: $P(x)}
```

Here `s := {x R: $P(x)}` is a definition of an intensional set. An intensional set looks like `{x ParentSet: Fact1(x), Fact2(x), ...}`.

### `let` - Free Declaration
Use `let` to declare an object without checking its existence.

Basic usage:
```litex
let n N, m N
```

With conditions:
```litex
let n, m N: n > 0, m > n
```

Multiple line usage:
```litex
let n, m N:
    n > 0
    m > n
```

System of equations:
```litex
let x, y R: 2*x + 3*y = 10, 4*x + 5*y = 14
```

Multiple line usage:
```litex
let x, y R:
    2*x + 3*y = 10
    4*x + 5*y = 14
```

Contradictory declarations (allowed but not recommended):
```litex
let a N: a = 2, a = 3
```

### Differences
- **`have`**: Requires non-empty set, guarantees object existence
- **`let`**: No existence check, allows arbitrary property binding

---

## Propositions and Facts

### Proposition Definition
Basic definition:
```litex
prop p(x R)
```

With equivalence condition:
```litex
prop p(x R): x > 0 <=> x + 1 > 1
```

With domain restrictions:
```litex
prop p(x R):
    x > 0
    <=>:
        x + 1 > 1
```

Inline definition:
```litex
prop p(x R) <=> x > 0
```

### Existential Propositions
Basic definition:
```litex
exist_prop x R st larger_than(y R):
    x > y
```

definition with domain restrictions:
```litex
exist_prop x R st larger_than_positive(y R):
    y > 0
    <=>:
        x > y
```

Proving existence:
```litex
exist_prop x R st larger_than(y R):
    x > y

exist 3 st $larger_than(2)
```

### Fact Invocation

Builtin proposition:
```litex
1 + 1 = 2
1 != 2
3 > 0
```

Prefix form:
```litex
prop p(x R)

know $p(1)

$p(1)
```

Infix form (binary propositions only):
```litex
1 $in N
```

```litex
prop divisible_by(x, y N):
    y > 0
    <=>:
        x % y = 0

6 $divisible_by 3
```

### Universal Facts
Multi-line form:
```litex
forall x R:
    x = 1
    =>:
        x = 1
```

Inline form:
```litex
forall x R: x = 1 => x = 1
```

With equivalence:
```litex
forall x R: x = 1 => not x = 2 <=> x != 2
```

Multi-line form with equivalence:
```litex
forall x R:
    dom:
        x = 1
    =>:
        x != 2
    <=>:
        not x = 2
```

### Know a Fact

Inline form:
```litex
let x R
know x > 0, x != 2, forall y R: y > 5 => y > x
```

Multi-line form:
```litex
let x R
know:
    x > 0
    x != 2
    forall y R:
        y > 5
        =>:
            y > x
```

### Named Universal Facts
Using @ symbol:
```litex
know @transitivity_of_less(a, b, c R):
    a < b
    b < c
    =>:
        a < c
```

Equivalent to:
```litex
prop transitivity_of_less(a, b, c R):
    a < b
    b < c

know:
    forall a, b, c R:
        $transitivity_of_less(a, b, c)
        =>:
            a < c
    forall a, b, c R:
        a < b
        b < c
        =>:
            a < c
```

---

## Functions

### Function Definition
Basic definition:
```litex
fn f(x R) R: x > 0 => f(x) > 0
```

With domain restrictions:
```litex
fn f(x R) R:
    dom:
        x > 0
    =>:
        f(x) > 0
```

Inline definition:
```litex
fn f(x R) R: x > 0 => f(x) > 0
```

With existence guarantee:
```litex
have fn g(x R) R = x
```

### Function Templates
Basic template:
```litex
fn_template sequence(s set):
    fn (n N) s
```

With parameters:
```litex
fn_template finite_sequence(s set, max N):
    dom:
        max > 0
    fn (n N) s:
        dom:
            n < max
```

Using templates:
```litex
let a sequence(R), b finite_sequence(Z, 10)
```

### Function Calls
Function definition:
```litex
fn square_root(x R) R: x >= 0 => square_root(x)^2 = x
```

Function call (note: doesn't compute specific values):
```litex
square_root(4) $in R
```

---

## Logical Operators

### Negation
```litex
let x R: x > 5
not x <= 5
```

### Disjunction
Multi-line form:
```litex
or:
    1 = 1
    1 = 2
```

Inline form:
```litex
1 = 1 or 1 = 2
```

### Equality
Basic equality:
```litex
let x, y R:
    x = y

x = y
x + 1 = y + 1
```

Multi-line equality:
```litex
=:
    1
    2 - 1
    1 * 1
```

Inline equality:
```litex
1 = 2 -1 = 1 * 1
```

Numeric equality:
```litex
1 + 1 = 2
4 / 2 = 2
```

### Set Membership
Explicit:
```litex
2 $in N
```

Implicit (in declarations):
```litex
let x N  # equivalent to let x; know x $in N
```

Implicit (in forall facts):
```litex
forall x N:
    x $in R
```

---

## Proof Strategies

### Claims and Proofs
Basic claim:
```
claim:
    fact_to_prove
    prove:
        # proof steps
```

Example:
```litex
claim:
    forall x R:
        x = 1
        =>:
            x > 0
    prove:
        1 > 0
        x > 0
```

```litex
let a, b, c, d R: 
    a = c
    b = d
    a + 2 * b + 3 * c + 2 = 3 * d + 4 * b + 5 * c + 6

claim:
    c + 2 * d + 3 * c + 2 = 3 * b + 4 * d + 5 * c + 6
    prove:
        a + 2 * b + 3 * c + 2 = 3 * d + 4 * b + 5 * c + 6
        a + 2 * b + 3 * c + 2 = c + 2 * d + 3 * c + 2
        c + 2 * d + 3 * c + 2 = 3 * b + 4 * d + 5 * c + 6
```

### Proof by Contradiction
```litex
prop p(x R)
prop q(x R)
know not $q(1)
know forall x R: $p(x) => $q(x)

claim:
    not $p(1)
    prove_by_contradiction:
        $p(1)
        $q(1)
```

### Proof by Cases
```litex
let a R:
    or:
        a = 1
        a = 0

prove_in_each_case:
    a = 0 or a = 1
    =>:
        a >= 0
    prove:
        0 >= 0
    prove:
        1 >= 0
```

### Mathematical Induction
```litex
prop p(x R, n N_pos)
let x R
know forall n N_pos: n >= 1, $p(x, n) => $p(x, n+1)
know $p(x, 1)

prove_by_induction($p(x, n), n, 1)
```

### Proof over Finite Set
```litex
prop p(x R)
have set s := {1, 2, 3}

prove_by_enum(x, s):
    x > 0
```

---

## Inline Syntax

### General Rules
- Specific facts end with `,`
- Universal facts end with `;`
- Final statement punctuation is optional

### Inline Examples
Multiple statements:
```litex
1 > 0, forall x R => x $in R; 2 > 1
```

Inline forall:
```litex
forall x R: x > 0 => x > 0
```

Inline or:
```litex
know forall x R => x > 1 or x = 1 or x < 1

let x R
x > 1 or x = 1 or x < 1
```

Inline equality:
```litex
let x, y, z :
    x = y
    y = z

=(x, y, z)
```

Inline function:
```litex
fn f(x R) R: x > 0 => f(x) > 0
```

Inline proposition:
```litex
prop p(x R) <=> x > 0
```

---

## Common Errors and Prevention

### 1. Statement vs Expression
❌ Error: 1 is not a statement:
```
1
```

✅ Correct: 1 = 1 is a statement:
```litex
1 = 1
```

### 2. Undeclared Objects
❌ Error: x is not declared:
```
x > 0
```

✅ Correct: declare first:
```litex
let x R: x > 0
```

### 3. Function Domain Violation
❌ Error: -1 doesn't satisfy domain condition:
```
fn f(x R) R: x > 0 => f(x) > 0
f(-1) > 0
```

✅ Correct: ensure parameters satisfy domain:
```litex
let x R: x > 0
f(x) > 0
```

### 4. Or Statement Execution Problem
❌ Error: cannot directly use universal facts:
```
know forall x, y R: x * y = 0 => x = 0 or y = 0
let a, b R: a * b = 0
a = 0 or b = 0  # won't work
```

✅ Correct: use named universal facts:
```
know @product_zero_implies_or_zero(x, y R):
    x * y = 0
    =>:
        x = 0 or y = 0
$product_zero_implies_or_zero(a, b)
```

### 5. Duplicate Declaration
❌ Error: duplicate declaration of same object:
```
let a N
let a N  # error
```

✅ Correct: use different names or reuse:
```litex
let a, b N
```

### 6. Set Type Error
❌ Error: 1 is not a set:
```
1 $in 1
```

✅ Correct: use a set:
```litex
1 $in N
```

### 7. Function Computation Misunderstanding
❌ Error: expecting function to compute specific values:
```
fn square_root(x R) R: x >= 0 => square_root(x)^2 = x
square_root(4) = 2  # error
```

✅ Correct: understand functions return symbols:
```litex
square_root(4) $in R  # correct
```

### 8. Never use undefined symbols
<!-- forall, exist, not equal -->
❌ Error: undefined symbols: ×, ÷, ≠, ≈, ≤, ≥, ∈, ∉, ⊆, ∪, ∩, ∀, ∃, ⇒, ⇔, ∞, ∑, ∏ do not appear in Litex. Use standard *, /, !=, <=, >=, $in, forall, exist, not equal, ... instead

---

## Built-in Sets and Operations

### Built-in Sets
```
N        # natural numbers
N_pos    # positive natural numbers
Z        # integers
Q        # rational numbers
R        # real numbers
C        # complex numbers
```

### Built-in Functions
```
+ - * / % ^  # arithmetic operations
```

### Built-in Propositions
```
= != > < >= <=  # comparison operations
$in             # set membership
```

### Built-in Facts
```litex
# numeric facts
1 + 1 = 2
17 $in N
-47 + 17 $in Z
17.17 $in Q
forall x Q => x $in R
```

### Sequence Templates
```litex
# built-in sequence templates
let a seq(R), b finite_seq(Z, 10)

a(1) $in R
b(1) $in Z
```

---

## Package Management

### Import Files
```litex
import "file.lit"
```

```litex
import "folder/file.lit"
```

### Import Packages
```litex
import "Package"
```

```litex
import "Package" as p
```

### Using Package Contents
```
Package::obj_1
```

---

## Comments

Single-line comment:
```litex
# single line comment
```

Multi-line comment:
```litex
"""
multi-line comment
multi-line comment
multi-line comment
"""
```

---

## Keywords

The keywords in Litex are almost identical in meaning and usage to the commonly used ones in mathematics. This makes writing in Litex a very pleasant experience.

| Keyword | Meaning |
|---------|---------|
| `let` | Define an object without checking its existence. |
| `prop` | Define a proposition. The verbs of logic. |
| `know` | Establish a fact |
| `forall` | Universal quantification |
| `exist` | Existential quantification |
| `have` | Introduce an object with checking its existence. |
| `exist_prop` | Existential quantification with a proposition |
| `or` | Disjunction |
| `not` | Negation |
| `fn` | Define a function without checking its existence |
| `fn_template` | Define a class of functions |
| `set` | set: a collection of objects |
| `in` | membership of an object in a set |
| `dom` | domain of a proposition, function, function template, etc. |
| `len`  | length of a set |
| `finite_set` | a set with a finite number of elements |
| `prove` | open a local environment to write some statements without affecting the global environment |
| `claim` | claim a factual statement, prove it here |
| `prove_by_contradiction` | prove by contradiction |
| `prove_in_each_case` | prove by case analysis |
| `prove_by_induction` | prove by mathematical induction |
| `prove_by_enum` | prove a universal statement by iterating over a finite set |
| `prove_in_range` | prove a universal statement by iterating over a range of integers |
| `import` | import a file or directory |
| `exist_item_in` | exist a object in a set |
| `set_defined_by_replacement` | define a set by a axiom of replacement |
| `obj_exist_as_preimage_of_prop` | exist a object as the preimage of a proposition |
| `obj_exist_as_preimage_of_fn` | exist a object as the preimage of a function |
| `N` `N_pos` `Z` `Q` `R` `C` `obj` | builtin sets: natural numbers, positive natural numbers, integers, rational numbers, real numbers, complex numbers, objects |
| `clear` | clear all facts |
| `set_product` | a product of sets |
| `proj` | a projection of a set product |
| `lift` | Point-wise lifting of an operator |

Although these keywords are rarely defined strictly in math textbooks, they are used everyday and everywhere. Litex creator can not find strict definition for keywords like `proposition`, `is`, `in` etc (actually, the word `definition` is also a vague word). He tried his best to make the meaning of these keywords as close to the meaning in our daily math expression, along with his own ideas and understanding, so that Litex is both intuitive and strict.

---

## Best Practices

1. **Use `have` instead of `let`** when you need to guarantee object existence
2. **Name universal facts** using `@` symbol to improve readability
3. **Inline syntax** for simplifying simple expressions
4. **Proof by cases** for handling complex logical branches
5. **Function templates** for defining families of similar functions
6. **Avoid contradictory declarations** unless defining axioms
7. **Understand match and substitution** - this is Litex's core mechanism
8. **Use comments** to improve code readability

---

*This cheatsheet is based on the Litex tutorial and covers the core syntax and common usage patterns of Litex.*
