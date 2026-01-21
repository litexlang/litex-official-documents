# Litex Syntax Cheat Sheet

_You can checkout any time you like but you can never leave._

_— The Eagles, Hotel California_

---

## Table of Contents
1. [Basic Concepts](#basic-concepts)
2. [Object Declaration](#object-declaration)
3. [Propositions and Facts](#propositions-and-facts)
4. [Functions](#functions)
5. [Set Theory and Logics](#set-theory-and-logics)
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

| Outcome | Meaning |
| :--- | :--- |
| **true** | Statement is proven to be true |
| **unknown** | Insufficient information to determine truth value |
| **error** | Syntax error or invalid operation |

### Core Mechanism: Match and Substitution
Litex verifies statements through two methods:

| Mode | Description |
| :--- | :--- |
| **Special → Special** | Direct matching of known facts |
| **General → Special** | Deriving specific instances from general rules |

---
## Comments

| Type | Example | Notes |
| :--- | :--- | :--- |
| **Single-line** | `# single line comment` | Starts with `#` |
| **Multi-line** | See examples below | Use one or more `"` as fences |

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
```litex
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
We declare a,b,c from set N,Q R respectively

From existential propositions:
```litex
prop larger(x,y R):
    x>y
know:
    forall y R: exist x R st $larger(x,y)   
have x R st $larger(x,1) # x $in R, x > 1
```
By defining proposition larger(x,y),we declare x in R satisfing larger(x,1)

Finite set enumeration:
```litex
have s set = {1,2,3,4,5}
```
We declare a finite set {1,2,3,4,5}

Subset definition:
```litex
prop P(x R)
have s set = {x R: $P(x)}
have t {x R:$P(x)}
```

Here `s := {x R: $P(x)}` is a definition of an intensional set. An intensional set looks like `{x ParentSet: Fact1(x), Fact2(x), ...}`.
It is also notable that only when $P(x) is not empty, our declaration is legal.

Function declaration:
```litex
have fn f(x R) R = x + 1
```
```litex
prove:
    have fn:
        h(x R) R:
            x > 0
            =>:
                h(x) > 1
        witness:
            100 > 1
        = 100
```
We define f(x)=x+1, and we prove the existence of h(x)

### `let` - Free Declaration
Use `let` to declare an object without checking its existence.

Basic usage:
```litex
let n N, m N
```
We take n, m from  N

With conditions:
```litex
let n, m N: n > 0, m > n
```
We take n,m as postive numbers in N

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
Use `prop` to define proposition

### Proposition Definition
Basic definition:
```litex
prop p(x R)
```
We define a proposition p for real number x

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
Use `exist` to state the existence of an object

Basic definition:
```litex
forall y R : exist x R st x>y
```

definition with domain restrictions:
```litex
forall y R:
    y > 0
    =>:
        exist x R st x > y
```

Proving existence:
Use `witness` to prove the existential  propositions

```litex
witness 1 : x N_pos st x > 0
exist x N_pos st x > 0
```
By witnessing 1>0 , we approach the fact that exist a positve natural number x>0

### Fact Invocation

Builtin proposition:
```litex
1 + 1 = 2
1 != 2
3 > 0
```
Litex have many builtin set and operations,see [Built-in Sets and Operations](#built-in-sets-and-operations) for further examples

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
Use `know` to invoke a fact without verification, which is an unsafe invacation.

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
We assume the universal fact: transitivity proposition of '<' without verification by using know.

---

## Functions

### Function Definition
Basic definition:
```litex
let fn f(x R) R : f(x)= x + 1
have fn g(x R) R = x+1
```
We use `let` and `have `to define f(x)=g(x)=x+1

With domain restrictions:
```litex
let fn f(x R) R:
    dom:
        x > 0
    =>:
        f(x) > 0
```

Inline definition:
```litex
let fn f(x R) R: x > 0 => f(x) > 0
```
We use let to difine f(x) satisifing specific proposition without proving its existence

With existence guarantee:
```litex
have fn g(x R) R = x
```

### Function Calls
Function call (note: doesn't compute specific values):
```litex
fn square_root(x R) R: x >= 0 => square_root(x)^2 = x
square_root(4) $in R
```
We call the function square_root(4) without computing to verify its value in R

### Function evaluation and algorithm
Use `algo` to write algorithm of functions for constructive proving or computing

Use `eval` to computing specific values of functions after `algo`
```litex
have fn f(x R) R =:
        case x > 0 :  x + 1
        case x < 0 :  x - 1
        case x=0: 0
algo f(x):
    if x = 0:
        return 0
    if x > 0:
        return x + 1 # it's ok to write `x + 2` here, but when you eval f(1), it is impossible to verify f(1) = 1 + 2, and the evaluation fails.
    if x < 0:
        return x - 1
eval f(1) # Invoke condition if x > 1 f(1) = 2
```
---
## Set Theory and Logics

### Logical Operators
Negation
```litex
let x R: x > 5
not x <= 5
```

Disjunction
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

Equality
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

### About Set 
# Litex Set Theory Cheatsheet

| Keywords | Meaning | Litex Examples |
| :--- | :--- | :--- |
| **Built-in Sets** | | |
| `set` | Generic set type definition | `have S set` |
| `finite_set` | A set with finite cardinality | `have F finite_set` |
| `nonempty_set` | A set containing at least one element | `have N nonempty_set` |
| `list_set` | Set defined by listing elements | `have A = list_set(1, 2, 3)` |
| `set_builder` | Set defined by a predicate property | `{x R:x>1} or set_builder(x R:X>1)` |
| `range` | Open interval or range | `have I range(2,6)` |
| `closed_range` | Closed interval | `have I closed_range(2,6)` |
| `N` | natural numbers | |
| `N_pos` | positive natural numbers | |
| `Z` | integers | |
| `Q` | rational numbers | |
| `R` | real numbers | |
| `C` | complex numbers | |
| **Relations & Logic** | | |
| `in` | Membership (Element belongs to Set) | `2 $in N` |
| `subset_of` | A is a subset of B (A $\subseteq$ B) | `N_pos $subset_of N` |
| `superset_of` | A is a superset of B (A $\supseteq$ B) | `N $superset_of N_pos` |
| `equal_set` | Set equality (A = B) | `N $equal_set N` |
| `is_set` | Type check: is object a set? | `N $is_set` |
| `is_finite_set` | Prop check: is cardinality finite? | `{1,2,3}$is_finite_set` |
| `is_nonempty_set` | Prop check: is cardinality > 0? | `N $is_nonempty_set` |
| **Set Operations** | | |
| `union` | Set Union (A $\cup$ B) | `have U union(A,B)` |
| `intersect` | Set Intersection (A $\cap$ B) | `have I Intersect(A,B)` |
| `set_diff` | Set Difference (A \ B) | `have D set_diff(A,B)` |
| `power_set` | Power Set (All subsets of A) | `have P power_set(Z)` |
| `choice` | Axiom of Choice selector | |
| `count` | Cardinality / Size of the set | `count({1,2,3})=3` |

### Cartesian
Use `cart` to create a Cartesian product of a fixed number of set

`set_dim`(x): Returns the dimension (number of components) of a Cartesian product

`proj`(x, i): Returns the i-th projection (the i-th component set) of a Cartesian product

`coord`(a, x, i): Returns the i-th coordinate of element a in Cartesian product x
```litex
have x set = cart(R, Q, Z)
set_dim(x) = 3
proj(x, 1) = R
proj(x, 2) = Q
proj(x, 3) = Z
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
    prove_contra:
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

prove_induc($p(x, n), n, 1)
```

### Proof over Finite Set
```litex
prop p(x R)
have set s := {1, 2, 3}

prove_enum(x, s):
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
1 > 0,
 forall x R => x $in R;
2 > 1
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
let x, y, z R:
    x = y
    y = z

x=y=z
```

Inline function:
```litex
let fn f(x R) R: x > 0 => f(x) > 0
```

Inline proposition:
```litex
prop p(x R) <=> x > 0
```

---

## Common Errors and Prevention

Quick index:

| # | Topic |
| :---: | :--- |
| 1 | Statement vs Expression |
| 2 | Undeclared Objects |
| 3 | Function Domain Violation |
| 4 | Or Statement Execution Problem |
| 5 | Duplicate Declaration |
| 6 | Set Type Error |
| 7 | Function Computation Misunderstanding |
| 8 | Never use undefined symbols |

### 1. Statement vs Expression
❌ Error: 1 is not a statement:
```litex
1
```

✅ Correct: 1 = 1 is a statement:
```litex
1 = 1
```

### 2. Undeclared Objects
❌ Error: x is not declared:
```litex
x > 0
```

✅ Correct: declare first:
```litex
let x R: x > 0
```

### 3. Function Domain Violation
❌ Error: -1 doesn't satisfy domain condition:
```litex
let fn f(x R) R: x > 0 => f(x) > 0
f(-1) > 0
```

✅ Correct: ensure parameters satisfy domain:
```litex
let fn f(x R) R: x>0 => f(x)>0
let x R: x > 0
f(x) > 0
```

### 4. Or Statement Execution Problem
❌ Error: cannot directly use universal facts:
```litex
know forall x, y R: x * y = 0 => x = 0 or y = 0
let a, b R: a * b = 0
a = 0 or b = 0  # won't work
```

✅ Correct: use named universal facts:
```litex
know @product_zero_implies_or_zero(x, y R):
    x * y = 0
    =>:
        x = 0 or y = 0
$product_zero_implies_or_zero(a, b)
```

### 5. Duplicate Declaration
❌ Error: duplicate declaration of same object:
```litex
let a N
let a N  # error
```

✅ Correct: use different names or reuse:
```litex
let a, b N
```

### 6. Set Type Error
❌ Error: 1 is not a set:
```litex
1 $in 1
```

✅ Correct: use a set:
```litex
1 $in N
```

### 7. Function Computation Misunderstanding
❌ Error: expecting function to compute specific values:
```litex
fn square_root(x R) R: x >= 0 => square_root(x)^2 = x
square_root(4) = 2  # error
```

✅ Correct: understand functions return symbols:
```litex
let fn square_root(x R) R: x >= 0 => square_root(x)^2 = x
square_root(4) $in R  # correct
```

### 8. Never use undefined symbols
<!-- forall, exist, not equal -->
❌ Error: undefined symbols: ×, ÷, ≠, ≈, ≤, ≥, ∈, ∉, ⊆, ∪, ∩, ∀, ∃, ⇒, ⇔, ∞, ∑, ∏ do not appear in Litex. Use standard *, /, !=, <=, >=, $in, forall, exist, not equal, ... instead

---

## Built-in  Operations
> Note: This section name is aligned with the Table of Contents as **Built-in Sets and Operations**.
### Built-in funcs and props
| Category | Items |
| :--- | :--- |
| **Built-in functions** | `+ - * / % ^` |
| **Built-in propositions** | `= != > < >= <=`, `$in` |

### Built-in Facts
```litex
# numeric facts
1 + 1 = 2
17 $in N
-47 + 17 $in Z
17.17 $in Q
forall x Q => x $in R
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
```litex
Package::obj_1
```

---

## Keywords in Litex

The keywords in Litex are almost identical in meaning and usage to the commonly used ones in mathematics. This makes writing in Litex a very pleasant experience.

### Litex Language Keywords Reference

| Keyword | Meaning |
| :--- | :--- |
| `let` | Define an object or variable without immediately checking existence (e.g., `let x R.`). |
| `know` | Establish a known fact or premise in the current context. |
| `have` | Introduce an intermediate object or conclusion that requires verification. |
| `claim` | State a proposition or theorem to be proved. |
| `prove` | Begin a proof block for a claim or verification. |
| `prop` | Define a new proposition (logic predicate). |
| `fn` | Define a function (mapping inputs to outputs). |
| `fn_set` | Define a set of functions (function space). |
| `algo` | Define an algorithmic procedure (computational function). |
| `dom` | Specify the domain, pre-conditions, or context for a block (e.g., `dom: x > 0.`). |
| `set` | Generic set type definition. |
| `in` | Membership operator ($\in$). Checks if an object belongs to a set. |
| `forall` | Universal quantification ($\forall$). "For all elements...". |
| `exist` | Existential quantification ($\exists$). "There exists an element...". |
| `st` | "Such that". Used with `exist`, `witness`, or `have` to specify properties. |
| `witness` | Provide a specific object to prove an existence claim (`exist`). |
| `witness_nonempty` | Provide a specific element to prove a set is `nonempty_set`. |
| `not` | Logical negation ($\neg$). |
| `or` | Logical disjunction ($\lor$). |
| `impossible` | Assert a contradiction (used to close a `contra` branch). |
| `contra` | Assume the negation of the conclusion (Proof by Contradiction). |
| `cases` | Begin a proof by case analysis (splitting the domain). |
| `case` | Define a specific branch in a case analysis. |
| `induc` | Proof by mathematical induction. |
| `enum` | Proof by enumeration (iterating through finite possibilities). |
| `subset_of` | Subset relation ($\subseteq$). Checks if set A is contained in B. |
| `superset_of` | Superset relation ($\supseteq$). Checks if set A contains B. |
| `equal_set` | Set equality relation ($=$). Checks if two sets have identical elements. |
| `union` / `cup` | Set union operator ($\cup$). Elements in A or B. |
| `intersect` / `cap` | Set intersection operator ($\cap$). Elements in both A and B. |
| `set_diff` / `set_minus` | Set difference operator ($\setminus$). Elements in A but not in B. |
| `power_set` | Power set operator ($\mathcal{P}$). The set of all subsets. |
| `list_set` | Construct a set by explicitly listing elements (e.g., `list_set(1, 2)`). |
| `set_builder` | Construct a set by property (e.g., `{x \| P(x)}`). |
| `range` | Define an open range/interval (e.g., `(a, b)`). |
| `closed_range` | Define a closed range/interval (e.g., `[a, b]`). |
| `choice` | Axiom of Choice selector. Picks an arbitrary element from a set. |
| `count` | Returns the cardinality (number of elements) of a set. |
| `finite_set` | Type: A set with finite cardinality. |
| `is_finite_set` | Proposition: Check if a set is finite. |
| `nonempty_set` | Type: A set containing at least one element. |
| `is_nonempty_set` | Proposition: Check if a set is not empty. |
| `is_set` | Type check: Is the object a set? |
| `N` | Natural numbers set ($\mathbb{N}$). |
| `N_pos` | Positive natural numbers set ($\mathbb{N}^+$). |
| `Z` | Integers set ($\mathbb{Z}$). |
| `Z_neg` | Negative integers set ($\mathbb{Z}^-$). |
| `Z_not0` | Non-zero integers set ($\mathbb{Z} \setminus \{0\}$). |
| `Q` | Rational numbers set ($\mathbb{Q}$). |
| `Q_pos` / `Q_neg` | Positive / Negative rational numbers. |
| `Q_not0` | Non-zero rational numbers. |
| `R` | Real numbers set ($\mathbb{R}$). |
| `R_pos` / `R_neg` | Positive / Negative real numbers. |
| `R_not0` | Non-zero real numbers. |
| `tuple` | Type definition for a tuple (ordered list). |
| `is_tuple` | Check if an object is a tuple. |
| `cart` | Cartesian product type (e.g., `R cart R`). |
| `is_cart` | Check if an object is a Cartesian product. |
| `dim` | Dimension of a tuple or vector. |
| `set_dim` | Dimension of a set (e.g., vector space dimension). |
| `proj` | Projection operator (extracts component from a tuple). |
| `obj_at_index` | Access an element at a specific index in a tuple. |
| `com_prop` | Declare or prove that an operation satisfies the Commutative Property. |
| `trans_prop` | Declare or prove that a relation satisfies the Transitive Property. |
| `infer` | Define a general inference rule (logic transformation). |
| `prop_infer` | Declare a proposition inference pattern. |
| `prove_prop_infer` | Prove a specific proposition inference rule. |
| `return` | Return a value from an `algo` block. |
| `if` | Conditional branching statement in algorithms. |
| `for` | Loop or iteration statement. |
| `eval` / `val` | Evaluate an expression or function application. |
| `import` | Import an external package or file. |
| `as` | Rename an imported package (aliasing). |
| `run_file` | Execute another Litex file immediately. |
| `exit` | Terminate the program execution. |
| `clear` | Clear the current context variables and assumptions. |
| `do_nothing` | No-operation placeholder statement. |

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
