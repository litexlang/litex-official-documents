<!-- # Recipe: Common Mathematical Symbols in Litex

version: 2025-12-01

<div align="center">
<img src="https://publisher.litexlang.org/litex_art_logo1.png" alt="The Litex Logo" width="300">
</div>

_Mathematics is nothing more than a game played according to certain simple rules with meaningless marks on a paper._

_— David Hilbert_

## Introduction

This document provides a recipe for translating common mathematical symbols (those typically found in standard LaTeX mathematical notation) into Litex syntax. Whether you're working with sets, functions, logical operators, or arithmetic expressions, this guide shows you how to express familiar mathematical concepts in Litex.

The mathematical symbols covered here are limited to those commonly encountered in undergraduate mathematics and standard mathematical notation—no more extensive than what you would typically see in LaTeX mathematical documents. This makes it easy to translate mathematical statements from traditional notation into Litex code.

# Set Theory

**Definition: Sets**

A set is an unordered collection of objects. For example, $\{3,8,5,2\}$ is a set. If $x$ is an object and $A$ is a set, we say $x$ is an element of $A$ (written $x \in A$) if $x$ belongs to the collection; otherwise we say $x \not\in A$.

**Correspondence in Litex**:
- **Keywords**: `set`, `$in`, `have set`
- **Expression**: `have A set = {item1, item2, ...}` or `have A set = {x parent_set: fact1, ...}`
- **Example**:
```litex
# Define set by enumeration
have A set = {3, 8, 5, 2}
have x A
x $in A

3 $in A
```
- **Note**: `set` is a built-in keyword in Litex, and `$in` is the membership predicate

**Axiom: All objects are sets**

Everything you defined as object is a set, satisfying `$is_a_set(object)`. This is because in set theory, everything is a set.

When you see statements like `have a set`. It means `$is_a_set(a)`. It does not mean `set` is a set and a is an element of the set of all sets. Indeed, it is just a syntax sugar for `$is_a_set(a)`. Similarly, `have a nonempty_set`, `have a finite_set`, etc. are just syntax sugar for `$is_a_nonempty_set(a)`, `$is_a_finite_set(a)`. There are and only are 3 kinds of such keywords: `set`, `nonempty_set`, `finite_set` that have special semantics. Everything else is just a syntax sugar for `a $in setName`.


**Definition: Equality of Sets**

Two sets $A$ and $B$ are equal (written $A = B$) if and only if they contain exactly the same elements. That is, every element of $A$ is an element of $B$, and every element of $B$ is an element of $A$. In symbols: $A = B \iff (\forall x, x \in A \iff x \in B)$.

**Correspondence in Litex**:
- **Keywords**: `=`, `forall`, `$in`, `<=>`
- **Expression**: `forall A, B set: A = B <=> (forall x A => x $in B), (forall x B => x $in A)`
- **Example**:
```litex
forall A, B set:
    A = B
    <=>:
        $equal_set(A, B)
        forall x A:
            x $in B
        forall x B:
            x $in A
```
- **Note**: Set equality is defined through the axiom of extensionality, which is the built-in semantics of equality in Litex

**Axiom: Empty Set**

There exists a set $\emptyset$ (called the empty set) that contains no elements. For every object $x$, we have $x \not\in \emptyset$. In symbols: $\exists \emptyset, \forall x, x \not\in \emptyset$.

**Correspondence in Litex**:
- **Keywords**: `have set`, `{}`, `exist`, `not`, `$in`
- **Expression**: `have set empty_set = {}` or `exist empty_set set: forall x obj => not x $in empty_set`
- **Example**:
```litex
# Define empty set by enumeration
have self_defined_empty_set set = {}
```
- **Note**: The empty set can be defined by enumeration `{}` or declared through an existence axiom

**Axiom: Singleton and Pair Sets**

For any object $a$, there exists a set $\{a\}$ (called a singleton set) containing only $a$. For any objects $a$ and $b$, there exists a set $\{a,b\}$ (called a pair set) containing exactly $a$ and $b$. In symbols: $\forall a, \exists \{a\}, \forall y, (y \in \{a\} \iff y = a)$; $\forall a, b, \exists \{a,b\}, \forall y, (y \in \{a,b\} \iff (y = a \lor y = b))$.

**Correspondence in Litex**:
- **Keywords**: `have set`, `{}`, `or`, `=`
- **Expression**: `have set s = {a}` or `have set s = {a, b}`
- **Example**:
```litex
# Singleton set
have a set
have singleton set = {a}
have y singleton
y = a

# Pair set
have a, b obj
have pair set = {a, b}
have y pair
y = a or y = b
```
- **Note**: Sets defined by enumeration correspond to the pairing axiom

**Axiom: Pairwise Union**

For any two sets $A$ and $B$, there exists a set $A \cup B$ (called the union of $A$ and $B$) whose elements are all objects that belong to $A$ or $B$ (or both). In symbols: $\forall A, B, \exists A \cup B, \forall x, (x \in A \cup B \iff (x \in A \lor x \in B))$.

**Correspondence in Litex**:
- **Keywords**: `union`, `or`, `$in`
- **Expression**: `union(A, B)` or defined through a function
- **Example**:
```litex
have a, b set
forall x a => x $in union(a, b)
forall x b => x $in union(a, b)
forall x union(a, b) => $item_in_union(x, a, b), x $in a or x $in b
```
- **Note**: Union can be declared as an axiom using `know`, or defined through a function

**Axiom: Specification (Separation)**

For any set $A$ and any property $P(x)$, there exists a set $\{x \in A : P(x)\}$ whose elements are exactly those elements $x$ of $A$ for which $P(x)$ is true. In symbols: $\forall A, \exists \{x \in A : P(x)\}, \forall y, (y \in \{x \in A : P(x)\} \iff (y \in A \land P(y)))$.

**Correspondence in Litex**:
- **Keywords**: `have set`, `{x parent_set: fact1, ...}`, `prop`
- **Expression**: `have s set = {x A: $P(x)}`
- **Example**:
```litex
have A set
prop P(x A)

have s set = {x A: $P(x)}
have y s
y $in A
$P(y)
```
- **Note**: The separation axiom is directly implemented through Litex's intensional set definition syntax

**Definition: Subsets**

For sets $A$ and $B$, we say $A$ is a subset of $B$ (written $A \subseteq B$) if every element of $A$ is also an element of $B$. We say $A$ is a proper subset of $B$ (written $A \subsetneq B$) if $A \subseteq B$ and $A \neq B$. In symbols: $A \subseteq B \iff (\forall x, x \in A \implies x \in B)$; $A \subsetneq B \iff (A \subseteq B \land A \neq B)$.

**Correspondence in Litex**:
- **Keywords**: `$subset_of`, `forall`, `=>`, `!=`
- **Expression**: `A $subset_of B <=> forall x A => x $in B`; `A $is_proper_subset_of B <=> (A $subset_of B), (A != B)`
- **Example**:
```litex
forall A, B set:
    A $subset_of B
    <=>:
        forall x A:
            x $in B

# Proper subset
prop self_defined_proper_subset(A set, B set):
    A $subset_of B
    A != B
```
- **Note**: Subset relations can be defined through predicates, or use the built-in `$subset_of`

**Definition: Intersection**

The intersection of two sets $S_1$ and $S_2$, denoted $S_1 \cap S_2$, is the set of all elements that belong to both $S_1$ and $S_2$. In symbols: $S_1 \cap S_2 := \{x \in S_1 : x \in S_2\}$; $x \in S_1 \cap S_2 \iff (x \in S_1 \land x \in S_2)$.

**Correspondence in Litex**:
- **Keywords**: `have intersection set`, `{x parent_set: fact}`, `$in`
- **Expression**: `have intersection set = {x S1: x $in S2}`
- **Example**:
```litex
have a, b set
forall x a:
    x $in b
    =>:
        x $in intersect(a, b)
forall x intersect(a, b) => $item_in_intersect(x, a, b), x $in a, x $in b
```
- **Note**: Intersection is implemented through the separation axiom (intensional set definition)

**Definition: Set Difference**

For sets $A$ and $B$, the set difference $A \setminus B$ (also written $A - B$) is the set of all elements of $A$ that do not belong to $B$. In symbols: $A \setminus B := \{x \in A : x \not\in B\}$; $x \in A \setminus B \iff (x \in A \land x \not\in B)$.

**Correspondence in Litex**:
- **Keywords**: `have difference set`, `{x parent_set: not fact}`, `not`, `$in`
- **Expression**: `have xxx set = {x A: not x $in B}`
- **Example**:
```litex
have a, b set
forall x a:
    not x $in b
    =>:
        x $in difference(a, b)
forall x difference(a, b) => x $in a, not x $in b
```
- **Note**: Set difference is implemented through the separation axiom and negation

**Definition: Functions**

A function $f : X \to Y$ from set $X$ to set $Y$ is defined by a property $P(x,y)$ such that for every $x \in X$, there is exactly one $y \in Y$ for which $P(x,y)$ is true. The function $f$ assigns to each input $x \in X$ the unique output $f(x) \in Y$ satisfying $P(x,f(x))$. In symbols: $f : X \to Y$; $\forall x \in X, \exists! y \in Y, P(x,y)$; $y = f(x) \iff P(x,y)$.

**Correspondence in Litex**:
- **Keywords**: `have fn`, `fn`, `prop`, `exist_prop`
- **Expression**: `have f fn(X)Y` or defined through `exist_prop`
- **Example**:
```litex
have X, Y nonempty_set

# Define function through have fn
have f fn(X)Y
# Function satisfies uniqueness: forall x X => exist! y Y: y = f(x)
```
- **Note**: Function definition requires proving existence and uniqueness, and `have fn` checks these conditions

**Definition: Equality of Functions**

Two functions $f : X \to Y$ and $g : X \to Y$ with the same domain and range are equal (written $f = g$) if and only if they agree on all inputs: $f(x) = g(x)$ for all $x \in X$. In symbols: $f = g \iff (\forall x \in X, f(x) = g(x))$.

**Correspondence in Litex**:
- **Keywords**: `=`, `forall`
- **Expression**: `f = g <=> forall x X => f(x) = g(x)`
- **Example**:
```litex
have X, Y nonempty_set

have f fn(X)Y
have g fn(X)Y

prop the_same_function_on_given_domain(X set, Y set,f fn(X)Y, g fn(X)Y):
    forall x X:
        f(x) = g(x)
```
- **Note**: Function equality is defined through extensionality, which is the built-in semantics of equality in Litex

**Definition: Function Composition**

For functions $f : X \to Y$ and $g : Y \to Z$, the composition $g \circ f : X \to Z$ is defined by $(g \circ f)(x) := g(f(x))$ for all $x \in X$.

**Correspondence in Litex**:
- **Keywords**: `have fn`, function composition
- **Expression**: `have composition fn(X)Z = g(f(x))`
- **Example**:
```litex
have X, Y, A nonempty_set
have x X

have f fn(X)Y
have g fn(Y)A

g(f(x)) $in A
```
- **Note**: Function composition is implemented through function definition and function calls

**Definition: Injective Functions**

A function $f : X \to Y$ is injective (or one-to-one) if different inputs produce different outputs: $x \neq x' \implies f(x) \neq f(x')$. Equivalently, $f$ is injective if $f(x) = f(x') \implies x = x'$. In symbols: $f$ is injective $\iff (\forall x, x' \in X, x \neq x' \implies f(x) \neq f(x')) \iff (\forall x, x' \in X, f(x) = f(x') \implies x = x')$.

**Correspondence in Litex**:
- **Keywords**: `prop`, `forall`, `=>`, `=`, `!=`
- **Expression**: `prop is_injective(f fn(X)Y): forall x, x' X: f(x) = f(x') => x = x'`
- **Example**:
```litex
have X, Y, A nonempty_set

have f fn(X)Y
prop is_injective(f fn(X)Y):
    forall x, x2 X:
        f(x) = f(x2)
        =>:
            x = x2
```
- **Note**: Injectivity can be defined through propositions

**Definition: Surjective Functions**

A function $f : X \to Y$ is surjective (or onto) if every element of $Y$ is the image of some element of $X$. That is, for every $y \in Y$, there exists $x \in X$ such that $f(x) = y$. In symbols: $f$ is surjective $\iff f(X) = Y \iff (\forall y \in Y, \exists x \in X, f(x) = y)$.

**Correspondence in Litex**:
- **Keywords**: `prop`, `forall`, `exist`, `=`
- **Expression**: `prop is_surjective(f fn(X)Y): forall y Y => exist x X: f(x) = y`
- **Example**:
```litex
have X, Y nonempty_set
have f fn(X)Y

exist_prop x X st has_preimage(X nonempty_set, Y nonempty_set, f fn(X)Y, y Y):
    f(x) = y

prop is_surjective(f fn(X)Y):
    forall y Y:
        =>:
            $has_preimage(X, Y, f, y)
```
- **Note**: Surjectivity can be defined through propositions and existential quantifiers

**Definition: Bijective Functions**

A function $f : X \to Y$ is bijective (or invertible) if it is both injective and surjective. In symbols: $f$ is bijective $\iff (f$ is injective $\land f$ is surjective$)$.

**Correspondence in Litex**:
- **Keywords**: `prop`, `,` (conjunction)
- **Expression**: `prop is_bijective(f fn(X)Y): $is_injective(f), $is_surjective(f)`
- **Example**:
```litex
have X, Y nonempty_set
have f fn(X)Y
prop is_bijective(f fn(X)Y):
    $is_injective(f)
    $is_surjective(f)
```
- **Note**: Bijectivity is the conjunction of injectivity and surjectivity

**Definition: Image of a Set**

For a function $f : X \to Y$ and a subset $S \subseteq X$, the image of $S$ under $f$ is the set $f(S) := \{f(x) : x \in S\}$. This set is a subset of $Y$.

**Correspondence in Litex**:
- **Keywords**: `have image set`, `{f(x): x parent_set}`
- **Expression**: `have image set = {f(x): x S}` (requires replacement axiom support)
- **Example**:
```litex
have X, Y nonempty_set
have f fn(X)Y
have S set = {x X: ...}
# Define image set through replacement axiom (currently needs to be assumed via know)
know exist set image: forall y Y => (y $in image <=> exist x S: f(x) = y)
```
- **Note**: The definition of image sets requires the replacement axiom, which Litex currently does not support, but can be assumed through `know`

**Definition: Inverse Image**

For a function $f : X \to Y$ and a subset $U \subseteq Y$, the inverse image of $U$ under $f$ is the set $f^{-1}(U) := \{x \in X : f(x) \in U\}$. In symbols: $f(x) \in U \iff x \in f^{-1}(U)$.

**Correspondence in Litex**:
- **Keywords**: `fn`, `{x parent_set: fact}`, `$subset_of`
- **Expression**: `Given f : X -> Y, U subset Y, then f^{-1}(U) = {x X : f(x) $in U}`
- **Example**:
```litex
# f^{-1}(U)

have X, Y, U set

fn f(x X) Y

have s set = {x X : f(x) $in U}
```
- **Note**: Inverse images are implemented through the separation axiom (intensional set definition)

**Axiom: Power Set (Function Space)**

For sets $X$ and $Y$, there exists a set $Y^X$ consisting of all functions from $X$ to $Y$. A function $f$ belongs to $Y^X$ if and only if $f : X \to Y$. In symbols: $\forall X, Y, \exists Y^X, \forall f, (f \in Y^X \iff (f : X \to Y))$.

**Correspondence in Litex**:
- **Keywords**: `fn`, `$in`
- **Expression**: `fn(X)Y` represents the set of all functions from X to Y, `f $in fn(X)Y` checks if f is a function from X to Y
- **Example**:
```litex
have X, Y nonempty_set

have f fn(X)Y
f $in fn(X)Y
```
- **Note**: The power set axiom is implemented through `fn_template`, representing the set of all functions from X to Y

**Definition: Cartesian Product**

For sets $X$ and $Y$, the Cartesian product $X \times Y$ is the set of all ordered pairs $(x,y)$ where $x \in X$ and $y \in Y$. In symbols: $X \times Y := \{(x,y) : x \in X, y \in Y\}$; $a \in (X \times Y) \iff (\exists x \in X, \exists y \in Y, a = (x,y))$.

**Correspondence in Litex**:
- **Keywords**: `cart`, `$is_cart`, `dim`, `proj`, `coord`
- **Expression**: `cart(X1, X2, ..., Xn)` for n-fold Cartesian product, `$is_cart(x)` to check if x is a Cartesian product, `dim(x)` for dimension, `proj(x, i)` for projection to i-th component, `coord(a, x, i)` for i-th coordinate of element a
- **Example**:
```litex
have x set = cart(R, Q, Z)
$is_cart(x)
dim(x) = 3
proj(x, 1) = R
proj(x, 2) = Q
proj(x, 3) = Z
x $in set

let a x
coord(a, x, 1) $in R

$is_cart(cart(R, Q))
let y cart(R, Q)
dim(cart(R, Q)) = 2
coord(y, cart(R, Q), 1) $in R
```
- **Note**: The definition of Cartesian products requires the replacement axiom, which Litex currently does not support, but can be assumed through `know`

**Definition: Ordered $n$-tuple and $n$-fold Cartesian Product**

For a natural number $n$, an ordered $n$-tuple $(x_1, \ldots, x_n)$ is a collection of $n$ objects. Two $n$-tuples are equal if and only if all their corresponding components are equal: $(x_i)_{1 \leq i \leq n} = (y_i)_{1 \leq i \leq n} \iff (\forall 1 \leq i \leq n, x_i = y_i)$.

For sets $X_1, \ldots, X_n$, their Cartesian product $\prod_{i=1}^n X_i$ (also written $X_1 \times \ldots \times X_n$) is the set of all $n$-tuples $(x_1, \ldots, x_n)$ where $x_i \in X_i$ for all $1 \leq i \leq n$. In symbols: $\prod_{1 \leq i \leq n} X_i := \{(x_i)_{1 \leq i \leq n} : x_i \in X_i \text{ for all } 1 \leq i \leq n\}$.

**Correspondence in Litex**:
- **Keywords**: `cart_prod`, `index_set_of_cart_prod`, `cart_prod_proj`, `fn` (for key-value function)
- **Expression**: `cart_prod(X, kv)` where X is an index set and kv is a function from X to sets, `index_set_of_cart_prod(cart_prod(X, kv)) = X`, `cart_prod_proj(cart_prod(X, kv), i) = kv(i)` for the i-th projection
- **Example**:
```litex
have X set = {1, 2, 3}
have fn kv(x X) set =:
    case x = 1: N
    case x = 2: Q
    case x = 3: Z

$is_a_set(cart_prod(X, kv))
index_set_of_cart_prod(cart_prod(X, kv)) = X
cart_prod_proj(cart_prod(X, kv), 1) = kv(1) = N


have fn kv2(x N) set =:
    case x >= 2: N
    case x < 2: Q

$is_a_set(cart_prod(N, kv2))
index_set_of_cart_prod(cart_prod(N, kv2)) = N
cart_prod_proj(cart_prod(N, kv2), 1) = kv2(1) = Q
cart_prod_proj(cart_prod(N, kv2), 2) = kv2(2) = N
```
- **Note**: n-tuples and n-fold Cartesian products can be defined through functions and the replacement axiom

## Summary: All Ways to Construct Sets from Sets in ZFC

In ZFC set theory, there are **6 fundamental axioms** for constructing new sets from given sets, plus **Cartesian products** which are constructed from these axioms. All mathematical objects (functions, sequences, trees, graphs, topological spaces, real numbers, etc.) are ultimately constructed through combinations of these operations. The following table shows how each construction method works in Litex:

| ZFC Axiom | What It Constructs | Litex Implementation | Example |
|-----------|---------------------|---------------------|---------|
| **Separation (Specification)** | Subsets of A satisfying property P | `have s set = {x A: $P(x)}` | ```litex<br>prop P(x A)<br>have s set = {x A: $P(x)}<br>``` |
| **Power Set** | Set of all subsets of A | `power_set(A)` or `fn self_defined_power_set(A set) set` | ```litex<br>have y power_set(R)<br>y $subset_of R<br>``` |
| **Pairing** | Set containing exactly two objects | `have pair set = {a, b}` | ```litex<br>have a, b obj<br>have pair set = {a, b}<br>``` |
| **Union** | Set containing all elements from sets in A | `union(A, B)` or `union_of_family(F)` | ```litex<br>have a, b set<br>forall x a => x $in union(a, b)<br>forall x b => x $in union(a, b)<br>``` |
| **Replacement** | Image of A under function F | Function application + `know` (if needed) | ```litex<br>have X, Y set<br>have fn f(x X) Y<br># f[A] = {f(x): x in A}<br>have image set = {y Y: exist x A => y = f(x)}<br>``` |
| **Cartesian Product** | Set of ordered n-tuples from sets X₁, X₂, ..., Xₙ | `cart(X1, X2, ..., Xn)` or `cart_prod(index_set, kv)` | ```litex<br>have x set = cart(R, Q, Z)<br>let a x<br>coord(a, x, 1) $in R<br>``` |

### Key Points:

1. **Separation** is implemented directly through Litex's intensional set syntax `{x parent_set: condition}`. This is the most commonly used construction method.

2. **Power Set** can use the built-in `power_set(A)` or be defined as a function:
   ```litex
   fn self_defined_power_set(A set) set:
       forall y self_defined_power_set(A):
           y $in set
           y $subset_of A
       forall y set:
           y $subset_of A
           =>:
               y $in self_defined_power_set(A)
   ```

3. **Pairing** creates finite sets through enumeration: `{a}`, `{a, b}`, `{a, b, c}`, etc.

4. **Union** combines sets. For pairwise union: `union(A, B)`. For union of a family: define a function `union_of_family(F)`.

5. **Replacement** constructs the image of a set under a function. In Litex, this is typically done by defining the image set explicitly:
   ```litex
   have set image = {y Y: exist x A => y = f(x)}
   ```

6. **Cartesian Product** constructs ordered tuples from sets. Litex provides two methods:
   - **Fixed-arity**: `cart(X1, X2, ..., Xn)` for a fixed number of sets
   - **Indexed**: `cart_prod(index_set, kv)` where `kv` is a function mapping indices to sets
   
   ```litex
   # Fixed-arity Cartesian product
   have set x = cart(R, Q, Z)
   let a x
   coord(a, x, 1) $in R
   coord(a, x, 2) $in Q
   coord(a, x, 3) $in Z
   
   # Indexed Cartesian product
   have set X = {1, 2, 3}
   have fn kv(x X) set =:
       case x = 1: N
       case x = 2: Q
       case x = 3: Z
   cart_prod(X, kv) $in set
   ```

### What Can Be Constructed?

Through combinations of these 7 operations (6 ZFC axioms + Cartesian product), you can construct:

- **Arbitrary finite sets** (pairing + union)
- **Arbitrary subsets** (separation)
- **Iterated power sets** (power set applied repeatedly)
- **Function images** (replacement)
- **Cartesian products** (`cart` or `cart_prod` - constructed via power set + separation)
- **Ordered pairs and n-tuples** (Cartesian products)
- **Quotient sets** (separation + replacement)
- **Recursive and transfinite constructions** (replacement)

**Note**: While Cartesian products are technically constructed from power set and separation axioms, they are such a fundamental construction that Litex provides direct support through `cart` and `cart_prod`.

**Important**: There are no other independent construction methods in ZFC. All set constructions in mathematics ultimately reduce to combinations of these operations.

# Natural Numbers

Natural numbers are ubiquitous in mathematics. They form the foundation for counting, arithmetic, and many other mathematical structures. The axioms that characterize natural numbers are known as the **Peano axioms** (named after the Italian mathematician Giuseppe Peano). Sometimes, as in Terence Tao's *Analysis I*, the Peano axioms for natural numbers are presented as part of set theory, where natural numbers are constructed from sets using the ZFC axioms.

The Peano axioms provide a complete characterization of the natural numbers. They consist of five axioms that define:
1. The existence of a starting element (0)
2. The successor operation
3. The fact that 0 is not a successor
4. The injectivity of the successor function
5. The principle of mathematical induction

All properties of natural numbers, including addition, multiplication, ordering, and exponentiation, can be derived from these axioms. Below we present the Peano axioms and related theorems that follow from them.

**Definition: Natural Numbers**

The set of natural numbers $\mathbf{N}$ consists of all non-negative integers: $\mathbf{N} := \{0, 1, 2, 3, 4, \ldots\}$. Each element of this set is called a natural number.

**Correspondence in Litex**:
- **Keywords**: `N` (built-in set)
- **Expression**: `N` is Litex's built-in set of natural numbers
- **Example**:
```litex
have n N
n $in N
0 $in N
1 $in N
```
- **Note**: `N` is a built-in keyword in Litex, representing the set of natural numbers, containing 0, 1, 2, 3, ...

**Axiom: Successor**

For any natural number $n$, its successor $n++$ (or $n+1$) is also a natural number. In symbols: $n \in \mathbf{N} \implies n++ \in \mathbf{N}$.

**Correspondence in Litex**:
- **Keywords**: built-in arithmetic operations
- **Expression**: `forall n N => n + 1 $in N`
- **Example**:
```litex
have n N
n + 1 $in N
```
- **Note**: In Litex, the successor operation for natural numbers is represented by `+ 1`, which is a built-in arithmetic operation

**Definition: Natural Number Notation**

We define natural numbers recursively: $1 := 0++$, $2 := 1++$, $3 := 2++$, and so on. Each natural number is the successor of the previous one.

**Correspondence in Litex**:
- **Keywords**: numeric literals, built-in arithmetic
- **Expression**: Numbers like `1`, `2`, `3` are built-in literals
- **Example**:
```litex
1 = 0 + 1
2 = 1 + 1
3 = 2 + 1
```
- **Note**: Litex directly supports numeric literals, and the natural number properties of these numbers are built-in

**Axiom: Zero is Not a Successor**

Zero is not the successor of any natural number. For every natural number $n$, we have $n++ \neq 0$. In symbols: $\forall n \in \mathbf{N}, n++ \neq 0$.

**Correspondence in Litex**:
- **Keywords**: `forall`, `!=`
- **Expression**: `forall n N => n + 1 != 0`
- **Example**:
```litex
prove forall n N: n + 1 != 0:
    prove_by_contradiction n + 1 != 0:
        n + 1 = 0
        n = -1
        -1 $in N
```
- **Note**: This is a fundamental property of natural numbers and can be declared as an axiom using `know`

**Axiom: Injectivity of Successor**

Different natural numbers have different successors. If $n \neq m$ for natural numbers $n$ and $m$, then $n++ \neq m++$. Equivalently, if two natural numbers have the same successor, then they must be equal: $n++ = m++ \implies n = m$. In symbols: $\forall n, m \in \mathbf{N}, (n \neq m \implies n++ \neq m++) \iff (n++ = m++ \implies n = m)$.

**Correspondence in Litex**:
- **Keywords**: `forall`, `=>`, `<=>`, `=`, `!=`
- **Expression**: `forall n, m N: (n != m => n + 1 != m + 1) <=> (n + 1 = m + 1 => n = m)`
- **Example**:
```litex
prove forall n, m N: n != m => n + 1 != m + 1:
    prove_by_contradiction n + 1 = m + 1:
        n = (n+1) - 1 = (m+1)-1 = m
        n = m

prove forall n, m N: not n + 1 = m + 1 => not n = m:
    prove_by_contradiction n = m:
        n + 1 = m + 1
```
- **Note**: This is the uniqueness axiom for natural number successors

**Axiom: Mathematical Induction**

If a property $P(n)$ holds for $n=0$, and whenever it holds for some natural number $n$, it also holds for $n++$, then $P(n)$ holds for all natural numbers $n$. In symbols: $(P(0) \land (\forall n \in \mathbf{N}, P(n) \implies P(n++))) \implies (\forall n \in \mathbf{N}, P(n))$.

**Correspondence in Litex**:
- **Keywords**: `prove_by_induction`
- **Expression**: `prove_by_induction($prop(x, n), n, base_case)`
- **Example**:
```litex
prop p(x R, n N)
let x R
know $p(x, 1)
know forall n N_pos: $p(x, n) => $p(x, n + 1)

prove_by_induction($p(x, n), n, 1)

forall n N_pos: $p(x, n)
```
- **Note**: `prove_by_induction` is Litex's built-in proof strategy for mathematical induction

**Assumption: Existence of Natural Numbers**

We assume that there exists a set $\mathbf{N}$ satisfying all the axioms above. The elements of this set are called natural numbers.

**Correspondence in Litex**:
- **Keywords**: `N` (built-in)
- **Expression**: `N` is Litex's built-in set that satisfies all natural number axioms
- **Example**:
```litex
N $in set
0 $in N
```
- **Note**: `N` is a built-in set in Litex, and its existence and properties are guaranteed by the system

**Definition: Addition**

Addition of natural numbers is defined recursively. For any natural number $m$, we define $0 + m := m$. If we have defined $n + m$, then we define $(n++) + m := (n + m)++$. In symbols: $0 + m := m$; $(n++) + m := (n + m)++$.

**Correspondence in Litex**:
- **Keywords**: `+` (built-in operator)
- **Expression**: Addition is a built-in operation in Litex
- **Example**:
```litex
have m N
0 + m = m
have n N
(n + 1) + m = (n + m) + 1
```
- **Note**: `+` is a built-in arithmetic operator in Litex that satisfies the recursive definition of natural number addition

**Definition: Positive Natural Numbers**

A natural number $n$ is positive if and only if it is not equal to 0. In symbols: $n > 0 \iff n \neq 0$.

**Correspondence in Litex**:
- **Keywords**: `>`, `!=`, `N_pos`
- **Expression**: `n > 0 <=> n != 0`, or use the built-in set `N_pos`
- **Example**:
```litex
have n N
forall n N: n > 0 => n != 0

# or use the built-in set
have n N_pos
n > 0
```
- **Note**: `N_pos` is a built-in set in Litex, representing positive natural numbers

**Definition: Ordering of Natural Numbers**

For natural numbers $n$ and $m$, we say $n$ is greater than or equal to $m$ (written $n \geq m$ or $m \leq n$) if there exists a natural number $a$ such that $n = m + a$. We say $n$ is strictly greater than $m$ (written $n > m$ or $m < n$) if $n \geq m$ and $n \neq m$. In symbols: $n \geq m \iff \exists a \in \mathbf{N}, n = m + a$; $n > m \iff (n \geq m) \land (n \neq m)$.

**Correspondence in Litex**:
- **Keywords**: `>=`, `>`, `exist`, `=`
- **Expression**: `n >= m <=> exist a N: n = m + a`; `n > m <=> (n >= m), (n != m)`
- **Example**:
```litex
have n, m N

# Define n >= m using exist_prop: n >= m is equivalent to there exists a in N such that n = m + a
exist_prop a N st self_defined_ge_by_sum(n, m N):
    <=>:
        n = m + a

# n >= m is equivalent to $self_defined_ge_by_sum(n, m)
forall n, m N: n >= m => exist n - m st $self_defined_ge_by_sum(n, m), $self_defined_ge_by_sum(n, m)

know forall n, m N: $self_defined_ge_by_sum(n, m) => n >= m

# n > m is equivalent to n >= m and n != m
forall n, m N: n > m <=> not n = m, not n < m
```
- **Note**: `>=` and `>` are built-in comparison operators in Litex

**Definition: Multiplication**

Multiplication of natural numbers is defined recursively. For any natural number $m$, we define $0 \times m := 0$. If we have defined $n \times m$, then we define $(n++) \times m := (n \times m) + m$. In symbols: $0 \times m := 0$; $(n++) \times m := (n \times m) + m$.

**Correspondence in Litex**:
- **Keywords**: `*` (built-in operator)
- **Expression**: Multiplication is a built-in operation in Litex
- **Example**:
```litex
have m N
0 * m = 0
have n N
(n + 1) * m = (n * m) + m
```
- **Note**: `*` is a built-in arithmetic operator in Litex that satisfies the recursive definition of natural number multiplication

**Definition: Exponentiation**

Exponentiation for natural numbers is defined recursively. For any natural number $m$, we define $m^0 := 1$ (in particular, $0^0 := 1$). If $m^n$ has been defined, then we define $m^{n++} := m^n \times m$. In symbols: $m^0 := 1$ (in particular, $0^0 := 1$); $m^{n++} := m^n \times m$.

**Correspondence in Litex**:
- **Keywords**: `^` (built-in operator)
- **Expression**: Exponentiation is a built-in operation in Litex
- **Example**:
```litex
have m N_pos
m ^ 0 = 1
have n N_pos
m >= 0
m != 0
m ^ (n + 1) = (m ^ n) * m
```
- **Note**: `^` is a built-in exponentiation operator in Litex that satisfies the recursive definition of natural number exponentiation

## Theorems About Natural Numbers

The following theorems about natural numbers can be derived from the Peano axioms and the definitions above. These theorems demonstrate the rich structure that emerges from the simple axioms.

**Theorem: Trichotomy of Natural Numbers**

For any two natural numbers $n$ and $m$, exactly one of the following holds: $n < m$, $n = m$, or $n > m$. In symbols: $\forall n, m \in \mathbf{N}, (n < m \lor n = m \lor n > m) \land \neg((n < m \land n = m) \lor (n < m \land n > m) \lor (n = m \land n > m))$.

**Correspondence in Litex**:
- **Keywords**: `<`, `=`, `>`, `or`, `not`
- **Expression**: `forall n, m N: (n < m or n = m or n > m), not ((n < m, n = m) or (n < m, n > m) or (n = m, n > m))`
- **Example**:
```litex
have n, m N
n < m or n = m or n > m
not ((n < m, n = m) or (n < m, n > m) or (n = m, n > m))
```
- **Note**: The trichotomy property is a fundamental ordering property of natural numbers

**Theorem: Commutativity of Addition**

For any natural numbers $n$ and $m$, we have $n + m = m + n$. In symbols: $\forall n, m \in \mathbf{N}, n + m = m + n$.

**Correspondence in Litex**:
- **Keywords**: `+`, `=`, `forall`
- **Expression**: `forall n, m N: n + m = m + n`
- **Example**:
```litex
have n, m N
n + m = m + n
```
- **Note**: Commutativity of addition can be proven by mathematical induction

**Theorem: Associativity of Addition**

For any natural numbers $n$, $m$, and $k$, we have $(n + m) + k = n + (m + k)$. In symbols: $\forall n, m, k \in \mathbf{N}, (n + m) + k = n + (m + k)$.

**Correspondence in Litex**:
- **Keywords**: `+`, `=`, `forall`
- **Expression**: `forall n, m, k N: (n + m) + k = n + (m + k)`
- **Example**:
```litex
have n, m, k N
(n + m) + k = n + (m + k)
```
- **Note**: Associativity of addition can be proven by mathematical induction

**Theorem: Commutativity of Multiplication**

For any natural numbers $n$ and $m$, we have $n \times m = m \times n$. In symbols: $\forall n, m \in \mathbf{N}, n \times m = m \times n$.

**Correspondence in Litex**:
- **Keywords**: `*`, `=`, `forall`
- **Expression**: `forall n, m N: n * m = m * n`
- **Example**:
```litex
have n, m N
n * m = m * n
```
- **Note**: Commutativity of multiplication can be proven by mathematical induction

**Theorem: Associativity of Multiplication**

For any natural numbers $n$, $m$, and $k$, we have $(n \times m) \times k = n \times (m \times k)$. In symbols: $\forall n, m, k \in \mathbf{N}, (n \times m) \times k = n \times (m \times k)$.

**Correspondence in Litex**:
- **Keywords**: `*`, `=`, `forall`
- **Expression**: `forall n, m, k N: (n * m) * k = n * (m * k)`
- **Example**:
```litex
have n, m, k N
(n * m) * k = n * (m * k)
```
- **Note**: Associativity of multiplication can be proven by mathematical induction

**Theorem: Distributivity of Multiplication over Addition**

For any natural numbers $n$, $m$, and $k$, we have $n \times (m + k) = (n \times m) + (n \times k)$. In symbols: $\forall n, m, k \in \mathbf{N}, n \times (m + k) = (n \times m) + (n \times k)$.

**Correspondence in Litex**:
- **Keywords**: `*`, `+`, `=`, `forall`
- **Expression**: `forall n, m, k N: n * (m + k) = (n * m) + (n * k)`
- **Example**:
```litex
have n, m, k N
n * (m + k) = (n * m) + (n * k)
```
- **Note**: Distributivity is a fundamental property connecting addition and multiplication

**Theorem: Cancellation Law for Addition**

For any natural numbers $n$, $m$, and $k$, if $n + k = m + k$, then $n = m$. In symbols: $\forall n, m, k \in \mathbf{N}, (n + k = m + k) \implies (n = m)$.

**Correspondence in Litex**:
- **Keywords**: `+`, `=`, `=>`, `forall`
- **Expression**: `forall n, m, k N: n + k = m + k => n = m`
- **Example**:
```litex
have n, m, k N
n + k = m + k
=>:
    n = m
```
- **Note**: The cancellation law follows from the injectivity of the successor function

**Theorem: Well-Ordering Principle**

Every non-empty subset of natural numbers has a least element. That is, for any non-empty set $S \subseteq \mathbf{N}$, there exists $m \in S$ such that for all $n \in S$, we have $m \leq n$. In symbols: $\forall S \subseteq \mathbf{N}, (S \neq \emptyset) \implies (\exists m \in S, \forall n \in S, m \leq n)$.

**Correspondence in Litex**:
- **Keywords**: `have set`, `{}`, `!=`, `exist`, `forall`, `<=`
- **Expression**: `forall S set: (S $subset_of N), (S != {}) => exist m S: forall n S => m <= n`
- **Example**:
```litex
have S set = {n N: ...}
S != {}
exist m S:
    forall n S:
        m <= n
```
- **Note**: The well-ordering principle is equivalent to the principle of mathematical induction

**Theorem: No Largest Natural Number**

For any natural number $n$, there exists a natural number $m$ such that $m > n$. In symbols: $\forall n \in \mathbf{N}, \exists m \in \mathbf{N}, m > n$.

**Correspondence in Litex**:
- **Keywords**: `forall`, `exist`, `>`
- **Expression**: `forall n N => exist m N: m > n`
- **Example**:
```litex
have n N
exist m N: m > n
# For example, m = n + 1
n + 1 > n
```
- **Note**: This theorem shows that the set of natural numbers is infinite

**Theorem: Addition Preserves Order**

For any natural numbers $n$, $m$, and $k$, if $n < m$, then $n + k < m + k$. In symbols: $\forall n, m, k \in \mathbf{N}, (n < m) \implies (n + k < m + k)$.

**Correspondence in Litex**:
- **Keywords**: `<`, `+`, `=>`, `forall`
- **Expression**: `forall n, m, k N: n < m => n + k < m + k`
- **Example**:
```litex
have n, m, k N
n < m
=>:
    n + k < m + k
```
- **Note**: This theorem shows that addition is order-preserving

**Theorem: Multiplication Preserves Order**

For any natural numbers $n$, $m$, and positive natural number $k$, if $n < m$, then $n \times k < m \times k$. In symbols: $\forall n, m \in \mathbf{N}, \forall k \in \mathbf{N}_{>0}, (n < m) \implies (n \times k < m \times k)$.

**Correspondence in Litex**:
- **Keywords**: `<`, `*`, `=>`, `forall`, `N_pos`
- **Expression**: `forall n, m N, k N_pos: n < m => n * k < m * k`
- **Example**:
```litex
have n, m N
have k N_pos
n < m
=>:
    n * k < m * k
```
- **Note**: This theorem shows that multiplication by a positive number is order-preserving -->