# Set Theory: The Solid Foundation of Modern Mathematics

_Even disregarding the intrinsic necessity of some new axiom, and even in case it has no intrinsic necessity at all, a probable decision about its truth is possible also in another way, namely, inductively by studying its "success". Success here means fruitfulness in consequences, in particular in "verifiable" consequences, i.e., consequences demonstrable without the new axiom, whose proofs with the help of the new axiom, however, are considerably simpler and easier to discover, and make it possible to contract into one proof many different proofs._

_Kurt Godel, What is Cantor's continuum problem?_

## A Little Bit of History

(Skip this section if you are not interested in history)

In 1931, a young Austrian logician named Kurt Gödel delivered a stunning blow to the mathematical world. He discovered what would become known as the incompleteness theorems, revealing a profound truth: in any mathematical system complex enough to define natural numbers, there will always be statements that can neither be proven true nor falsified. The mathematical universe, it turned out, had boundaries—and those boundaries were fundamentally ambiguous.

This revelation forced mathematicians to confront an uncomfortable reality: the choice of axioms was not a matter of finding the "correct" ones, but rather a matter of choosing which mathematical truths one wanted to explore. Different mathematicians could—and did—choose different axiomatic systems, each opening doors to some truths while closing others. There was no inherent right or wrong in these choices; they were neither good nor bad by nature, but rather different paths through the mathematical landscape.

Gödel himself offered a guiding principle: if an axiomatic system could easily derive a large class of facts, then it was appropriate. Following this wisdom, modern mathematics has overwhelmingly chosen set theory as its foundation. The choice was pragmatic: set theory is intuitive enough for most people to grasp, yet powerful enough to express calculus, algebra, and virtually all the mathematics that anyone—except perhaps logic PhD students—would ever need.

The birth of set theory in the late 19th century marked one of the most dramatic revolutions in the history of mathematics—a revolution that would ultimately provide mathematics with its unshakeable foundation. Georg Cantor, the visionary architect of this mathematical paradise, faced fierce resistance and personal attacks from the mathematical establishment of his time, with his revolutionary ideas about infinite sets being dismissed as "a disease from which mathematics will have to recover."

Yet, through decades of relentless pursuit of mathematical truth, Cantor's once-controversial theories about the infinite would eventually be recognized as the bedrock upon which all of modern mathematics rests.

Just as the history of natural science has shown time and again, the most profound truths are often the easiest to grasp. Everyone can understand the syllogism, yet it is almost the entire foundation of mathematical reasoning. Set theory, at its advanced levels, can become very difficult, but one of its great virtues is that we don't need to master the deepest parts. It is enough to learn just what is necessary to handle everyday mathematics. In fact, when it comes to writing Litex, all the set theory you need can be learned in just five minutes.

Zermelo–Fraenkel set theory, named after mathematicians Ernst Zermelo and Abraham Fraenkel, is an axiomatic system proposed in the early twentieth century to formulate a theory of sets free of paradoxes such as Russell's paradox. Today, Zermelo–Fraenkel set theory with the historically controversial axiom of choice (AC) included has become the standard form of axiomatic set theory and serves as the most common foundation of mathematics. When the axiom of choice is included, the system is abbreviated as ZFC (where C stands for "choice"),[1] while ZF refers to Zermelo–Fraenkel set theory without the axiom of choice.

Informally,[2] Zermelo–Fraenkel set theory aims to formalize a single primitive notion: that of a hereditary well-founded set. In this framework, all entities in the universe of discourse are such sets. Consequently, the axioms of Zermelo–Fraenkel set theory refer only to pure sets and prevent its models from containing urelements—elements that are not themselves sets. Additionally, proper classes—collections of mathematical objects defined by a shared property that are too large to be sets—can only be treated indirectly. 

Litex chooses set theory as its foundation precisely because it is the most accessible to ordinary people. If you need a more powerful axiomatic system than set theory, you can turn to other, more abstract formal languages such as Lean, Coq, and Isabelle, which are built on type theory and other advanced foundations. But for most people and most mathematical tasks, set theory provides the perfect balance of simplicity and power.

## Set Theory in Litex

Modern math is built upon set theory. In Litex, to ensure correctness and be more aligned with modern math, when the user wants to declare a new object, he must say which set it belongs to.

```litex
have a N, b Q, c R
let e N, f Q, g R
```

The keyword `set` is useless, unless there is a proposition that works together with it. In our case, as how math works, it is the keyword `in`.

```litex
have a N
a $in N
```

Actually, `have a N` has two effects: 1. declare an object `a` in current environment (context). 2. assume `a` is in set `N`, similar to `know a $in N`.

As `in` serves many use cases in math, it also serves many use cases in Litex.

1. serves as companion to `set`.

```litex
have a N
a $in N
```


3. As parameter condition for everything: function, proposition, etc.

It is easy to introduce wrong facts if we do not have `set` requirement of things that might receive parameters. For example, it is strange to pass a set object to `+` (e.g. It is strange to say `empty_set + empty_set` ). It's also strange to say `2 $in 1` because 1 is not a set. To solve such ambiguity, we use `in` to require the parameter to be in a set at definition time.

(It sort of has the same functionality as `type` in programming languages like C, Java, TypeScript, etc. The user can only pass parameters that satisfy certain conditions to a function, proposition, etc.)

## In

`in` is a built-in proposition in Litex. It is used when you want to claim an object is in a set. Since `in` facts are everywhere, Litex allows you to omit it in most cases. For example:

```litex
let n N
n $in N
```

`let n N` here has two effects:

1. Declare an object in current environment (context). For example, object `n` now exists in current environment. You can use it later.

2. Assume `n` is in set `N`. It has the same effect as `know n $in N`.

```litex
forall x N:
    x $in N
```

`x N` in `forall x N` is the same as `x $in N`.

```litex
fn f(x N) N
```

`x N` in `fn f(x N) N` means the parameter `x` that is passed to `f` is must satisfy `x $in N`, i.e. The domain of the first parameter `x` is subset of `N`.

```litex
prop p(x N)
```

`x N` in `prop p(x N)` means the parameter `x` that is passed to `p` is must satisfy `x $in N`, i.e. The domain of the first parameter `x` is subset of `N`.

As you can see, `in` is everywhere, in explicit and implicit ways.

Examples of not in special sets:

```litex 
# Examples of not in N (natural numbers)
not -1 $in N
not 3.5 $in N
not (-1 * 1) $in N
not (2 + 3.5) $in N
not (-2) $in N

# Examples of not in Z (integers)
not 3.5 $in Z
not 2.7 $in Z
not (1 + 0.5) $in Z
not (3 / 2) $in Z

# Examples of not in N_pos (positive integers)
not -1 $in N_pos
not -2 $in N_pos
not 0 $in N_pos
not 3.5 $in N_pos
not (-1 * 1) $in N_pos
not (2 - 3) $in N_pos
not (1 - 1) $in N_pos
```

## Cartesian Products

The Cartesian product is a fundamental operation in set theory that allows us to combine sets to form ordered tuples. In mathematics, the Cartesian product of sets $X$ and $Y$, denoted $X \times Y$, is the set of all ordered pairs $(x, y)$ where $x \in X$ and $y \in Y$.

More generally, for $n$ sets $X_1, X_2, \ldots, X_n$, their Cartesian product $X_1 \times X_2 \times \cdots \times X_n$ (also denoted $\prod_{i=1}^n X_i$) is the set of all ordered $n$-tuples $(x_1, x_2, \ldots, x_n)$ where $x_i \in X_i$ for each $i = 1, 2, \ldots, n$.

**Mathematical Definition**: If $X$ and $Y$ are sets, then we define the Cartesian product $X \times Y$ to be the collection of ordered pairs, whose first component lies in $X$ and second component lies in $Y$:

$$X \times Y := \{(x,y) : x \in X, y \in Y\}$$

Equivalently, $a \in (X \times Y) \iff (\exists x \in X, \exists y \in Y, a = (x,y))$.

Litex provides two ways to work with Cartesian products: `cart` for fixed-arity products and `cart_prod` for products defined by an index set.

### `cart`: Fixed-Arity Cartesian Products

The `cart` function creates a Cartesian product of a fixed number of sets. For sets $X_1, X_2, \ldots, X_n$, the Cartesian product $X_1 \times X_2 \times \ldots \times X_n$ is the set of all ordered $n$-tuples $(x_1, x_2, \ldots, x_n)$ where $x_i \in X_i$ for all $1 \leq i \leq n$.

**Keywords**: `cart`, `$is_cart`, `dim`, `proj`, `coord`, `set_dim`

**Built-in functions and predicates**:
- `cart(X1, X2, ..., Xn)`: Creates the Cartesian product of sets $X_1, X_2, \ldots, X_n$
- `$is_cart(x)`: A predicate that checks whether `x` is a Cartesian product
- `set_dim(x)`: Returns the dimension (number of components) of a Cartesian product
- `proj(x, i)`: Returns the $i$-th projection (the $i$-th component set) of a Cartesian product
- `coord(a, x, i)`: Returns the $i$-th coordinate of element `a` in Cartesian product `x`

**Example 1: Three-Dimensional Cartesian Product**

```litex
# Create a 3-fold Cartesian product: R × Q × Z
have x set = cart(R, Q, Z)
$is_cart(x)
set_dim(x) = 3
proj(x, 1) = R
proj(x, 2) = Q
proj(x, 3) = Z
$is_set(x)

# Access elements and coordinates
have a cart(R, Q, Z)
a[1] $in R
a[2] $in Q
a[3] $in Z
dim(a) = 3
```

**Explanation**:
1. **`have set x = cart(R, Q, Z)`**: This creates a Cartesian product of three sets: the real numbers $\mathbb{R}$, the rational numbers $\mathbb{Q}$, and the integers $\mathbb{Z}$. The result is stored in `x`, which represents the set $\mathbb{R} \times \mathbb{Q} \times \mathbb{Z}$.
2. **`$is_cart(x)`**: This verifies that `x` is indeed a Cartesian product. Litex can automatically verify this fact.
3. **`dim(x) = 3`**: The dimension of `x` is 3, meaning it is a product of three sets. This corresponds to the number of arguments passed to `cart()`.
4. **`proj(x, i)`**: Returns the $i$-th component set of the Cartesian product. For example, `proj(x, 1) = R`.
5. **`let a x`**: This declares an element `a` that belongs to the Cartesian product `x`. Since `x = cart(R, Q, Z)`, the element `a` is an ordered triple $(a_1, a_2, a_3)$ where $a_1 \in \mathbb{R}$, $a_2 \in \mathbb{Q}$, and $a_3 \in \mathbb{Z}$.
6. **`a[i] $in X_i`**: Extracts the $i$-th component of the ordered tuple `a` in the Cartesian product `x`. For example, `a[1] $in R` means the first coordinate of `a` belongs to $\mathbb{R}$.

**Example 2: Two-Dimensional Cartesian Product**

Litex can compute non-numeric values, such as the dimension of a Cartesian product:

```litex
$is_cart(cart(R, Q))
have y cart(R, Q)
dim(y) = 2
y[1] $in R
y[2] $in Q
```

**Explanation**:
1. **`$is_cart(cart(R, Q))`**: This verifies that `cart(R, Q)` is a Cartesian product. Note that we can use `cart(R, Q)` directly without assigning it to a variable first.
2. **`have y cart(R, Q)`**: This declares an element `y` in the Cartesian product $\mathbb{R} \times \mathbb{Q}$. The element `y` is an ordered pair $(y_1, y_2)$ where $y_1 \in \mathbb{R}$ and $y_2 \in \mathbb{Q}$.
3. **`set_dim(y) = 2`**: The dimension of `y` is 2, since it is a product of two sets. Litex can compute this value directly.

**Key Concepts**:

- **Dimension**: The dimension of a Cartesian product is the number of sets being multiplied together. For example:
  - `set_dim(y) = 2` (two-dimensional)
  - `set_dim(x) = 3` (three-dimensional)
  - `set_dim(x) = n` ($n$-dimensional)

- **Projections**: The projection `proj(x, i)` returns the $i$-th component set of the Cartesian product `x`. For `x = cart(X1, X2, ..., Xn)`:
  - `proj(x, 1) = X1`
  - `proj(x, 2) = X2`
  - ...
  - `proj(x, n) = Xn`

- **Coordinates**: For an element `a` in a Cartesian product `x = cart(X1, X2, ..., Xn)`, the coordinate `coord(a, x, i)` extracts the $i$-th component of `a`. The coordinate satisfies:
  - `coord(a, x, i) $in proj(x, i)` for all valid indices $i$

**Explanation**:
- `cart_prod(X, kv)` creates a Cartesian product where `X` is the index set and `kv` is a function from `X` to sets
- `index_set_of_cart_prod(cart_prod(X, kv))` returns the index set `X`
- `cart_prod_proj(cart_prod(X, kv), i)` returns the projection to the $i$-th component, which equals `kv(i)`

**When to use which**:
- Use `cart` when you have a fixed, small number of sets (e.g., `cart(R, Q, Z)`)
- Use `cart_prod` when you need to define a product over an arbitrary index set, especially when the index set might be large or infinite

**Applications**:

Cartesian products are fundamental in mathematics and have many applications:

1. **Coordinate Systems**: The Cartesian plane $\mathbb{R} \times \mathbb{R}$ is the foundation of analytic geometry.
2. **Relations**: A relation from set $X$ to set $Y$ is a subset of $X \times Y$.
3. **Functions**: A function $f: X \to Y$ can be viewed as a subset of $X \times Y$ with special properties.
4. **Product Spaces**: In topology and analysis, Cartesian products form product spaces.
5. **Multiple Variables**: When working with functions of multiple variables, the domain is often a Cartesian product.

## Power Set

### Natural Language Definition

The **power set** of a set $A$, denoted $\mathcal{P}(A)$ or $2^A$, is the set of all subsets of $A$. In other words, every element of the power set is itself a set that is a subset of $A$. For example, if $A = \{1, 2\}$, then $\mathcal{P}(A) = \{\emptyset, \{1\}, \{2\}, \{1, 2\}\}$.

In symbols: For any set $A$, the power set $\mathcal{P}(A)$ satisfies: $y \in \mathcal{P}(A) \iff y \subseteq A$.

### Built-in Power Set in Litex

Litex provides a built-in `power_set` function:

```litex
# Every element of power_set(R) is a subset of R
forall y power_set(R):
    y $subset_of R
```

**Keywords**: `power_set`, `$subset_of`

**Example**:
```litex
# The power set of R contains all subsets of R
have y power_set(R)
y $subset_of R

```

### Examples

**Example 1: Power set of a finite set**
```litex
# Define a finite set
have A set = {1, 2, 3}

# Use built-in power_set
$is_nonempty_set({1, 2, 3})
$is_set(A)
have y power_set(A)
y $subset_of A

# All subsets of A are in power_set(A)
have empty set = {}
empty $subset_of A
empty $in power_set(A)

have singleton1 set = {1}
singleton1 $subset_of A
singleton1 $in power_set(A)

have pair12 set = {1, 2}
prove_enum x pair12:
    x $in A
pair12 $subset_of A
pair12 $in power_set(A)

# A itself is in its power set
A $subset_of A
A $in power_set(A)
```

**Example 2: Using self-defined power set**
```litex
# Define a set
have B set = {5, 10}

# Use self-defined power set
let fn self_defined_power_set(A set) set:
    forall y self_defined_power_set(A):
        y $subset_of A
    forall y set:
        y $subset_of A
        =>:
            y $in self_defined_power_set(A)

# Check that subsets are in the power set
have subset1 set = {5}
subset1 $subset_of B
subset1 $in self_defined_power_set(B)

# The set itself is in its power set
B $subset_of B
B $in self_defined_power_set(B)
```

---

## Summary: All Ways to Construct Sets from Sets in ZFC

In ZFC set theory, there are **6 fundamental axioms** for constructing new sets from given sets, plus **Cartesian products** which are constructed from these axioms. All mathematical objects (functions, sequences, trees, graphs, topological spaces, real numbers, etc.) are ultimately constructed through combinations of these operations. The following table shows how each construction method works in Litex:

| ZFC Axiom | What It Constructs | Litex Implementation | Example |
|-----------|---------------------|---------------------|---------|
| **Separation (Specification)** | Subsets of A satisfying property P | `have set s = {x A: $P(x)}` | ```litex<br>prop P(x A)<br>have set s = {x A: $P(x)}<br>``` |
| **Power Set** | Set of all subsets of A | `power_set(A)` or `fn self_defined_power_set(A set) set` | ```litex<br>have y power_set(R)<br>y $subset_of R<br>``` |
| **Pairing** | Set containing exactly two objects | `have set s = {a, b}` | ```litex<br>have a, b obj<br>have set pair = {a, b}<br>``` |
| **Union** | Set containing all elements from sets in A | `union(A, B)` or `union_of_family(F)` | ```litex<br>have a, b set<br>forall x a => x $in union(a, b)<br>forall x b => x $in union(a, b)<br>``` |
| **Replacement** | Image of A under function F | Function application + `know` (if needed) | ```litex<br>have X, Y set<br>have fn f(x X) Y<br># f[A] = {f(x): x in A}<br>have set image = {y Y: exist x A => y = f(x)}<br>``` |
| **Cartesian Product** | Set of ordered n-tuples from sets X₁, X₂, ..., Xₙ | `cart(X1, X2, ..., Xn)` or `cart_prod(index_set, kv)` | ```litex<br>have set x = cart(R, Q, Z)<br>let a x<br>coord(a, x, 1) $in R<br>``` |

### Key Points:

Read [ZFC Axioms In Litex](https://litexlang.com/doc/How_Litex_Works/ZFC_Axioms_In_Litex) for more details.

1. **Separation** is implemented directly through Litex's intensional set syntax `{x parent_set: condition}`. This is the most commonly used construction method.

2. **Power Set** is built-in in Litex. It is a function that takes a set and returns the power set of that set, i.e. a set contains and only contains subsets of the input set.

3. **Pairing** creates finite sets through enumeration: `{a}`, `{a, b}`, `{a, b, c}`, etc.

4. **Union** combines sets. For pairwise union: `union(A, B)`. For union of a family: define a function `union_of_family(F)`.

5. **Replacement** constructs the image of a set under a function. In Litex, this is typically done by defining the image set explicitly.

6. **Cartesian Product** constructs ordered tuples from sets. 

### Intensional Set

The **intensional set** syntax `{x parent_set: facts}` is Litex's implementation of the **Separation Axiom** (also called the **Axiom of Specification**) from ZFC set theory. This is the most fundamental and commonly used way to construct subsets in Litex.

#### Syntax

The general form is:
```
have s set = {x parent_set: fact1, fact2, ...}
```

Where:
- `x` is a **bound variable** that ranges over elements
- `parent_set` is the **parent set** that `x` must belong to (i.e., `x $in parent_set`)
- `fact1, fact2, ...` are **conditions** (facts) that `x` must satisfy
- The result is a **subset** of `parent_set` containing exactly those elements that satisfy all the conditions

#### Mathematical Meaning

In mathematical notation, `{x parent_set: facts}` corresponds to:
$$\{x \in \text{parent\_set} : \text{facts}(x)\}$$

This reads as: "the set of all `x` in `parent_set` such that `facts` hold for `x`."

#### Automatic Facts Generated

When you define a set using intensional syntax, Litex automatically generates two facts:

1. **The set is indeed a set**: `s $in set`
2. **Membership characterization**: `forall x parent_set: fact1, fact2, ... <=> x $in s`

This means: an element `x` belongs to `s` if and only if `x` is in `parent_set` and satisfies all the conditions.

#### Examples

**Example 1: Simple condition**
```litex
# Define the set of positive real numbers
have positive_reals set = {x R: x > 0}

# Litex automatically knows:
# 1. positive_reals $in set
# 2. forall x R: x > 0 <=> x $in positive_reals

# Usage
3 $in positive_reals
# -1 $in positive_reals  # This will be false
```

**Example 2: Using a proposition**
```litex
# Define a proposition
prop is_even(n N):
    n % 2 = 0

# Define the set of even numbers
have even_numbers set = {n N: $is_even(n)}
```

**Example 3: Multiple conditions**
```litex
# Define the set of positive integers greater than 5
prop p(x R)
have large_positive set = {n N: $p(n), n > 0, n > 5}

# Or equivalently:
have large_positive2 set = {n N: $p(n), n > 5}
```

**Example 6: Subset of a Cartesian product**
```litex
# Define a relation (subset of R × R)
have less_than_relation set = {z cart(R, R): z[1] < z[2]}

# This defines all ordered pairs (x, y) where x < y
```

#### Key Points

1. **Parent set is required**: You must always specify `parent_set` to ensure type safety and correctness. This corresponds to the requirement in ZFC that separation can only create subsets of existing sets.

2. **Conditions are facts**: The conditions after the colon can be any facts (propositions, equations, inequalities, etc.) that involve the bound variable `x`.

3. **Multiple conditions**: You can list multiple conditions separated by commas. All conditions must be satisfied for an element to be in the set.

4. **Automatic derivation**: Litex automatically derives membership facts, so you don't need to manually prove that elements satisfying the conditions belong to the set.

5. **Most common construction**: This is the most frequently used method for constructing sets in Litex, as it directly implements the Separation Axiom, which is fundamental to set theory.

#### Proposition and Set Equivalence

**Important Note**: In Litex, there is a fundamental equivalence between propositions and sets. When you define a proposition on a set, you can equivalently think of it as defining a subset of that set.

Specifically:
- **Defining a proposition**: `prop p(x someset): facts` is equivalent to defining a set `have set_p set = {x someset: facts}`
- **Using the proposition**: `$p(x)` is equivalent to `x $in set_p`

This means that whenever you can express a property as a proposition on a set, you can also express it as a subset of that set, and vice versa.

**Example**:
```litex
# Method 1: Define a proposition
prop is_positive(x R):
    x > 0

# Method 2: Define the corresponding set
have positive_set set = {x R: x > 0}

# These are equivalent:
# - $is_positive(3) is equivalent to 3 $in positive_set
# - $is_positive(-1) is equivalent to -1 $in positive_set

# You can use either approach:
know $is_positive(5)
know 5 $in positive_set  # Same meaning
```

**Why this matters**: This equivalence allows you to choose the most convenient representation for your needs:
- Use **propositions** when you want to emphasize the logical property or when you need to use it in logical contexts
- Use **sets** when you want to emphasize the collection of objects or when you need to perform set operations (union, intersection, etc.)

Both approaches are mathematically equivalent and Litex treats them as such.

#### Relationship to ZFC

The intensional set syntax `{x parent_set: facts}` directly corresponds to the **Axiom of Separation** (also called **Axiom of Specification**) in ZFC:

**ZFC Axiom of Separation**: For any set $A$ and any property $P(x)$, there exists a set $B$ such that:
$$B = \{x \in A : P(x)\}$$

In Litex, this becomes:
```
prop P(x parent_set)
have B set = {x parent_set: $P(x)}
```

This axiom ensures that we can always form subsets by "separating" elements from a parent set that satisfy a given property.

#### Multi-Parameter Propositions and Cartesian Products

The equivalence between propositions and sets extends to multi-parameter propositions as well. A proposition with multiple parameters can correspond to a subset of a Cartesian product of sets.

**Example: Two-parameter proposition**
```litex
# Define a set of ordered pairs where both coordinates are positive
have cart_R_pos_R_pos set = {x cart(R, R): x[1] > 0, x[2] > 0}

# Define the equivalent proposition
prop larger_than_0_larger_than_0(x cart(R, R)):
    x[1] > 0
    x[2] > 0

# These are equivalent:
# - $larger_than_0_larger_than_0(x) is equivalent to x $in cart_R_pos_R_pos
forall x cart_R_pos_R_pos: $larger_than_0_larger_than_0(x)
```

Example:

```litex
prop p(x R)
prop q(x R, y R)

know:
    forall x R: 
        $p(x)
        =>:
            1 $in {a R: $q(x, a), a > 0}
            $is_nonempty_set({b R: $q(b, x), b > x})

    $p(1)

# 1 $in {a R: $q(1, a), a > 0}
$is_nonempty_set({a R: $q(a, 1), a > 1})
```

```litex
have fn f(x {y R: y > 0}) {z R: z > -1} = x
```

**General principle**: For a proposition `prop p(x1 set1, x2 set2, ..., xn setn): facts`, you can equivalently define:
- A set `have set set_p = {(x1, x2, ..., xn) cart(set1, set2, ..., setn): facts}`
- Where `$p(x1, x2, ..., xn)` is equivalent to `(x1, x2, ..., xn) $in set_p`

This shows that multi-parameter propositions naturally correspond to subsets of Cartesian products, which is consistent with how relations are typically defined in mathematics.

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

## Bonus: Two Perspectives on Cartesian Products

Set theory is the foundation of modern mathematics. When dealing with foundational concepts, it's easy to make errors or misunderstand them. A perfect example is the definition of Cartesian products.

There are two main approaches to defining Cartesian products: the **ordered pair approach** (recursive definition) and the **function approach** (mapping definition). While both are mathematically valid, the function approach is more modern and elegant, especially as mathematics has evolved to focus on **structure** rather than concrete implementation.

### The Ordered Pair Approach

This is the most common and intuitive introductory definition.

- **For two sets** \(A\) and \(B\):
  \[
  A \times B = \{(a,b) \mid a \in A, b \in B\}
  \]
  Here, \((a,b)\) must be implemented as a pure set in set theory. For example, using the Kuratowski definition:
  \[
  (a,b) := \{\{a\},\{a,b\}\}
  \]
  This distinguishes the order of elements.

- **For higher dimensions**, we use recursive definition:
  \[
  A \times B \times C := (A \times B) \times C
  \]
  So a triple is a **nested ordered pair** like \(((a,b),c)\).

**Advantages**:
- Intuitive and aligns with the everyday notion of "ordered lists"
- Strictly built on set-theoretic foundations (everything reduces to sets)

**Disadvantages**:
- The nested structure is asymmetric: triples are \(((a,b),c)\), quadruples are \((((a,b),c),d)\), etc. But what we actually want is a "flat" structure like \((a,b,c,d)\)
- Different lengths have different structures, lacking uniformity
- Ambiguity issues: For \(((0,1),2)\), what does \([1]\) refer to? Is it \(0\) or \((0,1)\)? This creates confusion
- Difficult to generalize to infinite index sets

### The Function Approach

The Cartesian product \(\prod_{i \in I} A_i\) is defined as the set of all functions \(f: I \to \bigcup_{i \in I} A_i\) such that \(f(i) \in A_i\) for all \(i \in I\).

**Advantages**:
- **Universal property**: The Cartesian product \(\prod A_i\) has the universal property: there is a family of projection maps \(\pi_j : \prod A_i \to A_j\) such that for any set \(X\) and any family of maps \(g_j: X \to A_j\), there exists a **unique** map \(u: X \to \prod A_i\) satisfying \(\pi_j \circ u = g_j\). The function definition directly satisfies this: \(u(x)\) is simply the function \(i \mapsto g_i(x)\)
- **Generalizes to infinity**: The function definition seamlessly extends to infinite index sets
- **Unified with other constructions**: In computer science, tuples are often viewed as records, which are essentially mappings from labels to values
- **Uniform structure**: All Cartesian products, regardless of dimension, have the same structure (functions from index sets)

### Equivalence of the Two Definitions

A key fact: there exists a natural **bijection** between the two representations.

- **From function to nested ordered pair**: Given \(f: \{1,2,3\} \to \bigcup A_i\) satisfying \(f(i) \in A_i\), we can map it to \(((f(1),f(2)),f(3))\) (a nested ordered pair)

- **From nested ordered pair to function**: Given \(((a,b),c)\), we can construct \(f\) such that \(f(1)=a, f(2)=b, f(3)=c\)

Although the concrete set structures differ (one is a set of functions, the other is a set of nested ordered pairs), mathematically, once we establish a bijection, we treat them as **isomorphic**. We don't distinguish implementation details; we only care about the **universal properties** they satisfy.

### Why the Function Approach is Preferred

As mathematics has advanced, the focus has shifted from concrete implementations to abstract structures. The function approach captures the essential structure of Cartesian products—their universal property—without getting bogged down in the messy details of nested pairs. This is why modern mathematics and Litex favor the function-based definition.

