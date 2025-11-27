# Set Theory: The Solid Foundation of Modern Mathematics

_From the paradise that Cantor created for us, no one shall be be able to expel us._

_— David Hilbert_

## A Little Bit of History

The birth of set theory in the late 19th century marked one of the most dramatic revolutions in the history of mathematics—a revolution that would ultimately provide mathematics with its unshakeable foundation. Georg Cantor, the visionary architect of this mathematical paradise, faced fierce resistance and personal attacks from the mathematical establishment of his time, with his revolutionary ideas about infinite sets being dismissed as "a disease from which mathematics will have to recover."

Yet, through decades of relentless pursuit of mathematical truth, Cantor's once-controversial theories about the infinite would eventually be recognized as the bedrock upon which all of modern mathematics rests.

Just as the history of natural science has shown time and again, the most profound truths are often the easiest to grasp. Everyone can understand the syllogism, yet it is almost the entire foundation of mathematical reasoning. Set theory, at its advanced levels, can become very difficult, but one of its great virtues is that we don’t need to master the deepest parts. It is enough to learn just what is necessary to handle everyday mathematics. In fact, when it comes to writing Litex, all the set theory you need can be learned in just five minutes.

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

2. A function satisfy a function template also uses the keyword `in`.

```litex
fn_template self_defined_seq(s set):
    fn (n N) s

fn f(n N) R

f $in self_defined_seq(R)
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

The Cartesian product is a fundamental operation in set theory that allows us to combine sets to form ordered tuples. Litex provides two ways to work with Cartesian products: `cart` for fixed-arity products and `cart_prod` for products defined by an index set.

### `cart`: Fixed-Arity Cartesian Products

The `cart` function creates a Cartesian product of a fixed number of sets. For sets $X_1, X_2, \ldots, X_n$, the Cartesian product $X_1 \times X_2 \times \ldots \times X_n$ is the set of all ordered $n$-tuples $(x_1, x_2, \ldots, x_n)$ where $x_i \in X_i$ for all $1 \leq i \leq n$.

**Keywords**: `cart`, `$is_cart`, `dim`, `proj`, `coord`

**Example**:
```litex
# Create a 3-fold Cartesian product: R × Q × Z
have set x = cart(R, Q, Z)
$is_cart(x)
dim(x) = 3
proj(x, 1) = R
proj(x, 2) = Q
proj(x, 3) = Z
x $in set

# Access elements and coordinates
let a x
coord(a, x, 1) $in R
coord(a, x, 2) $in Q
coord(a, x, 3) $in Z

# 2-fold Cartesian product: R × Q
$is_cart(cart(R, Q))
let y cart(R, Q)
dim(cart(R, Q)) = 2
coord(y, cart(R, Q), 1) $in R
coord(y, cart(R, Q), 2) $in Q
```

**Explanation**:
- `cart(X1, X2, ..., Xn)` creates an $n$-fold Cartesian product
- `$is_cart(x)` checks if `x` is a Cartesian product
- `dim(x)` returns the dimension (number of factors) of the Cartesian product
- `proj(x, i)` returns the $i$-th projection (the $i$-th set in the product)
- `coord(a, x, i)` returns the $i$-th coordinate of element `a` in Cartesian product `x`

### `cart_prod`: Indexed Cartesian Products

The `cart_prod` function creates a Cartesian product using an index set and a key-value function that maps each index to a set. This is useful when you want to define a product over an arbitrary (possibly infinite) index set.

**Keywords**: `cart_prod`, `index_set_of_cart_prod`, `cart_prod_proj`, `fn` (for key-value function)

**Example 1: Finite index set**:
```litex
# Define an index set
have set X = {1, 2, 3}

# Define a key-value function mapping indices to sets
have fn kv(x X) set =:
    case x = 1: N
    case x = 2: Q
    case x = 3: Z

# Create the Cartesian product: N × Q × Z
cart_prod(X, kv) $in set
index_set_of_cart_prod(cart_prod(X, kv)) = X
cart_prod_proj(cart_prod(X, kv), 1) = kv(1) = N
cart_prod_proj(cart_prod(X, kv), 2) = kv(2) = Q
cart_prod_proj(cart_prod(X, kv), 3) = kv(3) = Z
```

**Example 2: Infinite index set**:
```litex
# Use natural numbers as index set
have fn kv2(x N) set =:
    case x >= 2: N
    case x < 2: Q

# Create Cartesian product indexed by natural numbers
cart_prod(N, kv2) $in set
index_set_of_cart_prod(cart_prod(N, kv2)) = N
cart_prod_proj(cart_prod(N, kv2), 1) = kv2(1) = Q
cart_prod_proj(cart_prod(N, kv2), 2) = kv2(2) = N
cart_prod_proj(cart_prod(N, kv2), 3) = kv2(3) = N
```

**Explanation**:
- `cart_prod(X, kv)` creates a Cartesian product where `X` is the index set and `kv` is a function from `X` to sets
- `index_set_of_cart_prod(cart_prod(X, kv))` returns the index set `X`
- `cart_prod_proj(cart_prod(X, kv), i)` returns the projection to the $i$-th component, which equals `kv(i)`

**When to use which**:
- Use `cart` when you have a fixed, small number of sets (e.g., `cart(R, Q, Z)`)
- Use `cart_prod` when you need to define a product over an arbitrary index set, especially when the index set might be large or infinite

## Power Set

### Natural Language Definition

The **power set** of a set $A$, denoted $\mathcal{P}(A)$ or $2^A$, is the set of all subsets of $A$. In other words, every element of the power set is itself a set that is a subset of $A$. For example, if $A = \{1, 2\}$, then $\mathcal{P}(A) = \{\emptyset, \{1\}, \{2\}, \{1, 2\}\}$.

In symbols: For any set $A$, the power set $\mathcal{P}(A)$ satisfies: $y \in \mathcal{P}(A) \iff y \subseteq A$.

### Built-in Power Set in Litex

Litex provides a built-in `power_set` function:

```litex
# Every element of power_set(R) is a subset of R
forall y power_set(R):
    y $is_subset_of R
```

**Keywords**: `power_set`, `$is_subset_of`

**Example**:
```litex
# The power set of R contains all subsets of R
have y power_set(R)
y $is_subset_of R

# The empty set is in the power set of any set
empty_set $is_subset_of R # empty_set is a builtin set. it is defined by `have set empty_set = {}`
empty_set $in power_set(R)
```

### Self-Defined Power Set

You can also define your own power set function using Litex's set definition capabilities:

```litex
# Define power set as a function from sets to sets
fn self_defined_power_set(A set) set:
    forall y self_defined_power_set(A):
        y $in set
        y $is_subset_of A
    forall y set:
        y $is_subset_of A
        =>:
            y $in self_defined_power_set(A)
```

**Explanation**:
- `self_defined_power_set(A)` is a function that takes a set `A` and returns a set
- The first `forall` states that every element of `self_defined_power_set(A)` is a subset of `A`
- The second `forall` states that every subset of `A` is an element of `self_defined_power_set(A)`
- Together, these define the power set: it contains exactly all subsets of `A`

**Keywords**: `fn`, `set`, `$is_subset_of`, `$in`, `forall`, `=>`

### Examples

**Example 1: Power set of a finite set**
```litex
# Define a finite set
have set A = {1, 2, 3}

# Use built-in power_set
have y power_set(A)
y $is_subset_of A

# All subsets of A are in power_set(A)
have set empty = {}
empty $is_subset_of A
empty $in power_set(A)

have set singleton1 = {1}
singleton1 $is_subset_of A
singleton1 $in power_set(A)

have set pair12 = {1, 2}
pair12 $is_subset_of A
pair12 $in power_set(A)

# A itself is in its power set
A $is_subset_of A
A $in power_set(A)
```

**Example 2: Using self-defined power set**
```litex
# Define a set
have set B = {5, 10}

# Use self-defined power set
fn self_defined_power_set(A set) set:
    forall y self_defined_power_set(A):
        y $is_subset_of A
    forall y set:
        y $is_subset_of A
        =>:
            y $in self_defined_power_set(A)

# Check that subsets are in the power set
have set subset1 = {5}
subset1 $is_subset_of B
subset1 $in self_defined_power_set(B)

# The set itself is in its power set
B $is_subset_of B
B $in self_defined_power_set(B)
```

**Example 3: Power set properties**
```litex
# The empty set is always in the power set
have set empty = {}
have A set

empty $is_subset_of A
empty $in power_set(A)

# The set itself is always in its power set
A $is_subset_of A
A $in power_set(A)

# If B is a subset of A, then power_set(B) is a subset of power_set(A)
have B set
B $is_subset_of A
=>:
    forall y power_set(B):
        y $is_subset_of B
        y $is_subset_of A
        y $in power_set(A)
    forall y power_set(B) => y $in power_set(A)
    power_set(B) $is_subset_of power_set(A)
```

**Example 4: Power set of natural numbers**
```litex
# Power set of N contains all subsets of natural numbers
have y power_set(N)
y $is_subset_of N

# Examples of subsets in power_set(N)
have set even_numbers = {n N: exist k N => n = 2 * k}
even_numbers $is_subset_of N
even_numbers $in power_set(N)

have set positive_numbers = N_pos
N_pos $is_subset_of N
N_pos $in power_set(N)
```

---

## Summary: All Ways to Construct Sets from Sets in ZFC

In ZFC set theory, there are **6 fundamental axioms** for constructing new sets from given sets, plus **Cartesian products** which are constructed from these axioms. All mathematical objects (functions, sequences, trees, graphs, topological spaces, real numbers, etc.) are ultimately constructed through combinations of these operations. The following table shows how each construction method works in Litex:

| ZFC Axiom | What It Constructs | Litex Implementation | Example |
|-----------|---------------------|---------------------|---------|
| **Separation (Specification)** | Subsets of A satisfying property P | `have set s = {x A: $P(x)}` | ```litex<br>prop P(x A)<br>have set s = {x A: $P(x)}<br>``` |
| **Power Set** | Set of all subsets of A | `power_set(A)` or `fn self_defined_power_set(A set) set` | ```litex<br>have y power_set(R)<br>y $is_subset_of R<br>``` |
| **Pairing** | Set containing exactly two objects | `have set s = {a, b}` | ```litex<br>have a, b obj<br>have set pair = {a, b}<br>``` |
| **Union** | Set containing all elements from sets in A | `union(A, B)` or `union_of_family(F)` | ```litex<br>have a, b set<br>forall x a => x $in union(a, b)<br>forall x b => x $in union(a, b)<br>``` |
| **Replacement** | Image of A under function F | Function application + `know` (if needed) | ```litex<br>have X, Y set<br>have fn f(x X) Y<br># f[A] = {f(x): x in A}<br>have set image = {y Y: exist x A => y = f(x)}<br>``` |
| **Cartesian Product** | Set of ordered n-tuples from sets X₁, X₂, ..., Xₙ | `cart(X1, X2, ..., Xn)` or `cart_prod(index_set, kv)` | ```litex<br>have set x = cart(R, Q, Z)<br>let a x<br>coord(a, x, 1) $in R<br>``` |

### Key Points:

1. **Separation** is implemented directly through Litex's intensional set syntax `{x parent_set: condition}`. This is the most commonly used construction method.

2. **Power Set** can use the built-in `power_set(A)` or be defined as a function:
   ```litex
   fn self_defined_power_set(A set) set:
       forall y self_defined_power_set(A):
           y $in set
           y $is_subset_of A
       forall y set:
           y $is_subset_of A
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

---