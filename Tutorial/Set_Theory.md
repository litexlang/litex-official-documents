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

