# Cartesian Product (卡氏积)

The Cartesian product is one of the fundamental concepts in set theory, allowing us to construct new sets from existing ones by forming ordered tuples. In mathematics, the Cartesian product of sets $X$ and $Y$, denoted $X \times Y$, is the set of all ordered pairs $(x, y)$ where $x \in X$ and $y \in Y$.

More generally, for $n$ sets $X_1, X_2, \ldots, X_n$, their Cartesian product $X_1 \times X_2 \times \cdots \times X_n$ (also denoted $\prod_{i=1}^n X_i$) is the set of all ordered $n$-tuples $(x_1, x_2, \ldots, x_n)$ where $x_i \in X_i$ for each $i = 1, 2, \ldots, n$.

## Mathematical Definition

**Definition (Cartesian product).** If $X$ and $Y$ are sets, then we define the Cartesian product $X \times Y$ to be the collection of ordered pairs, whose first component lies in $X$ and second component lies in $Y$:

$$X \times Y := \{(x,y) : x \in X, y \in Y\}$$

Equivalently, $a \in (X \times Y) \iff (\exists x \in X, \exists y \in Y, a = (x,y))$.

**Definition (Ordered $n$-tuple and $n$-fold Cartesian product).** For $n$ sets $X_1, X_2, \ldots, X_n$, their Cartesian product is defined as:

$$\prod_{i=1}^n X_i := \{(x_1, x_2, \ldots, x_n) : x_i \in X_i \text{ for all } 1 \leq i \leq n\}$$

## Cartesian Product in Litex

In Litex, the Cartesian product is created using the `cart()` function. This function takes multiple sets as arguments and returns their Cartesian product. Litex provides several built-in functions and predicates to work with Cartesian products:

- `cart(X1, X2, ..., Xn)`: Creates the Cartesian product of sets $X_1, X_2, \ldots, X_n$
- `$is_cart(x)`: A predicate that checks whether `x` is a Cartesian product
- `dim(x)`: Returns the dimension (number of components) of a Cartesian product
- `proj(x, i)`: Returns the $i$-th projection (the $i$-th component set) of a Cartesian product
- `coord(a, x, i)`: Returns the $i$-th coordinate of element `a` in Cartesian product `x`

## Examples

### Example 1: Three-Dimensional Cartesian Product

Let's start with a three-dimensional Cartesian product:

```litex
have set x = cart(R, Q, Z)
$is_cart(x)
dim(x) = 3
proj(x, 1) = R
proj(x, 2) = Q
proj(x, 3) = Z
x $in set

let a x
coord(a, x, 1) $in R
```

**Explanation:**

1. **`have set x = cart(R, Q, Z)`**: This creates a Cartesian product of three sets: the real numbers $\mathbb{R}$, the rational numbers $\mathbb{Q}$, and the integers $\mathbb{Z}$. The result is stored in `x`, which represents the set $\mathbb{R} \times \mathbb{Q} \times \mathbb{Z}$.

2. **`$is_cart(x)`**: This verifies that `x` is indeed a Cartesian product. Litex can automatically verify this fact.

3. **`dim(x) = 3`**: The dimension of `x` is 3, meaning it is a product of three sets. This corresponds to the number of arguments passed to `cart()`.

4. **`proj(x, 1) = R`**: The first projection of `x` is $\mathbb{R}$. In general, `proj(x, i)` returns the $i$-th component set of the Cartesian product.

5. **`proj(x, 2) = Q`**: The second projection is $\mathbb{Q}$.

6. **`proj(x, 3) = Z`**: The third projection is $\mathbb{Z}$.

7. **`x $in set`**: This confirms that the Cartesian product `x` itself is a set, as expected in set theory.

8. **`let a x`**: This declares an element `a` that belongs to the Cartesian product `x`. Since `x = cart(R, Q, Z)`, the element `a` is an ordered triple $(a_1, a_2, a_3)$ where $a_1 \in \mathbb{R}$, $a_2 \in \mathbb{Q}$, and $a_3 \in \mathbb{Z}$.

9. **`coord(a, x, 1) $in R`**: The first coordinate of `a` (i.e., $a_1$) belongs to $\mathbb{R}$. The `coord(a, x, i)` function extracts the $i$-th component of the ordered tuple `a` in the Cartesian product `x`.

### Example 2: Two-Dimensional Cartesian Product

Litex can now compute non-numeric values, such as the dimension of a Cartesian product:

```litex
# litex现在可以计算出来非数字的值了，比如dim(cart(R, Q)) = 2
$is_cart(cart(R, Q))
let y cart(R, Q)
dim(cart(R, Q)) = 2
coord(y, cart(R, Q), 1) $in R
```

**Explanation:**

1. **`$is_cart(cart(R, Q))`**: This verifies that `cart(R, Q)` is a Cartesian product. Note that we can use `cart(R, Q)` directly without assigning it to a variable first.

2. **`let y cart(R, Q)`**: This declares an element `y` in the Cartesian product $\mathbb{R} \times \mathbb{Q}$. The element `y` is an ordered pair $(y_1, y_2)$ where $y_1 \in \mathbb{R}$ and $y_2 \in \mathbb{Q}$.

3. **`dim(cart(R, Q)) = 2`**: The dimension of `cart(R, Q)` is 2, since it is a product of two sets. Litex can compute this value directly.

4. **`coord(y, cart(R, Q), 1) $in R`**: The first coordinate of `y` belongs to $\mathbb{R}$. Similarly, we could check that `coord(y, cart(R, Q), 2) $in Q`.

## Key Concepts

### Dimension

The dimension of a Cartesian product is the number of sets being multiplied together. For example:
- `dim(cart(R, Q)) = 2` (two-dimensional)
- `dim(cart(R, Q, Z)) = 3` (three-dimensional)
- `dim(cart(X1, X2, ..., Xn)) = n` ($n$-dimensional)

### Projections

The projection `proj(x, i)` returns the $i$-th component set of the Cartesian product `x`. For `x = cart(X1, X2, ..., Xn)`:
- `proj(x, 1) = X1`
- `proj(x, 2) = X2`
- ...
- `proj(x, n) = Xn`

### Coordinates

For an element `a` in a Cartesian product `x = cart(X1, X2, ..., Xn)`, the coordinate `coord(a, x, i)` extracts the $i$-th component of `a`. The coordinate satisfies:
- `coord(a, x, i) $in proj(x, i)` for all valid indices $i$

## Applications

Cartesian products are fundamental in mathematics and have many applications:

1. **Coordinate Systems**: The Cartesian plane $\mathbb{R} \times \mathbb{R}$ is the foundation of analytic geometry.

2. **Relations**: A relation from set $X$ to set $Y$ is a subset of $X \times Y$.

3. **Functions**: A function $f: X \to Y$ can be viewed as a subset of $X \times Y$ with special properties.

4. **Product Spaces**: In topology and analysis, Cartesian products form product spaces.

5. **Multiple Variables**: When working with functions of multiple variables, the domain is often a Cartesian product.

## Summary

The Cartesian product in Litex provides a natural way to work with ordered tuples and multi-dimensional structures. The built-in functions `cart()`, `$is_cart()`, `dim()`, `proj()`, and `coord()` make it easy to construct and manipulate Cartesian products, aligning with standard mathematical notation and concepts.
