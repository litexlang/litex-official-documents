# Basic Knowledge: Everyday Math, the Litex Way

_Never forget where you came from._

_— Street Proverb_

## Numbers

Numbers like `0`, `3.14159`, `-1` are recognized directly in Litex.
You can use them without any special declaration. Litex has built-in support for numeric literals, basic arithmetic, and comparisons. For example:

```litex
1 + 1 = 2
0 * 4 + (9 - 3) * (2 - 1) = 6
2 != 3
3 > 0
1 + 2 + 3 + 4 + 5 + 6 + 7 + 8 + 9 + 10 = 55
```

* **Functional operators** like `+`, `-`, `*`, `/`, `%`, `^` are built-in.
* **Factual operators** like `=`, `!=`, `>`, `<`, `>=`, `<=` are also built-in.

## Symbolic Arithmetic

Polynomials appear everywhere in mathematics.
Unlike many formal languages, Litex has **native support for polynomials**, making them much easier to write and read.

For example:

```litex
have x R, y R, z R
(x + z * z) * (x + 7 * y) = x * x + 7 * y * x + z * x * z + y * (3 + 4) * z * z
```

## Basic Set

Since modern mathematics is built on set theory, Litex provides built-in support for many commonly used sets:

* `N`: natural numbers
* `N_pos`: positive natural numbers
* `Z`: integers
* `Q`: rational numbers
* `R`: real numbers
* `C`: complex numbers

Many fundamental facts about these sets are also built into Litex. For example:

```litex
17 $in N
-47 + 17 $in Z
17.17 $in Q
forall x Q => x $in R
```

Here:

* `17` is a natural number.
* `-47 + 17` is an integer.
* `17.17` is a rational number.
* Every rational number is also a real number.

## A Simple Example

Let’s see how to formalize and solve a system of multivariate equations step by step:

```litex
let x R, y R:
    2 * x + 3 * y = 10
    4 * x + 5 * y = 14

2 * (2 * x + 3 * y) = 2 * 10
4* x + 6 * y = 2 * 10
(4*x + 6 * y) - (4*x + 5 * y) = 2 * 10 - 14
(4*x + 6 * y) - (4*x + 5 * y) = y
y = 6
2 * x + 3 * 6 = 10
2 * x + 18 - 18 = 10 - 18
2 * x + 18 - 18 = -8
(2 * x) / 2 = -8 / 2
(2 * x) / 2 = x
x = -4
```

Step by step, we find:

$$
y = 6, \quad x = -4
$$

## Wrap-Up

Looks simple, doesn’t it? Litex is designed to be **concise, readable, and close to everyday math**.

At first, you might still make mistakes when writing your own proofs — and that’s perfectly fine. In this short tutorial, we’ll guide you through everything you need to know about Litex, so you can confidently express and verify mathematics the Litex way.