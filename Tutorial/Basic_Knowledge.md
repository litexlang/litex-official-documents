# Basic Knowledge: Everyday Math, the Litex Way

_Common Sense Is Not So Common_

_— Voltaire_

## Numbers

Numbers like `0`, `3.14159`, `-1` are recognized directly in Litex.
You can use them without any special declaration. Litex has built-in support for numeric literals, basic arithmetic, and comparisons. For example:

```litex
1 + 1 = 2
0 * 4 + (9 - 3) * (2 - 1) = 6
2 != 3 # inequality, equivalent to `not 2 = 3`
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

Litex has these common facts built in, since it can verify them automatically through simple polynomial expansion and combination.

```litex
forall a, b, c R => (a + b) * c = a * c + b * c
forall a, b, c R => (a - b) * c = a * c - b * c
forall a, b, c R => a * (b - c) = a * b - a * c
forall a, b, c R => a * (b + c) = a * b + a * c
forall a, b, c, d R => (a + b) * (c + d) = a * c + a * d + b * c + b * d
forall a, b, c, d R => (a - b) * (c - d) = a * c - a * d - b * c + b * d
forall a, b, c, d R => (a - b) * (c + d) = a * c + a * d - b * c - b * d
forall a, b, c, d R => (a + b) * (c - d) = a * c + b * c - a * d - b * d
forall a, b, c R => (a + b) + c = a + (b + c)
forall a, b, c R => (a - b) - c = a - (b + c)
forall a, b, c R => (a * b) * c = a * (b * c)
forall a, b R => a * b = b * a, a + b = b + a
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

## Symbol

Everything is a symbol in Litex. A symbol can equal to other symbols. When two symbols are equal, they are interchangeable and they share all properties.

## Value

We left-hand-side or right-hand-side of a equal statement is a numerical symbol, Litex remembers it as the value of the symbol on the other side, for example:

```litex
let a, b R: a = 1, 2 = b
```

In this case, `1` is the value of `a` and `2` is value of `b`.

When the Litex kernel is verifying statements about a given symbol, it first replaces the symbol with its value and verify (if its value is known). If the verification works, the verification process is done. If it does not work, we use the symbol as it is to do verification.

This can be extremely useful in the following ways:

1. We know `x = 1` we want to prove `x > 0`. Since `1 > 0` and the verification process replaces `x > 0` with `1 > 0`, everything is done immediately. You do not need to write `1 > 0, x > 0` and use match-and-substitution to do so.

## Comment

Litex support to add one-line Comment by symbol `# ` and multi-line Comment by symbol `"` (If you write one `"`, it can be translated to markdown style comment in display; If you write two `"`, it can be translated to LaTeX style comment in display, others to LaTeX style comment in display):

```litex
# claim an Object x in R and make x > 1
let x R:
    x > 1
```

```litex
"""
some comment
some comment
some comment
"""

"
Multi-line comment start with ", or any number of " except two can be translated to markdown style comment in display.
"

""
Multi-line comment start with "" can be translated to LaTeX style comment in display; 
""
```

Comments are very helpful for you to understand the code and for the system to check your code.

## Wrap-Up

Looks simple, doesn’t it? Litex is designed to be **concise, readable, and close to everyday math**.

At first, you might still make mistakes when writing your own proofs — and that’s perfectly fine. In this short tutorial, we’ll guide you through everything you need to know about Litex, so you can confidently express and verify mathematics the Litex way.