# Equal: Why `=` Rules Mathematics

_Equal: regarding or affecting all objects in the same way._

_— Merriam-Webster Dictionary_

`=` is the most important proposition in math. It is used to build equal relation between two objects. In other words, when `x = y`, there is no difference between `x` and `y` any more. For example:

```litex
let x N, y N:
    x = y
    x > 0

y > 0
```

Last statement `y > 0` is true, because `x = y` and `x > 0` are true. As you can see, once two objects are equal, they can be used interchangeably in any context.

You can think of `a = b` as `a` is an alias of `b`, or `b` is an alias of `a`.

Since `=` is so important, it has the most abundant built-in support for it. We will introduce them one by one.

## Literally the same

The most fundamental and basic way to verify if two objects are equal is to check if they are literally the same object. For example:

```litex
have x N
x = x
x + 2 = x + 2
```

Ultimately, the way to establish equality between the left and right sides of `=` is that they are exactly the same as strings (the only exception is when comparing numeric literals).

## Use known transitivity of equality to prove equality

The most basic property of equality is that it is transitive. For example:

```litex
let a, b, c R:
    a = b
    b = c

a = c
```

How is `a = c` verified using transitivity of equality? When `a = b` is known to be true, the Litex kernel means a dictionary that maps both `a` and `b` to a shared set {a, b}. Then `b = c` is known, we put `c` into the set and map `a`, `b`, `c` to {a, b, c}. Now we know `a` and `c` are in the same set, so `a = c` is true. That is how transitivity of equality is used to prove equality.

Here is a more complicated example:

```litex
let a, b, c, d, e R:
    (a + 2) * d * e = a
    a = c

(a + 2) * d * e = c
```

How is `(a + 2) * d * e = c` verified using transitivity of equality? When `(a + 2) * d * e = a` is known to be true, the Litex kernel means a dictionary that maps both `(a + 2) * d * e` and `a` to a shared set {(a + 2) * d * e, a}. Then `a = c` is known, we put `c` into the set and map `a`, `c`, `(a + 2) * d * e` to {a, c, (a + 2) * d * e}. Now we know `(a + 2) * d * e` and `c` are in the same set, so `(a + 2) * d * e = c` is true. Notice besides single-word symbol like `a`, objects like `(a + 2) * d * e` are also called a symbol, a symbol composed by multiple words (in Litex, a multiple-word symbol is often in the shape of functionName(parameter1, parameter2, ...)). 

## Two Return Values of Function

It's very often that the included symbols are not literally the same, for example:

```litex
let a, b, c R:
    (a * 2) + b = c
fn f(a, b R) R
f(a, c) = f(a, (a * 2) + b)
```

There is no known factual statement that says `f(a, c) = f(a, (a * 2) + b)` and there is nothing to transitive, why does it still work?

It turns out that Litex checks the equality of two symbols inductively. Now, left-hand-side is the return value of a function (in this case, left-hand-side is return value of function `f` with parameters `a` and `c`: f(a, c)) and the right-hand-side is also the return value of a function (in this case, right-hand-side is return value of function `f` with parameters `a` and `(a * 2) + b`). Now, the Litex kernel checks whether the two functions are equal (in this case, `f` = `f`), if two functions are equal, then checks their first parameter is equal or not, (in this case, `a` = `a`), then checks their second parameter is equal or not (in this case `c` = `(a * 2) + b`, it is true because it is known to be true).

The above example is very representative, since in most cases, literal equality does not work. When we are dealing with symbols, we often deal with functions, and in many cases we want to replace some parameters of that with equal parameters. This functionality is essential for such cases.

Here is a more complicated example, with literally different function name, parameters, but all these literally different things are equal

```litex
let a, b, c, d R:
    a = 2
    b = c * a
    c + a = (b + 10) * d

fn f(a, b, c R) R
fn g(a, b, c R) R
know f = g

f(a, b, c + a) = g(2, c * a, (b + 10) * d)
```

If you run the above code, you might receive message like this:

```
f = g
is true. proved by
known fact:
f = g
a = 2
is true. proved by
known fact:
a = 2
b = (c * a)
is true. proved by
known fact:
b = (c * a)
(c + a) = ((b + 10) * d)
is true. proved by
known fact:
(c + a) = ((b + 10) * d)
---
Success! :)
```

The above message means that `f = g` is true, because `f = g` is known to be true, and `a = 2` is true, because `a = 2` is known to be true, and `b = (c * a)` is true, because `b = (c * a)` is known to be true, and `(c + a) = ((b + 10) * d)` is true, because `(c + a) = ((b + 10) * d)` is known to be true. Since function names are equal `f = g`, parameters are the same `a = 2`, `b = c * a`, `c + a = (b + 10) * d`. Therefore, `f(a, b, c + a) = g(2, c * a, (b + 10) * d)` is true.

## Numerical Equality

When the left-hand-side and right-hand-side of `=` are both numbers, Litex will use the built-in functionality to verify if they are equal. For example:

```litex
1 + 1 = 2
4 / 2 = 2
3 * (2 + 5) = 9 + 12
(3 + 4) / (2 + 5) = 7 / 7
```

## Polynomial Expansion and Combination

When the left-hand-side and right-hand-side of `=` are both symbols and the related functions are basic numerical functions like `+`, `-`, `*`, `/`, `^`, Litex will use the built-in functionality to verify if they are equal. 

Litex has built-in polynomial simplification / expansion / factorization, which allows users to manipulate symbolic polynomials directly without manually expanding or combining like terms. This is extremely convenient for many mathematical tasks, including Algebraic reasoning, Solving equations, Cancellation / reduction, Expression simplification / constant folding, Constructing or verifying complex formulas, etc.

For example:

```litex
let x, y R: y != 0
(x + 2 * y) * y = x * y + y * y * (3 - 1)
(10 * x + 20 * y) / 10 = x + 2 * y
x ^ 2 = x * x
(x ^ 2 * y + y ^ 2) / y = x ^ 2 + y
```

## Multi Equation

It's very common to write multiple equations in a single line. For example:

```litex
let x, y R: x = -4, y = 6
2 * x + 3 * y =  2 * -4 + 3 * 6 = 10
4 * x + 5 * y = 4 * -4 + 5 * 6 = 14
```

Litex provides `=:` to express a multiline equation:

```litex
let x, y R:
    x = -4
    y = 6
=:
    2 * x + 3 * y
    2 * -4 + 3 * 6
    10
=:
    4 * x + 5 * y
    4 * -4 + 5 * 6
    14
```

`=:` and `.. = .. = .. = ..` are the syntax sugar for `=`. The following two pieces of code are equivalent:

```litex
let veryLongSymbol, veryLongSymbol2, veryLongSymbol3, veryLongSymbol4, veryLongSymbol5, veryLongSymbol6 R:
    veryLongSymbol = veryLongSymbol2
    veryLongSymbol2 = veryLongSymbol3
    veryLongSymbol3 = veryLongSymbol4
    veryLongSymbol4 = veryLongSymbol5
    veryLongSymbol5 = veryLongSymbol6
```

```litex
let veryLongSymbol, veryLongSymbol2, veryLongSymbol3, veryLongSymbol4, veryLongSymbol5, veryLongSymbol6 R:
    =:
        veryLongSymbol
        veryLongSymbol2
        veryLongSymbol3
        veryLongSymbol4
        veryLongSymbol5
        veryLongSymbol6
```

```litex
let veryLongSymbol, veryLongSymbol2, veryLongSymbol3, veryLongSymbol4, veryLongSymbol5, veryLongSymbol6 R: veryLongSymbol = veryLongSymbol2 = veryLongSymbol3 = veryLongSymbol4 = veryLongSymbol5 = veryLongSymbol6 
```

As you can see, `=:` and `.. = .. = .. = ..` saves you from writing a lot of `=` statements. This is especially useful when you are writing a long equation and using transitivity of equality to prove equality.