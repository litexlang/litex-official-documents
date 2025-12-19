# Equal: Why `=` Rules Mathematics

_Equal: regarding or affecting all objects in the same way._

_— Merriam-Webster Dictionary_

---

## Section 1: Understanding Equality

### Introduction

In this section, we'll explore the most important proposition in mathematics: equality (`=`). Equality is fundamental because it allows us to say that two objects are the same, and once two objects are equal, they can be used interchangeably. By the end of this section, you'll understand how equality works in Litex and why it's so powerful.

### From Natural Language to Litex

`=` is the most important proposition in math. It is used to build equal relation between two objects. In other words, when `x = y`, there is no difference between `x` and `y` any more.

**Natural Language**: "x equals y, and x is greater than zero, so y is greater than zero"  
**Litex**:
```litex
let x N, y N:
    x = y
    x > 0

y > 0
```

Last statement `y > 0` is true, because `x = y` and `x > 0` are true. As you can see, once two objects are equal, they can be used interchangeably in any context.

**You can think of `a = b` as `a` is an alias of `b`, or `b` is an alias of `a`.**

Since `=` is so important, it has the most abundant built-in support for it. We will introduce them one by one.

### Summary

- Equality (`=`) is the most important proposition in mathematics
- When two objects are equal, they are completely interchangeable
- Equal objects share all properties
- Litex has extensive built-in support for equality

### Litex Syntax Reference

**Equality**: `x = y` means "x equals y"

**Interchangeability**: If `x = y`, then any property of x is also a property of y

**Built-in support**: Litex has many built-in rules for verifying equality

### Exercises

1. If `a = b` and `a > 0`, what can you say about `b`?
2. Explain why equality is transitive (if `a = b` and `b = c`, then `a = c`).
3. Give an example where two equal objects are used interchangeably.

### Bonus: The Philosophy of Equality

Equality is more than just a symbol—it's a fundamental concept that allows us to reason about sameness. When we say two things are equal, we're saying they're the same in every relevant way. This is why equal objects are interchangeable: if they're truly the same, there's no reason to treat them differently.

---

## Section 2: How Litex Verifies Equality

### Introduction

In this section, we'll explore the different ways Litex verifies equality. Litex uses multiple strategies, from simple literal comparison to complex inductive checking. By the end of this section, you'll understand all the mechanisms Litex uses to determine if two objects are equal.

### From Natural Language to Litex

**Natural Language**: "x equals x" (always true)  
**Litex**: `x = x` → **Result**: Verified by literal equality

**Natural Language**: "If a equals b and b equals c, then a equals c"  
**Litex**: 
```litex
let a, b, c R:
    a = b
    b = c

a = c
```
→ **Result**: Verified by transitivity

### Literally the Same

The most fundamental and basic way to verify if two objects are equal is to check if they are literally the same object. For example:

```litex
have x N
x = x
x + 2 = x + 2
```

Ultimately, the way to establish equality between the left and right sides of `=` is that they are exactly the same as strings (the only exception is when comparing numeric literals).

### Use Known Transitivity of Equality

The most basic property of equality is that it is transitive. For example:

```litex
let a, b, c R:
    a = b
    b = c

a = c
```

**How is `a = c` verified using transitivity of equality?**

When `a = b` is known to be true, the Litex kernel maintains a dictionary that maps both `a` and `b` to a shared set {a, b}. Then when `b = c` is known, we put `c` into the set and map `a`, `b`, `c` to {a, b, c}. Now we know `a` and `c` are in the same set, so `a = c` is true. That is how transitivity of equality is used to prove equality.

Here is a more complicated example:

```litex
let a, b, c, d, e R:
    (a + 2) * d * e = a
    a = c

(a + 2) * d * e = c
```

**How is `(a + 2) * d * e = c` verified?**

When `(a + 2) * d * e = a` is known to be true, the Litex kernel maps both `(a + 2) * d * e` and `a` to a shared set. Then `a = c` is known, we put `c` into the set. Now we know `(a + 2) * d * e` and `c` are in the same set, so `(a + 2) * d * e = c` is true.

Notice: besides single-word symbols like `a`, objects like `(a + 2) * d * e` are also called symbols—symbols composed by multiple words (in Litex, a multiple-word symbol is often in the shape of `functionName(parameter1, parameter2, ...)`).

### Two Return Values of Function

It's very often that the included symbols are not literally the same, for example:

```litex
let a, b, c R:
    (a * 2) + b = c
fn f(a, b R) R
f(a, c) = f(a, (a * 2) + b)
```

There is no known factual statement that says `f(a, c) = f(a, (a * 2) + b)` and there is nothing to transitive, why does it still work?

**The Answer**: Litex checks the equality of two symbols inductively.

- Left-hand-side is the return value of function `f` with parameters `a` and `c`: `f(a, c)`
- Right-hand-side is the return value of function `f` with parameters `a` and `(a * 2) + b`: `f(a, (a * 2) + b)`

The Litex kernel checks:
1. Whether the two functions are equal (in this case, `f` = `f`) ✅
2. Whether their first parameter is equal (in this case, `a` = `a`) ✅
3. Whether their second parameter is equal (in this case `c` = `(a * 2) + b`, which is true because it is known) ✅

Since all checks pass, `f(a, c) = f(a, (a * 2) + b)` is verified.

The above example is very representative, since in most cases, literal equality does not work. When we are dealing with symbols, we often deal with functions, and in many cases we want to replace some parameters of that with equal parameters. This functionality is essential for such cases.

### Complex Example with Different Function Names

Here is a more complicated example, with literally different function names and parameters, but all these literally different things are equal:

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

If you run the above code, you might receive a message like this:

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

The above message means that:
- `f = g` is true (known fact)
- `a = 2` is true (known fact)
- `b = (c * a)` is true (known fact)
- `(c + a) = ((b + 10) * d)` is true (known fact)

Since function names are equal (`f = g`), and all corresponding parameters are equal, `f(a, b, c + a) = g(2, c * a, (b + 10) * d)` is true.

### Summary

- Litex verifies equality through multiple mechanisms:
  1. **Literal equality**: Symbols that are exactly the same
  2. **Transitivity**: If `a = b` and `b = c`, then `a = c`
  3. **Inductive checking**: For function calls, checks function equality and parameter equality
- The kernel maintains equivalence sets to track equal objects
- Complex expressions can be verified by checking their components

### Litex Syntax Reference

**Literal equality**: `x = x` (always true for any x)

**Transitive equality**: If `a = b` and `b = c`, then `a = c` automatically

**Function equality**: `f(params1) = g(params2)` is verified by checking `f = g` and `params1 = params2` component-wise

**Equivalence sets**: Litex maintains sets of equal objects internally

### Exercises

1. Explain how Litex verifies `f(x, y) = f(a, b)` when `x = a` and `y = b`.
2. Given `a = b`, `b = c`, and `c = d`, how does Litex verify `a = d`?
3. Why does literal equality work for `x = x` but not for `f(1) = f(1)` when f is a function?

### Bonus: The Elegance of Inductive Checking

The inductive checking mechanism for function equality is elegant because it mirrors how we think about equality in mathematics. If two functions are the same and we apply them to the same arguments, we get the same result. Litex makes this explicit by checking each component, making the verification process transparent and understandable.

---

## Section 3: Numerical and Polynomial Equality

### Introduction

In this section, we'll explore how Litex handles equality for numbers and polynomials. Litex has built-in support for numerical computation and polynomial manipulation, making it easy to verify equalities involving arithmetic expressions.

### From Natural Language to Litex

**Natural Language**: "One plus one equals two"  
**Litex**: `1 + 1 = 2` → **Result**: Verified by numerical computation

**Natural Language**: "For any real numbers x and y, (x + y)² equals x² + 2xy + y²"  
**Litex**: 
```litex
let x, y R
(x + y) * (x + y) = x * x + 2 * x * y + y * y
```
→ **Result**: Verified by polynomial expansion

### Numerical Equality

When the left-hand-side and right-hand-side of `=` are both numbers, Litex will use the built-in functionality to verify if they are equal. For example:

```litex
1 + 1 = 2
4 / 2 = 2
3 * (2 + 5) = 9 + 12
(3 + 4) / (2 + 5) = 7 / 7
```

All of these are automatically verified by Litex's numerical computation engine.

### Polynomial Expansion and Combination

When the left-hand-side and right-hand-side of `=` are both symbols and the related functions are basic numerical functions like `+`, `-`, `*`, `/`, `^`, Litex will use the built-in functionality to verify if they are equal.

Litex has built-in polynomial simplification / expansion / factorization, which allows users to manipulate symbolic polynomials directly without manually expanding or combining like terms. This is extremely convenient for many mathematical tasks, including:
- Algebraic reasoning
- Solving equations
- Cancellation / reduction
- Expression simplification / constant folding
- Constructing or verifying complex formulas

**Example:**

```litex
let x, y R: y != 0
(x + 2 * y) * y = x * y + y * y * (3 - 1)
(10 * x + 20 * y) / 10 = x + 2 * y
x ^ 2 = x * x
(x ^ 2 * y + y ^ 2) / y = x ^ 2 + y
```

All of these are automatically verified through polynomial manipulation.

### Summary

- Litex has built-in numerical computation for verifying number equalities
- Polynomial expansion, simplification, and factorization are built-in
- This makes algebraic reasoning much easier
- No need to manually expand or simplify expressions

### Litex Syntax Reference

**Numerical equality**: `1 + 1 = 2` - automatically computed

**Polynomial equality**: `(x + y)^2 = x^2 + 2xy + y^2` - automatically expanded

**Built-in operations**: `+`, `-`, `*`, `/`, `^` are supported for polynomial manipulation

### Exercises

1. Verify that `(x + 1)^2 = x^2 + 2x + 1` for any real number x.
2. Simplify and verify: `(2x + 4y) / 2 = x + 2y`.
3. Explain how Litex's polynomial manipulation helps with algebraic reasoning.

### Bonus: The Power of Built-in Polynomial Support

Most formal languages require you to manually expand and simplify polynomials, which is tedious and error-prone. Litex's built-in polynomial support means you can write mathematics naturally, just as you would on paper, and Litex will handle the algebraic manipulation automatically. This is one of the features that makes Litex so intuitive and easy to use.

---

## Section 4: Multi-Equation Syntax

### Introduction

In this section, we'll explore Litex's syntax for writing multiple equations and long chains of equalities. This makes it easier to express step-by-step calculations and proofs.

### From Natural Language to Litex

**Natural Language**: "x equals -4, y equals 6, so 2x + 3y equals 10"  
**Litex**: 
```litex
let x, y R: x = -4, y = 6
2 * x + 3 * y = 2 * -4 + 3 * 6 = 10
```

### Writing Multiple Equations

It's very common to write multiple equations in a single line. For example:

```litex
let x, y R: x = -4, y = 6
2 * x + 3 * y =  2 * -4 + 3 * 6 = 10
4 * x + 5 * y = 4 * -4 + 5 * 6 = 14
```

### Multi-Line Equation Syntax

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

### Syntax Sugar

`=:` and `.. = .. = .. = ..` are syntax sugar for `=`. The following two pieces of code are equivalent:

**Version 1: Using multiple `=` statements**
```litex
let veryLongSymbol, veryLongSymbol2, veryLongSymbol3, veryLongSymbol4, veryLongSymbol5, veryLongSymbol6 R:
    veryLongSymbol = veryLongSymbol2
    veryLongSymbol2 = veryLongSymbol3
    veryLongSymbol3 = veryLongSymbol4
    veryLongSymbol4 = veryLongSymbol5
    veryLongSymbol5 = veryLongSymbol6
```

**Version 2: Using `=:` syntax**
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

**Version 3: Using chained `=`**
```litex
let veryLongSymbol, veryLongSymbol2, veryLongSymbol3, veryLongSymbol4, veryLongSymbol5, veryLongSymbol6 R: 
    veryLongSymbol = veryLongSymbol2 = veryLongSymbol3 = veryLongSymbol4 = veryLongSymbol5 = veryLongSymbol6 
```

As you can see, `=:` and `.. = .. = .. = ..` saves you from writing a lot of `=` statements. This is especially useful when you are writing a long equation and using transitivity of equality to prove equality.

### Summary

- Multiple equations can be written on one line using chained `=`
- `=:` syntax allows multi-line equation chains
- These are syntax sugar for multiple `=` statements
- Very useful for step-by-step calculations and proofs

### Litex Syntax Reference

**Chained equality**: `a = b = c = d` - equivalent to `a = b`, `b = c`, `c = d`

**Multi-line equality**: `=: a b c d` - equivalent to `a = b`, `b = c`, `c = d`

**Use case**: Step-by-step calculations, long proofs, showing intermediate steps

### Exercises

1. Rewrite the following using `=:` syntax:
```litex
let x R: x = 1
x = 1 + 0
1 + 0 = 1
```

2. Write a chain of equalities showing that `(x + 1)^2 = x^2 + 2x + 1`.

3. Explain when you would use `=:` instead of chained `=`.

### Bonus: Making Proofs Readable

The `=:` syntax and chained equality make proofs much more readable. Instead of writing many separate equality statements, you can show the entire chain of reasoning in a clear, linear fashion. This mirrors how mathematicians write proofs on paper, making Litex code more natural and easier to follow.
