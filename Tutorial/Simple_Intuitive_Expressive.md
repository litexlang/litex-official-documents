# Introduction: Begin the journey with Litex

_Design is not just what it looks like and feels like. Design is how it works._

_— Steve Jobs_

The experience of writing Litex feels like magic. Since a 10-year-old can reason about basic math, even a 10-year-old should be able to learn and use Litex easily to solve their own problems. Whether it’s a human or an AI, learning Litex is very easy, because Litex’s syntax is extremely close to natural language. The three key features of Litex are: **intuitive, simple, and expressive**.

## Intuitive

Litex support all common expression in math like numbers, variables, functions, etc. 

Here is an example: to determine the correctness of solution of multivariate linear equation: 2x + 3y = 10, 4x + 5y = 14:

```litex
let x R, y R:
    2 * x + 3 * y = 10
    4 * x + 5 * y = 14
2 * (2 * x + 3 * y) = 2 * 10
4* x + 6 * y = 2 * 10
(4*x + 6 * y) - (4*x + 5 * y) = 2 * 10 - 14
(4*x + 6 * y) - (4*x + 5 * y) = y
y  = 6
2 * x + 3 * 6 = 10
2 * x + 18 - 18 = 10 - 18
2 * x + 18 - 18 = -8
(2 * x) / 2 = -8 / 2
(2 * x) / 2 = x
x = -4
```

Anyone can understand the above code. There is almost zero difference between how we write math and how we write Litex. However, traditional formal languages like Lean requires you to learn a lot of complicated syntax and concepts.

## Simple

The difficulty of writing mathematics in a formal language is usually about equal to the difficulty of the mathematics itself plus the difficulty of expressing that mathematics in the formal language. Litex’s goal is to reduce the latter to as close to zero as possible, allowing users to focus on the mathematics itself rather than on the language they are using.

Here is an example: to prove sqrt(2) is irrational:

```litex
# prove sqrt(2) is irrational
# 证明 sqrt(2) 是无理数

fn logBase(x, y N) N:
    dom:
        x != 0

know forall x, y, z N => logBase(z, x^y) = y * logBase(z, x), logBase(z, x*y) = logBase(z, x) + logBase(z, y)

know forall x N: x != 0 => logBase(x, x) = 1

claim:
    not sqrt(2) $in Q
    prove_by_contradiction:
        sqrt(2) > 0
        have x, y st $rational_positive_number_representation_in_fraction(sqrt(2))
        
        x = sqrt(2) * y
        x ^ 2 = (sqrt(2) ^ 2) * (y ^ 2)
        sqrt(2) ^ 2 = 2
        x ^ 2 = 2 * (y ^ 2)

        logBase(2, x ^ 2) = logBase(2, 2 * (y ^ 2))     
        logBase(2, x ^ 2) = 2 * logBase(2, x)
        logBase(2, y ^ 2) = 2 * logBase(2, y)

        logBase(2, 2 * (y ^ 2)) = logBase(2, 2) + logBase(2, y ^ 2)
        logBase(2, 2) = 1
        logBase(2, 2 * (y ^ 2)) = 1 + logBase(2, y ^ 2)

        logBase(2, x ^ 2) = 1 + 2 * logBase(2, y)
        2 * logBase(2, x) = 1 + 2 * logBase(2, y)

        =:
            0
            (2 * logBase(2, x)) % 2            
            (1 + 2 * logBase(2, y)) % 2
            
        =:
            (1 % 2 + (2 * logBase(2, y)) % 2) % 2
            (1 + 2 * logBase(2, y)) % 2
            (1 % 2 + (2 * logBase(2, y)) % 2) % 2
            (1 + 0) % 2
            1
        0 = 1
```

Litex code is pretty straightforward. Try to read the above code yourself. It is not hard. Below is the same example in Lean.

## Expressive

Mathematics studies abstraction. It is about finding the most general and abstract patterns in the world. Litex is very good at expressing such patterns. Here is an example: to define a group, and prove R and Z are groups.

```litex
prop is_group(s set, mul fn(s, s)s, inv fn(s)s, e s):
    forall x s, y s, z s:
        mul(mul(x, y), z) = mul(x, mul(y, z))
    forall x s:
        mul(x, inv(x)) = e
        mul(inv(x), x) = e

fn inverse(x R)R:
    inverse(x) + x = 0

forall x R:
    inverse(x) + x = 0
    x + inverse(x) = 0

forall x Z:
    x + inverse(x) = 0
    inverse(x) = -x
    -x $in Z
    inverse(x) $in Z

$is_group(R, +, inverse, 0)
$is_group(Z, +, inverse, 0)
```

## How to read this tutorial

The biggest strength of Litex is its intuitiveness. In the ideal case, we hope users can read and use Litex without having to learn it at all! 

Please don’t feel any pressure when reading this tutorial — Litex is truly very simple. Code in this tutorial can be run in your browser! Run it to have the first taste of Litex!

It’s perfectly fine if you don’t remember everything the first time. When you encounter a specific problem, coming back to review the relevant section of this tutorial is just as effective.

The purpose of this slim tutorial is:

1. To record the most basic Litex syntax and keywords, ensuring there is no ambiguity for users.
2. To provide some examples for beginners to reference.

Don't forget to run the examples yourself! You can learn much much faster if you read and write the examples yourself!

The best way to learn Litex is to try writing the examples from the tutorial yourself, or translate the mathematics (or reasoning) you care about into Litex.
