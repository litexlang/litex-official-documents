# How Litex Automatically Derives Facts For You

_Before you speak, you are its master; after you speak, you are its slave._

_— Chinese Proverb_

---

## Introduction

Litex has invested tremendous effort—indeed, most of its effort—into improving user experience. This means that **if the kernel can mechanically help users automatically derive facts, it will automatically derive and save them for you**. At the same time, Litex incorporates many techniques to help users think about mathematics the way they naturally think about mathematics in everyday life. This document explains how Litex achieves this goal.

The core philosophy behind Litex's automatic derivation is simple: **mathematics should feel natural, not mechanical**. When you write mathematics on paper, you don't manually track every single equality relation or substitution—your mind automatically connects related facts. Litex does the same: it automatically maintains equivalence sets, performs substitutions, simplifies expressions, and derives new facts from known ones, all behind the scenes, so you can focus on the mathematics itself.

The fundamental working principle is: 1. Verify the factual statement 2. Save this factual statement 3. Automatically derive something from this factual statement (we call this post-processing after knowing a fact). When using `know` or `let`, the verification step (step 1) is skipped.

Although Litex has many, many built-in techniques provided by the kernel to make proofs more convenient, you don't need to remember them all. Essentially, you only need to remember: 1. When Litex encounters statements that are entirely numeric (and polynomial), it processes them the way humans do in everyday situations. 2. Litex's fundamental working principle is match and substitution—when verifying, it replaces all related symbols with equal symbols to verify. Even without relying on these techniques, we can prove all facts.

---

## Method 1: Post-Processing After Saving Specific Facts

If a fact matches certain characteristics after being saved, Litex can automatically derive additional facts from it.

Below are some statements and their corresponding automatic derivations:

### 1. Post-processing for `a = {1, 2, 3}` (e.g., `have set a = {1, 2, 3}`)

The following facts are automatically established:
1. `a $in set`
2. `forall x obj: x $in a <=> x = 1 or x = 2 or x = 3`

### 2. Post-processing for `x = cart(R, Q, Z)` (e.g., `have set x = cart(R, Q, Z)`)

The following facts are automatically established:
1. `$is_cart(x)`
2. `dim(x) = 3`
3. `proj(x, 1) = R`
4. `proj(x, 2) = Q`
5. `proj(x, 3) = Z`
6. `x $in set`

### 3. Defining `prop` Predicates

If you define a `prop` predicate, Litex automatically knows that the predicate is equivalent to its `iffFacts`.

```litex
prop p(x R):
    $q(x)
    <=>:
        $t(x)
```

After this definition, Litex automatically saves the following fact:

```litex
forall x R:
    $q(x)
    =>:
        $p(x)
    <=>:
        $t(x)
```

### 4. a = {x parent_set: fact1, fact2, ...}

即：a = {x parent_set: fact1, fact2, ...} 会自动生成 `a $in set`,`forall x parent_set: fact1, fact2, ... <=> x $in a`

举例：`have set a = {x R: x > 0}`
```litex
have set a = {x R: x > 0}
```

The following facts are automatically established:
1. `a $in set`
2. `forall x R: x > 0 <=> x $in a`

## Method 2: Special Verification Methods for Facts Matching Certain Conditions

If a fact matches certain conditions, Litex provides additional special verification methods.

### 1. Numeric Expression Computation

If both sides of an equality or inequality are entirely numeric expressions, Litex will compute them for you.

**Examples:**

```litex
1 + 1 = 2
4 * 2 - 10 = -2 + (7 - 7)
7^2 = 49
2 / 3 = 4 / 6
```

Addition, subtraction, and multiplication operations use string-based computation (not floating-point arithmetic), so theoretically, adding 100-digit numbers in Litex is feasible and can be quite fast.

If the exponent is a positive integer, Litex will compute it. If it's not an integer, it remains unchanged.

Division verification does not compute floating-point values. Instead, it uses the properties of division to transform the equation into an equality with only multiplication, addition, and exponentiation on both sides (`a / b = c / d` becomes `a * d = b * c`, where `b` and `d` cannot be 0). For example, `2 / 3 = 4 / 6` is first transformed into `2 * 6 = 3 * 4`, and then addition, subtraction, and multiplication are verified.

```litex
2 > 1
-3 * 8 <= 0
```

Inequality verification is similar to equality verification—it also uses string-based computation (not floating-point arithmetic) and then verifies.

### 2. Polynomial Reduction

If both sides are entirely polynomial expressions (addition, subtraction, multiplication, division, exponentiation), Litex reduces both sides.

#### 2.1 Without Division

```litex
(x + 1) * (x + 1) = x * x + 2 * x + 1
```

When Litex sees such expressions, it automatically simplifies them to their canonical form (addition expressions sorted in dictionary order, like `x * x + 2 * x + 1`), and then verifies the equality. If the canonical forms of both sides are the same, the equality is established.

#### 2.2 With Division

```litex
(x + 1) * (x + 1) / y = x * x + 2 * x + 1 / (y + 1 - 1)
```

First, it is transformed into a multiplication expression, then reduced. The above expression is equivalent to:

```litex
(x + 1) * (x + 1) * (y + 1 - 1) = (x * x + 2 * x + 1) * y
```

### 3. Symbol Value Substitution

If symbols on the left or right side have numeric values, Litex will help verify the equality.

**Examples:**

```litex
1 + 1 = 2
4 * 2 - 10 = -2 + (7 - 7)
7^2 = 49
2 / 3 = 4 / 6
```

### 4. Automatic Verification Using Symbol Values

If symbols on the left or right side have corresponding values, Litex will help verify the equality.

```litex
have a R = 1
a > 0
```

Since `1` is the value of `a`, `a > 0` is automatically established because `a = 1` is known. `a > 0` is replaced with `1 > 0`, and then `1 > 0` is verified to be true.