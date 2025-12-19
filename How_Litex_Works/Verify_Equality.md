# Equality: The Foundation of All Mathematics

version: 2025-12-01

_If it looks like a duck, swims like a duck, and quacks like a duck, then it probably is a duck._

_- Duck Test_

---

## The Fundamental Role of Equality

Equality (`=`) is the **most fundamental proposition** in mathematics. It is not merely one proposition among many; rather, **all other propositions depend on equality** for their definition and verification.

In mathematics and Litex, equality serves as the foundation because:

Equality makes symbols that are literally different have the same meaning. A symbol can be an atom (like `1`, `a`) or a function expression (like `1 + 2`, `f(x)`). When we say two symbols are equal, we mean they have completely identical meaning, even though they may look different.

**Example 1: Equality makes different literal symbols equivalent**

```litex
have a, b R
a = a # left-hand-side and right-hand-side of equality are the same.

# Numeric equality: 1 + 1 and 2 are different symbols, but equal
1 + 1 = 2

# Variable equality: 20 * x and y + z are different symbols, but equal
have x R
have y R = 3 * x
have z R = 17 * x
20 * x = 3 * x + 17 * x = y + z

# Function equality: f(a) and g(b) are different symbols, but equal
have fn f(a R) R = a
have fn g(a R) R = f(a)
have a2 R
have b2 R = a2
f(a2) = g(b2)
```

In all these cases, equality connects symbols that are literally different but semantically identical.

**Example 2: Other propositions depend on equality for verification**

```litex
# We know a > b is true
let a, b, c R:
    a > b
    a = c

# Because a = c, we can substitute c for a
# Therefore c > b is also true
c > b

prop p(a R)
know $p(a)
$p(c) # $p(c) is true because $p(a) is true and a = c
```

When `a = c` is known, `a` can be equivalently replaced with `c` in any proposition. This is why `c > b` is verified: Litex substitutes `c` for `a` in the known fact `a > b`. **In essence, equality means that different symbols (whether atoms like `1`, `a`, or function expressions like `1 + 2`, `f(x)`) have completely identical meaning.**

## How Litex Verifies Equality

When proving equality, Litex tries each step in order from the first to the last.

Litex's fundamental working logic is to iterate through a fixed set of verification strategies. As long as verification passes under any strategy, the fact is considered verified. If all strategies fail to verify, then the fact is considered unverified. Failure to verify does not necessarily mean the statement is incorrect; it only means that Litex has not found a method to prove the fact.

**Step 1: Check that all functions appearing on both sides of the equality have arguments in their domains**

For example, `+`, `-`, `*`, `/` in Litex can only take elements from `R` as parameters. If an element is not a real number, such as `R` itself, it cannot appear in arithmetic expressions.

```text
R + R # Error! What does it mean to add two sets of real numbers?
```

**Step 2: left-hand-side and right-hand-side are the same**

```litex
have a R
a = a
```

`a = a` is because left hand side and right hand side of equality are the same. This is the most fundamental way of proving equality.

**Step 3: Simplify numeric expressions**

## Symbol Values

If both sides of the equality are numeric expressions (such as `2`, `1.5`, `2/3`, but not `a`, `a + c`, `f(b)`), or symbols with numeric values, Litex simplifies and actually computes them.

**Note**: This is string matching, not floating-point arithmetic. When division doesn't result in an integer, the `/` is preserved. For example, `2/3 = 4/6` is not verified by computing the actual values, but by proving that `3 * 4 = 2 * 6`.

If verification passes at this step, then the fact is considered verified.

If verification fails at this step, Litex will continue to try the next step.

**Step 4: Search known facts**

Before searching known facts, we need to understand how Litex stores equality facts. The storage method for equality facts differs from other facts because equality has special properties such as transitivity and symmetry.

**Storage Mechanism**: Litex uses a hashmap to store equality relations. For each group of equal symbols, Litex creates an equivalence set and maps each symbol in the set to this set.

**Note**: The working principle of `equalityMap` described here is the same as in the Litex kernel, but the actual implementation details may differ because the kernel uses various optimization techniques. However, the fundamental working logic remains consistent.

**Example**: Suppose we know that symbols `a`, `1+b`, and `f(c)` are equal. Litex creates an equivalence set `{a, 1+b, f(c)}` and maps each symbol to this set:
- `equalityMap["a"] = {a, 1+b, f(c)}`
- `equalityMap["1+b"] = {a, 1+b, f(c)}`
- `equalityMap["f(c)"] = {a, 1+b, f(c)}`

Similarly, if symbols `h` and `8+t` are equal, they form another equivalence set:
- `equalityMap["h"] = {h, 8+t}`
- `equalityMap["8+t"] = {h, 8+t}`

**Merging Equivalence Sets**: When we prove a new equality relation that connects two different equivalence sets, Litex merges them. For example, if we prove `a = 8 + t`, then the set containing `a`, `{a, 1+b, f(c)}`, and the set containing `8+t`, `{h, 8+t}`, are merged into a new equivalence set `{a, 1+b, f(c), h, 8+t}`. All related symbols are then updated to point to this merged set:
- `equalityMap["a"] = {a, 1+b, f(c), h, 8+t}`
- `equalityMap["1+b"] = {a, 1+b, f(c), h, 8+t}`
- `equalityMap["f(c)"] = {a, 1+b, f(c), h, 8+t}`
- `equalityMap["h"] = {a, 1+b, f(c), h, 8+t}`
- `equalityMap["8+t"] = {a, 1+b, f(c), h, 8+t}`

In this way, by checking whether two symbols are in the same equivalence set, Litex can quickly determine if they are equal.

**How does this storage relate to proving symbol equality?**

For example, if we want to prove `1 + b = h`, we check whether `equalityMap["1+b"]` and `equalityMap["h"]` are in the same equivalence set. If they are, then `1 + b = h` is true. If we find they are indeed equal, then it's verified.

Another example: if we want to prove `2 - 1 + b = h`, we find that `2-1+b` hasn't appeared before in the entire project, so there's no key for it in `equalityMap`. However, `equalityMap` has a key `"h"`, so we iterate through all symbols in `"h"`'s list to see if any equals `2-1+b`. If we find a match, it's verified. For example, when iterating through `{a, 1+b, f(c), h, 8+t}`, we find that `2-1+b = 1+b`, so it's verified.

If verification passes at this step, then the fact is considered verified.

If verification fails at this step, Litex will continue to try the next step.

**Step 5: Function names and all function parameters are equal**

```litex
have fn f(a R) R = a
let g fn(R) R: g = f
have a R
have b R = a
f(a) = g(b)
```

How is `f(a) = g(b)` verified? There are no keys for `f(a)` and `g(b)` in `equalityMap` because they were just defined.

When both sides of the equality are function expressions rather than atoms, Litex recursively unwraps them, proving new equality facts. For example, here it proves `f = g`, then verifies that their parameters are equal, i.e., `a = b`.

Since `f(a)` and `g(b)` are both function expressions, not atoms, we need to recursively unwrap them. First, we verify that the function heads `f` and `g` are equal, then verify that their parameters `a` and `b` are equal. If they all match, it's verified.

If verification passes at this step, then the fact is considered verified.

If verification fails at this step, Litex will continue to try the next step.

**Step 6: Verify using known `or` facts**

When we have a known fact of the form `a = v1 or a = v2 or ... or a = vn`, we can use it to prove `a = vi` for some specific `vi` by eliminating all other possibilities.

**Example**: If we know `a = 1 or a = 2 or a = 3`, and we want to prove `a = 2`, Litex uses the following strategy:

1. First, check if `not a = 1` is true
2. Then, check if `not a = 3` is true
3. If both `not a = 1` and `not a = 3` are verified, then `a = 2` must be true

This is because if `a` can only be one of `1`, `2`, or `3`, and we've eliminated both `1` and `3` as possibilities, then `a` must equal `2`.

```litex
let a R:
    a = 1 or a = 2 or a = 3
    not a = 1
    not a = 3
a = 2  # Verified by eliminating other possibilities
```

**Internal Storage**: Litex internally maintains a `knownOrFactsMap` to store known `or` facts. For example, `knownOrFactsMap["="]` contains `{..., a = 1 or a = 2 or a = 3, ...}`. When we want to prove `a = 2`, Litex matches `a = 2` from the list in `knownOrFactsMap["="]`, specifically finding `a = 1 or a = 2 or a = 3` that contains `a = 2`. Then it verifies whether `not a = 1` and `not a = 3` are both true. If both are verified, then `a = 2` is proven.

**Note**: The working principle of `knownOrFactsMap` described here is the same as in the Litex kernel, but the actual implementation details may differ because the kernel uses various optimization techniques. However, the fundamental working logic remains consistent.

This elimination method works for any number of alternatives in an `or` statement. Litex systematically checks and eliminates each alternative until only one possibility remains, which must then be true.

**Step 7: Verify using known forall facts**

```litex
prop p(x, y R)
know forall x, y R: $p(x, y) => x = y
let a, b R: $p(a, b)
a = b
```

Litex internally maintains a dedicated storage for known forall facts, called `ForallFactMap`. Each map's key is a proposition name, and the value is a list of related forall facts. For example, when you use `know` or prove a fact yourself, and learn that `forall x, y R: $p(x, y) => x = y` is true, then `ForallFactMap["="]` will add `forall x, y R: $p(x, y) => x = y` to its list.

**Note**: The working principle of `ForallFactMap` described here is the same as in the Litex kernel, but the actual implementation details may differ because the kernel uses various optimization techniques. However, the fundamental working logic remains consistent.

When we want to prove `a = b`, we iterate through all forall facts in `ForallFactMap["="]`. During iteration, we see `forall x, y R: $p(x, y) => x = y`. We then verify: if we substitute `x` with `a` and `y` with `b`, are `a $in R`, `b $in R`, and `$p(a, b)` true? If yes, we then verify whether the corresponding `x = y` with `x` and `y` replaced by `a` and `b` respectively, i.e., `a = b`, is true. If that's also true, then it's verified.

If this method fails to prove `a = b`, Litex will try the same approach to prove `b = a` (since equality is symmetric).

**Combining forall with `or` facts**: When a forall fact contains an `or` statement involving equality, Litex can use elimination to prove specific equality cases.

**Example**: Suppose we have:
```litex
have a set = {1, 2, 3}
forall x a: x = 1 or x = 2 or x = 3
let x a:
    not x = 1
    not x = 3
x = 2
```

To prove `x = 2`, Litex follows this process:

1. First, it finds the relevant forall fact: `forall x a: x = 1 or x = 2 or x = 3`
2. It substitutes the specific variable `x` into this forall statement, obtaining: `x = 1 or x = 2 or x = 3`
3. It then applies the `or` elimination method: verify that `not x = 1` and `not x = 3` are both true
4. Since all alternatives except `x = 2` have been eliminated, `x = 2` must be true

This combines the forall fact matching mechanism with the `or` elimination strategy: Litex first matches the forall pattern to extract the relevant `or` statement for the specific variable, then uses elimination to prove the desired equality.

## Special Properties

### 1. Symbols with Corresponding Values

Numeric values are special. If in a known fact `a = b`, either `a` or `b` is entirely a numeric expression (such as `a = 2`, `b = 1 / 7`, `f(x, y) = 11 / 8 * 9 + 3`), then Litex stores this numeric expression as the symbol's value. The `ValueMap["a"] = 2`, `ValueMap["b"] = 1 / 7`, `ValueMap["f(x,y)"] = 11 / 8 * 9 + 3` will be stored.

**Note**: The working principle of `ValueMap` described here is the same as in the Litex kernel, but the actual implementation details may differ because the kernel uses various optimization techniques. However, the fundamental working logic remains consistent. 

For example, if we previously know `a = 2`, then `a + 3 = 5` can also be automatically verified, because the kernel finds the value of `a` is `2` in the ValueMap, so `a + 3 = 2 + 3 = 5`.

### 2. Polynomial Reduction

If both sides are entirely polynomial expressions (addition, subtraction, multiplication, division, exponentiation), Litex reduces both sides.

#### 2.1 Without Division

```litex
forall x R: (x + 1) * (x + 1) = x * x + 2 * x + 1
```

When Litex sees such expressions, it automatically simplifies them to their canonical form (addition expressions sorted in dictionary order, like `x * x + 2 * x + 1`), and then verifies the equality. If the canonical forms of both sides are the same, the equality is established.

#### 2.2 With Division

```litex
forall x R, y R: y ！= 0 => (x + 1) * (x + 1) / y = x * x + 2 * x + 1 / y
```

First, it is transformed into a multiplication expression, then reduced. The above expression is equivalent to:

```litex
forall x R, y R:
    (x + 1) * (x + 1) * (y + 1 - 1) = (x * x + 2 * x + 1) * y
```

## Chained Equality

When verifying a chain of equalities like `a = b = c = d`, Litex first verifies `a = b`, then `c = b` and `c = a` (if `c = b` is verified, `c = a` won't be verified again), and finally `d = c` and `d = b`, `d = a` (if `d = c` is verified, `d = b` and `d = a` won't be verified again). If all these verifications pass, then `a = b = c = d` is verified.

```litex
have a R = 10
have b R = 20 / 2
have c R = (a + b) / 2
have d R = (a + b + c) / 3

a = b = c = d
```

## Summary

Equality (`=`) is the most fundamental proposition in mathematics and Litex. All other propositions depend on equality for their definition and verification. Equality enables symbols that are literally different to have the same meaning, allowing substitution in any context.

Litex verifies equality through a multi-step process:

**Step 1**: Check that all functions appearing on both sides have arguments in their domains.

**Step 2**: If the left-hand side and right-hand side are the same, the equality is verified.

**Step 3**: **Numeric Simplification**: If both sides are numeric expressions, simplify and compute them (using string matching, not floating-point arithmetic).

**Step 4**: **Equivalence Set Lookup**: Litex maintains an `equalityMap` that stores equivalence sets. Two symbols are equal if they belong to the same equivalence set. When new equalities are proven, equivalence sets are merged accordingly.

**Step 5**: **Recursive Function Checking**: For function expressions, Litex recursively verifies that function names and all corresponding parameters are equal.

**Step 6**: **Or Fact Elimination**: When a known fact has the form `a = v1 or a = v2 or ... or a = vn`, Litex can prove `a = vi` by verifying that all other alternatives are false (i.e., `not a = vj` for all `j ≠ i`).

**Step 7**: **Forall Fact Matching**: Litex searches through known forall facts in `ForallFactMap` and attempts to match the equality statement by substituting variables and verifying conditions. When a forall fact contains an `or` statement involving equality, Litex can use elimination to prove specific equality cases.

Additionally, Litex has special handling for:
- **Symbols with numeric values**: When a symbol has a stored numeric value, Litex automatically substitutes it during verification.
- **Polynomial expressions**: Litex automatically reduces polynomial expressions to canonical form for comparison.

The special storage mechanism for equality (using equivalence sets) reflects its fundamental role: equality is not just another proposition, but the foundation that enables all mathematical reasoning through substitution and equivalence.

## Bonus

### Litex's Duck Test Philosophy

Litex follows the **duck test** philosophy (inspired by Python's duck typing): *"If it looks like a duck, swims like a duck, and quacks like a duck, then it probably is a duck."* This principle is reflected in how Litex handles fundamental mathematical concepts.

Many theorem provers define everything from scratch—they define integers, real numbers, arithmetic operations, and even basic concepts like sets and functions within the language itself. Litex takes a different approach that is more aligned with how humans learn mathematics and how mathematics developed historically.

**How Humans Learn Mathematics**: A person typically encounters concepts like integers at a very young age, but may never learn—or only learn much later—that integers are "defined" using Peano axioms or other foundational systems. Despite not knowing the formal definition, people can use integers and understand their basic properties.

**Litex's Approach**: Litex adopts a similar philosophy. Symbols like `Z` (integers), `R` (real numbers), and expressions like `1 + 1` are not "defined" in the traditional sense. Instead, they exist directly in the kernel, and Litex has built-in knowledge of all common operations and properties for these fundamental mathematical objects.

This means that when you write `1 + 1 = 2` in Litex, you don't need to prove that `1` is a natural number, that `+` is a valid operation, or that the equality holds based on some definition. Litex recognizes these patterns and verifies them using its built-in knowledge, just as a human mathematician would recognize and work with these concepts intuitively.

This design choice makes Litex more intuitive and closer to how mathematics is actually practiced, where we work with familiar concepts without constantly referring back to their foundational definitions.
