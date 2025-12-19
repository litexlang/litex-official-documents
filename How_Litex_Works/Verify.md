# How Factual Statements Are Checked

version: 2025-12-01

_Logic will get you from A to B. Imagination will take you everywhere._

_— Albert Einstein_

---

# Introduction

From the moment we learn to count as children, we never need to study mathematical axioms or learn how to verify mathematics. We simply know, intuitively, what is mathematically correct and what is not. When we hear "two plus two equals four," we accept it without question. When someone claims "two plus two equals five," we immediately recognize it as wrong—not because we've memorized rules, but because it feels wrong in our bones.

As we progress through high school and university, we might encounter formal mathematical axioms: Euclidean geometry, Peano arithmetic, set theory. Yet even then, we never truly learn *how* a statement is verified. We just accept that "All humans are mortal, Socrates is human, therefore Socrates is mortal" is correct—we don't question it, we don't analyze the mechanism behind it. We simply know it's right.

This is, in essence, a remarkable phenomenon: we spend our entire lives verifying mathematics without ever understanding *how* mathematics is verified. Every time you calculate change at a store, every time you check if an equation balances, every time you follow a logical argument—you're performing mathematical verification, yet you've never been taught the underlying system that makes this possible.

Litex changes this. It captures and implements the very system of verification that we've been using unconsciously all along. Litex provides a computer-automated verification system (written in software, not relying on AI) that is remarkably intuitive—so intuitive, in fact, that it mirrors how we naturally think—yet it is powerful enough to verify all of mathematics. For the first time, you can see the hidden machinery of mathematical reasoning made explicit, accessible, and automatic.

## The Role of Factual Statements

Factual statements (propositions) are the building blocks of mathematical reasoning in Litex. Unlike equality, which connects symbols, factual statements express properties and relationships that hold for specific objects or symbols.

When we say `$p(a)` is true, we mean that the proposition `p` holds for the symbol `a`. Litex's verification system allows us to extend this knowledge: if we know `$p(a)` and `a = b`, then we can conclude `$p(b)` without explicitly stating it.

**Example: Substitution in factual statements**

```litex
prop is_positive(x R)
let a, b R:
    $is_positive(a)
    a = b
$is_positive(b)  # Verified because a = b and $is_positive(a)
```

This demonstrates how factual statements work together with equality to enable mathematical reasoning through substitution.

Remarkably, in Litex, you don't need to give names to the facts you want to use and call them manually later. This releases huge productivity for the user.

## How Litex Verifies SpecificFactual Statements

A specific factual statement is a statement that is neither a forall fact nor an or fact. It is typically written as `$propName(object...)` (if there are two parameters, it can be written as `a $propName b`. If it is a built-in prop, such as `=`, `>`, then the `$` can be omitted).

**Example**:
```litex
1 > 0 
1 + 1 = 2

prop is_positive(x R):
    x > 0
$is_positive(17)
```

When proving a specific factual statement, Litex tries each step in order from the first to the last.

Litex's fundamental working logic is to iterate through a fixed set of verification strategies. As long as verification passes under any strategy, the fact is considered verified. If all strategies fail to verify, then the fact is considered unverified. Failure to verify does not necessarily mean the statement is incorrect; it only means that Litex has not found a method to prove the fact.

1. **Step 1: Search known facts**

Before searching known facts, we need to understand how Litex stores factual statements. The storage method for factual statements differs from equality because factual statements don't have the same special properties (like transitivity and symmetry) that equality has.

**Storage Mechanism**: Litex uses a hashmap called `knownFactsMap` to store factual statements. Each map's key is a proposition name, and the value is a list of known facts for that proposition.

**Note**: The working principle of `knownFactsMap` described here is the same as in the Litex kernel, but the actual implementation details may differ because the kernel uses various optimization techniques. However, the fundamental working logic remains consistent.

**Example**: Suppose we know that `$p(a)` and `$p(b)` are true. Litex stores them as:
- `knownFactsMap["p"] = [$p(a), $p(b)]`

Similarly, if we know `$q(x)` and `$q(y)` are true:
- `knownFactsMap["q"] = [$q(x), $q(y)]`

**How does this storage relate to proving factual statements?**

For example, if we want to prove `$p(c)`, Litex iterates through all facts in `knownFactsMap["p"]`. During iteration, it finds `$p(a)` and `$p(b)`. For each fact `$p(a)`, Litex checks whether `a = c` is true. If `a = c` is verified, then `$p(c)` is proven. Similarly, it checks whether `b = c` is true. If `b = c` is verified, then `$p(c)` is proven.

```litex
prop p(x R)
know $p(a)
know $p(b)
let c R = a
$p(c)  # Verified because c = a and $p(a)
```

If verification passes at this step, then the fact is considered verified.

If verification fails at this step, Litex will continue to try the next step.

2. **Step 2: Verify using known `or` facts**

When we have a known fact of the form `$p(a) or $p(b) or ... or $p(c)`, we can use it to prove `$p(vi)` for some specific `vi` by eliminating all other possibilities.

**Storage Mechanism**: Litex maintains a `knownOrFactsMap` to store known `or` facts. Each map's key is a proposition name, and the value is a list of related `or` facts.

**Note**: The working principle of `knownOrFactsMap` described here is the same as in the Litex kernel, but the actual implementation details may differ because the kernel uses various optimization techniques. However, the fundamental working logic remains consistent.

**Example**: If we know `$p(a) or $p(b) or $p(c)` is true, then `knownOrFactsMap["p"]` contains this fact in its list.

To prove `$p(b)`, Litex uses the following strategy:

1. First, it finds the relevant `or` fact: `$p(a) or $p(b) or $p(c)`
2. It matches `$p(b)` from this `or` statement
3. It then verifies that `not $p(a)` and `not $p(c)` are both true
4. If both are verified, then `$p(b)` must be true

```litex
prop p(x R)
let a, b, c R:
    $p(a) or $p(b) or $p(c)
    not $p(a)
    not $p(c)
$p(b)  # Verified by eliminating other possibilities
```

This elimination method works for any number of alternatives in an `or` statement. Litex systematically checks and eliminates each alternative until only one possibility remains, which must then be true.

If verification passes at this step, then the fact is considered verified.

If verification fails at this step, Litex will continue to try the next step.

3. **Step 3: Verify using known `forall` facts**

```litex
prop p(x R)
know forall x R: $p(x)
let a R
$p(a)
```

**Storage Mechanism**: Litex internally maintains a dedicated storage for known `forall` facts, called `knownForallFactsMap`. Each map's key is a proposition name, and the value is a list of related `forall` facts.

For example, when you use `know` or prove a fact yourself, and learn that `forall x R: $p(x)` is true, then `knownForallFactsMap["p"]` will add `forall x R: $p(x)` to its list.

**Note**: The working principle of `knownForallFactsMap` described here is the same as in the Litex kernel, but the actual implementation details may differ because the kernel uses various optimization techniques. However, the fundamental working logic remains consistent.

When we want to prove `$p(a)`, we iterate through all `forall` facts in `knownForallFactsMap["p"]`. During iteration, we see `forall x R: $p(x)`. We then verify: if we substitute `x` with `a`, is `a $in R` true? If yes, we then verify whether the corresponding `$p(x)` with `x` replaced by `a`, i.e., `$p(a)`, is true. If that's also true, then it's verified.

If verification passes at this step, then the fact is considered verified.

If verification fails at this step, Litex will continue to try the next step.

4. **Step 4: Verify using `forall` with `or` facts**

**Combining `forall` with `or` facts**: When a `forall` fact contains an `or` statement involving the proposition, Litex can use elimination to prove specific cases.

**Storage Mechanism**: Litex maintains a `knownForallOrFactsMap` to store known `forall` facts containing `or` statements. Each map's key is a proposition name, and the value is a list of related `forall` facts with `or` statements.

**Note**: The working principle of `knownForallOrFactsMap` described here is the same as in the Litex kernel, but the actual implementation details may differ because the kernel uses various optimization techniques. However, the fundamental working logic remains consistent.

**Example**: Suppose we have:
```litex
prop p(x R)
have set s = {1, 2, 3}
forall x s: $p(x) or $q(x)
let x s = 2:
    not $q(x)
$p(x)
```

To prove `$p(x)` where `x = 2`, Litex follows this process:

1. First, it finds the relevant `forall` fact: `forall x s: $p(x) or $q(x)`
2. It substitutes the specific variable `x` into this `forall` statement, obtaining: `$p(x) or $q(x)`
3. It then applies the `or` elimination method: verify that `not $q(x)` is true
4. Since the alternative `$q(x)` has been eliminated, `$p(x)` must be true

This combines the `forall` fact matching mechanism with the `or` elimination strategy: Litex first matches the `forall` pattern to extract the relevant `or` statement for the specific variable, then uses elimination to prove the desired factual statement.

If verification passes at this step, then the fact is considered verified.

If verification fails at this step, Litex will continue to try the next step.

5. **Step 5: Special properties**

Litex also handles special properties of predicates that can help verify factual statements:

**Commutativity**: If a binary predicate `p` is commutative, and `$p(a, b)` cannot be proven directly, then Litex will try to prove `$p(b, a)` instead.

```litex
prop is_equal(x, y R)
prove_is_commutative_prop is_equal
let a, b R:
    $is_equal(b, a)
$is_equal(a, b)  # Verified by commutativity
```

**Transitivity**: If a binary predicate has transitivity, and both `$p(a, b)` and `$p(b, c)` can be proven true, then `$p(a, c)` is automatically proven.

```litex
prop is_greater(x, y R)
prove_is_transitive_prop is_greater
let a, b, c R:
    a > b
    b > c
a > c  # Automatically verified by transitivity
```

**Numeric value substitution**: If parameters have corresponding numeric values (for example, if we previously recorded `a = 2`, `b = 1 / 7`), Litex automatically substitutes symbols with numeric values with their values, then proves the related facts.

```litex
let a R = 2
a > 1  # Verified automatically: Litex substitutes a with 2, then verifies 2 > 1
```

This is because Litex maintains a record of symbol values. When proving `a > 1`, Litex finds that `a = 2` is stored, substitutes `a` with `2`, then verifies `2 > 1` using built-in numeric comparison.

If verification passes at this step, then the fact is considered verified.

If verification fails at this step, the fact is considered unverified.

## Check or fact

When we have a known fact of the form `$p(a) or $p(b) or $p(c)`, we are essentially proving it by:

1. Assuming that `not $p(b)` and `not $p(c)` are false, then proving that `$p(a)` is correct
2. Assuming that `not $p(a)` and `not $p(c)` are false, then proving that `$p(b)` is correct
3. Assuming that `not $p(a)` and `not $p(b)` are false, then proving that `$p(c)` is correct

If any of the above cases is true, then `$p(a) or $p(b) or $p(c)` is correct.

For example:

```litex
have x R = 1
x = 1 or x = 2 or x = 3
```

Since we know `x = 1`, then `x = 1 or x = 2 or x = 3` is correct.

```litex
let a, b, c R:
    forall:
        a != b
        =>:
            a = c

    a != b

a = c  # Verified because a != b and a = c
```

## check forall fact

check `forall x set1: domFact1, domFact2, ... => thenFact1, thenFact2, ...` is true by checking if `x $in set1` is true and if `domFact1, domFact2, ...` are true, then `thenFact1, thenFact2, ...` are true.

For example:

```litex
forall x R:
    x > 10
    =>:
        x > 1
```

Here, assuming we know that `x > 10` is correct, then we can prove that `x > 1` is correct.

Note that, essentially, proving `forall` and proving `or` both involve creating a new local environment, adding additional conditions, and then proving a specific fact.

## Summary

Factual statements are fundamental to mathematical reasoning in Litex. They express properties and relationships that hold for specific objects, and work together with equality to enable substitution-based reasoning.

Litex verifies factual statements through a five-step process:

1. **Known Facts Search**: Litex maintains a `knownFactsMap` that stores known factual statements. When proving `$p(c)`, Litex searches through `knownFactsMap["p"]` and checks if any known fact `$p(a)` can be matched by verifying `a = c`.

2. **Or Fact Elimination**: When a known fact has the form `$p(a) or $p(b) or ... or $p(c)`, Litex can prove `$p(vi)` by verifying that all other alternatives are false (i.e., `not $p(vj)` for all `j ≠ i`).

3. **Forall Fact Matching**: Litex searches through known `forall` facts in `knownForallFactsMap` and attempts to match the factual statement by substituting variables and verifying conditions.

4. **Combining `forall` with `or` facts**: When a `forall` fact contains an `or` statement involving the proposition, Litex can use elimination to prove specific cases.

5. **Special Properties**: Litex handles commutativity, transitivity, and numeric value substitution to automatically prove related facts.

The verification system for factual statements reflects their role in mathematical reasoning: they enable us to express and verify properties of objects, working seamlessly with equality to build complex mathematical proofs through substitution and logical inference.
