# Prove For: Iterative Proofs Over Ranges

_You can checkout anytime you like but you can never leave._

_— Hotel California_

When proving universal statements over ranges of integers, Litex provides a powerful and intuitive mechanism called `prove_for`. This feature allows you to prove properties that hold for all elements in a range by iterating through each element, making it particularly useful for finite ranges and bounded integer sets.

---

## Why Prove For?

In mathematics, we often need to prove statements like "for all integers \(i\) in the range \([1, 10)\), property \(p(i)\) holds." While we could express this using a general `forall` statement, there are several compelling reasons why `prove_for` is essential:

### 1. **Computational Verification**

Unlike general `forall` statements that work through logical deduction, `prove_for` enables **computational verification** by explicitly iterating over each element in the range. This is crucial when:
- The property needs to be checked computationally for each value
- The proof strategy differs for different values in the range
- We want to leverage Litex's ability to automatically verify facts for specific values

### 2. **Explicit Iteration Control**

`prove_for` gives you explicit control over the iteration process. You can:
- Specify exactly which range to iterate over
- Use different range types (`range`, `closed_range`)
- Have fine-grained control over the proof process for each element

### 3. **Bridge Between Logic and Computation**

`prove_for` bridges the gap between logical statements (`forall`) and computational verification. It allows you to prove universal statements by showing that the property holds for each element through direct computation or explicit proof steps.

### 4. **Handling Finite Ranges Efficiently**

For finite ranges, `prove_for` is more efficient and clearer than general universal quantification. It makes the iterative nature of the proof explicit, which is especially important when the range is bounded and can be exhaustively checked.

---

## Syntax and Usage

The basic syntax of `prove_for` is:

```
prove_for variable_name range_type(lower, upper):
    =>:
        # then facts (what you want to prove)
    prove:
        # proof steps for each element
```

### Range Types

Litex supports two types of ranges:

1. **`range(a, b)`**: Represents the half-open interval \([a, b)\), containing all integers \(i\) such that \(a \leq i < b\)
2. **`closed_range(a, b)`**: Represents the closed interval \([a, b]\), containing all integers \(i\) such that \(a \leq i \leq b\)

### Basic Example

```litex
prop p(x R)

prove_for i range(1, 10):
    =>:
        $p(i)
    prove:
        know $p(i)
```

This iterates over all integers \(i\) from 1 to 9 (inclusive of 1, exclusive of 10) and proves that \(p(i)\) holds for each.

### With Closed Range

```litex
prove_for i closed_range(1, 10):
    i > 0
```

This iterates over all integers \(i\) from 1 to 10 (inclusive) and proves that \(i > 0\) for each.

---

## Relationship to Other Constructs

### `prove_for` vs `forall`

`prove_for` is closely related to `forall`, but serves a different purpose:

**Using `prove_for`**:
```litex
prop p(x R)

prove_for i range(1, 10):
    =>:
        $p(i)
    prove:
        know $p(i)
```

This explicitly iterates over the range and proves the property for each element.

### `prove_for` vs `prove_in_range`

`prove_for` is similar to `prove_in_range`, but with a more intuitive syntax:

**Using `prove_in_range`**:
```litex
have s set = {x Z : 1 <= x, x < 10}
prove_for i range(1, 10):
    i $in s
```

The `prove_for` syntax is more direct and doesn't require explicitly defining the set.


---

## When to Use `prove_for`

Use `prove_for` when:

1. **You have a finite, bounded range** of integers to iterate over
2. **You want explicit iteration** rather than logical deduction
3. **The proof strategy benefits from** checking each element individually
4. **You need computational verification** for each value in the range
5. **You want to make the iterative nature** of the proof clear and explicit

Use `forall` when:

1. **You need general logical quantification** over potentially infinite sets
2. **The proof relies on logical deduction** rather than enumeration
3. **You're working with unbounded or infinite ranges**

---

## Summary

`prove_for` is an essential tool in Litex for proving universal statements over ranges of integers. It provides:

- **Explicit iteration** over finite ranges
- **Computational verification** capabilities
- **Clear, intuitive syntax** for range-based proofs
- **Bridge between logic and computation**

By making the iterative proof process explicit, `prove_for` helps you write clearer, more verifiable proofs for bounded integer ranges, complementing the more general `forall` statement for logical quantification.
