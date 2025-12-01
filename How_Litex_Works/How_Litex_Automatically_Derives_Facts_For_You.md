# Side Effects of Statements

_Before you speak, you are its master; after you speak, you are its slave._

_— Chinese Proverb_

---

## Introduction

When you write Litex code, each statement not only performs its primary function but also has **side effects**—it updates various internal data structures in the Litex kernel. Understanding these side effects is crucial for understanding how Litex verifies facts and reasons about mathematical statements.

This document systematically records the side effects of each Litex statement type, detailing which internal maps and data structures are updated when each statement is executed.

**Note**: The working principles described here are the same as in the Litex kernel, but the actual implementation details may differ because the kernel uses various optimization techniques. However, the fundamental working logic remains consistent.

---

## Statement: `prop`

### Primary Function
Declares a predicate (proposition template) that can be applied to objects.

### Side Effects

When you define a predicate with equivalent facts using `<=>`, Litex automatically adds a `forall` fact to `knownForallFactsMap`:

**Example:**
```litex
prop is_positive(x R):
    x > 0
```

**Side Effect:**
- `knownForallFactsMap["is_positive"]` adds: `forall x R: $is_positive(x) <=> x > 0`

**More Complex Example:**
```litex
prop can_form_triangle(x, y, z R):
    x > 0
    y > 0
    z > 0
    <=>:
        x + y > z
        x + z > y
        y + z > x
```

**Side Effect:**
- `knownForallFactsMap["can_form_triangle"]` adds: `forall x, y, z R: x > 0, y > 0, z > 0 => $can_form_triangle(x, y, z) <=> x + y > z, x + z > y, y + z > x`

**Note**: If a predicate is declared without equivalent facts (just `prop p(x R)`), no `forall` fact is added to `knownForallFactsMap` until equivalent facts are specified later using `know`.

---

## Statement: `know`

### Primary Function
Declares that a fact is known to be true (an axiom or previously proven fact).

### Side Effects

The side effects of `know` depend on the type of fact being declared:

#### 1. Specific Factual Statement

```litex
prop p(x R)
know $p(5)
```

**Side Effect:**
- `knownFactsMap["p"]` adds: `$p(5)`

#### 2. Universal Fact (`forall`)

```litex
prop p(x R)
know forall x R: $p(x)
```

**Side Effect:**
- `knownForallFactsMap["p"]` adds: `forall x R: $p(x)`

#### 3. `Or` Fact

```litex
prop p(x R)
know $p(1) or $p(2) or $p(3)
```

**Side Effect:**
- `knownOrFactsMap["p"]` adds: `$p(1) or $p(2) or $p(3)`

#### 4. `Forall` with `Or` Fact

```litex
prop p(x R)
have set s = {1, 2, 3}
know forall x s: $p(x) or $q(x)
```

**Side Effect:**
- `knownForallOrFactsMap["p"]` adds: `forall x s: $p(x) or $q(x)`
- `knownForallOrFactsMap["q"]` adds: `forall x s: $p(x) or $q(x)`

#### 5. Equality Fact

```litex
know a = b
```

**Side Effect:**
- `equalityMap` is updated: symbols `a` and `b` are added to the same equivalence set
- If either `a` or `b` is a numeric expression, `ValueMap` is updated accordingly

#### 6. Universal Equality Fact

```litex
prop p(x, y R)
know forall x, y R: $p(x, y) => x = y
```

**Side Effect:**
- `ForallFactMap["="]` adds: `forall x, y R: $p(x, y) => x = y`

---

## Statement: `let`

### Primary Function
Declares objects without checking their existence.

### Side Effects

#### 1. Basic Declaration

```litex
let a R
```

**Side Effect:**
- Creates a new symbol `a` in the current scope
- No facts are added to any map

#### 2. Declaration with Equality

```litex
let a R = 5
```

**Side Effect:**
- `equalityMap` is updated: `a` and `5` are added to the same equivalence set
- `ValueMap["a"] = 5` (since `5` is a numeric expression)

#### 3. Declaration with Conditions

```litex
let a R: a > 0
```

**Side Effect:**
- The condition `a > 0` is verified, but no facts are automatically added to maps
- If you want to use `a > 0` later, you need to explicitly state it or use `know`

---

## Statement: `have`

### Primary Function
Declares objects with existence guarantee (requires non-empty set).

### Side Effects

Similar to `let`, but with existence verification:

#### 1. Basic Declaration

```litex
have a R
```

**Side Effect:**
- Creates a new symbol `a` in the current scope
- Verifies that `R` is non-empty (existence check)
- No facts are added to any map

#### 2. Declaration with Equality

```litex
have a R = 5
```

**Side Effect:**
- `equalityMap` is updated: `a` and `5` are added to the same equivalence set
- `ValueMap["a"] = 5`
- Verifies that `R` is non-empty

---

## Statement: `forall`

### Primary Function
Declares a universal fact (for all objects satisfying certain conditions, certain conclusions hold).

### Side Effects

When a `forall` statement is verified (either through `know` or by being proven), it is added to the appropriate map:

#### 1. Simple `forall`

```litex
forall x R: $p(x)
```

**Side Effect (when verified):**
- `knownForallFactsMap["p"]` adds: `forall x R: $p(x)`

#### 2. `forall` with Conditions

```litex
forall x R: x > 0 => $p(x)
```

**Side Effect (when verified):**
- `knownForallFactsMap["p"]` adds: `forall x R: x > 0 => $p(x)`

#### 3. `forall` with `or`

```litex
forall x s: $p(x) or $q(x)
```

**Side Effect (when verified):**
- `knownForallOrFactsMap["p"]` adds: `forall x s: $p(x) or $q(x)`
- `knownForallOrFactsMap["q"]` adds: `forall x s: $p(x) or $q(x)`

#### 4. `forall` for Equality

```litex
forall x, y R: $p(x, y) => x = y
```

**Side Effect (when verified):**
- `ForallFactMap["="]` adds: `forall x, y R: $p(x, y) => x = y`

**Note**: A `forall` statement only has side effects when it is verified (either through `know` or by being proven). An unverified `forall` statement does not update any maps.

---

## Statement: `exist_prop`

### Primary Function
Declares an existential proposition (there exists an object satisfying certain properties).

### Side Effects

```litex
exist_prop x R st larger_than(y R):
    x > y
```

**Side Effect:**
- Creates a new existential proposition `larger_than`
- When verified with `know`, adds to appropriate maps based on how it's used

**Example with `know`:**
```litex
exist_prop x R st larger_than(y R):
    x > y

know forall y R => $larger_than(y)
```

**Side Effect:**
- `knownForallFactsMap["larger_than"]` adds: `forall y R => $larger_than(y)`

---

## Statement: Equality (`=`)

### Primary Function
Declares that two symbols are equal.

### Side Effects

#### 1. Simple Equality

```litex
a = b
```

**Side Effect:**
- `equalityMap` is updated: `a` and `b` are merged into the same equivalence set
- If `a` and `b` were in different equivalence sets, those sets are merged

#### 2. Equality with Numeric Value

```litex
a = 5
```

**Side Effect:**
- `equalityMap` is updated: `a` and `5` are in the same equivalence set
- `ValueMap["a"] = 5` (since `5` is a numeric expression)

#### 3. Equality in `forall`

```litex
know forall x R: x = x
```

**Side Effect:**
- `ForallFactMap["="]` adds: `forall x R: x = x`

---

## Statement: Factual Statement (Verification)

### Primary Function
Verifies whether a factual statement is true.

### Side Effects

When a factual statement is verified (returns `true`), it may be added to `knownFactsMap`:

```litex
prop p(x R)
know forall x R: x > 0 => $p(x)
let a R = 5
$p(a)  # This is verified
```

**Side Effect:**
- `knownFactsMap["p"]` may add: `$p(a)` (depending on kernel implementation)

**Note**: The exact behavior of whether verified facts are automatically added to `knownFactsMap` may vary depending on kernel implementation and optimization strategies.

---

## Summary Table

| Statement | Primary Function | Side Effects |
|-----------|-----------------|--------------|
| `prop` with `<=>` | Declare predicate with equivalent facts | Adds `forall` fact to `knownForallFactsMap` |
| `know` + specific fact | Declare known fact | Adds to `knownFactsMap` |
| `know` + `forall` | Declare universal fact | Adds to `knownForallFactsMap` or `ForallFactMap` |
| `know` + `or` fact | Declare disjunction | Adds to `knownOrFactsMap` |
| `know` + `forall` + `or` | Declare universal disjunction | Adds to `knownForallOrFactsMap` |
| `let` / `have` with `=` | Declare object with value | Updates `equalityMap` and `ValueMap` |
| `forall` (when verified) | Universal statement | Adds to appropriate `forall` map |
| `=` (equality) | Declare equality | Updates `equalityMap`, possibly `ValueMap` |
| Factual statement (when verified) | Verify fact | May add to `knownFactsMap` |

---

## Important Notes

1. **Verification vs. Declaration**: Some statements (like `forall`) only have side effects when they are verified, not just when they are declared.

2. **Map Updates are Cumulative**: Each statement adds to existing maps; it doesn't replace previous entries.

3. **Optimization**: The actual kernel implementation may use various optimization techniques, so the exact data structures may differ, but the fundamental working logic remains consistent.

4. **Scope**: Side effects are scoped to the current context. When you exit a scope (like a `let` block), the symbols declared in that scope are no longer accessible, but facts added to maps may persist depending on the kernel's implementation.

5. **Automatic Inference**: When facts are added to maps, Litex may automatically infer and add related facts based on logical relationships (e.g., transitivity, symmetry).

---

This document provides a comprehensive reference for understanding how each Litex statement affects the kernel's internal state, which is essential for understanding how Litex verifies facts and reasons about mathematical statements.

