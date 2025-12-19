# Objects: Nouns of Logic

_Objects are typically noun phrases. Objects normally follow the verb in a clause._

_— Cambridge Dictionary_

---

## Section 1: The Foundation - Why We Need Set Membership

### Introduction

In this section, we'll learn why every object in Litex must belong to a set. This requirement comes directly from set theory, the foundation of modern mathematics. By the end of this section, you'll understand the fundamental principle that governs all object declarations in Litex.

### From Natural Language to Litex

Modern mathematics is built on set theory. In Litex, to stay consistent with this foundation, whenever you declare a new object, you must also specify the set it belongs to.

**Natural Language**: "Let a be a natural number"  
**Litex**: `let a N`

**Natural Language**: "Let x and y be real numbers"  
**Litex**: `let x R, y R`

### The Two Ways to Declare Objects

There are two main ways to declare an object:

1. **`have`** – the *safe* way. The set must be non-empty (i.e., `$item_exists_in(setName)` must be true, such as `$item_exists_in(R)`), or the set must be explicitly declared as a `set` or `nonempty_set`.

   > Note: `set $in set` is **not** true in Litex, as this would violate the rules of set theory.

2. **`let`** – the *unsafe* way. The set which the object belongs to might be empty, and you can even attach arbitrary properties to the object.

**Example:**
```litex
have a N, b Q, c R  # Safe: N, Q, R are known to be non-empty
let e N, f Q, g R   # Unsafe: no existence check
```

### Summary

- Every object in Litex must belong to a set
- This requirement comes from set theory, the foundation of modern mathematics
- `have` requires the set to be non-empty (safe)
- `let` does not check existence (unsafe, but flexible)

### Litex Syntax Reference

**Safe declaration**: `have object_name set_name` - requires set to be non-empty

**Unsafe declaration**: `let object_name set_name` - no existence check

**Multiple declarations**: `let a, b, c R` declares multiple objects in the same set

**Built-in sets**: `N` (natural numbers), `Z` (integers), `Q` (rationals), `R` (reals), `C` (complex numbers)

### Exercises

1. Declare three real numbers using `have`.
2. Declare two integers using `let`.
3. What's the difference between `have a R` and `let a R`?

### Bonus: Why Set Theory Matters

Set theory is the foundation of modern mathematics. Every mathematical object is a set or belongs to a set. By requiring objects to belong to sets, Litex ensures that all declarations are mathematically sound. This might seem like a small requirement, but it prevents many common errors and makes reasoning more rigorous.

---

## Section 2: Using `let` - The Flexible Way

### Introduction

The `let` keyword gives you maximum flexibility when declaring objects. You can attach any properties to objects, even contradictory ones. This section explores the power and danger of `let`, and when to use it.

### From Natural Language to Litex

**Natural Language**: "Let a be a natural number equal to 2"  
**Litex**: `let a N: a = 2`

**Natural Language**: "Let x and y be real numbers such that 2x + 3y = 10"  
**Litex**: 
```litex
let x, y R:
    2 * x + 3 * y = 10
```

### The Power (and Danger) of `let`

The simplest usage is to assign a known property:

```litex
let a N: a = 2
```

But `let` can also bind *contradictory* or unsafe properties:

```litex
let a N: a = 2, a = 3
```

**What?** `a` is both 2 and 3? Yes. In Litex, `let` is intentionally powerful and allows you to bind **any** properties to an object.

**Why such freedom?** Because when defining **axioms** and making **assumptions**, this flexibility is essential.

For example, the existence of the empty set is itself an axiom:

```litex
let self_defined_empty_set set: forall x set => not x $in self_defined_empty_set
```

### Declaring Multiple Objects

You can declare multiple objects at once:

```litex
let n, m N
```

This is equivalent to:

```litex
let n N
let m N
```

### Syntactic Sugar for Shared Sets

If multiple objects belong to the same set, you can group them:

```litex
let n, m N
```

This also works with other keywords like `fn`, `forall`, and `prop`.

You can also mix sets in one line:

```litex
let n, m N, z Z
```

Or even declare an object inside a set you just defined:

```litex
let s set, n s
```

> Note: The order matters — `s` must be declared before `n`, otherwise Litex won't know what `s` is.

### Adding Restrictions at Declaration

You can attach facts directly when declaring objects.

**Example**: two natural numbers `n` and `m` with conditions `n > 0` and `m > n`:

```litex
let n, m N:
    n > 0
    m > n
```

Or declare a system of equations:

```litex
let x, y R:
    2 * x + 3 * y = 10
    4 * x + 5 * y = 14
```

### Summary

- `let` is flexible and allows any properties to be attached
- `let` can even bind contradictory properties (useful for axioms)
- Multiple objects can be declared in one statement
- Properties can be attached directly at declaration time
- Order matters when declaring objects that depend on each other

### Litex Syntax Reference

**Basic declaration**: `let object_name set_name`

**With properties**: `let object_name set_name: property1, property2`

**Multiple objects**: `let obj1, obj2, obj3 set_name`

**Mixed sets**: `let obj1 set1, obj2 set2`

**Nested declaration**: `let s set, n s` (s must be declared first)

### Exercises

1. Declare a real number x that is greater than 0.
2. Declare two natural numbers n and m such that m > n.
3. Why might you want to use `let` instead of `have`?

### Bonus: When to Use `let`

Use `let` when:
- Defining axioms (like the empty set)
- Making assumptions in proofs
- You need maximum flexibility
- The set might be empty

Use `have` when:
- You want safety guarantees
- The object's existence is important
- Working with known non-empty sets

---

## Section 3: Using `have` - The Safe Way

### Introduction

While `let` assumes nothing, `have` requires proof that the object's set is **non-empty**. This section explores how to use `have` safely and when it's the right choice.

### From Natural Language to Litex

**Natural Language**: "There exists a natural number"  
**Litex**: `have n N`

**Natural Language**: "There exists a set containing 1, 2, 3"  
**Litex**: `have set s := {1, 2, 3}`

### Declaring Non-Empty Sets

You can define a non-empty set by enumerating its elements:

```litex
have s1 set = {1, 2, 3}
```

Or by restricting an existing domain:

```litex
have s2 set = {n N: n > 0, n < 4}
```

Here `s1` is explicitly finite, while `s2` is defined by conditions. They are different, even though both happen to describe `{1, 2, 3}`.

### Declaring Objects from Existential Propositions

If you've proven an existential proposition, you can declare an object satisfying it:

```litex
exist_prop x R st larger_than(y R):
    y > 0
    <=>:
        x > y

know forall y N_pos => $larger_than(y)

let m N_pos

have x st $larger_than(m)

x $in R
x > m
```

Here, `x` is guaranteed to exist because `$larger_than(m)` has been proven.

### Declaring Objects in Built-In Sets

```litex
have n N, z Z, q Q, r R
```

You can also declare objects in custom sets, provided you prove the set is non-empty:

```litex
have s nonempty_set

have n s
```

### Declare Objects When Existential Fact is True

`have` keyword can work together with existential facts.

```
have object1, object2, ... st $existential_fact(param1, ...)
```

When `$existential_fact(param1, ...)` is true, the `have` statement above works. The new objects `object1, ...` are declared, with corresponding properties based on the definition of `existential_fact`.

**Example:**

```litex
exist_prop x R st exist_number_larger_than(y R):
    x > y

exist 17 st $exist_number_larger_than(1)

$exist_number_larger_than(1)

have a st $exist_number_larger_than(1)

a $in R
a > 1
```

In this case, we use `17` to prove `$exist_number_larger_than(1)` and `have a st $exist_number_larger_than(1)` declares an object a with properties `a $in R` and `a > 1`. Notice `a = 17` is unknown, because `have` statement is choosing from one of the objects which satisfies the properties of `exist_number_larger_than`.

### Have Finite Set by Enumeration

When we were children, the first thing we learn about math is counting from `1` to `5`. Litex thus allows you to define a set by enumeration. (Do not underestimate enumeration: in fact, the very reason we are able to define a finite set by enumeration is guaranteed by the axioms of set theory — and this is something quite profound.)

```litex
have one_to_five set = {1,2,3,4,5}
```

If a set is finite, then to prove that forall x in this set some property holds, we can simply check each element one by one. In this way, unlike the general case of infinite sets, the conclusion can be obtained by directly traversing all the elements in the set.

```litex
have one_to_five set = {1,2,3,4,5}
prove_by_enum(x one_to_five):
    x = 1 or x = 2 or x = 3 or x = 4 or x = 5
```

As you can see, when there is nothing to prove, you can write nothing in the `prove` section (`x = 1 or x = 2 or x = 3 or x = 4 or x = 5` is immediately true when x is in one_to_five).

### Have A Set As A Subset Of Another Set Whose Items Have Certain Properties

Often, we are given a set, and we want to get a subset of that set whose items have certain properties. i.e. y∈ {x∈A: P(x) is true} <=> (y∈A and P(y) is true).

How to define {x∈A: P(x) is true}?

```litex
prop P(x R)

have s set = {x R: $P(x)}
```

Example:
```litex
have s set = {x R: 1 = 0}
```

### The Difference Between `let` and `have`

Although both declare objects, they differ in a fundamental way:

* **`have`**: the object's existence is guaranteed. Litex checks that the set is non-empty.
* **`let`**: no existence check is performed. You can declare anything — even contradictory objects — which is useful for assumptions and axioms.

In short:

* Use **`have`** when you want *safe, guaranteed existence*.
* Use **`let`** when you need *freedom*, even at the cost of safety.

### Summary

- `have` requires the set to be non-empty (safe)
- `have` can work with existential propositions
- Finite sets can be defined by enumeration
- Subsets can be defined by properties
- `have` guarantees existence, `let` does not

### Litex Syntax Reference

**Basic declaration**: `have object_name set_name`

**From existential fact**: `have object_name st $existential_fact(params)`

**Finite set by enumeration**: `have set set_name := {elem1, elem2, ...}`

**Subset by property**: `have set set_name := {x set_name: $prop(x)}`

**Built-in sets**: `N`, `Z`, `Q`, `R` are always non-empty

### Exercises

1. Declare a finite set containing the numbers 1, 2, 3, 4, 5.
2. Declare a subset of real numbers containing all positive numbers.
3. When would you use `have` instead of `let`?

### Bonus: The Safety of `have`

The `have` keyword provides safety guarantees that `let` does not. When you use `have`, you're telling Litex: "I guarantee this object exists." Litex will verify that guarantee before allowing the declaration. This prevents many common errors and makes your code more robust.

However, this safety comes at a cost: you must prove existence. Sometimes, especially when defining axioms or making assumptions, you don't want this check. That's when `let` is the right choice.

