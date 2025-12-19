# Know: Use It Wisely

_Faith is taking the first step without seeing the whole staircase._

_— Martin Luther King, Jr._

---

## Section 1: Understanding `know`

### Introduction

In this section, we'll explore the `know` keyword—one of the most powerful and important keywords in Litex. `know` allows you to establish facts as true without proving them. By the end of this section, you'll understand when and how to use `know` effectively, and why it's both powerful and dangerous.

### From Natural Language to Litex

Math is about deriving new facts from a very small set of facts. The facts we agree with are called axioms. In Litex, we use `know` to assume facts that are agreed with.

**Natural Language**: "We assume that all natural numbers are greater than or equal to zero"  
**Litex**: `know forall x N => x >= 0`

**Natural Language**: "We know that 1 is greater than 0"  
**Litex**: `know 1 > 0`

Just like faith and belief are priceless in our life, the consensus of facts we agree with is the most precious thing in math. In fact, the search of a truly solid foundation of math, the ultimate set of axioms we all agree with and still powerful enough to build all of math, took thousands of years before Cantor finally established set theory.

In other words, those `known` facts are the first step of math without seeing the whole staircase.

### Two Ways to Use `know`

There are two ways to use `know`: **multi-line** and **inline**.

**Multi-line:**

Write `know:` and list the facts below. Each fact can itself be inline or multi-line.

```
know:
    fact_1
    fact_2
    ...
```

**Example:**

```litex
know:
    1 > 0
    forall x R:
        x $in R
    forall x R => x $in R
    2 > 1
```

**Inline:**

Write `know` followed by a sequence of inline facts. Specific facts end with `,` and universal facts with `;`. The final ending mark may be omitted.

```
know specific_fact_1, universal_fact_1; specific_fact_2, universal_fact_2; ...
```

**Example:**

```litex
know 1 > 0, forall x R => x $in R; forall x R => x $in R; 2 > 1
```

### Summary

- `know` establishes facts as true without proof
- These facts are like axioms—the foundation of reasoning
- Can be written in multi-line or inline format
- Inline format uses `,` for specific facts and `;` for universal facts

### Litex Syntax Reference

**Multi-line**: `know: fact1 fact2 ...`

**Inline**: `know fact1, fact2; fact3, ...`

**Specific facts**: End with `,` in inline format

**Universal facts**: End with `;` in inline format

### Exercises

1. Write a `know` statement establishing that all integers are rational numbers.
2. Convert this multi-line `know` to inline format:
```litex
know:
    1 > 0
    forall x R => x $in R
```
3. Explain why `know` is like "faith" in mathematics.

### Bonus: The Foundation of Mathematics

The search for a solid foundation of mathematics took thousands of years. From Euclid's axioms to Cantor's set theory, mathematicians have been searching for the right set of assumptions that are both simple and powerful enough to build all of mathematics. When you use `know`, you're participating in this tradition—establishing the facts that will serve as the foundation for all your reasoning.

---

## Section 2: When to Use `know`

### Introduction

In this section, we'll explore the different situations where `know` is appropriate. You'll learn when to use `know` for axioms, theorems, and binding properties to objects or functions.

### From Natural Language to Litex

Besides assuming axioms, we often need to assume certain facts instead of proving them. For example, when introducing a new object with specific properties, or when using a theorem as a premise without going through its full proof. In such cases, we use the `know` keyword. After all, any math problem is just giving you a bunch of known facts and asking you to derive new facts from them! You must be very familiar with this process.

### 1. Bind Facts to Propositions

You can declare a proposition and attach equivalent facts to it:

```litex
prop n_larger_than_10(n N_pos) # declare a proposition
know forall n N_pos => n > 10 <=> $n_larger_than_10(n)
```

Equivalent to:

```litex
prop n_larger_than_10(n N_pos):
    n > 10
```

While mathematically the same, explicitly stating equivalences makes definitions clearer. Litex's kernel will also infer related equivalences automatically when given, which makes proofs more direct.

### 2. Define Axioms

Axioms are assumed true without proof. Use `know` to introduce them:

```litex
know forall x N => x >= 0
```

This establishes a fundamental fact about natural numbers that we accept as true without proof.

### 3. Assume Theorems Without Proof

Sometimes you want to use results without formalizing them. For example:

```litex
prop fermat_last_theorem(x, y, z, n N_pos): n >= 3 <=> x^n + y^n = z^n
know forall x, y, z, n N_pos: n >= 3 => $fermat_last_theorem(x, y, z, n)
```

Fermat's Last Theorem, proved by Andrew Wiles in 1994, is extremely hard to formalize. Yet Litex lets you use it directly with `know`, so you can build on established results without being blocked by their complexity.

### 4. Bind Properties to Objects or Functions

If too few facts are known about an object, you can't derive much from it. That's why we often bind related facts when defining objects or functions.

**For objects:**

```litex
let n N_pos
know n > 10
```

Equivalent to:

```litex
let n N_pos: n > 10
```

**For functions:**

```litex
fn fibonacci(n N_pos) N_pos
know fibonacci(1) = 1, fibonacci(2) = 1, forall n N_pos => fibonacci(n+2) = fibonacci(n+1) + fibonacci(n)
```

Or for multiple functions:

```litex
fn g(x R) R
fn s(x R) R
fn q(x R) R
know forall x R => g(x) + s(x) + q(x) = g(x) + 17
```

### Summary

- Use `know` to bind facts to propositions
- Use `know` to define axioms
- Use `know` to assume theorems without proof
- Use `know` to bind properties to objects or functions
- `know` is flexible and can be used in many contexts

### Litex Syntax Reference

**Binding to proposition**: `know forall params => prop(params) <=> fact`

**Axiom**: `know fundamental_fact`

**Theorem**: `know forall params => theorem_statement`

**Object property**: `know object_property`

**Function property**: `know forall params => function_property`

### Exercises

1. Use `know` to establish that the sum of two even numbers is even.
2. Use `know` to assume Fermat's Last Theorem (you don't need to prove it).
3. Bind a property to a function using `know`.

### Bonus: Building on Established Results

One of the great advantages of `know` is that it lets you build on established mathematical results without having to formalize their proofs. This is especially valuable for complex theorems like Fermat's Last Theorem, which took hundreds of years to prove. You can use these results as building blocks for your own work, focusing on what you want to prove rather than re-proving everything from scratch.

---

## Section 3: Be Careful with `know`

### Introduction

In this section, we'll explore the dangers of `know`. While `know` is powerful, it can also break consistency if used carelessly. By the end of this section, you'll understand why `know` must be used wisely.

### From Natural Language to Litex

`know` can make **any** statement true.

```litex
know 1 = 2
1 = 2   # true, because you know 1 = 2
1 != 2  # also true, because 1 != 2 is a built-in fact
```

As this example shows, careless use of `know` can break consistency. Use it wisely.

**Natural Language**: "We know that 1 equals 2" (even though this contradicts basic arithmetic)  
**Litex**: `know 1 = 2` → This makes `1 = 2` true, but also creates a contradiction with `1 != 2`

### The Danger

When you use `know`, you're telling Litex: "Trust me, this is true." Litex will trust you, even if what you say contradicts other known facts. This can lead to inconsistent systems where both a statement and its negation are true.

**Example of inconsistency:**

```litex
know 1 = 2
know 2 = 3
1 = 3  # This is now true through transitivity!
```

### When It's Safe

`know` is safe when:
- You're establishing axioms (fundamental truths)
- You're assuming well-established theorems
- You're binding properties that are consistent with existing facts
- You're working in a controlled environment where you understand all the facts

### When It's Dangerous

`know` is dangerous when:
- You're not sure if the fact is consistent with other facts
- You're experimenting and might introduce contradictions
- You're binding contradictory properties
- You're assuming facts without understanding their implications

### Summary

- `know` can make any statement true, even contradictory ones
- Careless use can break consistency
- Use `know` only when you're confident the facts are consistent
- Always verify that your `know` statements don't contradict existing facts

### Litex Syntax Reference

**Power**: `know` can establish any fact as true

**Responsibility**: You must ensure consistency

**Verification**: Litex doesn't check for contradictions automatically

**Best practice**: Only use `know` for facts you're certain about

### Exercises

1. What happens if you write `know 1 = 2`? Why is this dangerous?
2. Give an example of a safe use of `know`.
3. Give an example of a dangerous use of `know`.

### Bonus: The Responsibility of Knowledge

With great power comes great responsibility. `know` gives you the power to establish any fact as true, but this power must be used wisely. In mathematics, we carefully choose our axioms to ensure consistency. When you use `know`, you're making a similar choice—you're deciding what facts to accept as true. Choose wisely, because these choices determine what you can and cannot prove in your system.

---

## Section 4: Conclusion

### Summary

`know` is a powerful tool. You can use it to:

1. Bind facts to propositions
2. Define axioms
3. Assume theorems without proof
4. Bind properties to objects and functions

There are no strict rules—use `know` when it makes your code clearer and easier to read, but always with caution.

### Best Practices

- Use `know` for axioms and fundamental facts
- Use `know` for well-established theorems you don't want to prove
- Use `know` to bind properties to objects and functions
- Always verify consistency when using `know`
- Prefer proving facts when possible, use `know` only when necessary

### Final Thoughts

`know` is the foundation of all reasoning in Litex. Just as mathematics is built on axioms, your Litex code is built on the facts you establish with `know`. Choose these facts carefully, and they will serve as a solid foundation for all your mathematical reasoning.
