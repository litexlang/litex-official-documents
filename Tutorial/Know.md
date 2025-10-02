# Know: Use It Wisely

_Faith is taking the first step without seeing the whole staircase._

_— Martin Luther King, Jr._

Math, is about deriving new facts from a very small set of facts. The facts we are agree with are called axioms. In Litex, we use `know` to assume facts that are agreed with. Just like faith and belief is priceless is our life, the census of facts we agree with is the most precious thing in math. In fact, the search of a truly solid foundation of math, the ultimate set of axioms we all agree with and still powerful enough to build all of math, took thousands of years before Cantor finally established the set theory.

In other words, those `known` facts are the fist step of math without seeing the whole staircase.

Besides assuming axioms, we often need to assume certain facts instead of proving them. For example, when introducing a new object with specific properties, or when using a theorem as a premise without going through its full proof. In such cases, we use the `know` keyword. Afterall, any math problem is just giving you a bunch of known facts and asking you to derive new facts from them! You must be very familiar with this process.

There are two ways to use `know`: **multi-line** and **inline**.

### Multi-line

Write `know:` and list the facts below. Each fact can itself be inline or multi-line.

```litex
know:
    fact_1
    fact_2
    ...
```

Example (facts are trivial here, just for demonstration):

```litex
know:
    1 > 0
    forall x R:
        x $in R
    forall x R => x $in R
    2 > 1
```

### Inline

Write `know` followed by a sequence of inline facts. Specific facts end with `,` and universal facts with `;`. The final ending mark may be omitted.

```litex
know specific_fact_1, universal_fact_1; specific_fact_2, universal_fact_2; ...
```

Example:

```litex
know 1 > 0, forall x R => x $in R; forall x R => x $in R; 2 > 1
```

---

## When to use `know`

### 1. Bind facts to propositions

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

While mathematically the same, explicitly stating equivalences makes definitions clearer. Litex’s kernel will also infer related equivalences automatically when given, which makes proofs more direct.

---

### 2. Define axioms

Axioms are assumed true without proof. Use `know` to introduce them:

```litex
know forall x N => x >= 0
```

---

### 3. Assume theorems without proof

Sometimes you want to use results without formalizing them. For example:

```litex
prop fermat_last_theorem(x, y, z, n N_pos): n >= 3 <=> x^n + y^n = z^n
know forall x, y, z, n N_pos: n >= 3 => $fermat_last_theorem(x, y, z, n)
```

Fermat’s Last Theorem, proved by Andrew Wiles in 1994, is extremely hard to formalize. Yet Litex lets you use it directly with `know`, so you can build on established results without being blocked by their complexity.

---

### 4. Bind properties to objects or functions

If too few facts are known about an object, you can’t derive much from it. That’s why we often bind related facts when defining objects or functions.

```litex
let n N_pos
know n > 10
```

Equivalent to:

```litex
let n N_pos: n > 10
```

Another example:

```litex
fn fibonacci(n N_pos) N_pos
know fibonacci(1) = 1, fibonacci(2) = 1, forall n N_pos => fibonacci(n+2) = fibonacci(n+1) + fibonacci(n)
```

Or for functions:

```litex
fn g(x R) R
fn s(x R) R
fn q(x R) R
know forall x R => g(x) + s(x) + q(x) = g(x) + 17
```

---

## Be careful with `know`

`know` can make **any** statement true.

```litex
know 1 = 2
1 = 2   # true, because you know 1 = 2
1 != 2  # also true, because 1 != 2 is a built-in fact
```

As this example shows, careless use of `know` can break consistency. Use it wisely.

---

## Conclusion

`know` is a powerful tool. You can use it to:

1. Bind facts to propositions
2. Define axioms
3. Assume theorems without proof
4. Bind properties to objects and functions

There are no strict rules—use `know` when it makes your code clearer and easier to read, but always with caution.

