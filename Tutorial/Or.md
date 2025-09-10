# Or: Stop Thinking in Black and White

Or represents an inclusive disjunction, meaning at least one of the conditions is true. You can use it like:

```litex
let x R: x = 1

or:
    x = 1
    x = 2

or(x = 1, x = 2)
```

You can write specific facts under `or` facts.

`or` facts can be written in `forall` facts:

```litex
let s set, a s: forall x s => or(x = 1, x = 2); not a = 1

a = 2
```

`or` can also appear as dom of a `forall` fact

```litex
know forall x R: or(x = 1, x = 2) => x < 3
```

## Or & Prove In Each Case

`or` is often used with `prove_in_each_case` to prove a fact in each case.

```litex
let a R: or(a = 0, a = 1)

prove_in_each_case:
    or(a = 0, a = 1)
    =>:
        a >= 0
    prove:
        a = 0
    prove:
        a = 1
```

Without `prove_in_each_case`, Litex would never be able to express many mathematical facts. Read "prove_in_each_case" section for more details.

## How is Or Facts Executed?

When the Litex kernel reads `or(fact1, fact2, ..., factN)`, it will check if `fact1` is true or not under the assumption that `fact2`, ..., `factN` are not true.

Why the following code does not work?

```
know forall x, y R: x * y = 0 => or(x = 0, y = 0)
let a,b R
know a*b=0
or(a=0,b=0)
```

Answer: The reason why it does not work, is related to how an `or` statement is executed.

When the Litex kernel reads `or(a=0,b=0)`, it will check if `a = 0` is true or not under the assumption that `b = 0` is not true. However, when we use `forall x, y R: x * y = 0 => or(x = 0, y = 0)` to check whether `a = 0` is true, it the kernel could not know what `y = b` just by reading `a = 0`.

To fix this, give a name to the known fact `forall x, y R: x * y = 0 => or(x = 0, y = 0)`.

Example 1:

```litex
know @product_zero_implies_or(x, y R):
    x * y = 0
    =>:
        or(x = 0, y = 0)
let a,b R
know a*b=0
$product_zero_implies_or(a,b)
```


## Specific fact, Or Fact, and Forall Fact

You can not write `or` fact and `forall` fact under `or`.