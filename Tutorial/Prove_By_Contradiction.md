# Prove by Contradiction: A coin cannot be heads and tails at the same time.

In math, one common way to prove a statement is to prove its negation is false. This method is called `Prove by Contradiction`.

```
claim:
    fact_you_want_to_prove
    prove_by_contradiction:
        statement1
        ...
        final_statement
```

`prove_by_contradiction` should always be used in `claim` block. In the environment of `prove_by_contradiction`, `not fact_you_want_to_prove` is assumed to be true. To make the process of proving by contradiction works, the `final_statement` should be a fact that is both true and false. After that, the assumption `not fact_you_want_to_prove` is false and `fact_you_want_to_prove` is true.

For example:

```litex
prop g(x R)
prop s(x R)
prop q(x R)

know:
    forall x R: $g(x) => $s(x)
    forall x R: $s(x) => $q(x)
    not $q(17)

claim:
    not $g(17)
    prove_by_contradiction:
        $s(17)
        $q(17)
```

Here is a classic example, prove sqrt(2) is irrational using Proof by Contradiction:

```litex
fn logBase(x, y N) N:
    dom:
        x != 0

know forall x, y, z N => logBase(z, x^y) = y * logBase(z, x), logBase(z, x*y) = logBase(z, x) + logBase(z, y)

know forall x N: x != 0 => logBase(x, x) = 1

claim:
    not sqrt(2) $in Q
    prove_by_contradiction:
        have x, y st $rational_number_representation_in_fraction(sqrt(2))
        
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

        (2 * logBase(2, x)) % 2 = (1 + 2 * logBase(2, y)) % 2
        (2 * logBase(2, x)) % 2 = 0
        0 = (1 + 2 * logBase(2, y)) % 2

        (1 + 2 * logBase(2, y)) % 2 = 1 % 2 + (2 * logBase(2, y)) % 2
        1 % 2 + (2 * logBase(2, y)) % 2 = 1 + 0
        0 = 1
```


