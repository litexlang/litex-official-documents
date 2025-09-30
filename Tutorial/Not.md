# Not: Truth only matters when something can be false.

Any specific fact can be negated by `not`. 

The following example shows how to negate a specific fact:

```litex
let x R: x > 5

not x <= 5
```

To prove the negation of a specific fact, you can use `prove_by_contradiction` in `claim` block. For example:

```litex
prop p(x R)
prop q(x R)
know forall x R: $p(x) => $q(x); not $q(1)
claim:
    not $p(1)
    prove_by_contradiction:
        $q(1) # is true, because $p(1) is assumed to be true
```

You can not write `not forall` in Litex. When you want to negate a universal fact, You must declare a `exist_prop` first and try to prove the existence of such an item that leads to `not forall`.

You can also negate an existence-proposition fact:

```litex
exist_prop x N_pos st exist_positive_natural_number_smaller_than_given_real_number(y R):
    x < y

know not $exist_positive_natural_number_smaller_than_given_real_number(0)
```

`!=` means `not =`. For example:

```litex
let little_little_o, little_o R:
    little_little_o != little_o

not little_little_o = little_o # true
```