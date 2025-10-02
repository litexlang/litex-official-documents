# Factual Statement: Math is About Deriving New Facts from Established Ones

_There is nothing without a reason._

_— Leibniz_

Math is about deriving new facts from established ones. Such process is called deduction (also called inference, reasoning) and can be verified by a very small set of mechanical rules. Thus, we can write a computer program like Litex to verify the correctness of a piece of reasoning. Easy, right?

## What Is a Factual Statement?

The most fundamental concept in both mathematics and **Litex** is the **Factual Statement**.

A Factual Statement can take on exactly one of the following truth values:

* **true**

e.g. `1 > 0` is true

* **unknown** (not enough information to prove or disprove)

e.g. `0 > 1` is unknown. Actually it is false. In Litex, `unknown` is used in two situations: 1. this is a true statement, but the user has not provided enough information to prove it; 2. this is a false statement.

* **error** (e.g., syntax error)

e.g. `let birthday R: birthday = 2003.4.2` is error because `2003.4.2` is not a real number.

Don’t confuse a **Factual Statement** with a *true statement*. A Factual Statement might just as well be false, unknown, or even an error.
Don’t confuse a **Factual Statement** with a *Proposition*. A Proposition is more like a “verb” waiting for its objects; once the objects are supplied, it turns into a Factual Statement.

## Deriving New Facts by *Match and Substitution*

Mathematics is about deriving new facts from established ones. Verification ensures that these new facts hold true. In Litex, there are only two ways to verify a fact:

1. **From special case to special case.**
Example:

```litex
have a R
know a = 1
a = 1
```

The second statement is true simply because it matches the first one exactly. This is called **match**.

2. **From general case to special case.**
Example:

```litex
know forall x N: x >= 47 => x >= 17
let x N: x = 47
x >= 17
```

By substituting `x` with `xxg`, the `xxg >= 17` matches the known universal statement `forall x N: x >= 47 => x >= 17` after substitution. This is called **match and substitution**.

Thus, Litex builds mathematics from two kinds of factual statements: **General Facts** and **Specific Facts**. Everything revolves around these two.

In short, *match and substitution* is the fundamental mechanism for deriving new facts in Litex. Once basic arithmetic and counting are built in, the entire mathematical system can be constructed this way.

## How Do You Call a Factual Statement?

To derive new facts, we write factual statements one after another. The Litex kernel automatically verifies each one using **match and substitution**. But first, we must declare a proposition:

```litex
prop larger_than_zero(x R):
    x > 0

$larger_than_zero(1)
```

Here, `larger_than_zero` is a proposition. The symbol `>` is a built-in proposition. When we supply `1`, it becomes the factual statement `$larger_than_zero(1)`. Since `1 > 0` is true, the factual statement is true.

The `$` symbol distinguishes a factual statement from a function.

When a proposition takes exactly two objects, Litex even allows you to write it **infix**, making it look like ordinary math:

```litex
$in(1, N)
1 $in N
```

## Existential Facts

There is another kind of specific fact that is called **existential facts**. It is used to prove the existence of an object.

```litex
exist_prop x R st larger_than(y R):
    y > 0
    <=>:
        x > y

know forall y R => $larger_than(y)

```

The above example defines an existential proposition `larger_than`(For all `y` in `R` and `y > 0`, there exists `x` in `R` such that `x > y`). We know by default that `larger_than` is true for all `y` in `R`.

Existential facts are used as opposite of universal facts. For example, to disprove `forall x R => x > 0`, we only need to find a single `x` that is smaller than 0. Litex does not support `not forall` directly. You have to declare the related existential fact and then use the validation of this existential fact to represent the negation of a universal statement.

## Not: Truth only matters when something can be false.

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

## Or

Or represents an inclusive disjunction, meaning at least one of the conditions is true. You can use it like:

```litex
let x R: x = 1

or:
    x = 1
    x = 2

or(x = 1, x = 2)
```

The syntax is:

```
or:
    specific_fact1
    specific_fact2
    ...
    specific_factN

or(specific_fact1, specific_fact2, ..., specific_factN)
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

That explains why the following code does not work:

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

There are basically three kinds of facts: specific fact (ordinary specific fact, existential fact), `or` fact, and `forall` fact.

You can not write `or` fact and `forall` fact under `or`. Only specific facts are allowed. You can write `or` fact and `forall` fact in `forall` fact.

## Conclusion

In this chapter, we have learned the most fundamental concept in Litex: **Factual Statement**. We have also learned how to derive new facts from established ones by **match and substitution**.

<!-- TODO: FACT HIERARCHY -->