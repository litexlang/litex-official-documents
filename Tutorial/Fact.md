# Factual Statement: Math is About Deriving New Facts from Established Ones

> *“Mathematics is nothing more than a game played according to certain simple rules with meaningless marks on a paper.”*
> — David Hilbert

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

## Conclusion

In this chapter, we have learned the most fundamental concept in Litex: **Factual Statement**. We have also learned how to derive new facts from established ones by **match and substitution**.

<!-- TODO: FACT HIERARCHY -->