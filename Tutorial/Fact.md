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

## Specific Facts: Building Blocks of Reasoning

Just like in natural language, facts in mathematics are also composed of verbs and nouns. For example, in the statement 1 < 2, the verb is “<”, while the arguments, 1 and 2, serve as nouns. We call facts of this form specific facts, to distinguish them from universal facts that begin with forall.

Here are some examples:

```litex
17 < 47 # verb: <, nouns: 17, 47
17 * 47 = 799 # verb: =, nouns: 17 * 47, 799
17 != 47 # verb: !=, nouns: 17, 47
```

Besides builtin propositions (verb) like `>`, `=`, `!=`, you can also use your own propositions using `prop` keyword.

## Forall Statements: Force enabling reasoning to expand infinitely

_Deduction: inference in which the conclusion about particulars follows necessarily from general or universal premises._

_— Merriam-Webster Dictionary_

Mathematics is fundamentally about deducing new facts from previously established ones. Among these, **universal facts** (statements beginning with `forall`, also called `forall` statements) play a central role: they allow us to derive infinitely many specific instances.

For example, the universal statement

```litex
forall x N_pos => x $in N
```

can generate infinitely many specific statements of the form `x $in N`:

```
1 $in N
2 $in N
...
```

Since there are infinitely many positive natural numbers, this single universal statement gives rise to infinitely many true statements.

---

## Universal Facts in Litex

Universal statements in Litex express the idea of “for all …, if certain assumptions hold, then certain conclusions follow.”

Here is a trivial but valid example:

```litex
forall x N_pos:
    x $in N_pos
```

This reads: *for all `x` in `N_pos` (the set of positive natural numbers), `x` is in `N_pos`.*
The assumption and the conclusion are identical, so the statement is always true.

---

## Syntax of `forall`

The complete syntax is:

```
forall parameter1 set1, parameter2 set2, ...:
    domFact1
    domFact2
    ...
    =>:
        thenFact1
        thenFact2
        ...
```

This means: *for all parameter1 in set1, parameter2 in set2, …, if domain facts (domFacts) are satisfied, then the conclusions (thenFacts) are true.*
You can think of domain facts as the **restrictions or assumptions** required for the parameters.

The symbol `$in` is a built-in proposition in Litex that means “is in.” So you can write either:

```litex
1 $in N_pos
```

or equivalently:

```litex
$in(1, N_pos)
```

Both assert the obvious fact: *for all `x` in `N_pos`, `x` is in `N_pos`.*

---

## Inline Universal Statements

Litex also supports a compact **inline form**:

```
forall parameter1 set1, parameter2 set2, ... : inline domain facts => inline conclusion facts
```

Inline facts follow two rules:

1. A **specific fact** is followed by `,`
2. A **universal fact** is followed by `;`

Examples:

```litex
forall x N_pos => x $in N_pos
forall x N_pos: forall y N_pos: y > x => y > x; x > 10 => forall y N_pos: y > x => y > x; x > 10
```

(The second example is deliberately meaningless—it only demonstrates the syntax for nesting inline universal facts.)

---

## Universal Facts with Restrictions

Often, we want to express universal statements with additional restrictions. For instance:

*For all real numbers `x` and `y`, if `x > 0` and `y > 0`, then `x > 0` and `y > 0`.*

In Litex:

```litex
know forall x, y R: x > 0, y > 0 => x > 0, y > 0
```

To make such declarations more concise, Litex lets you omit some reserved words in certain contexts. For example, `dom` can be hidden:

```litex
forall x, y R:
    x > 0
    y > 0
    =>:
        x > 0
        y > 0
```

Inline version is

```litex
forall x, y R: x > 0, y > 0 => x > 0, y > 0
```

If `x` is already declared to be in `N_pos` (the set of positive natural numbers), there is no need to restate its domain. Similarly, `iff` can sometimes be omitted.

So, the canonical form of the opening example would be:

```litex
forall x N_pos:
    =>:
        x $in R
```

Inline version is

```litex
forall x N_pos => x $in R
```

---

## Equivalent Facts

Sometimes, you want to assert that two conclusions are **equivalent** under the same restrictions. In that case, you can add an `iff` block:

```litex
forall x R:
    dom:
        x > 1
    =>:
        not x = 2
    <=>:
        x != 2
```

Inline version is

```litex
forall x R: x > 1 => not x = 2 <=> x != 2
```

> **Note:** This format only supports equivalences of the form `fact_1 <=> fact_2`. Both facts must be logically equivalent.

## Examples

Universal statements are everywhere in math, so we will see many examples in the following sections to help you understand how to use them.

Sometimes, a proposition has reflection properties. For example, being friends is a symmetric relation.

```litex
have people nonempty_set
have oddie_bird, hippo_dog people
prop we_are_friends(x, y people)
know:
    forall x, y people => $we_are_friends(x, y) <=> $we_are_friends(y, x)
    $we_are_friends(oddie_bird, hippo_dog)
$we_are_friends(hippo_dog, oddie_bird)
```

## What will happen if your requirements in a universal fact are wrong?

Suppose we have the following code

```litex
forall x, y R:
    2 * x + 3 * y = 4
    4 * x + 6 * y = 7
    =>:
        =:
            2 * (2 * x + 3 * y)
            2 * 4
            4 * x + 6 * y
            7
        7 = 8
```

Wait, why `7 = 8` is true without any contradiction?

The answer is that the requirements in the universal fact are wrong. There is no such `x` and `y` that satisfies the requirements. The reason why validation won't cause any trouble is, no such `x` and `y` exists that can match the requirements of the universal fact. So the newly verified fact will never be used to verify other facts.

## Conditional Universal Facts

Sometimes, you want to express a universal fact without universal parameters. For example:

```litex
have x R

forall:
    x = 1
    =>:
        x = 1 * 1
```

Notice that no extra parameters are needed in the universal fact. What we are doing is: assuming a parameter defined else-where (not in the scope of the universal fact) and assuming it satisfies the requirements of the universal fact. This is very similar to `if` statement in programming languages. We actually allow you to use keyword `if` to do so in Litex:

```litex
have x R

if:
    x = 1
    =>:
        x = 1 * 1
```

This looks much natural and readable, right?

## Match and Substitution: How a Factual Statement is Verified in Litex

How does Litex verify a statement?
It all comes down to **match and substitution**—as simple as pressing `Ctrl + F` in your browser.

There are only two ways to perform match and substitution:

1. **From special case to special case**
2. **From general case to special case**

## From Special Case to Special Case

If we know a fact is true, then whenever we recall it later, it remains true.

```litex
have a R # It means a is in set R (R: The set of all real numbers)
know a = 1
a = 1
```

Here, since we already know `a = 1`, reclaiming it simply reproduces the same fact.

## From General Case to Special Case

The other way is to move from a general rule to a specific instance.

```litex
# Define three propositions
prop g(x Q)
prop s(x Q)
prop q(x Q)

know $g(1)
know forall x Q => $s(x)
know $q(1)
know forall x N: x > 7 => $g(x)
know forall x Q: x > 17 => $g(x)
$g(17.17)
```

We want to verify whether `$g(17.17)` is true.
To do this, Litex scans all known facts with the proposition name `g`. Other facts (like `$q(1)` or `forall x Q => $s(x)`) are ignored because they use different proposition names.

Relevant facts for `g` are:

1. `$g(1)`
2. `forall x N: x > 7 => $g(x)`
3. `forall x Q: x > 17 => $g(x)`

Now we check:

* **Fact 1:** `$g(1)` applies only to `x = 1`. Since `1 ≠ 17.17`, it doesn’t help.
* **Fact 2:** For all natural numbers greater than 7, `g(x)` holds. But `17.17 ∉ N`, so this fact does not apply. (Q means the set of all rational numbers, N means the set of all natural numbers)
* **Fact 3:** For all rationals greater than 17, `g(x)` holds. Since `17.17 ∈ Q` and `17.17 > 17`, this fact applies.

Therefore, `$g(17.17)` is verified. Once obtained, `$g(17.17)` itself becomes a new fact that can be used in future reasoning.

## Summary

In short, **match and substitution** is the fundamental mechanism by which Litex derives new facts. With basic arithmetic and axioms built in, the entire mathematical system can be constructed step by step through this simple yet powerful method. It is just a miracle how we can build a whole mathematical system by this simple method!!

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

## Examples

1. Why the following code does not work?

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

Example 2:

```litex
prop product_zero_implies_or(x, y R):
    x * y = 0
    <=>:
        or(x = 0, y = 0)
know forall x, y R: x * y = 0 => $product_zero_implies_or(x, y)

let a,b R
know a*b=0
$product_zero_implies_or(a,b)
```

## Set Equals An Enumeration 

## Conclusion

In this chapter, we have learned the most fundamental concept in Litex: **Factual Statement**. We have also learned how to derive new facts from established ones by **match and substitution**.

<!-- TODO: FACT HIERARCHY -->