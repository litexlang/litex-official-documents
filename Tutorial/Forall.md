# Forall Statements: Force enabling reasoning to expand infinitely

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