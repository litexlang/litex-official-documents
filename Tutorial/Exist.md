# Exist

## What is an existential proposition

In logic and mathematics, an **existential proposition** is a statement asserting that *there exists at least one object for which a certain property holds*. It is usually written as:

$$
\exists x \, P(x)
$$

where:

* $\exists$ means “there exists,”
* $x$ is a variable,
* $P(x)$ is a property or predicate concerning $x$.

**Intuitive understanding:**

* For example, “There exists an integer $x$ such that $x^2 = 4$” is an existential proposition, because $x = 2$ or $x = -2$ satisfies it.
* It is the counterpart to a **universal proposition**, which asserts that *all objects satisfy a property*, written as $\forall x \, P(x)$.

**Key points:**

1. The proposition is true if at least one example satisfies $P(x)$.
2. It is false if no objects satisfy $P(x)$.
3. In formal proofs, demonstrating an existential proposition usually involves providing a **witness**—an explicit example of $x$ that satisfies the property.

If you want, I can also explain the **difference in proof strategies** between existential and universal propositions—it’s a subtle but important point in formal logic.

An **existential proposition** can be expressed in terms of a universal proposition with negation. Specifically:

$$
\exists x \, P(x) \quad \text{is equivalent to} \quad \neg \forall x \, \neg P(x)
$$

**Intuition:**

* “There exists an $x$ such that $P(x)$ is true” means it is **not the case** that $P(x)$ is false for all $x$.
* In other words, if it were true that $P(x)$ is false for every $x$ ($\forall x \, \neg P(x)$), then clearly no $x$ satisfies $P(x)$.
* So asserting existence is logically the same as denying that $P(x)$ is false for all $x$.

**Example:**

* Existential: “There exists an integer $x$ such that $x^2 = 4$” → $\exists x \, (x^2 = 4)$
* Universal negation: “It is not the case that for all integers $x$, $x^2 \neq 4$” → $\neg \forall x \, (x^2 \neq 4)$

Both statements are logically equivalent. Since forall plays a central role in Litex, existential propositions are also an essential component of the language.

In Litex, to express not forall, you first define an existential proposition and then use the validation of this existential fact to represent the negation of a universal statement.

## Claim an Exist Proposition

You can claim an Exist Proposition `larger_than`(For all `y` in `R` and `y > 0`, there exists `x` in `R` such that `x > y`):

```litex
exist_prop x R st larger_than(y R):
    dom:
        y > 0
    <=>:
        x > y
```
`exist_prop` is the reserved word of Exist Proposition. `st` means *such that*. As you can see `exist_prop ... st ...` is a fixed match when you claim an Exist Proposition. 

Also, you can hide the `dom`:

```litex
exist_prop x R st larger_than(y R):
    y > 0
    <=>:
        x > y
```

If you make `y` in `N_pos`, you can hide `iff`, too:

```litex
exist_prop x R st larger_than(y N_pos):
    x > y
```

## Prove claimed Exist Proposition

When being called, exist proposition behaves exactly like how a normal proposition does. For example, here we assume `larger_than` is true for all `y` in `N_pos` and we claim there is some object that is larger than 2.

```litex
exist_prop x R st larger_than(y R):
    x > y

know forall y R => $larger_than(y)

$larger_than(2)
```

However, there is one big difference between exist proposition and normal proposition. You can prove an exist proposition by providing a specific object. For example, here we prove `larger_than(2)` by providing `3`:

```litex
exist_prop x R st larger_than(y R):
    x > y

exist 3 st $larger_than(2)
```

Since `not exist` is equivalent to `forall not`, when the reverse of a existential fact is true, then the related `forall not` fact is automatically true. See the following example:

```litex
prop q(x R, y R)

exist_prop x R st p(y R):
    $q(x, y)

know not $p(2)

forall x R:
    not $q(x, 2)
```

Unlike programming languages, where you can declare anything without checking its existence, Litex as well as math require you to declare the existence of an object before you can use it.