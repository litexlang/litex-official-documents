# Exist

_The beginning is the most important part of the work._

_-— Plato_

## Key Difference between Math and Programming: You must prove the existence of an object before using it.

When programming, say in Python, we are so familiar with declaring an object directly and using it directly. For example:

```python
x = 1
print(x)
```

However, in math, we are not allowed to use an object directly without proving its existence. For example, many new-comers of Litex may try to write the following code:

```litex
let x R:
    x = 2
    x + 1 = 5
```

The code runs, but you might be confused by `x = 2` and `x = 4` are both true. This is because Litex does not check the existence of `x` when you are using keyword `let` to declare an object.

To overcome this unsafe declaration, Litex introduces the keyword `exist` and `have`. `exist` represents an existential fact, and `have` represents a declaration of an object with existential promise.

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

## Work with Have

One big difference between math and programming is that math requires you to prove the existence of an object before using it, and when programming in Python or C you do not have to do that. In Litex, `have` keyword allows you to declare a new object with existential promise.

`have` keyword can work together with existential facts.

```
have object1, object2, ... st $existential_fact(param1, ...)
```

When `$existential_fact(param1, ...)` is true, the `have` statement above works. The new objects `object1, ...` are declared, with corresponding properties based on the definition of `existential_fact`

For example

```litex
exist_prop x R st exist_number_larger_than(y R):
    x > y

exist 17 st $exist_number_larger_than(1)

$exist_number_larger_than(1)

have a st $exist_number_larger_than(1)

a $in R
a > 1
```

In this case, We use `17` to prove `$exist_number_larger_than(1)` and `have a st $exist_number_larger_than(1)` declares an object a with properties `a $in R` and `a > 1`. Notice `a = 17` is unknown, because `have` statement is choosing from one of the objects which satisfies the properties of `exist_number_larger_than`.

## Not Forall and Exist

Consider the following statement: `not forall x R: x > 0`. This statement is equivalent to `exist x R: not x > 0`. In Litex, you can not write `not forall`, because verifying it and using it to prove other statements is against the basic mechanism of `match and substitution` of Litex (i.e. It is almost impossible to think of a way to verify or use `not forall` to prove other statements without breaking the design of Litex).

However, you can write `exist x R: not x > 0` to represent `not forall x R: x > 0`. Logically, they are equivalent.

## Example

This example shows how to write 

```
# ∀ x : R, ∃ f : R -> R, ∀ y : R, ∃ z in R, f(x + z) = y
# Easy to prove by setting f = id, and z = y - x
```

```litex
exist_prop z R st exist_z(f fn(R) R, x R, y R):
    f(x + z) = y

exist_prop f fn(R) R st exist_f(x R):
    forall y R:
        $exist_z(f, x, y)

have fn f(x R) R = x

claim:
    forall x R => $exist_f(x)
    prove:
        claim:
            forall y R => $exist_z(f,x,y)
            prove:
                exist y - x st $exist_z(f, x, y)
        exist f st $exist_f(x)
```

When encountering a fact such as "exist A st forall B exist C st forall D exist E st F," a simple formalization technique is to define an exist_prop A st exist_A(...): ... every time an "exist A" is encountered. Here, exist_A needs to be defined as equivalent to forall B exist C st forall D exist E st F. Just as mathematics is built upon layers of abstraction, here we peel back the layers of "exist" and "forall" step by step to define exist_prop.

Also, good naming is essential. It makes abstraction process cleaner.