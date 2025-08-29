# First Example: Common Sense Is Not So Common

_“If you define the problem correctly, you almost have the solution.”_
_— Steve Jobs_

Mathematics is the art of deriving new facts from established ones. To illustrate, let’s start with a classical syllogism proposed by Aristotle, which formalizes deductive reasoning.

This example states: **All humans are intelligent. Jordan is a human. Therefore, Jordan is intelligent.**

```litex
let human set, Jordan human
prop intelligent(x human)
know forall x human => $intelligent(x)
$intelligent(Jordan)
```

Let’s unpack it step by step:

* `human` is defined as the set of all humans, which is not empty.
* We define a proposition `intelligent`, which applies to any element of `human`.
* Using `know`, we establish the universal fact: all humans are intelligent.
* Finally, when we ask whether `Jordan` is intelligent, Litex automatically applies **match and substitution**.

The kernel looks at the universal fact `forall x human => $intelligent(x)`, substitutes `x` with `Jordan`, and checks whether the result holds. Since `Jordan ∈ human`, the statement `$intelligent(Jordan)` is verified as true.

### Outcomes of Statements

In Litex, every statement has one of four possible outcomes: **true, false, unknown, or error**.
Factual statements are prefixed with `$` to distinguish them from functions.[^1]

When you run the above code, Litex will print a message showing exactly how it verified the statement. You’ll see that `$intelligent(Jordan)` is established by applying the universal fact `forall x human => $intelligent(x)` to the specific case of `Jordan`.

This is the **classic example of match and substitution**—the most fundamental way people derive new facts. Keep it in mind as you move to the next section.

[^1]: Factual statements are typically written as `$propName(objects)`. They begin with `$` to distinguish them from functions. To make writing closer to everyday math, Litex provides three conveniences:

1. Built-in operators like `=`, `>` can be written directly in mathematical form.
2. If a proposition takes exactly two objects, you may write `object1 $propName object2`.
