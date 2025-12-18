# Define, Verify, Infer, Memorize

Date: 2025-12-18; Author: Jiachen Shen

_Failure is the mother of success._

_- Thomas Edison_

---

Complicated things are easy to forget. Simple things are easy to remember. Often, complicated things can be divided into simple pieces which are much easier to understand and remember.

Math is hard, so is the implementation details of Litex. However, the basic concept behind how Litex works is actually quite simple. By following these fundamental methods — **Define**, **Verify**, **Infer**, and **Memorize** — anyone can better understand Litex and use it effectively, and even learn how to write the Litex kernel! This document serves exactly this purpose.

## Example

Let's start with a simple example of syllogism:

"All humans are intelligent. Jordan is a human. Therefore, Jordan is intelligent. Since being intelligent is equivalent to being smart, Jordan is smart."

In Litex, this becomes:

```litex
# Define objects (nouns): human, Jordan
have human nonempty_set, Jordan human

# Define proposition predicates (verbs): is_smart, is_intelligent
prop is_smart(x human)
prop is_intelligent(x human):
    $is_smart(x)

# Memorize fact
know forall x human => $is_intelligent(x)

# Verify factual statement
$is_intelligent(Jordan)

# After execution of `$is_intelligent(Jordan)`, Litex will automatically infer that `$is_smart(Jordan)` is true by definition of `is_intelligent`. `$is_intelligent(Jordan)` and `$is_smart(Jordan)` are both memorized as known facts for future verification.

# Verify factual statement
$is_smart(Jordan)
```

**How this example demonstrates the four methods:**

1. **Define**: We define objects (`human`, `Jordan`) and proposition predicates (`is_smart`, `is_intelligent`). These definitions establish the vocabulary and structure that Litex will work with.

2. **Memorize**: We use `know` to memorize facts without any verification: all humans are intelligent. This fact is stored in Litex's knowledge base for future use. `know` keyword is often used to memorize axioms, self-evident definitions, and assumptions.

3. **Verify**: When we verify `$is_intelligent(Jordan)`, Litex checks if this statement can be proven using the memorized facts and definitions. After Litex searched for known facts, it found `forall x human => $is_intelligent(x)`, which matches the statement `$is_intelligent(Jordan)` and requirement `Jordan $in human` is also true. Therefore, `$is_intelligent(Jordan)` is verified.

4. **Infer**: During verification, Litex automatically infers that `$is_smart(Jordan)` must be true, because `is_intelligent` is defined in terms of `is_smart`. This inference happens automatically based on the definitions.

5. **Memorize (again)**: Both `$is_intelligent(Jordan)` and the inferred `$is_smart(Jordan)` are memorized as known facts, so when we later verify `$is_smart(Jordan)`, Litex can immediately confirm it without re-deriving it.

6. **Verify (again)**: We verify `$is_smart(Jordan)` again. It is true because it is already memorized as a known fact.

This cycle of **Define** → **Memorize** → **Verify** → **Infer** → **Memorize** is the fundamental pattern that drives all of Litex's mathematical reasoning.

## Each litex statement involves some of the steps: define, verify, infer, and memorize

For example: `have x R = 17` involves:

1. **define**: Define objects (nouns)
2. **verify**: Verify that the object 17 is indeed an element of R
3. **memorize**: x = 17 is memorized as a known fact

For example: `x > 0` involves:
1. **verify**: Verify x > 0
2. **memorize**: x > 0 is memorized as a known fact
3. **infer**: Because being greater than 0 is very common, Litex will automatically memorize many additional facts, such as x != 0, not x < 0, x >= 0

Different types of statements involve different steps, meaning their semantics differ. Litex's design is very intuitive—essentially, when users write mathematics, Litex practices it the same way their minds think about it. This also reveals another benefit of Litex: on one hand, Litex is very natural; on the other hand, Litex indeed makes users think about mathematics more carefully and thoroughly.

## Define

There are two cases:

1. Define objects (nouns)
2. Define proposition predicates (verbs), existential proposition predicates, and implication predicates

The difference between defining predicates and defining nouns:

1. Nouns do not have the ability to be judged as true or false
2. Defining predicates does not require verifying existence

See [litexlang.com/How_Litex_Works/Define](https://litexlang.com/How_Litex_Works/Define)

## Verify

This is the core of Litex. 任何能进行验证的系统都离不开两个东西

1. 公理

2. 推理规则

公理就是已知事实。推理规则就是Litex怎么基于已知的事实来验证新的事实。从公理出发，结合推理规则，我们可以验证新的事实。验证成功的事实，会被保存下来，成为新的可能被未来使用到的已知事实。

See [litexlang.com/How_Litex_Works/Verify](https://litexlang.com/How_Litex_Works/Verify)

## Infer

See [litexlang.com/How_Litex_Works/Infer](https://litexlang.com/How_Litex_Works/Infer)

## Memorize

See [litexlang.com/How_Litex_Works/Memorize](https://litexlang.com/How_Litex_Works/Memorize)