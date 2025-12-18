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

## 每个litex语句（statement）都涉及到的define, verify, infer, memorize中的某几个步骤

比如：have x R = 17 涉及到

1. define: 定义对象（nouns） objects
2. verify: 验证对象 17 确实是 R 的元素
3. memorize: x = 17 被 memorize 为 known fact

比如：x > 0 涉及到
1. 验证 x > 0
2. memorize: x > 0 被 memorize 为 known fact
3. infer: 因为 大于0太常见了，所以litex会自动memorize很多额外的事实，比如叫 x != 0, not x < 0, x >= 0这些

不同类型的语句涉及到的步骤不同，即他们的语义不同。litex的涉及非常直观，本质上用户在写数学的时候，他们脑子是怎么想的，litex也是怎么实践的。这也看出来litex的另外一个好处：一方面litex很自然，一方面litex确实让用户更仔细细致地思考数学。

## Define

分两种情况：

1. 定义对象（nouns） objects
2. 定义命题谓词（verbs） proposition predicates 和 existential proposition predicates 和 implication predicates
定义谓词和定义名词的区别

1. 名词不具备被判断对错的能力
2. 定义谓词不需要验证存在性

阅读 Define 

## Verify

这是Litex的核心。