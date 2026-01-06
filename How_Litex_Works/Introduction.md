# Introduction

Author: Jiachen Shen
Version: 2025-12-18
This document is a summary of how Litex works. Still under drastic revision.

_Mathematics is the language with which God has written the universe._
_— Galileo Galilei_

---

# Define, Verify, Infer, Memorize
Mathematics is complicated, and so are the implementation details of Litex. However, the fundamental concepts behind how Litex, as a set-theory based LCF, works are actually quite straightforward and elegant.

At its heart, Litex operates through four fundamental operations: **Define**, **Verify**, **Infer**, and **Memorize**. Every statement you write in Litex involves some combination of these operations, just like how they works in mathematics. Let's start with a simple example of syllogism (三段论). Read [comparison with other LCFs](https://litexlang.com/doc/How_Litex_Works/Litex_vs_Lean_Set_Theory_Examples) if you want to know more about the differences between Litex and other formal languages.

## Example

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

1. **Define**: First, we define the objects (nouns) that we'll be working with: `human` as a nonempty set, and `Jordan` as an element of that set. We also define proposition predicates (verbs) that express properties: `is_smart` and `is_intelligent`. The definition of `is_intelligent` establishes that being intelligent is equivalent to being smart. These definitions establish the vocabulary and logical structure that Litex will use throughout the reasoning process.

2. **Memorize**: We use the `know` keyword to memorize a fact without verification: all humans are intelligent. This fact is stored in Litex's knowledge base as an axiom—a foundational truth that we accept without proof. The `know` keyword is typically used to memorize axioms, self-evident definitions, and assumptions that serve as the starting point for our reasoning.

3. **Verify**: When we attempt to verify `$is_intelligent(Jordan)`, Litex searches through its knowledge base to see if this statement can be proven. It finds the memorized fact `forall x human => $is_intelligent(x)`, which states that all humans are intelligent. It then checks whether `Jordan $in human` is true (which it is, since we defined `Jordan` as an element of `human`). Since both conditions are satisfied, Litex successfully verifies that `$is_intelligent(Jordan)` is true.

4. **Infer**: During the verification process, Litex automatically infers that `$is_smart(Jordan)` must also be true. This inference follows directly from the definition of `is_intelligent`: since `is_intelligent` is defined as equivalent to `is_smart`, any statement about intelligence automatically implies the corresponding statement about being smart. This inference happens automatically based on the definitions we provided.

5. **Memorize (again)**: Once verified, both `$is_intelligent(Jordan)` and the newly inferred `$is_smart(Jordan)` are memorized as known facts in Litex's knowledge base. This means that in future verification attempts, Litex can immediately confirm these facts without needing to re-derive them from scratch.

6. **Verify (again)**: When we later verify `$is_smart(Jordan)`, Litex can immediately confirm it as true because it's already stored in the knowledge base from the previous inference step. This demonstrates how memorization improves efficiency by avoiding redundant computations.

This cycle of **Define** → **Memorize** → **Verify** → **Infer** → **Memorize** is the fundamental pattern that drives all of Litex's mathematical reasoning.

## How different statement types use these operations

Not every statement uses all four operations. Different types of statements involve different combinations of these steps, which reflects their different semantic meanings. Let's examine a few concrete examples:

**Example 1: Object definition with assignment**

The statement `have x R = 17` involves:

1. **Define**: The statement defines a new object `x` of type `R` (the real numbers)
2. **Verify**: Litex verifies that the value `17` is indeed a valid element of `R` (which it is, since 17 is a real number)
3. **Memorize**: Once verified, the equality `x = 17` is memorized as a known fact in Litex's knowledge base

**Example 2: Inequality verification**

The statement `x > 0` involves:

1. **Verify**: Litex attempts to verify that `x > 0` is true, using known facts about `x` from the knowledge base
2. **Memorize**: If the verification succeeds, `x > 0` is memorized as a known fact
3. **Infer**: Because inequalities like `x > 0` are common in mathematical reasoning, Litex automatically infers and memorizes several related facts that are logically equivalent or implied, such as:
   - `x != 0` (x is not equal to zero)
   - `not (x < 0)` (x is not less than zero)
   - `x >= 0` (x is greater than or equal to zero)

These automatically inferred facts are stored for future use, making subsequent verifications more efficient.

**The philosophy behind Litex's design**

Litex's design philosophy is to mirror how mathematicians naturally think about mathematics. When you write mathematics in Litex, the system processes it in a way that closely aligns with how your mind processes mathematical reasoning. This design choice has two important benefits:

1. **Naturalness**: Litex feels intuitive because it follows familiar patterns of mathematical thought
2. **Rigor**: By requiring explicit definitions and verifications, Litex encourages users to think more carefully and thoroughly about their mathematical reasoning, catching potential errors or gaps in logic

## Define

Definition is the process of establishing the vocabulary and structure that Litex will work with. In Litex, there are two fundamental types of definitions:

1. **Define objects (nouns)**: These are mathematical entities like sets, numbers, functions, or any other mathematical objects. Objects are the "things" that we reason about.

2. **Define proposition predicates (verbs)**: These include:
   - Proposition predicates: Properties or relations that can be true or false
   - Existential proposition predicates: Predicates that assert the existence of something
   - Implication predicates: Predicates that express conditional relationships

**Key differences between defining objects and defining predicates:**

1. **Truth value**: Objects (nouns) do not have truth values—they cannot be judged as true or false. Predicates (verbs), on the other hand, express statements that can be evaluated as true or false.

2. **Existence verification**: When defining a predicate, Litex does not require you to verify that the predicate can actually be satisfied. You can define a predicate without proving that there exists an object for which it is true. This allows for more flexible mathematical reasoning.

For more detailed information about definitions in Litex, see [litexlang.com/How_Litex_Works/Define](https://litexlang.com/How_Litex_Works/Define).

## Memorize

Memorization is the mechanism by which Litex stores verified facts in its knowledge base for future use. This is conceptually the simplest of the four operations, but it's crucial for efficiency—without memorization, Litex would need to re-derive every fact from scratch each time it's needed.

**How facts are organized**

Facts are stored and organized by their predicates. Litex maintains separate dictionaries for different types of facts:

1. **Specific facts**: These are facts about particular objects, such as `$p(a)`. When a specific fact like `$p(a)` is memorized, it is added to a list associated with the predicate `p` in the specific fact dictionary. This allows Litex to quickly look up all known instances where predicate `p` is true.

2. **Universal facts (forall facts)**: These are facts that apply to all elements of a set, such as `forall x R: $p(x)`. When such a fact is memorized, it is stored in the forall fact dictionary, again organized by predicate. For example, if we have `forall x R: $p(x), $q(1, x)`, then:
   - `forall x R: $p(x)` is stored in `map["p"]` in the forall fact dictionary
   - `forall x R: $q(1, x)` is stored in `map["q"]` in the forall fact dictionary

**Special handling of equality**

Equality facts require special handling because of the mathematical properties of equality: transitivity (if `a = b` and `b = c`, then `a = c`) and symmetry (if `a = b`, then `b = a`). Rather than storing each equality fact separately, Litex maintains equivalence classes—groups of expressions that are known to be equal to each other.

**Example: How equality equivalence classes work**

Suppose we know the following facts:
- `a = f(b) = 2 * t`
- `g(x)(1) = 10 / 7`

Initially, Litex creates two separate equivalence classes:
- Class 1: `{a, f(b), 2 * t}` (all known to be equal)
- Class 2: `{g(x)(1), 10 / 7}` (all known to be equal)

Now, if we learn a new fact `a = 10 / 7`, Litex recognizes that this connects the two equivalence classes. It merges them into a single class:
- Merged class: `{a, f(b), 2 * t, g(x)(1), 10 / 7}`

**Using equivalence classes for verification**

When you later ask Litex to verify `20 / 14 = a`, Litex:
1. Looks up the equivalence class containing `a`
2. Checks if any expression in that class can be proven equal to `20 / 14`
3. The Litex kernel can perform symbolic computation to determine that `20 / 14 = 10 / 7` (by simplifying the fraction)
4. Since `10 / 7` is in the same equivalence class as `a`, Litex concludes that `20 / 14 = a` is true
5. At this point, `20 / 14` is also added to the equivalence class

This approach makes equality verification very efficient, as Litex only needs to check one equivalence class rather than comparing against every known equality fact individually.

## Verify

Verification is the core operation of Litex—it's what makes Litex a proof assistant rather than just a programming language. Any system capable of mathematical verification must be built on two fundamental components:

1. **Axioms**: These are foundational facts that we accept as true without proof. ZFC set theory is the axiom that Litex, as a LCF, chooses to use. ZFC set theory is the most common foundation of mathematics, and it is the most accessible to ordinary people. So every object in Litex is a set.

2. **Inference rules**: These are the logical rules that determine how Litex can derive new facts from existing ones. Inference rules specify what conclusions can be drawn from given premises. Basic inference rules include:

1. match and substitution: if a = b, then $p(a) => $p(b); forall x human: $is_intelligent(x) and Jordan $in human => $is_intelligent(Jordan)

2. numeric expression computation (as string not floating-point): if a = 10 / 7, b = 20 / 14, then a = b

3. builtin rules like: any set in the form of {...} satisfy $is_finite_set({...}), transitivity of >, <, etc.

The verification process works as follows: Starting from axioms (known facts), Litex applies inference rules to derive new facts. When a new fact is successfully verified, it is memorized in the knowledge base and becomes available for future verification attempts. This creates a growing body of mathematical knowledge that can be used to verify increasingly complex statements.

**Two types of inference processes**

Litex handles two distinct types of verification, which are processed separately:

1. **Equality verification**: This handles statements of the form `a = b`. As discussed in the Memorize section, equality facts are stored in equivalence classes, which makes equality verification particularly efficient.

2. **Non-equality verification**: This handles all other types of statements, such as inequalities, membership relations, and predicate applications. Non-equality verification often depends on equality facts—for example, to verify `$p(b)`, Litex might first need to establish that `a = b` and then use the fact `$p(a)`.

**Equality verification techniques**

Equality verification leverages the special mathematical properties of equality:

- **Transitivity and symmetry**: As shown in the memorization example, if we know `a = 10 / 7` and we can prove `20 / 14 = 10 / 7` (by simplifying the fraction), then we can conclude `20 / 14 = a` using transitivity.

- **Automatic simplification**: If both sides of an equality involve basic arithmetic operations (`+`, `-`, `*`, `/`, `^`), Litex automatically simplifies both sides symbolically and then compares the results. For example, if `a = 10 / 7` and `b = 20 / 14`, Litex will:
  1. Simplify `20 / 14` to `10 / 7`
  2. Recognize that both sides equal `10 / 7`
  3. Conclude that `a = b` is true

**Using universal and specific facts**

Litex can verify specific facts by combining universal facts (forall statements) with equality or membership facts:

1. **Substitution using equality**: If we know the specific fact `$p(a)` and we can verify that `a = b`, then by substitution, we can conclude `$p(b)`. This is because if `a` and `b` are equal, any property that holds for `a` must also hold for `b`.

2. **Universal instantiation**: If we know a universal fact like `forall x human: $is_intelligent(x)` and we can verify that `Jordan $in human` (i.e., Jordan is an element of the set `human`), then we can instantiate the universal statement with `Jordan` to conclude `$is_intelligent(Jordan)`.

**Verification outcomes**

After executing a statement you want to verify, Litex returns one of three possible outcomes:

- **`true`**: The statement has been successfully verified or executed. This means Litex was able to prove the statement using the available axioms and inference rules.

- **`error`**: The statement is syntactically invalid or uses undeclared objects. This indicates a problem with how the statement was written, not with its mathematical content.

- **`unknown`**: The statement cannot be verified with the current knowledge. This outcome means either:
  - The statement is actually false, but Litex doesn't have enough information to prove it false, or
  - The current knowledge base is insufficient to determine the truth value (the statement might be true, but we need more facts to prove it)

See [litexlang.com/How_Litex_Works/Verify](https://litexlang.com/How_Litex_Works/Verify)

## Infer

Inference is the process by which Litex automatically derives new facts from existing ones, based on logical relationships and definitions. This is crucial for making Litex both powerful and user-friendly.

**Logical equivalences and transformations**

Litex recognizes important logical equivalences that allow it to automatically transform statements. For example, the equivalence `not exist <=> forall not` means that "there does not exist an x such that P(x)" is logically equivalent to "for all x, not P(x)". When Litex encounters one form, it can automatically infer the other.

**Inference from definitions**

When you define a predicate, Litex can automatically infer facts based on that definition. For example, if you define `p(x)` in terms of other predicates, and you later establish that `p(x)` is true for some object, Litex can automatically derive the related facts implied by the definition.

**Automatic inference for common patterns**

To make Litex more convenient to use, the system includes automatic inference rules for common mathematical patterns. These rules recognize frequently occurring situations and automatically derive and memorize related facts. For example:

- When you verify `a > 0`, Litex automatically infers and memorizes:
  - `a != 0` (a is not zero, since zero is not greater than zero)
  - `not (a < 0)` (a is not less than zero)
  - `a >= 0` (a is greater than or equal to zero)
  - `1 / a > 0` (the reciprocal of a positive number is also positive)

These automatically inferred facts are immediately available for future verifications, making it easier to work with inequalities and other common mathematical structures.

For more detailed information about inference in Litex, see [litexlang.com/How_Litex_Works/Infer](https://litexlang.com/How_Litex_Works/Infer).

For more detailed information about memorization in Litex, see [litexlang.com/How_Litex_Works/Memorize](https://litexlang.com/How_Litex_Works/Memorize).

## Summary

**The core purpose of Litex**: Litex is designed to verify mathematical reasoning, not to compute numerical values. 

Litex serves as a proof assistant that helps you verify the correctness of your mathematical proofs. It does this by applying very strict and rigorous logical rules to check whether your reasoning is valid. The four operations — *Define, Verify, Infer, and Memorize* — work together to create a system that can rigorously check mathematical arguments while remaining intuitive and natural to use.

By understanding these four fundamental operations, you now have a clear picture of how Litex processes mathematical statements and verifies their correctness. This foundation will help you use Litex more effectively and understand how it can assist you in your mathematical work.
