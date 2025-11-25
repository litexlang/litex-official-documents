# First Example: Your First Steps with Litex

_Classes will dull your mind. Destroy the potential for authentic creativity._

_— John Nash_

Litex is a language full of fun. It's a completely new way of bridging the world of math and programming, so let your creativity fly when learning it! Think of some examples on your own when reading this tutorial.

---

## Section 1: Understanding Match and Substitution

### Introduction

In this section, we'll explore the most fundamental mechanism in Litex: **match and substitution**. This is how Litex derives new facts from established ones—exactly like how humans reason in everyday mathematics. By the end of this section, you'll understand how Litex automatically verifies statements by matching patterns and substituting values.

### From Natural Language to Litex

Mathematics is the art of deriving new facts from established ones. To illustrate, let's start with a classical syllogism proposed by Aristotle, which formalizes deductive reasoning.

In natural language, we say: **"All humans are intelligent. Jordan is a human. Therefore, Jordan is intelligent."**

In Litex, this becomes:

```litex
have human nonempty_set, Jordan human
prop intelligent(x human)
know forall x human => $intelligent(x)
$intelligent(Jordan)
```

### Breaking Down the Example

Let's unpack it step by step:

**Natural Language** → **Litex Code**:

1. **"There is a set of humans"** → `have human nonempty_set`
   - We define `human` as the set of all humans, which is not empty.

2. **"Jordan is a human"** → `have Jordan human`
   - We declare that Jordan belongs to the set of humans.

3. **"Intelligence is a property that applies to humans"** → `prop intelligent(x human)`
   - We define a proposition `intelligent`, which applies to any element of `human`.

4. **"All humans are intelligent"** → `know forall x human => $intelligent(x)`
   - Using `know`, we establish the universal fact: all humans are intelligent.

5. **"Is Jordan intelligent?"** → `$intelligent(Jordan)`
   - Finally, when we ask whether `Jordan` is intelligent, Litex automatically applies **match and substitution**.

### How Match and Substitution Works

The kernel looks at the universal fact `forall x human => $intelligent(x)`, substitutes `x` with `Jordan`, and checks whether the result holds. Since `Jordan ∈ human`, the statement `$intelligent(Jordan)` is verified as true.

**The process:**
1. Litex sees the statement `$intelligent(Jordan)`
2. It searches for known facts about `intelligent`
3. It finds `forall x human => $intelligent(x)`
4. It checks if `Jordan` matches the pattern (i.e., `Jordan ∈ human`)
5. It substitutes `x` with `Jordan` in the universal fact
6. The result is `$intelligent(Jordan)`, which matches what we want to prove

### Understanding Factual Statements

Factual statements are prefixed with `$` to distinguish them from functions. When the factual statement takes exactly two objects, you may write `object1 $propName object2`. You do not have to write `$` for builtin propositions like `=`, `>`, etc.

**Example:**
```litex
# Using $ prefix
$intelligent(Jordan)

# Using infix notation (when proposition takes two objects)
prop is_friend_of(x, y people)
know Jordan $is_friend_of Alice
```

### Outcomes of Statements

In Litex, every statement has one of four possible outcomes: **true, false, unknown, or error**. When you run the above code, Litex will print a message showing exactly how it verified the statement.

You'll see that `$intelligent(Jordan)` is established by applying the universal fact `forall x human => $intelligent(x)` to the specific case of `Jordan`. In this case, `forall x human => $intelligent(x)` is matched with `$intelligent(Jordan)`, and we can substitute `x` with `Jordan` in the universal fact to get `$intelligent(Jordan)`.

### Summary

- **Match and substitution** is the fundamental way Litex verifies statements
- Universal facts (`forall`) can generate infinitely many specific instances
- The `$` prefix distinguishes factual statements from functions
- Litex automatically matches patterns and substitutes values to verify statements
- This is the **classic example of match and substitution**—the most fundamental way people derive new facts

### Litex Syntax Reference

**Universal quantification**: `forall x set => fact` means "for all x in set, fact is true"

**Proposition declaration**: `prop propName(x set)` declares a proposition that can be applied to elements of a set

**Factual statement**: `$propName(object)` applies a proposition to a specific object

**Know keyword**: `know fact` establishes a fact as known/true

**Set declaration**: `have set_name nonempty_set` declares a non-empty set

**Object declaration**: `have object_name set_name` declares an object belonging to a set

### Exercises

1. Write Litex code to express: "All birds can fly. Tweety is a bird. Therefore, Tweety can fly."

2. Given the following code:
   ```litex
   have numbers nonempty_set, three numbers
   prop is_positive(x numbers)
   know forall x numbers => $is_positive(x)
   ```
   What statement would verify that `three` is positive?

3. Explain in your own words how match and substitution works in the following example:
   ```litex
   have animals nonempty_set, cat animals
   prop has_fur(x animals)
   know forall x animals => $has_fur(x)
   $has_fur(cat)
   ```

### Bonus: The Power of Abstraction

This simple mechanism—match and substitution—is incredibly powerful. It's the foundation of all mathematical reasoning. Once you understand this, you can see how:

- **Universal facts** (`forall`) allow us to make general statements
- **Specific facts** allow us to apply those general statements to concrete cases
- **Match and substitution** automatically connects the general to the specific

This is exactly how mathematicians think: they establish general principles, then apply them to specific situations. Litex just makes this process explicit and verifiable.

Keep this example in mind as you move to the next section. The same mechanism will appear everywhere in Litex!
