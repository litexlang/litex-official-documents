# Statements: The Building Blocks of Litex

_The highest form of pure thought is mathematics._

_— Plato_

---

## Section 1: Understanding Statement Outcomes

### Introduction

In this section, we'll explore what happens when you write a statement in Litex. Every statement produces an outcome, and understanding these outcomes is crucial for writing correct Litex code. By the end of this section, you'll know the three possible outcomes of statements and how to interpret them. Proofs in Litex are formed by creatively and accurately combining many, many statements together. Notice the statements can be highly abstract and very far from the real world.

### From Natural Language to Litex

In mathematics, when we write a statement, it can be:
- **True** (correct)
- **False** (incorrect)
- **Meaningless** (syntactically invalid)

In Litex, statements have three possible outcomes: **true, unknown, or error**.

### The Three Outcomes

**1. True** ✅

When your factual statement is proven true, or other types of statements are correctly executed, the result is **true**.

```litex
1 = 1 # true
let a R # Successfully declared a real number
```

**Natural Language**: "One equals one" → **Litex**: `1 = 1` → **Outcome**: `true`

**2. Unknown** ❓

If you enter a factual statement but the interpreter cannot find the corresponding known fact or built-in rule, it outputs **unknown**.

```litex
# The following code will output unknown
1 = 2
```

**Natural Language**: "One equals two" → **Litex**: `1 = 2` → **Outcome**: `unknown` (because it's false, and Litex doesn't have enough information to prove it false)

**3. Error** ❌

When you write an invalid sentence, such as operating on an undeclared object or entering a syntactically incorrect sentence, it results in an **error**.

```litex
# The following code will output error
You can checkout any time you like but you can never leave.
What the F**K are you talking about?
```

**Natural Language**: Random text → **Litex**: Invalid syntax → **Outcome**: `error`

### Common Mistakes

A very common mistake is writing just a number:

```litex
# The following code will output error
1
```

**Why?** `1` is not a statement. You can write `1 = 1` to make it a statement.

```litex
1 = 1  # This is a statement
```

**Natural Language**: "One equals one" → **Litex**: `1 = 1` → **Outcome**: `true`

### Different Types of Statements

Besides factual statements, which output true, unknown, or error, Litex also has other types of statements, such as:

- **Declaration of objects**: `have a R`
- **Definition of propositions**: `prop p(x R)`
- **Assertion of facts**: `know a > 0`

These statements are neither right nor wrong—they are not something to be proved. As long as they run properly, they output true; otherwise, they produce an error.

```litex
have a R # declaration of objects → true (if successful)
prop p(x R) # definition of propositions → true (if successful)
know a > 0 # assertion of facts → true (if successful)
```

### Understanding Statement Outputs

Notice that these three kinds of outputs are produced by the Litex kernel **to the outside world of Litex**. They are not passed along to other Litex statements. This is different from programming: in programming, a statement's output can often be used as the input of another statement (for example, in Python the result of `1 != 2` can be stored in a variable, and that variable can then be passed as a parameter to another statement).

**Natural Language Analogy**: When you read a mathematical statement, you register in your mind whether it's correct, incorrect, or ill-formed—rather than writing it down as an intermediate value for the next sentence to consume.

### What Happens When Things Go Wrong?

If an **unknown** or **error** occurs, the Litex kernel will terminate the current execution and notify you of the issue. If everything you wrote is correct, then the result is **success**!

**Example of error handling:**
```litex
let x R
x + y = 5  # Error: y is not declared
```

**Example of unknown:**
```litex
let x, y R
x > y  # Unknown: we don't know if x > y
```

### Summary

- Litex statements have three outcomes: **true**, **unknown**, or **error**
- **True**: Statement is verified or successfully executed
- **Unknown**: Statement cannot be verified (may be true or false, but insufficient information)
- **Error**: Statement is syntactically invalid or uses undeclared objects
- Statement outcomes are not passed to other statements (unlike programming languages)
- Errors and unknowns terminate execution and notify the user

### Litex Syntax Reference

**Factual statement**: Any statement that can be true or false (e.g., `1 = 1`, `x > 0`)

**Declaration statement**: Creates new objects, propositions, or facts (e.g., `have a R`, `prop p(x R)`, `know fact`)

**Outcome checking**: Litex automatically reports the outcome of each statement

**Error termination**: When an error or unknown occurs, execution stops

### Exercises

1. What is the outcome of the following statement? Why?
   ```litex
   2 + 2 = 4
   ```

2. What is the outcome of the following code? Why?
   ```litex
   let x R
   x = y
   ```

3. Explain the difference between `unknown` and `error` outcomes.

4. Why does `1` produce an error, but `1 = 1` produces true?

### Bonus: The Philosophy Behind Statement Outcomes

This design actually makes sense. When a human is reasoning about mathematics, they see a sentence, and the outcome of that sentence (whether it's correct, incorrect, or ill-formed) is registered in their mind—rather than being written down as an intermediate value for the next sentence to consume.

This is fundamentally different from programming languages, where statements often produce values that flow into other statements. In mathematics and Litex, statements are about establishing facts, not computing values. The outcome tells you whether the fact was established, but it doesn't become data for the next statement.

This design choice makes Litex closer to how humans actually think about mathematics, which is one of the reasons Litex feels so natural to use.

## Bonus: Difference between Mathematics and Programming

While programming and mathematics share some similarities in their thinking patterns, they are fundamentally different in their approach and purpose. Litex differs from general programming languages like Python because Litex is designed to mirror mathematical thinking—where we establish facts and verify truth, rather than compute values and control execution flow.

Here is a table that summarizes the differences between mathematics and programming:

| Feature | Mathematics | Programming |
|----------|--------------|-------------|
| **Variable** | No real “variable” — once an object is defined, its meaning is fixed | Variables can change values during execution |
| **Existential Quantification** | You have to prove the existence of an object before using it. | You can use and declare a variable directly. |
| **Function** | A symbol that builds new expressions from input symbols (no execution) | A block of executable code that performs computation or side effects |
| **Execution** | No execution — everything is symbolic manipulation or `match and substitution` | Involves actual computation steps and runtime behavior |
| **Control Flow** | Uses logical constructs like ∀ (for all) to reason about all cases | Uses constructs like `for`, `while`, `if` to control the flow of execution |
| **Iteration** | Infinite or large domains handled abstractly (e.g. by induction or logic) | Requires explicit loops and step-by-step computation |
| **Purpose** | To prove or verify truth symbolically | To perform tasks, process data, interact with systems |
