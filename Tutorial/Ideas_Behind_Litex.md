# Ideas Behind Litex

_三人行，必有我师焉。(There must be someone I can learn from among the three people I walk with.)_

_— 孔子 (Confucius)_

## Math is not a programming language, so is not Litex

_Mathematics is the language with which God has written the universe._

_— Galileo Galilei_

Before we officially introduce you to Litex, I hope you can keep in mind that reasoning (or generally, math) is not a programming language, so is not Litex. Generally, math is used to explain something, and programming is used to implement something. There are huge gaps between reasoning and programming.

| Feature              | Mathematics                                                                 | Programming                                                                    |
|----------------------|------------------------------------------------------------------------------|--------------------------------------------------------------------------------|
| **Variable**          | No real "variable" — once an object is defined, its meaning is fixed        | Variables can change values during execution                                   |
| **Existential Quantification** |  You have to prove the existence of an object before using it. | You can use and declare a variable directly. |
| **Function**          | A symbol that builds new expressions from input symbols (no execution)      | A block of executable code that performs computation or side effects           |
| **Execution**         | No execution — everything is symbolic manipulation or `match and substitution`           | Involves actual computation steps and runtime behavior                         |
| **Control Flow**      | Uses logical constructs like `∀` (for all) to reason about all cases (no execution flow)        | Uses constructs like `for`, `while`, `if` to control the flow of execution     |
| **Iteration**         | Infinite or large domains handled abstractly (e.g. by induction or logic)    | Requires explicit loops and step-by-step computation                           |
| **Purpose**           | To prove or verify truth symbolically                                        | To perform tasks, process data, interact with systems                          |

Litex, as a domain language, takes advantage of the difference between programming and verification, and is designed to be a simple and intuitive reasoning verifier. Technically, Litex is a "Read-Only Turing Machine". It does not have variables, execution, control flow, iteration, etc. Everything in Litex is built around the concept of `match and substitution`, which is exactly how we human reason.

**Litex’s syntax is simplified to such an extreme that it is nearly impossible for any language to be closer to mathematics.** Traditional formal languages (Lean, Coq, etc.), are programming languages, no different from Python. They may be easier than Python for expressing mathematics, but they are still too complex. Being a programming language sort of robbed you of the joy of exploring mathematics by forcing you to spend most of your time wrestling with the formal language itself. Litex brings that joy back!

## Everyday Math in Litex: Whatever everyday mathematics needs to express, Litex provides. No more, no less.

_Programs must be written for people to read, and only incidentally for machines to execute._

_— Abelson and Sussman, SICP, preface to the first edition_

Math is a difficult discipline. But the basic building blocks of forming a reasoning (or of math as a whole) are not actually complicated. For example, modern math is based on the ZFC axioms, which consist of only nine axioms. From these nine, we can derive the entire edifice of math we are familiar with. It is truly remarkable that such a vast structure can be built from so few tools. And precisely because these basic units of math are easy to understand, everyone—from elementary school students to professional mathematicians—possesses some fundamental reasoning ability.

The goal of Litex is to write reasoning (or math in general) as code. Since no matter how complex a piece of reasoning (or math) is, it is always built from a set of basic units, what Litex needs to do is simply provide these fundamental building blocks. Below is how everyday mathematical expressions correspond to their Litex formulations. Here is a summary of Litex keywords, refer to it from time to time when you are reading the tutorial.

---

### **Basics**

* Numbers (e.g. `0`, `-17.17`)
* Arithmetic (e.g. `1 + 1 = 2`)
* Basic facts (e.g. `1 > 0`， `1 $in R`, `1 + 1 = 2`)
* Sets (keywords: `set`, `nonempty_set`, `R` for real numbers, `N` for natural numbers, etc.)

---

### **Objects**

* Definitions of objects

  * Keyword: `have`, `let`
  * Example: `have a N = 1` defines a new object `a` in set `N` with value `1`

---

### **Facts**

* Defining propositions

  * Keywords: `prop`, `exist_prop`
  * Example: `prop larger_than(x, y) <=> x > y`
* Specific facts (e.g. `1 $in R`, `2 > 0`)
* Universal facts (e.g. `forall x N => x >= 0`)
* Existential facts (e.g. `exist 1 st $exist_in(R)`)

---

### **Functions**

* Function definitions

  * Keywords: `fn`, `have fn`
  * Example: `have fn f(x R) R = x`
* Function templates

  * Keyword: `fn_template`
  * Example: `fn_template sequence(s set): fn (n N) s` defines a series of objects which are all in set `s`

---

### **Special Proof Strategies**

* `prove_by_contradiction`
* `prove_in_each_case`
* `prove_by_induction`
* `prove_over_finite_set`

---

### **Others**

* Assumptions or declaring facts without proof

  * Keyword: `know`
* Claiming a fact

  * Keyword: `claim`
* Package management

  * Keyword: `import`
* Clearing all facts

  * Keyword: `clear`

---

Litex is a language that stays very close to the essence of mathematics and everyday mathematical reasoning. Each Litex keyword actually corresponds to a common mathematical expression; sometimes, you can even guess the purpose of a keyword without studying the Litex tutorial. This makes Litex more approachable to more people.