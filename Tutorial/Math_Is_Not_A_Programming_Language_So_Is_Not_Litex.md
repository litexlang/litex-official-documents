## Math is not a programming language, so is not Litex

Before we officially introduce you to Litex, I hope you can keep in mind that reasoning (or generally, math) is not a programming language, so is not Litex. There are huge gaps between reasoning and programming.

| Feature              | Mathematics                                                                 | Programming                                                                    |
|----------------------|------------------------------------------------------------------------------|--------------------------------------------------------------------------------|
| **Variable**          | No real "variable" — once an object is defined, its meaning is fixed        | Variables can change values during execution                                   |
| **Existential Quantification** |  You have to prove the existence of an object before using it. | You can use and declare a variable directly. |
| **Function**          | A symbol that builds new expressions from input symbols (no execution)      | A block of executable code that performs computation or side effects           |
| **Execution**         | No execution — everything is symbolic manipulation or `match and substitution`           | Involves actual computation steps and runtime behavior                         |
| **Control Flow**      | Uses logical constructs like `∀` (for all) to reason about all cases         | Uses constructs like `for`, `while`, `if` to control the flow of execution     |
| **Iteration**         | Infinite or large domains handled abstractly (e.g. by induction or logic)    | Requires explicit loops and step-by-step computation                           |
| **Purpose**           | To prove or verify truth symbolically                                        | To perform tasks, process data, interact with systems                          |

Litex, as a domain language, takes advantage of the difference between programming and verification, and is designed to be a simple and intuitive reasoning verifier. Technically, Litex is a "Read-Only Turing Machine". It does not have variables, execution, control flow, iteration, etc. Everything in Litex is built around the concept of `match and substitution`, which is exactly how we human reason. 

**Litex’s syntax is simplified to such an extreme that it is nearly impossible for any language to be closer to mathematics.** Traditional formal languages (Lean, Coq, etc.), are programming languages, no different from Python. They may be easier than Python for expressing mathematics, but they are still too complex. Being a programming language sort of robbed you of the joy of exploring mathematics by forcing you to spend most of your time wrestling with the formal language itself. Litex brings that joy back!
