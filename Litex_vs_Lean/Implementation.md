# Litex vs Lean Implementation

Lean compiles to an intermediate representation. The value of this intermediate representation lies in its simplicity: it is straightforward to verify, design, and implement executors that can completely ensure the correctness of statements.

However, this also results in Lean's very slow execution. Each time Mathlib is imported, a substantial amount of content must be compiled.

Litex's method of verifying facts is essentially a sophisticated version of Ctrl+F: it matches target facts against known facts, and if a match succeeds, the target fact is considered established. This approach achieves extremely high runtime efficiency—typically, Litex completes execution while Lean is still compiling.

Litex's compiler-independent working principle also makes it easier to integrate and interact with other system tools, such as LLMs.

Mathematics has many different axiomatic systems, and choosing different foundational axiom systems as the basis for a formal language results in vastly different user experiences. Lean chooses type theory as its foundation, while Litex chooses set theory.

This design makes Lean easier to maintain and theoretically more general, which experts prefer. Litex's design, on the other hand, is more intuitive and easier to learn, built on familiar set theory, aims to democratize formal mathematics while maintaining rigor, even for 10-year-olds. Think of Litex as the Python of formal languages.

Litex achieves its simplicity by imitating how people reason and how mathematics works. Litex is based on set theory. It searches for known facts mechanically and effectively to prove new facts for you. The user no longer has to memorize and recall known facts and inference rules by hand. Each Litex statement has and only has some of the following 4 effects: *define, verify, memorize and infer*, which is printed out in the output, making the user easy to know how the proof process works.

```litex
have a R = 17 # define a new object a in the set R, and equal to 17
prop p(x, y R) # define a proposition

1 + 3 = 4 # verify the correctness of the statement. If it's verified, it is memorized.
forall a, b R: (a+b)^2 = a^2 + 2*a*b + b^2 # verify a forall 
```

# How Litex verifies statements

Among the 4 effects, verification is the most important one. Litex uses `match and substitution` to use `forall` facts to verify the correctness of the statements. It's impossible to explain how it works in a few words. So we put an example here. When `forall x human => $intelligent(x)` is already stored in memory and `Jordan $in human` is also stored in memory, when the users type `$intelligent(Jordan)`, Litex will substitute `Jordan` with `x` in the statement `forall x human => $intelligent(x)` and check if the statement is true. If it is, the statement is verified.

Think of this: when the user inputs a fact with proposition name `intelligent`, Litex will search all known facts with proposition name `intelligent` (including `forall` facts like `forall x human => $intelligent(x)` and specific facts like `$intelligent(Jordan)`) and check if the given fact matches the known fact. If matched, then it is correct. 

It works like `ctrl+f` in your browser, which mimics how our brain works when verifying a fact. Unlike Lean, which compiles your statements to an intermediate representation, Litex verifies statements directly.