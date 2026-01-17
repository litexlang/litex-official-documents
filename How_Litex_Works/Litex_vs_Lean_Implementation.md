# Litex vs Lean Implementation

Lean compiles to an intermediate representation. The value of this intermediate representation lies in its simplicity: it is straightforward to verify, design, and implement executors that can completely ensure the correctness of statements.

However, this also results in Lean's very slow execution. Each time Mathlib is imported, a substantial amount of content must be compiled.

Litex's method of verifying facts is essentially a sophisticated version of Ctrl+F: it matches target facts against known facts, and if a match succeeds, the target fact is considered established. This approach achieves extremely high runtime efficiency—typically, Litex completes execution while Lean is still compiling.

Litex's compiler-independent working principle also makes it easier to integrate and interact with other system tools, such as LLMs.