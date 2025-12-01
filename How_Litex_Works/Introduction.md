# Introduction

version: 2025-12-01

_Mathematics is the language with which God has written the universe._

_— Galileo Galilei_

---

This folder explains **how Litex works internally**—specifically, how Litex implements its inference rules to derive new facts from known facts. While the Tutorial folder teaches you *how to use* Litex, this folder reveals *how Litex works* under the hood.

## What Are Inference Rules?

Inference rules are the mechanisms that allow Litex to derive new facts from existing ones. For example, if we know `a = b` and `b = c`, Litex can infer `a = c` through the transitivity of equality. These rules are the foundation of Litex's verification system.

## What Are Axioms?

Axioms are the starting points of Litex's verification system. They are the most basic facts that are assumed to be true without proof. For example, the axiom of equality is `a = a` for all `a`.

## Axioms + Inference Rules = Mathematical World

With 1. axioms, i.e. facts we assume to be true, and 2. inference rules, i.e. a mechanism to derive new facts from existing ones, we can build a whole mathematical world. Litex implements these axioms and inference rules to verify mathematical statements.

Great news: when a factual statement is verified, litex prints out how the fact is verified. So you can know exactly how the fact is verified. This can be very helpful when you are debugging your proofs. AIs can also use this to improve their proof writing capabilities.

## What This Folder Covers

This folder documents:

1. **How Litex derives new facts**: The step-by-step process of how Litex takes known facts and uses inference rules to verify new statements
2. **Implementation details**: How these inference rules are implemented in code, including data structures and algorithms
3. **Core mechanisms**: The fundamental operations that make Litex's verification system work

## Current Contents

- **How Equality Is Checked**: Explains how Litex verifies equality statements, including the equivalence set data structure and the multi-step verification process

## Why This Matters

Understanding how Litex works internally helps you:

- **Write more efficient code**: Knowing how Litex verifies statements helps you structure your proofs more effectively
- **Debug verification failures**: When a statement fails to verify, understanding the internal mechanism helps identify why
- **Appreciate the design**: See how mathematical principles translate into code implementation

## Litex's Fundamental Difference from Programming Languages

**⚠️ Important**: It's crucial to understand that **Litex works fundamentally differently from programming languages**:

1. **Litex is not for execution**: Unlike programming languages that execute code to perform computations, Litex is designed for **reasoning and verification**. It doesn't compute values—it verifies mathematical statements.

2. **Litex is not for calculating**: You don't write Litex code to calculate a number or produce a result. Instead, you write Litex code to **establish and verify facts**.

3. **Every statement has three possible outcomes**:
   - **`true`**: The statement is verified or successfully executed
   - **`error`**: The statement is syntactically invalid or uses undeclared objects
   - **`unknown`**: The statement cannot be verified. This means either:
     - The statement is false (but Litex doesn't have enough information to prove it false), or
     - The current knowledge is insufficient to determine the truth value

4. **No value flow**: Unlike programming languages where function return values flow into other computations, Litex statement outcomes are **observed but never passed along** to other statements. Each statement stands alone in establishing facts.

**The core purpose of Litex**: To verify mathematical reasoning, not to compute values. Every statement you write is about establishing whether something is true, not about calculating what something equals.

In short, just like how a calculator executes a mathematical formula based on a given set of rules and prints the result, litex executes your statements based on the given axioms and inference rules and prints the result: true, unknown, or error. When a factual statement is verified, it also prints out how the fact is verified.

Litex can not write proof for you, it just helps you verify the correctness of your own proofs. 