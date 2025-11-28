# Introduction

This folder explains **how Litex works internally**—specifically, how Litex implements its inference rules to derive new facts from known facts. While the Tutorial folder teaches you *how to use* Litex, this folder reveals *how Litex works* under the hood.

## What Are Inference Rules?

Inference rules are the mechanisms that allow Litex to derive new facts from existing ones. For example, if we know `a = b` and `b = c`, Litex can infer `a = c` through the transitivity of equality. These rules are the foundation of Litex's verification system.

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

---

_This folder is under active development. More documentation on other inference rules and mechanisms will be added over time._
