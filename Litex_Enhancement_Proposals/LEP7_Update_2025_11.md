# Update 2025-11

## New Keywords

1. **`algo`**: Used to define and execute functions like in programming, with the key difference that each execution step is verified. See: https://litexlang.com/doc/Tutorial/Algorithm_Evaluation

2. **`prove_algo`**: Abstracts proof logic into reusable algorithms. When called with `by`, it executes the proof steps with different parameters using the same proof logic to obtain conclusions (i.e., the predicates in each statement of the proof remain unchanged, but the nouns are instantiated with the substituted parameters). See: https://litexlang.com/doc/Tutorial/Prove_Algo

3. **`import`**: Import files or packages. See: https://litexlang.com/doc/Tutorial/Import

## Major Features

1. **Definition-Computation Consistency Guarantee** (keyword: `algo`)
   - Ensures that function definitions and their computations are consistent
   - Documentation: https://litexlang.com/doc/Tutorial/Algorithm_Evaluation

2. **`prove_algo`** - Modular and Reusable Proof Process
   - Encapsulates proof processes containing condition checks, computation steps, and reasoning into reusable algorithms
   - When called with `by`, executes these steps and automatically obtains conclusions
   - Examples: proving a number is prime, computing equation roots, defining Lisp-like `cons` keyword in Litex
   - Documentation: https://litexlang.com/doc/Tutorial/Prove_Algo

3. **Cartesian Product** (finite and infinite) - `cart`, `cart_product`
   - Documentation: https://litexlang.com/doc/Tutorial/Set_Theory

4. **Multi-language Support**
   - Litex now supports Chinese, Greek, and other non-English characters as identifiers

5. **Litex from a Mathematical Perspective**
   - Documentation: https://litexlang.com/doc/Tutorial/Litex_From_A_Mathematical_Perspective
   - Aims to explain Litex's rigor and completeness from a mathematical standpoint

## Documentation Updates

- Refined Litex theoretical framework
- Partial formalization of high school mathematics textbooks in Litex

## Current Status

While software bugs may exist, Litex's functionality is approaching completeness from an engineering perspective. However, Litex currently lacks theoretical explanations of its rigor and completeness. We welcome discussions with interested researchers and practitioners.

We also welcome contributions to:
- Building Litex standard library
- Creating datasets
- Setting up AI pipelines

For more information, please contact us at litexlang@outlook.com

## Related Documentation

- How Litex verifies a fact: See `How_Litex_Works/How_Factual_Statements_Are_Checked.md` and `How_Litex_Works/How_Equality_Is_Checked.md`
