# Litex vs Lean: Number Examples

# Example 1: Prove that 1 + 1 = 2

## Litex Solution

```litex
1 + 1 = 2
```

Litex automatically verifies this basic arithmetic fact through its built-in arithmetic rules—no imports or proof tactics needed.

## Lean Solution

```lean
import Mathlib.Data.Nat.Basic

example : 1 + 1 = 2 := by
  norm_num
```

Lean requires importing a library and using a proof tactic (`norm_num`) even for this simplest of arithmetic facts.

## Example 2: Prove that the integers greater than or equal to 5 and less than 8 are exactly 5, 6, and 7

## Litex Solution

```litex
prove_for i $in range(5, 8):
    i = 5 or i = 6 or i = 7

forall i Z: i = 5 or i = 6 or i = 7 => i >= 5, i < 8
```

First, we prove that if `i $in range(5, 8)`, then `i = 5 or i = 6 or i = 7`.
Second, we prove that if `i = 5 or i = 6 or i = 7`, then `i $in range(5, 8)`.

Litex's `prove_for` makes range-based proofs straightforward and explicit, directly expressing the mathematical intent.

## Lean Solution

```lean
import Mathlib.Tactic

example : {n : ℕ | n ≥ 5 ∧ n < 8} = ({5, 6, 7} : Finset ℕ) := by
  ext n
  constructor
  · intro hn
    have h1 : n ≥ 5 := hn.1
    have h2 : n < 8 := hn.2
    -- Since n < 8 and n ≥ 5, n can only be 5, 6, or 7
    interval_cases n <;> simp
  · intro hn
    have : n = 5 ∨ n = 6 ∨ n = 7 := by simpa [Finset.mem_insert, Finset.mem_singleton] using hn
    rcases this with (rfl|rfl|rfl) <;> refine ⟨by norm_num, by norm_num⟩
```

Lean requires explicit set equality proof with multiple tactics, case analysis, and manual construction of intermediate facts. This is because Lean's foundational axioms are based on type theory, and set theory is merely a consequence derived from type theory. 

Since Lean's kernel can only provide built-in functionality for type theory (its foundation), it cannot provide built-in functionality for set theory. Consequently, users must manually implement set-theoretic operations and proofs. 

# Example 3: Prove that forall a, b, c, d R: (a + b) * (c + d) / (a * c + b * d) = 1

## Litex Solution

```litex
forall a, b, c, d R:
    (a + b) * (c + d) / (a * c + b * d) = 1
```

Litex directly expresses the universal statement, and the kernel automatically handles the algebraic verification.

## Lean Solution

```lean
import Mathlib.Data.Real.Basic

example : forall a, b, c, d : ℝ, (a + b) * (c + d) / (a * c + b * d) = 1 := by
  intro a b c d
  field_simp
```

Lean requires importing the real number library and using a field simplification tactic, even though the statement is straightforward algebra.