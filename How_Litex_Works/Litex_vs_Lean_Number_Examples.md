# Litex vs Lean: Number Examples

This document compares Litex and Lean in expressing number-related statements through side-by-side code examples. Numbers are fundamental to mathematics, and through arithmetic and number theory we can observe how different formal languages express everyday mathematical concepts.

Our goal is not to criticize Lean (which Litex team deeply respects), but to propose complementary ideas where Lean may be less intuitive, particularly in number theory. We explore alternative design choices that prioritize accessibility while maintaining rigor.

---

## Example 1: Prove that 1 + 1 = 2

**Task**: Prove the basic arithmetic fact that 1 + 1 = 2.

<table style="border-collapse: collapse; width: 100%;">
  <tr>
    <th style="border: 2px solid black; padding: 4px; text-align: left; width: 50%;">Litex</th>
    <th style="border: 2px solid black; padding: 4px; text-align: left; width: 50%;">Lean</th>
  </tr>
  <tr>
    <td style="border: 2px solid black; padding: 2px; line-height: 1.5; vertical-align: top;">
      <code>1 + 1 = 2</code>
    </td>
    <td style="border: 2px solid black; padding: 2px; line-height: 1.5; vertical-align: top;">
      <code>import Mathlib.Data.Nat.Basic</code><br><br>
      <code>example : 1 + 1 = 2 := by</code><br>
      <code>&nbsp;&nbsp;norm_num</code>
    </td>
  </tr>
</table>

Litex automatically verifies this basic arithmetic fact through its built-in arithmetic rules—no imports or proof tactics needed.

Lean requires importing a library and using a proof tactic (`norm_num`) even for this simplest of arithmetic facts.

```litex
1 + 1 = 2
```

---

## Example 2: Prove that forall a, b, c, d R: (a + b) * (c + d) / (a * c + b * d) = 1

**Task**: Prove that for all real numbers a, b, c, d, the expression `(a + b) * (c + d) / (a * c + b * d)` equals 1.

<table style="border-collapse: collapse; width: 100%;">
  <tr>
    <th style="border: 2px solid black; padding: 4px; text-align: left; width: 50%;">Litex</th>
    <th style="border: 2px solid black; padding: 4px; text-align: left; width: 50%;">Lean</th>
  </tr>
  <tr>
    <td style="border: 2px solid black; padding: 2px; line-height: 1.5; vertical-align: top;">
      <code>forall a, b, c, d R:</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;(a + b) * (c + d) / (a * c + b * d) = 1</code>
    </td>
    <td style="border: 2px solid black; padding: 2px; line-height: 1.5; vertical-align: top;">
      <code>import Mathlib.Data.Real.Basic</code><br><br>
      <code>example : forall a, b, c, d : ℝ, (a + b) * (c + d) / (a * c + b * d) = 1 := by</code><br>
      <code>&nbsp;&nbsp;intro a b c d</code><br>
      <code>&nbsp;&nbsp;field_simp</code>
    </td>
  </tr>
</table>

Litex directly expresses the universal statement, and the kernel automatically handles the algebraic verification.

Lean requires importing the real number library and using a field simplification tactic (`field_simp`), even though the statement is straightforward algebra. The concept of a "field" is typically only taught in university mathematics courses, which can be a barrier for ordinary users.

```litex
forall a, b, c, d R:
    (a + b) * (c + d) / (a * c + b * d) = 1
```

---

## Example 3: Proving Primality by Enumeration

**Task**: Define the property of being prime and prove that 97 is prime by checking that it is not divisible by any number from 2 to 96.

<table style="border-collapse: collapse; width: 100%;">
  <tr>
    <th style="border: 2px solid black; padding: 4px; text-align: left; width: 50%;">Litex</th>
    <th style="border: 2px solid black; padding: 4px; text-align: left; width: 50%;">Lean</th>
  </tr>
  <tr>
    <td style="border: 2px solid black; padding: 2px; line-height: 1.5; vertical-align: top;">
      <code>prop is_prime(x N_pos):</code><br>
      <code>&nbsp;&nbsp;dom:</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;x >= 2</code><br>
      <code>&nbsp;&nbsp;<=>:</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;forall y N_pos:</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;y >= 2</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;y < x</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;=>:</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;x % y != 0</code><br><br>
      <code>prove_for i $in range(2, 97):</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;97 % i != 0</code><br><br>
      <code>$is_prime(97)</code>
    </td>
    <td style="border: 2px solid black; padding: 2px; line-height: 1.5; vertical-align: top;">
      <code>import Mathlib.Data.Nat.Prime</code><br>
      <code>import Mathlib.Tactic</code><br><br>
      <code>-- Define primality property</code><br>
      <code>def is_prime (n : ℕ) : Prop :=</code><br>
      <code>&nbsp;&nbsp;2 ≤ n ∧ ∀ m : ℕ, 2 ≤ m → m < n → ¬(m ∣ n)</code><br><br>
      <code>-- Prove 97 is prime</code><br>
      <code>example : is_prime 97 := by</code><br>
      <code>&nbsp;&nbsp;constructor</code><br>
      <code>&nbsp;&nbsp;· norm_num  -- Prove 2 ≤ 97</code><br>
      <code>&nbsp;&nbsp;· intro m hm1 hm2</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;-- Need to prove that no m in [2, 96] divides 97</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;-- Using decide tactic to check all cases</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;decide</code><br><br>
      <code>-- Alternative: using Mathlib's built-in primality</code><br>
      <code>example : Nat.Prime 97 := by</code><br>
      <code>&nbsp;&nbsp;norm_num</code>
    </td>
  </tr>
</table>

Litex allows direct definition of the primality property using domain-restricted propositions, and `prove_for` makes it straightforward to verify primality by checking all potential divisors in a range. The syntax directly expresses the mathematical definition: a number is prime if it is at least 2 and has no divisors between 2 and itself. The verification process is explicit and transparent.

Lean requires defining primality as a proposition with explicit quantifiers and logical connectives. Proving primality by enumeration requires using specialized tactics like `decide` (which performs case-by-case checking but may not be transparent about the process) or relying on library functions. While Lean's `Nat.Prime` can be proven with `norm_num` for specific numbers, the underlying enumeration process is hidden from the user.

```litex
prop is_prime(x N_pos):
    dom:
        x >= 2
    <=>:
        forall y N_pos:
            y >= 2
            y < x
            =>:
                x % y != 0
        
prove_for i $in range(2, 97):
    97 % i != 0

$is_prime(97)
```

---

## Summary

Since Lean's kernel is built on type theory, it provides built-in functionality for type-theoretic concepts but requires manual implementation or library support for number-theoretic operations that are more naturally expressed in set theory. Litex, being built on set theory, can directly express number-theoretic concepts using familiar mathematical notation.

The examples above demonstrate that Litex's design allows for more direct expression of arithmetic and number-theoretic statements, with the kernel automatically handling verification. Lean's approach, while powerful and general, often requires understanding abstract concepts (like fields) and using specialized tactics that may not be immediately accessible to users without advanced mathematical training.
