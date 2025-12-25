# Litex vs Lean: Basic Math Examples

_Nothing in biology makes sense except in the light of evolution._

_- Theodosius Dobzhansky_

<style>
/* Code block styling - bright pink for visibility */
table code {
  color: #ff00ff;
  padding: 2px 6px;
  font-family: 'Consolas', 'Monaco', 'Courier New', monospace;
  font-size: 0.9em;
  display: inline-block;
  line-height: 1.4;
  font-weight: 500;
}
</style>

---

This document compares Litex and Lean in expressing basic math statements through side-by-side code examples. All the examples below represent common categories of mathematical expressions, such as defining functions, basic arithmetic operations, proving existence, etc. 

On one hand, we hope readers can learn how to express everyday mathematics using Litex. While languages like Lean and Coq excel in library richness and the abstraction level of logical expression, Litex has advantages in simplicity of its keywords and syntax. Starting from simple examples, we can glimpse the fundamental units of more complex logic and imagine how the edifice of mathematics evolves.

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

## Example 2: Prove that forall a, b, c, d R: (a + b) * (c + d) / (a * c + a * d + b * c + b * d) = 1

**Task**: Prove that for all real numbers a, b, c, d, the expression `(a + b) * (c + d) / (a * c + a * d + b * c + b * d)` equals 1.

<table style="border-collapse: collapse; width: 100%;">
  <tr>
    <th style="border: 2px solid black; padding: 4px; text-align: left; width: 50%;">Litex</th>
    <th style="border: 2px solid black; padding: 4px; text-align: left; width: 50%;">Lean</th>
  </tr>
  <tr>
    <td style="border: 2px solid black; padding: 2px; line-height: 1.5; vertical-align: top;">
      <code>forall a, b, c, d R:</code><br>
      <code>&nbsp;&nbsp;dom:</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;a * c + b * d != 0</code><br>
      <code>&nbsp;&nbsp;=>:</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;(a + b) * (c + d) / (a * c + a * d + b * c + b * d) = 1</code>
    </td>
    <td style="border: 2px solid black; padding: 2px; line-height: 1.5; vertical-align: top;">
      <code>import Mathlib.Data.Real.Basic</code><br><br>
      <code>example : forall a, b, c, d : ℝ, (a + b) * (c + d) / (a * c + a * d + b * c + b * d) = 1 := by</code><br>
      <code>&nbsp;&nbsp;intro a b c d</code><br>
      <code>&nbsp;&nbsp;field_simp</code>
    </td>
  </tr>
</table>

Litex directly expresses the universal statement, and the kernel automatically handles the algebraic verification.

Lean requires importing the real number library and using a field simplification tactic (`field_simp`), even though the statement is straightforward algebra. The concept of a "field" is typically only taught in university mathematics courses, which can be a barrier for ordinary users.

```litex
forall a, b, c, d R:
    dom:
        a * c + a * d + b * c + b * d != 0
    =>:
        (a + b) * (c + d) / (a * c + a * d + b * c + b * d) = 1
```

---

## Example 3: Proving by Enumeration

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
      <code>prove_for i range(2, 97):</code><br>
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
    x >= 2
    <=>:
        forall y N_pos: y >= 2, y < x => x % y != 0
        
prove_for i range(2, 97):
    97 % i != 0

$is_prime(97)
```

## Example 4: Congruence Modulo

**Task**: Define the congruence relation (two numbers are congruent modulo n if they have the same remainder when divided by n) and prove that addition is commutative modulo any nonzero integer.

<table style="border-collapse: collapse; width: 100%;">
  <tr>
    <th style="border: 2px solid black; padding: 4px; text-align: left; width: 50%;">Litex</th>
    <th style="border: 2px solid black; padding: 4px; text-align: left; width: 50%;">Lean</th>
  </tr>
  <tr>
    <td style="border: 2px solid black; padding: 2px; line-height: 1.5; vertical-align: top;">
      <code>prop 同余(x, y, z Z):</code><br>
      <code>&nbsp;&nbsp;dom:</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;z != 0</code><br>
      <code>&nbsp;&nbsp;<=>:</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;x % z = y % z</code><br><br>
      <code>forall a, b, c Z:</code><br>
      <code>&nbsp;&nbsp;c != 0</code><br>
      <code>&nbsp;&nbsp;=>:</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;(a + b) % c = (b + a) % c</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;$同余(a+b, b+a, c)</code>
    </td>
    <td style="border: 2px solid black; padding: 2px; line-height: 1.5; vertical-align: top;">
      <code>import Mathlib.Data.Int.Basic</code><br>
      <code>import Mathlib.Data.ZMod.Basic</code><br><br>
      <code>-- Define congruence relation</code><br>
      <code>def 同余 (x y z : ℤ) : Prop :=</code><br>
      <code>&nbsp;&nbsp;z ≠ 0 → x % z = y % z</code><br><br>
      <code>-- Prove addition is commutative modulo</code><br>
      <code>example (a b c : ℤ) (hc : c ≠ 0) :</code><br>
      <code>&nbsp;&nbsp;(a + b) % c = (b + a) % c ∧ 同余 (a + b) (b + a) c := by</code><br>
      <code>&nbsp;&nbsp;constructor</code><br>
      <code>&nbsp;&nbsp;· -- Prove (a + b) % c = (b + a) % c</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;rw [Int.add_comm]</code><br>
      <code>&nbsp;&nbsp;· -- Prove congruence</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;intro h</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;rw [Int.add_comm]</code>
    </td>
  </tr>
</table>

Litex allows direct definition of the congruence relation using a domain-restricted proposition. The definition naturally expresses that two numbers are congruent modulo `z` if they have the same remainder when divided by `z`. Once defined, Litex automatically infers that `(a + b) % c = (b + a) % c` (by commutativity of addition) and that `$同余(a+b, b+a, c)` holds (by the definition of congruence).

Lean requires explicit definition of the congruence relation and manual proof construction. The proof must separately establish that `(a + b) % c = (b + a) % c` (using commutativity of addition) and that the congruence relation holds, even though these facts are closely related. The proof structure requires understanding of tactics like `rw` (rewrite) and `constructor` (for splitting conjunctions).

```litex
prop 同余(x, y, z Z):
    dom:
        z != 0
    <=>:
        x % z = y % z

forall a, b, c Z: c != 0 => (a + b) % c = (b + a) % c, $同余(a+b, b+a, c)
```

## Example 5: Euler's Conjecture Counterexample

**Task**: Define Euler's conjecture (that there are no solutions to `a^4 + b^4 + c^4 = d^4` for positive integers) and prove that it is false by providing a counterexample: `95800^4 + 217519^4 + 414560^4 = 422481^4`.

<table style="border-collapse: collapse; width: 100%;">
  <tr>
    <th style="border: 2px solid black; padding: 4px; text-align: left; width: 50%;">Litex</th>
    <th style="border: 2px solid black; padding: 4px; text-align: left; width: 50%;">Lean</th>
  </tr>
  <tr>
    <td style="border: 2px solid black; padding: 2px; line-height: 1.5; vertical-align: top;">
      <code>exist_prop a, b, c, d N_pos st Euler_conjecture():</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;a ^ 4 + b ^ 4 + c ^ 4 = d ^ 4</code><br><br>
      <code>exist 95800, 217519, 414560, 422481 st $Euler_conjecture()</code>
    </td>
    <td style="border: 2px solid black; padding: 2px; line-height: 1.5; vertical-align: top;">
      <code>import Mathlib.Data.Nat.Basic</code><br>
      <code>import Mathlib.Tactic</code><br><br>
      <code>-- Define Euler's conjecture property</code><br>
      <code>def Euler_conjecture (a b c d : ℕ) : Prop :=</code><br>
      <code>&nbsp;&nbsp;a > 0 ∧ b > 0 ∧ c > 0 ∧ d > 0 ∧</code><br>
      <code>&nbsp;&nbsp;a ^ 4 + b ^ 4 + c ^ 4 = d ^ 4</code><br><br>
      <code>-- Prove counterexample</code><br>
      <code>example : ∃ a b c d : ℕ, Euler_conjecture a b c d := by</code><br>
      <code>&nbsp;&nbsp;use 95800, 217519, 414560, 422481</code><br>
      <code>&nbsp;&nbsp;constructor</code><br>
      <code>&nbsp;&nbsp;· norm_num</code><br>
      <code>&nbsp;&nbsp;· constructor</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;· norm_num</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;· constructor</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;· norm_num</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;· constructor</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;· norm_num</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;· norm_num</code>
    </td>
  </tr>
</table>

Litex's `exist_prop` allows direct definition of an existential property with named variables, making it natural to express conjectures and their counterexamples. The `exist` statement with concrete values automatically verifies that the property holds for those values, providing a straightforward way to disprove conjectures.

Lean requires explicit definition of the property as a function returning a `Prop`, with all conditions (positivity of all variables and the equation) explicitly stated. Proving the existence requires using the `use` tactic to provide witnesses, then manually proving each condition using tactics like `norm_num`. The proof structure requires nested `constructor` calls to handle the conjunction of conditions, making it more verbose.

```litex
exist_prop a, b, c, d N_pos st Euler_conjecture():
    a ^ 4 + b ^ 4 + c ^ 4 = d ^ 4

exist 95800, 217519, 414560, 422481 st $Euler_conjecture()
```

## Example 6: Define function

**Task**: Define a function `f` that takes a real number `x` and an integer `y`, and returns `x * y`. Then verify that `f(1, 2) = 2`.

<table style="border-collapse: collapse; width: 100%;">
  <tr>
    <th style="border: 2px solid black; padding: 4px; text-align: left; width: 50%;">Litex</th>
    <th style="border: 2px solid black; padding: 4px; text-align: left; width: 50%;">Lean</th>
  </tr>
  <tr>
    <td style="border: 2px solid black; padding: 2px; line-height: 1.5; vertical-align: top;">
      <code>have fn f(x R, y Z) R = x * y</code><br><br>
      <code>f(1, 2) = 2</code>
    </td>
    <td style="border: 2px solid black; padding: 2px; line-height: 1.5; vertical-align: top;">
      <code>import Mathlib.Data.Real.Basic</code><br>
      <code>import Mathlib.Data.Int.Basic</code><br><br>
      <code>def f (x : ℝ) (y : ℤ) : ℝ := x * y</code><br><br>
      <code>example : f 1 2 = 2 := by</code><br>
      <code>&nbsp;&nbsp;simp [f]</code><br>
      <code>&nbsp;&nbsp;norm_num</code>
    </td>
  </tr>
</table>

Litex allows direct definition of functions with mixed types (real and integer) and automatically handles type conversions. The verification `f(1, 2) = 2` is straightforward and requires no explicit proof steps.

Lean requires explicit type annotations and manual handling of type conversions. When multiplying a real number with an integer, Lean automatically coerces the integer to a real number, but the proof still requires tactics like `simp` and `norm_num` to verify the equality.

```litex
have fn f(x R, y Z) R = x * y
f(1, 2) = 2
```

If you pass `f(1, 1.2) = 1.2`, then `1.2 $in Z` is not true, and Litex will report an error:

```
Function f requires its 2nd argument to satisfy the domain constraint:
1.2 $in Z
but verification failed
```

## Example 7: Proving Universal Statement by Enumeration

**Task**: Prove that every element in `{4, 17, 6.6}` is greater than every element in `{1, 2 * 0.2, 3.0}`.

<table style="border-collapse: collapse; width: 100%;">
  <tr>
    <th style="border: 2px solid black; padding: 4px; text-align: left; width: 50%;">Litex</th>
    <th style="border: 2px solid black; padding: 4px; text-align: left; width: 50%;">Lean</th>
  </tr>
  <tr>
    <td style="border: 2px solid black; padding: 2px; line-height: 1.5; vertical-align: top;">
      <code>prove_by_enum(x {4, 17, 6.6}, y {1, 2 * 0.2, 3.0}):</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;x > y</code>
    </td>
    <td style="border: 2px solid black; padding: 2px; line-height: 1.5; vertical-align: top;">
      <code>import Mathlib.Data.Real.Basic</code><br>
      <code>import Mathlib.Data.Finset.Basic</code><br>
      <code>import Mathlib.Tactic</code><br><br>
      <code>def set1 : Finset ℝ := {4, 17, 6.6}</code><br>
      <code>def set2 : Finset ℝ := {1, 2 * 0.2, 3.0}</code><br><br>
      <code>example : ∀ x ∈ set1, ∀ y ∈ set2, x > y := by</code><br>
      <code>&nbsp;&nbsp;intro x hx y hy</code><br>
      <code>&nbsp;&nbsp;simp [set1, set2] at hx hy</code><br>
      <code>&nbsp;&nbsp;rcases hx with (rfl|rfl|rfl)</code><br>
      <code>&nbsp;&nbsp;· rcases hy with (rfl|rfl|rfl) <;> norm_num</code><br>
      <code>&nbsp;&nbsp;· rcases hy with (rfl|rfl|rfl) <;> norm_num</code><br>
      <code>&nbsp;&nbsp;· rcases hy with (rfl|rfl|rfl) <;> norm_num</code>
    </td>
  </tr>
</table>

Litex's `prove_by_enum` directly expresses the universal statement over finite sets and automatically enumerates all cases to verify the property. The syntax is intuitive: for all `x` in the first set and all `y` in the second set, prove that `x > y`. Litex handles the enumeration and verification automatically.

Lean requires explicit definition of the finite sets, then manual case analysis using tactics like `rcases` to enumerate all possibilities. The proof must explicitly handle each combination of elements from the two sets, requiring nested `rcases` calls and multiple `norm_num` applications. While the proof is correct, it is verbose and requires understanding of tactics like `rcases` and `simp`.

```litex
prove_by_enum(x {4, 17, 6.6}, y {1, 2 * 0.2, 3.0}):
    x > y
```

---

## Example 8: Proving Universal Statement over Ranges with Domain Restrictions

**Task**: Prove that for all even numbers `i` in `range(1, 6)` and all odd numbers `j` in `closed_range(1, 5)`, the sum `i + j` is odd (i.e., `(i + j) % 2 = 1`). Then use this conclusion to prove equivalent universal statements.

<table style="border-collapse: collapse; width: 100%;">
  <tr>
    <th style="border: 2px solid black; padding: 4px; text-align: left; width: 50%;">Litex</th>
    <th style="border: 2px solid black; padding: 4px; text-align: left; width: 50%;">Lean</th>
  </tr>
  <tr>
    <td style="border: 2px solid black; padding: 2px; line-height: 1.5; vertical-align: top;">
      <code>prove_for i range(1, 6), j closed_range(1, 5):</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;dom:</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;i % 2 = 0</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;j % 2 = 1</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;=>:</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;(i + j) % 2 = 1</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;prove:</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;do_nothing</code><br><br>
    </td>
    <td style="border: 2px solid black; padding: 2px; line-height: 1.5; vertical-align: top;">
      <code>import Mathlib.Data.Int.Basic</code><br>
      <code>import Mathlib.Data.Finset.Basic</code><br>
      <code>import Mathlib.Tactic</code><br><br>
      <code>theorem even_plus_odd_mod_two_in_range :</code><br>
      <code>&nbsp;&nbsp;∀ i ∈ (Finset.Icc 1 5 : Finset ℤ), ∀ j ∈ (Finset.Icc 1 6 : Finset ℤ),</code><br>
      <code>&nbsp;&nbsp;i % 2 = 0 → j % 2 = 1 → (i + j) % 2 = 1 := by</code><br>
      <code>&nbsp;&nbsp;decide</code>
  </tr>
</table>

Litex's `prove_for` provides a natural way to express universal statements over ranges with domain restrictions. The syntax clearly separates the domain conditions (`dom:`) from the conclusion (`=>:`), and Litex automatically enumerates all valid cases (where domain conditions hold) to verify the property. The `prove:` section allows for additional proof steps if needed, but in this case `do_nothing` suffices as the property follows directly from arithmetic. After proving with `prove_for`, Litex automatically generates the equivalent universal statement, which can then be used directly or rewritten in different but equivalent forms.

Lean requires explicit quantification over finite sets (`Finset.Icc` for closed intervals) with all conditions stated in the premise. For finite cases, Lean's `decide` tactic can automatically verify the statement by exhaustive enumeration, which is concise but hides the enumeration process from the user. While `decide` is powerful for finite domains, it requires the domain to be explicitly finite (using `Finset`), and the enumeration process is not transparent. The equivalent statement using explicit conditions would require more verbose proof steps if not using `decide`.

```litex
prove_for i range(1, 6), j closed_range(1, 5):
    dom:
        i % 2 = 0
        j % 2 = 1
    =>:
        (i + j) % 2 = 1
    prove:
        do_nothing
```

---

## Summary

Since Lean's kernel is built on type theory, it provides built-in functionality for type-theoretic concepts but requires manual implementation or library support for number-theoretic operations that are more naturally expressed in set theory. Litex, being built on set theory, can directly express number-theoretic concepts using familiar mathematical notation.

The examples above demonstrate that Litex's design allows for more direct expression of arithmetic and number-theoretic statements, with the kernel automatically handling verification. Lean's approach, while powerful and general, often requires understanding abstract concepts (like fields) and using specialized tactics that may not be immediately accessible to users without advanced mathematical training.
