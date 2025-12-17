# Litex vs Lean: Set Theory Examples

This document compares Litex and Lean in expressing set-theoretic statements through side-by-side code examples. Set is *the most basic concept in mathematics*, and through sets we can observe the similarities and differences in how different formal languages express everyday mathematical concepts, sharing their distinctive characteristics.

Our goal is not to criticize Lean (which Litex team deeply respects), but to propose complementary ideas where Lean may be less intuitive, particularly in set theory. We explore alternative design choices that prioritize accessibility while maintaining rigor.

---

## Example 1: Simple Set Membership Proof

**Task**: Prove that `1` is an element of the set `{1, 2}`.

<table style="border-collapse: collapse; width: 100%;">
  <tr>
    <th style="border: 2px solid black; padding: 4px; text-align: left; width: 50%;">Litex</th>
    <th style="border: 2px solid black; padding: 4px; text-align: left; width: 50%;">Lean</th>
  </tr>
  <tr>
    <td style="border: 2px solid black; padding: 2px; line-height: 1.5; vertical-align: top;">
      <code>1 $in {1, 2}</code>
    </td>
    <td style="border: 2px solid black; padding: 2px; line-height: 1.5; vertical-align: top;">
      <code>import Mathlib.Data.Finset.Basic</code><br><br>
      <code>-- Define the set</code><br>
      <code>def my_set : Finset ℕ := {1, 2}</code><br><br>
      <code>-- Prove membership</code><br>
      <code>example : 1 ∈ my_set := by</code><br>
      <code>&nbsp;&nbsp;simp [my_set]</code><br>
      <code>&nbsp;&nbsp;-- or more explicitly:</code><br>
      <code>&nbsp;&nbsp;-- rw [Finset.mem_insert]</code><br>
      <code>&nbsp;&nbsp;-- simp</code>
    </td>
  </tr>
</table>

Litex's design allows automatic verification of set membership in a single line, directly expressing the mathematical statement without requiring additional setup.

Lean requires explicit set definition and proof tactics. The `simp` tactic can simplify the proof, but the setup (imports, type annotations, and proof structure) is more verbose.

```litex
1 $in {1, 2}
```

---

## Example 2: Sets Containing Sets

**Task**: Define a set containing sets as elements: `{{}, {1, 2}}`, and prove that `{1, 2}` is an element of this set.

<table style="border-collapse: collapse; width: 100%;">
  <tr>
    <th style="border: 2px solid black; padding: 4px; text-align: left; width: 50%;">Litex</th>
    <th style="border: 2px solid black; padding: 4px; text-align: left; width: 50%;">Lean</th>
  </tr>
  <tr>
    <td style="border: 2px solid black; padding: 2px; line-height: 1.5; vertical-align: top;">
      <code>{1, 2} $in {{}, {1, 2}}</code>
    </td>
    <td style="border: 2px solid black; padding: 2px; line-height: 1.5; vertical-align: top;">
      <code>import Mathlib.Data.Finset.Basic</code><br><br>
      <code>-- Lean requires explicit types, making this awkward</code><br>
      <code>-- You need to use a structure to represent sets of sets</code><br>
      <code>structure MySet where</code><br>
      <code>&nbsp;&nbsp;val : Finset ℕ</code><br><br>
      <code>def my_set_of_sets : Finset MySet := {</code><br>
      <code>&nbsp;&nbsp;MySet.mk ({} : Finset ℕ),</code><br>
      <code>&nbsp;&nbsp;MySet.mk ({1, 2} : Finset ℕ)</code><br>
      <code>}</code><br><br>
      <code>-- To prove membership, you need to construct the set element explicitly</code><br>
      <code>example : MySet.mk ({1, 2} : Finset ℕ) ∈ my_set_of_sets := by</code><br>
      <code>&nbsp;&nbsp;simp [my_set_of_sets]</code><br>
      <code>&nbsp;&nbsp;-- Requires explicit construction and proof steps</code><br>
      <code>&nbsp;&nbsp;-- Or use a more complex type hierarchy</code>
    </td>
  </tr>
</table>


Litex's set-theoretic foundation naturally supports sets containing sets as elements, reflecting the mathematical principle that sets are objects.

Lean requires explicit type structures (like `MySet`) to represent sets of sets, as its type system needs explicit type annotations. This adds boilerplate but provides type safety.

```litex
{1, 2} $in {{}, {1, 2}}
```

---

## Example 3: Disjunction from Set Membership

**Task**: If `x` is an element of `{1, 2}`, then `x = 1` or `x = 2`.

<table style="border-collapse: collapse; width: 100%;">
  <tr>
    <th style="border: 2px solid black; padding: 4px; text-align: left; width: 50%;">Litex</th>
    <th style="border: 2px solid black; padding: 4px; text-align: left; width: 50%;">Lean</th>
  </tr>
  <tr>
    <td style="border: 2px solid black; padding: 2px; line-height: 1.5; vertical-align: top;">
      <code>have x {1, 2}</code><br>
      <code>x = 1 or x = 2</code>
    </td>
    <td style="border: 2px solid black; padding: 2px; line-height: 1.5; vertical-align: top;">
      <code>import Mathlib.Data.Finset.Basic</code><br><br>
      <code>variable (x : ℕ)</code><br><br>
      <code>example (h : x ∈ ({1, 2} : Finset ℕ)) : x = 1 ∨ x = 2 := by</code><br>
      <code>&nbsp;&nbsp;simp [Finset.mem_insert, Finset.mem_singleton] at h</code><br>
      <code>&nbsp;&nbsp;cases h with</code><br>
      <code>&nbsp;&nbsp;| inl h1 => left; exact h1</code><br>
      <code>&nbsp;&nbsp;| inr h2 => right; exact h2</code>
    </td>
  </tr>
</table>

Litex automatically derives disjunctions from set membership, recognizing that membership in a finite enumerated set implies equality to one of its elements.

Lean requires explicit proof steps using tactics like `simp`, `cases`, or `tauto` to derive the disjunction from set membership. The proof structure is more explicit but requires more manual steps.

```litex
have x {1, 2}
x = 1 or x = 2
```
---

## Example 4: Properties from Set Builder Membership

**Task**: If `x` is an element of `{y R: y > 0}`, then `x > 0`.

<table style="border-collapse: collapse; width: 100%;">
  <tr>
    <th style="border: 2px solid black; padding: 4px; text-align: left; width: 50%;">Litex</th>
    <th style="border: 2px solid black; padding: 4px; text-align: left; width: 50%;">Lean</th>
  </tr>
  <tr>
    <td style="border: 2px solid black; padding: 2px; line-height: 1.5; vertical-align: top;">
      <code>forall x {y R: y > 0}:</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;x > 0</code>
    </td>
    <td style="border: 2px solid black; padding: 2px; line-height: 1.5; vertical-align: top;">
      <code>import Mathlib.Data.Set.Basic</code><br><br>
      <code>variable (x : ℝ)</code><br><br>
      <code>example (h : x ∈ {y : ℝ | y > 0}) : x > 0 := by</code><br>
      <code>&nbsp;&nbsp;simp [Set.mem_setOf_eq] at h</code><br>
      <code>&nbsp;&nbsp;exact h</code>
    </td>
  </tr>
</table>

Litex automatically derives properties from Set Builder membership, recognizing that membership in a set defined by a condition implies that condition—a fundamental mathematical pattern.

Lean requires explicit rewriting with `Set.mem_setOf_eq` to extract the condition from set membership. The proof is straightforward but requires manual application of the membership definition.

```litex
forall x {y R: y > 0}:
    x > 0
```

---
## Example 5: Proving Set Inequality by Cardinality

**Task**: Prove that `{1, 2, 3} ≠ {1, 2}` by showing that `{1, 2, 3}` has 3 elements while `{1, 2}` has 2 elements.

<table style="border-collapse: collapse; width: 100%;">
  <tr>
    <th style="border: 2px solid black; padding: 4px; text-align: left; width: 50%;">Litex</th>
    <th style="border: 2px solid black; padding: 4px; text-align: left; width: 50%;">Lean</th>
  </tr>
  <tr>
    <td style="border: 2px solid black; padding: 2px; line-height: 1.5; vertical-align: top;">
      <code>prove_by_contradiction {1,2,3} != {1,2}:</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;count({1,2,3}) = 3</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;count({1,2}) = 2</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;count({1,2,3}) = count({1,2})</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;3 = 2</code>
    </td>
    <td style="border: 2px solid black; padding: 2px; line-height: 1.5; vertical-align: top;">
      <code>import Mathlib.Data.Finset.Basic</code><br><br>
      <code>example : ({1, 2, 3} : Finset ℕ) ≠ ({1, 2} : Finset ℕ) := by</code><br>
      <code>&nbsp;&nbsp;intro h</code><br>
      <code>&nbsp;&nbsp;have h1 : ({1, 2, 3} : Finset ℕ).card = 3 := by simp</code><br>
      <code>&nbsp;&nbsp;have h2 : ({1, 2} : Finset ℕ).card = 2 := by simp</code><br>
      <code>&nbsp;&nbsp;rw [h] at h1</code><br>
      <code>&nbsp;&nbsp;rw [h2] at h1</code><br>
      <code>&nbsp;&nbsp;norm_num at h1</code>
    </td>
  </tr>
</table>

Litex's built-in cardinality operations and proof by contradiction mechanism make this type of proof straightforward and intuitive.

Lean requires explicit cardinality computation using `.card` and manual proof by contradiction. The proof structure is clear but requires more steps to establish the contradiction.

```litex
prove_by_contradiction {1,2,3} != {1,2}:
    count({1,2,3}) = 3
    count({1,2}) = 2
    count({1,2,3}) = count({1,2})
    3 = 2
```

---
## Example 6: Sets Cannot Contain Duplicate Elements

**Task**: Demonstrate that sets cannot contain duplicate elements. The statement `{1, 1} = {1, 1}` may seem correct, but it is actually problematic because a set cannot contain the same element twice.

<table style="border-collapse: collapse; width: 100%;">
  <tr>
    <th style="border: 2px solid black; padding: 4px; text-align: left; width: 50%;">Litex</th>
    <th style="border: 2px solid black; padding: 4px; text-align: left; width: 50%;">Lean</th>
  </tr>
  <tr>
    <td style="border: 2px solid black; padding: 2px; line-height: 1.5; vertical-align: top;">
      <code># have a N</code><br>
      <code># {a, 1} = {a, 1}</code>
    </td>
    <td style="border: 2px solid black; padding: 2px; line-height: 1.5; vertical-align: top;">
      <code>import Mathlib</code><br><br>
      <code>variable (a : ℕ)  -- Assume a is a variable of type ℕ</code><br><br>
      <code>-- This still causes an error! Because Lean cannot infer what {} is</code><br>
      <code>-- example : ({a, 1} : Set ℕ) = ({a, 1} : Set ℕ) := rfl</code><br>
      <code>-- Error: ambiguous overload, possible interpretations: ...</code><br><br>
      <code>-- This also causes an error</code><br>
      <code>-- example : {a, 1} = {a, 1} := rfl</code>
    </td>
  </tr>
</table>

Litex detects the issue when it cannot verify that set elements are distinct (e.g., when `a ≠ 1` is unknown), providing a clear error message that explains the mathematical principle that sets are collections of distinct elements.

Lean encounters type inference issues when dealing with sets containing variables, making it difficult to express this scenario. `Finset` enforces distinctness at the type level, but type inference can be problematic with variables.

```litex
# This example demonstrates an error case
# have a N
# {a, 1} = {a, 1} 
# Error: parameters in set must be different from one another, inequality of a and 1 in {a, 1} is unknown
```

## Example 7: Proving Set Equality by Range Enumeration

**Task**: Prove that the integers greater than or equal to 5 and less than 8 are exactly 5, 6, and 7.

The proof proceeds in two steps:
1. First, we prove that if `i $in range(5, 8)`, then `i = 5 or i = 6 or i = 7` using `prove_for`.
2. Second, we prove that if `i = 5 or i = 6 or i = 7`, then `i $in range(5, 8)` (i.e., `i >= 5` and `i < 8`).

<table style="border-collapse: collapse; width: 100%;">
  <tr>
    <th style="border: 2px solid black; padding: 4px; text-align: left; width: 50%;">Litex</th>
    <th style="border: 2px solid black; padding: 4px; text-align: left; width: 50%;">Lean</th>
  </tr>
  <tr>
    <td style="border: 2px solid black; padding: 2px; line-height: 1.5; vertical-align: top;">
      <code>prove_for i $in range(5, 8):</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;i = 5 or i = 6 or i = 7</code><br><br>
      <code>prove forall x Z: x = 5 or x = 6 or x = 7 => x >= 5, x < 8:</code><br>
      <code>&nbsp;&nbsp;prove_case_by_case:</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;=>:</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;x >= 5</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;x < 8</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;case x = 5:</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;do_nothing</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;case x = 6:</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;do_nothing</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;case x = 7:</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;do_nothing</code>
    </td>
    <td style="border: 2px solid black; padding: 2px; line-height: 1.5; vertical-align: top;">
      <code>import Mathlib.Tactic</code><br><br>
      <code>example : {n : ℕ | n ≥ 5 ∧ n < 8} = ({5, 6, 7} : Finset ℕ) := by</code><br>
      <code>&nbsp;&nbsp;ext n</code><br>
      <code>&nbsp;&nbsp;constructor</code><br>
      <code>&nbsp;&nbsp;· intro hn</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;have h1 : n ≥ 5 := hn.1</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;have h2 : n < 8 := hn.2</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;interval_cases n <;> simp</code><br>
      <code>&nbsp;&nbsp;· intro hn</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;have : n = 5 ∨ n = 6 ∨ n = 7 := by simpa [Finset.mem_insert, Finset.mem_singleton] using hn</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;rcases this with (rfl|rfl|rfl)</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;· exact ⟨by norm_num, by norm_num⟩</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;· exact ⟨by norm_num, by norm_num⟩</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;· exact ⟨by norm_num, by norm_num⟩</code>
    </td>
  </tr>
</table> 

Litex's `prove_for` provides a direct, intuitive way to prove range-based set equalities, making the mathematical intent explicit through iterative verification.

Lean requires explicit set extensionality (`ext`) and case analysis (`interval_cases`, `rcases`) to prove range-based set equalities. The proof is rigorous but requires more manual construction of the cases.

```litex
prove_for i $in range(5, 8):
    i = 5 or i = 6 or i = 7

prove forall x Z: x = 5 or x = 6 or x = 7 => x >= 5, x < 8:
    prove_case_by_case:
        =>:
            x >= 5
            x < 8
        case x = 5:
            do_nothing
        case x = 6:
            do_nothing
        case x = 7:
            do_nothing
```

---
## Example 8: Set Inclusion Transitivity

**Task**: Demonstrate that an object belonging to one set automatically belongs to other sets through set inclusion. If `A ⊆ B` and `B ⊆ C`, then any element `x` in `A` also belongs to both `B` and `C`.

<table style="border-collapse: collapse; width: 100%;">
  <tr>
    <th style="border: 2px solid black; padding: 4px; text-align: left; width: 50%;">Litex</th>
    <th style="border: 2px solid black; padding: 4px; text-align: left; width: 50%;">Lean</th>
  </tr>
  <tr>
    <td style="border: 2px solid black; padding: 2px; line-height: 1.5; vertical-align: top;">
      <code>have a, b, c nonempty_set</code><br>
      <code>know forall x a => x $in b</code><br>
      <code>know forall x b => x $in c</code><br><br>
      <code>have x a</code><br>
      <code>x $in b</code><br>
      <code>x $in c</code>
    </td>
    <td style="border: 2px solid black; padding: 2px; line-height: 1.5; vertical-align: top;">
      <code>import Mathlib</code><br><br>
      <code>variable {α : Type*}  -- Arbitrary type</code><br>
      <code>variable (A B C : Set α)  -- Three sets</code><br><br>
      <code>-- Premises</code><br>
      <code>variable (hA_nonempty : Set.Nonempty A)  -- A is nonempty</code><br>
      <code>variable (hAB : ∀ x, x ∈ A → x ∈ B)      -- ∀x∈A, x∈B (i.e., A ⊆ B)</code><br>
      <code>variable (hBC : ∀ x, x ∈ B → x ∈ C)      -- ∀x∈B, x∈C (i.e., B ⊆ C)</code><br><br>
      <code>-- Conclusion</code><br>
      <code>example (x : α) (hx : x ∈ A) : x ∈ C := by</code><br>
      <code>&nbsp;&nbsp;-- Since x ∈ A, we have x ∈ B</code><br>
      <code>&nbsp;&nbsp;have hxB : x ∈ B := hAB x hx</code><br>
      <code>&nbsp;&nbsp;-- Since x ∈ B, we have x ∈ C</code><br>
      <code>&nbsp;&nbsp;exact hBC x hxB</code>
    </td>
  </tr>
</table>

Litex automatically handles transitive set membership through its built-in reasoning, recognizing the logical chain from set inclusion facts.

Lean requires explicit application of the inclusion hypotheses and manual construction of intermediate facts. The proof structure is clear but requires explicit steps for each logical inference.

```litex
have a, b, c nonempty_set
know forall x a => x $in b
know forall x b => x $in c

have x a
x $in b
x $in c
```

---

## Example 9: Membership in Set Builders with Domain-Restricted Propositions

**Task**: Prove that `17` belongs to the set `{x N: x % 17 = 0, $p(x)}` where `p` is a proposition with domain restriction `{z Z: z < 100}`, and `p` is derived from another proposition `q` with domain `{y Q: y > 0}` through a universal rule.

This example demonstrates how Litex and Lean handle propositions with domain restrictions (subsets as domains) and the complexity of type conversions between different number systems.

<table style="border-collapse: collapse; width: 100%;">
  <tr>
    <th style="border: 2px solid black; padding: 4px; text-align: left; width: 50%;">Litex</th>
    <th style="border: 2px solid black; padding: 4px; text-align: left; width: 50%;">Lean</th>
  </tr>
  <tr>
    <td style="border: 2px solid black; padding: 2px; line-height: 1.5; vertical-align: top;">
      <code>have a R = 17</code><br>
      <code>prop p(x {z Z: z < 100})</code><br>
      <code>prop q(x {y Q: y > 0})</code><br>
      <code>know $q(17)</code><br>
      <code>know forall x Z: x $in {y Z: y < 20, $q(y)} => $p(x)</code><br>
      <code>a $in {x N: x % 17 = 0, $p(x)}</code>
    </td>
    <td style="border: 2px solid black; padding: 2px; line-height: 1.5; vertical-align: top;">
      <code>import Mathlib.Data.Int.Basic</code><br>
      <code>import Mathlib.Data.Rat.Basic</code><br><br>
      <code>-- Define constant R</code><br>
      <code>def R : ℤ := 17</code><br><br>
      <code>-- 1. Define predicates with range restrictions (Subtypes)</code><br>
      <code>-- The domain of p is {z : ℤ | z < 100}</code><br>
      <code>def DomainP := {z : ℤ // z < 100}</code><br>
      <code>variable (p : DomainP → Prop)</code><br><br>
      <code>-- The domain of q is {y : ℚ | y > 0}</code><br>
      <code>def DomainQ := {y : ℚ // y > 0}</code><br>
      <code>variable (q : DomainQ → Prop)</code><br><br>
      <code>-- 2. know q(17)</code><br>
      <code>-- Here we need to prove 17 > 0 to construct an element of DomainQ</code><br>
      <code>axiom q_17 : q ⟨17, by norm_num⟩</code><br><br>
      <code>-- 3. know ∀ x ∈ ℤ: x ∈ {y ∈ ℤ : y < 20, q(y)} => p(x)</code><br>
      <code>-- Here we need to handle type conversions: x must satisfy x > 0 to pass to q, and x < 100 to pass to p</code><br>
      <code>axiom p_rule : ∀ (x : ℤ),</code><br>
      <code>&nbsp;&nbsp;(h_range : x < 20) →</code><br>
      <code>&nbsp;&nbsp;(h_pos : x > (0 : ℚ)) →</code><br>
      <code>&nbsp;&nbsp;q ⟨x, h_pos⟩ →</code><br>
      <code>&nbsp;&nbsp;p ⟨x, by linarith⟩</code><br><br>
      <code>-- 4. a ∈ {x ∈ ℕ : x % 17 = 0, p(x)}</code><br>
      <code>-- a is a natural number satisfying both conditions</code><br>
      <code>structure InSetA (a : ℕ) : Prop where</code><br>
      <code>&nbsp;&nbsp;mod_17 : a % 17 = 0</code><br>
      <code>&nbsp;&nbsp;-- Similarly, here we need to prove a < 100 to pass a to p</code><br>
      <code>&nbsp;&nbsp;h_lt_100 : (a : ℤ) < 100</code><br>
      <code>&nbsp;&nbsp;prop_p : p ⟨(a : ℤ), h_lt_100⟩</code><br><br>
      <code>-- Declare that a belongs to this set</code><br>
      <code>variable (a : ℕ)</code><br>
      <code>variable (ha : InSetA p a)</code>
    </td>
  </tr>
</table>

Litex automatically handles domain restrictions, type conversions, and verification of all conditions, making complex scenarios involving multiple constraints and type systems more manageable. The convenience of Litex's automatic handling is especially evident in more complex examples like this one.

Lean requires explicit definition of subtypes (`DomainP`, `DomainQ`) to represent domain-restricted propositions. Each type conversion (ℕ → ℤ → ℚ) must be explicit, and domain conditions must be proven manually. For `q(17)`, we must explicitly prove `17 > 0` to construct the subtype element. The universal rule requires explicit handling of all type conversions and domain conditions. The membership condition requires defining a custom structure `InSetA` with explicit proofs of all conditions.

```litex
have a R = 17
prop p(x {z Z: z < 100})
prop q(x {y Q: y > 0})
know $q(17)
know forall x Z: x $in {y Z: y < 20, $q(y)} => $p(x)
a $in {x N: x % 17 = 0, $p(x)}
```

---

## Example 10: Proof by Enumeration

**Task**: Prove that for any element x in the set `{1, 2, 3, 4, 17}`, if x is even (i.e., `x % 2 = 0`), then x must be either 2 or 4.

This example demonstrates how Litex's `prove_by_enum` construct allows direct proof by enumerating all cases in a finite set, which is a common and intuitive proof technique.

<table style="border-collapse: collapse; width: 100%;">
  <tr>
    <th style="border: 2px solid black; padding: 4px; text-align: left; width: 50%;">Litex</th>
    <th style="border: 2px solid black; padding: 4px; text-align: left; width: 50%;">Lean</th>
  </tr>
  <tr>
    <td style="border: 2px solid black; padding: 2px; line-height: 1.5; vertical-align: top;">
      <code>prove_by_enum(x {1, 2, 3, 4, 17}):</code><br>
      <code>&nbsp;&nbsp;dom:</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;x % 2 = 0</code><br>
      <code>&nbsp;&nbsp;=>:</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;x = 2 or x = 4</code><br>
      <code>&nbsp;&nbsp;prove:</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;do_nothing</code>
    </td>
    <td style="border: 2px solid black; padding: 2px; line-height: 1.5; vertical-align: top;">
      <code>import Mathlib.Data.Finset.Basic</code><br>
      <code>import Mathlib.Data.Nat.Basic</code><br><br>
      <code>example (x : ℕ) (hx : x ∈ ({1, 2, 3, 4, 17} : Finset ℕ)) (heven : x % 2 = 0) : x = 2 ∨ x = 4 := by</code><br>
      <code>&nbsp;&nbsp;-- Enumerate all cases</code><br>
      <code>&nbsp;&nbsp;have h : x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 ∨ x = 17 := by</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;simp [Finset.mem_insert, Finset.mem_singleton] at hx</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;tauto</code><br>
      <code>&nbsp;&nbsp;-- Check each case</code><br>
      <code>&nbsp;&nbsp;rcases h with (rfl|rfl|rfl|rfl|rfl)</code><br>
      <code>&nbsp;&nbsp;· -- Case x = 1: 1 % 2 = 1 ≠ 0, contradiction</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;norm_num at heven</code><br>
      <code>&nbsp;&nbsp;· -- Case x = 2: satisfies conclusion</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;left; rfl</code><br>
      <code>&nbsp;&nbsp;· -- Case x = 3: 3 % 2 = 1 ≠ 0, contradiction</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;norm_num at heven</code><br>
      <code>&nbsp;&nbsp;· -- Case x = 4: satisfies conclusion</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;right; rfl</code><br>
      <code>&nbsp;&nbsp;· -- Case x = 17: 17 % 2 = 1 ≠ 0, contradiction</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;norm_num at heven</code>
    </td>
  </tr>
</table>

Litex's `prove_by_enum` provides a direct and intuitive way to prove statements about finite sets by automatically checking all cases. The `dom` clause specifies the domain condition, the `=>` clause specifies what needs to be proven, and `prove` contains the proof steps (which can be `do_nothing` when the enumeration itself is sufficient).

Lean requires explicit case analysis using tactics like `rcases` and manual verification of each case. The proof structure is clear but requires more boilerplate to enumerate all possibilities and handle each case separately.

```litex
prove_by_enum(x {1, 2, 3, 4, 17}):
    dom:
        x % 2 = 0
    =>:
        x = 2 or x = 4
    prove:
        do_nothing
```

---

## Summary

Since Lean's kernel can only provide built-in functionality for type theory (its foundation), it cannot provide built-in functionality for set theory. Consequently, users must manually implement set-theoretic operations and proofs. 

It is understandable why Lean's expression of set theory is more complex than Litex's. Lean is built on type theory as its foundational axiom system. Type theory is a more abstract mathematical theory than set theory (type theory can derive set theory, but set theory cannot derive type theory). Naturally, Lean's support for set theory will be less direct than Litex, which takes set theory as its foundation.

Mathematics has many different axiomatic systems, and choosing different foundational axiom systems as the basis for a formal language results in vastly different user experiences. The choice of foundation fundamentally shapes how users express mathematical concepts, what operations are built-in versus requiring manual implementation, and the overall learning curve and accessibility of the language. 

This design makes Lean easier to maintain and more general, but means that Lean's expression of set theory—the most fundamental mathematical theory taught in schools—is significantly more complex than Litex's. The high barrier to entry in Lean creates a highly professional community, but limits accessibility. In contrast, Litex's lower barrier to entry, built on familiar set theory, aims to democratize formal mathematics while maintaining rigor.

In the meantime, Lean's extensive standard library (Mathlib) is a significant strength, and all of Litex contributors show great respect for the Lean community and the work of the Lean developers. Wish the Lean community a bright future and Litex will continuously learn and collaborate with the Lean community.