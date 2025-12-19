# Litex vs Lean: Set Theory Examples

This document compares [Litex](https://litexlang.com) and [Lean](https://leanprover.github.io) in expressing set-theoretic statements through side-by-side code examples. Set is *the most basic concept in mathematics*, and through sets we can observe the similarities and differences between Litex and other formal languages.

Lean, the most popular formal language in the world and the language that Litex community deeply appreciate, is chosen to compare with Litex. We show Litex offers a more natural way to express some basic mathematical statements. Star the [Litex GitHub](https://github.com/litexlang/golitex) if you like Litex!

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

Litex's design allows automatic verification of set membership in a single line, by iterating over items in the list set and finding the item that equals to the item we are looking for.

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


Litex's set-theoretic foundation naturally supports sets containing sets as elements.

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

The meaning of an item is in a list set is that the item equals to one of the items in the list. So Litex automatically derives the fact `x = 1 or x = 2` from the fact `x $in {1, 2}` for the user.

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

The meaning of an item is in a set builder set is that the item satisfies the condition. So Litex automatically derives the fact `x > 0` from the fact `x $in {y R: y > 0}` for the user. 

Also, Litex searches related facts from the database mechanically to derive the fact, you don't need to give names to the facts you want to use and call them manually later like Lean, so words like `simp [Set.mem_setOf_eq]` are not needed. This releases huge productivity for the user.

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

Litex's built-in count function derives the number of items in a set. So Litex automatically derives the fact `count({1,2,3}) = 3` and `count({1,2}) = 2`.

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

Litex's `prove_for` provides iterates over items in a range and when the item satisfies the condition (domain restriction), it runs the proof section and the then section. After all items are iterated, it concludes the proof. `forall i range(x, y): domain_facts => then_facts`. In this case. there is no domain restriction and no proof section, it concludes `forall i range(5, 8): i = 5 or i = 6 or i = 7`. Here `range(x, y) = {i Z: x <= i, i < y}`.

Lean requires explicit set extensionality (`ext`) and case analysis (`interval_cases`, `rcases`) to prove range-based set equalities.

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

In set theory, an item can belong to multiple sets. So Litex also supports this way of writing naturally.

Lean requires explicit application of the inclusion hypotheses and manual construction of intermediate facts. Since type theory only supports one type at a time, it requires extra steps and explicit type conversions between different types.

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

This example demonstrates how Litex and Lean handle propositions with domain restrictions (subsets as domains).

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

Litex automatically handles domain restrictions, set builder sets, and verification of all conditions.

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

Litex's `prove_by_enum` iterates over items in a set and when the item satisfies the condition (domain restriction), it runs the proof section and the then section, then concludes the universal fact `forall x some_list_set: dom => then`. In this case, the domain condition is `x % 2 = 0`, the then condition is `x = 2 or x = 4`, and the proof steps are `do_nothing`. After all items are iterated, it concludes the `forall x {1, 2, 3, 4, 17}: x % 2 = 0 => x = 2 or x = 4`.

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

## Example 11: A Function is in a set of functions

**Task**: Define a function `g` that maps from the set of positive real numbers to real numbers, and show that `g` belongs to the set of functions from positive reals to positive reals.

<table style="border-collapse: collapse; width: 100%;">
  <tr>
    <th style="border: 2px solid black; padding: 4px; text-align: left; width: 50%;">Litex</th>
    <th style="border: 2px solid black; padding: 4px; text-align: left; width: 50%;">Lean</th>
  </tr>
  <tr>
    <td style="border: 2px solid black; padding: 2px; line-height: 1.5; vertical-align: top;">
      <code>have fn g(x {y R: y > 0}) R = x + 1</code><br><br>
      <code>forall x {y R: y > 0}: g(x) = x + 1, x + 1 > 0, g(x) > 0</code><br><br>
      <code>g $in fn({y R: y > 0}) {y R: y > 0}</code>
    </td>
    <td style="border: 2px solid black; padding: 2px; line-height: 1.5; vertical-align: top;">
      <code>import Mathlib.Tactic</code><br><br>
      <code>-- Define a subtype of real numbers that are greater than 0</code><br>
      <code>def PositiveReal := {x : ℝ // x > 0}</code><br><br>
      <code>-- Define function g: PositiveReal -> PositiveReal</code><br>
      <code>-- Must prove that x.val + 1 > 0 when x > 0</code><br>
      <code>def g (x : PositiveReal) : PositiveReal :=</code><br>
      <code>&nbsp;&nbsp;⟨x.val + 1, by</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;let hx := x.property  -- x > 0</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;linarith              -- proves x + 1 > 0</code><br>
      <code>&nbsp;&nbsp;⟩</code><br><br>
      <code>-- Prove that g(x) = x + 1</code><br>
      <code>example (x : PositiveReal) : (g x).val = x.val + 1 := by</code><br>
      <code>&nbsp;&nbsp;rfl</code><br><br>
      <code>-- Prove that g(x) > 0</code><br>
      <code>lemma g_pos (x : PositiveReal) : (g x).val > 0 := by</code><br>
      <code>&nbsp;&nbsp;exact (g x).property</code>
    </td>
  </tr>
</table>

Litex's function definition with set builder notation naturally handles domain restrictions. When we define `g(x {y R: y > 0}) R = x + 1`, Litex automatically:
- Recognizes that the domain is the set of positive real numbers
- Verifies that `x + 1 > 0` when `x > 0` (since if `x > 0`, then `x + 1 > 1 > 0`)
- Infers that `g(x) > 0` for all positive `x`
- Allows us to state that `g` belongs to the set of functions from positive reals to positive reals

Lean requires explicit definition of a subtype (`PositiveReal`) to represent the domain restriction. The function definition must include a proof that the return value satisfies the codomain constraint (`x + 1 > 0`). Additional lemmas are needed to establish properties like `g(x) = x + 1` and `g(x) > 0`, and the function membership statement requires explicit type annotations and proofs. Furthermore, Lean requires writing `(g x).val` to access the value of a subtype in an object-oriented way, which is not how mathematics is typically written in everyday practice.

```litex
have fn g(x {y R: y > 0}) R = x + 1
forall x {y R: y > 0}: g(x) = x + 1, x + 1 > 0, g(x) > 0
g $in fn({y R: y > 0}) {y R: y > 0}
```

## Example 12: Define a function with existence proof

**Task**: Prove that there exists a function `h : ℝ → ℝ` such that `h(x) > 1` for all `x > 0`, and show that `h(1) > 1`.

<table style="border-collapse: collapse; width: 100%;">
  <tr>
    <th style="border: 2px solid black; padding: 4px; text-align: left; width: 50%;">Litex</th>
    <th style="border: 2px solid black; padding: 4px; text-align: left; width: 50%;">Lean</th>
  </tr>
  <tr>
    <td style="border: 2px solid black; padding: 2px; line-height: 1.5; vertical-align: top;">
      <code>have fn:</code><br>
      <code>&nbsp;&nbsp;h(x R) R:</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;x > 0</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;=>:</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;h(x) > 1</code><br>
      <code>&nbsp;&nbsp;prove:</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;100 > 1</code><br>
      <code>&nbsp;&nbsp;= 100</code><br><br>
      <code>h(1) > 1</code>
    </td>
    <td style="border: 2px solid black; padding: 2px; line-height: 1.5; vertical-align: top;">
      <code>import Mathlib.Tactic</code><br><br>
      <code>def Property (f : ℝ → ℝ) : Prop :=</code><br>
      <code>&nbsp;&nbsp;∀ x > 0, f x > 1</code><br><br>
      <code>lemma exists_h : ∃ f : ℝ → ℝ, Property f := by</code><br>
      <code>&nbsp;&nbsp;use (λ _ => 2)</code><br>
      <code>&nbsp;&nbsp;intro x hx</code><br>
      <code>&nbsp;&nbsp;simp [Property]</code><br>
      <code>&nbsp;&nbsp;norm_num</code><br><br>
      <code>example : ∃ h : ℝ → ℝ, Property h ∧ h 1 > 0 := by</code><br>
      <code>&nbsp;&nbsp;obtain ⟨h, h_prop⟩ := exists_h</code><br>
      <code>&nbsp;&nbsp;</code><br>
      <code>&nbsp;&nbsp;use h</code><br>
      <code>&nbsp;&nbsp;constructor</code><br>
      <code>&nbsp;&nbsp;· exact h_prop</code><br>
      <code>&nbsp;&nbsp;· have h1_gt_1 : h 1 > 1 := h_prop 1 (by norm_num)</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;linarith</code>
    </td>
  </tr>
</table>

Litex's `have fn` statement provides a direct way to prove the existence of a function by specifying a concrete value that satisfies the conditions. In this example, we prove that there exists a function `h` such that `h(x) > 1` for all `x > 0` by showing that when `h(x) = 100` for all `x > 0`, the condition `h(x) > 1` is satisfied (since `100 > 1`). Once the function is defined, we can immediately use it: `h(1) > 1` is automatically verified because `1 > 0` and `h(1) = 100 > 1`.

Lean requires explicit definition of the property as a separate proposition, a lemma to prove existence, and then constructing the final example by combining the lemma with additional properties. The proof structure is rigorous but requires more steps: defining the property, proving existence with a witness function, and then manually applying the property to specific values.

```litex
have fn:
    h(x R) R:
        x > 0
        =>:
            h(x) > 1
    prove:
        100 > 1
    = 100
h(1) > 1
```

---

## Summary

Mathematics has many different axiomatic systems, and choosing different foundational axiom systems as the basis for a formal language results in vastly different user experiences. Lean chooses type theory as its foundation, while Litex chooses set theory.

This design makes Lean easier to maintain and theoretically more general, which experts prefer. Litex's design, on the other hand, is more intuitive and easier to learn, built on familiar set theory, aims to democratize formal mathematics while maintaining rigor, even for 10-year-olds.

For the time being, Litex is still a toy language for learning purposes and toy projects, very far from being a serious language for professional use. We wish experts and enthusiasts of formal languages to contact Litex team [litexlang@outlook.com](mailto:litexlang@outlook.com) to point out any mistakes or suggestions. Join our [Zulip](https://litex.zulipchat.com/join/c4e7foogy6paz2sghjnbujov/) to discuss Litex with us!