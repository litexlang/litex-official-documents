# Litex vs Lean: Set Theory Examples

This document compares Litex and Lean in expressing set-theoretic statements through side-by-side code examples. Set is *the most basic concept in mathematics*, and through sets we can observe the similarities and differences in how different formal languages express everyday mathematical concepts, sharing their distinctive characteristics.

Our goal is not to criticize Lean (which Litex team deeply respects), but to propose complementary ideas where Lean may be less intuitive, particularly in set theory. We explore alternative design choices that prioritize accessibility while maintaining rigor.

---

## Example 1: Simple Set Membership Proof

**Task**: Prove that `1` is an element of the set `{1, 2}`.

<table>
<tr>
<td width="50%">

**Litex**

```litex
1 $in {1, 2}
```

</td>
<td width="50%">

**Lean**

```lean
import Mathlib.Data.Finset.Basic

-- Define the set
def my_set : Finset ℕ := {1, 2}

-- Prove membership
example : 1 ∈ my_set := by
  simp [my_set]
  -- or more explicitly:
  -- rw [Finset.mem_insert]
  -- simp
```

</td>
</tr>
</table>

Litex's design allows automatic verification of set membership in a single line, directly expressing the mathematical statement without requiring additional setup.

Lean requires explicit set definition and proof tactics. The `simp` tactic can simplify the proof, but the setup (imports, type annotations, and proof structure) is more verbose.

---

## Example 2: Sets Containing Sets

**Task**: Define a set containing sets as elements: `{{}, {1, 2}}`, and prove that `{1, 2}` is an element of this set.

<table>
<tr>
<td width="50%">

**Litex**

```litex
{1, 2} $in {{}, {1, 2}}
```

</td>
<td width="50%">

**Lean**

```lean
import Mathlib.Data.Finset.Basic

-- Lean requires explicit types, making this awkward
-- You need to use a structure to represent sets of sets
structure MySet where
  val : Finset ℕ

def my_set_of_sets : Finset MySet := {
  MySet.mk ({} : Finset ℕ),
  MySet.mk ({1, 2} : Finset ℕ)
}

-- To prove membership, you need to construct the set element explicitly
example : MySet.mk ({1, 2} : Finset ℕ) ∈ my_set_of_sets := by
  simp [my_set_of_sets]
  -- Requires explicit construction and proof steps
  -- Or use a more complex type hierarchy
```

</td>
</tr>
</table>


Litex's set-theoretic foundation naturally supports sets containing sets as elements, reflecting the mathematical principle that sets are objects.

Lean requires explicit type structures (like `MySet`) to represent sets of sets, as its type system needs explicit type annotations. This adds boilerplate but provides type safety.

---

## Example 4: Disjunction from Set Membership

**Task**: If `x` is an element of `{1, 2}`, then `x = 1` or `x = 2`.

<table>
<tr>
<td width="50%">

**Litex**

```litex
have x {1, 2}
x = 1 or x = 2
```


</td>
<td width="50%">

**Lean**

```lean
import Mathlib.Data.Finset.Basic

variable (x : ℕ)

example (h : x ∈ ({1, 2} : Finset ℕ)) : x = 1 ∨ x = 2 := by
  simp [Finset.mem_insert, Finset.mem_singleton] at h
  cases h with
  | inl h1 => left; exact h1
  | inr h2 => right; exact h2
```

</td>
</tr>
</table>

Litex automatically derives disjunctions from set membership, recognizing that membership in a finite enumerated set implies equality to one of its elements.

Lean requires explicit proof steps using tactics like `simp`, `cases`, or `tauto` to derive the disjunction from set membership. The proof structure is more explicit but requires more manual steps.
---

## Example 5: Properties from Set Builder Membership

**Task**: If `x` is an element of `{y R: y > 0}`, then `x > 0`.

<table>
<tr>
<td width="50%">

**Litex**

```litex
forall x {y R: y > 0}:
    x > 0
```

</td>
<td width="50%">

**Lean**

```lean
import Mathlib.Data.Set.Basic

variable (x : ℝ)

example (h : x ∈ {y : ℝ | y > 0}) : x > 0 := by
  simp [Set.mem_setOf_eq] at h
  exact h
```

</td>
</tr>
</table>

Litex automatically derives properties from Set Builder membership, recognizing that membership in a set defined by a condition implies that condition—a fundamental mathematical pattern.

Lean requires explicit rewriting with `Set.mem_setOf_eq` to extract the condition from set membership. The proof is straightforward but requires manual application of the membership definition.

---
## Example 6: Proving Set Inequality by Cardinality

**Task**: Prove that `{1, 2, 3} ≠ {1, 2}` by showing that `{1, 2, 3}` has 3 elements while `{1, 2}` has 2 elements.

<table>
<tr>
<td width="50%">

**Litex**

```litex
prove_by_contradiction {1,2,3} != {1,2}:
    count({1,2,3}) = 3
    count({1,2}) = 2
    count({1,2,3}) = count({1,2})
    3 = 2
```

</td>
<td width="50%">

**Lean**

```lean
import Mathlib.Data.Finset.Basic

example : ({1, 2, 3} : Finset ℕ) ≠ ({1, 2} : Finset ℕ) := by
  intro h
  have h1 : ({1, 2, 3} : Finset ℕ).card = 3 := by simp
  have h2 : ({1, 2} : Finset ℕ).card = 2 := by simp
  rw [h] at h1
  rw [h2] at h1
  norm_num at h1
```

</td>
</tr>
</table>

Litex's built-in cardinality operations and proof by contradiction mechanism make this type of proof straightforward and intuitive.

Lean requires explicit cardinality computation using `.card` and manual proof by contradiction. The proof structure is clear but requires more steps to establish the contradiction.

---
## Example 7: Sets Cannot Contain Duplicate Elements

**Task**: Demonstrate that sets cannot contain duplicate elements. The statement `{1, 1} = {1, 1}` may seem correct, but it is actually problematic because a set cannot contain the same element twice.

<table>
<tr>
<td width="50%">

**Litex**

```litex
# This is a problem, because a set cannot contain the same element twice. In this case, we do not know if a != 1 or not, so we cannot prove {a, 1} is a valid set.
# have a N
# {a, 1} = {a, 1} 
```

Litex detects the issue when it cannot verify that set elements are distinct (e.g., when `a ≠ 1` is unknown), providing a clear error message that explains the mathematical principle that sets are collections of distinct elements.

</td>
<td width="50%">

**Lean**

```lean
import Mathlib

variable (a : ℕ)  -- Assume a is a variable of type ℕ

-- This still causes an error! Because Lean cannot infer what {} is
-- example : ({a, 1} : Set ℕ) = ({a, 1} : Set ℕ) := rfl
-- Error: ambiguous overload, possible interpretations: ...

-- This also causes an error
-- example : {a, 1} = {a, 1} := rfl
```

Lean encounters type inference issues when dealing with sets containing variables, making it difficult to express this scenario. `Finset` enforces distinctness at the type level, but type inference can be problematic with variables.

</td>
</tr>
</table>

## Example 8: Proving Set Equality by Range Enumeration

**Task**: Prove that the integers greater than or equal to 5 and less than 8 are exactly 5, 6, and 7.

The proof proceeds in two steps:
1. First, we prove that if `i $in range(5, 8)`, then `i = 5 or i = 6 or i = 7` using `prove_for`.
2. Second, we prove that if `i = 5 or i = 6 or i = 7`, then `i $in range(5, 8)` (i.e., `i >= 5` and `i < 8`).

<table>
<tr>
<td width="50%">

**Litex**

```litex
prove_for i $in range(5, 8):
    i = 5 or i = 6 or i = 7

forall i Z: i = 5 or i = 6 or i = 7 => i >= 5, i < 8
```

</td>
<td width="50%">

**Lean**

```lean
import Mathlib.Tactic

example : {n : ℕ | n ≥ 5 ∧ n < 8} = ({5, 6, 7} : Finset ℕ) := by
  ext n
  constructor
  · intro hn
    have h1 : n ≥ 5 := hn.1
    have h2 : n < 8 := hn.2
    interval_cases n <;> simp
  · intro hn
    have : n = 5 ∨ n = 6 ∨ n = 7 := by simpa [Finset.mem_insert, Finset.mem_singleton] using hn
    rcases this with (rfl|rfl|rfl)
    · exact ⟨by norm_num, by norm_num⟩
    · exact ⟨by norm_num, by norm_num⟩
    · exact ⟨by norm_num, by norm_num⟩
```

</td>
</tr>
</table> 

Litex's `prove_for` provides a direct, intuitive way to prove range-based set equalities, making the mathematical intent explicit through iterative verification.

Lean requires explicit set extensionality (`ext`) and case analysis (`interval_cases`, `rcases`) to prove range-based set equalities. The proof is rigorous but requires more manual construction of the cases.

---
## Example 9: Set Inclusion Transitivity

**Task**: Demonstrate that an object belonging to one set automatically belongs to other sets through set inclusion. If `A ⊆ B` and `B ⊆ C`, then any element `x` in `A` also belongs to both `B` and `C`.

<table>
<tr>
<td width="50%">

**Litex**

```litex
have a, b, c nonempty_set
know forall x a => x $in b
know forall x b => x $in c

have x a
x $in b
x $in c
```

</td>
<td width="50%">

**Lean**

```lean
import Mathlib

variable {α : Type*}  -- Arbitrary type
variable (A B C : Set α)  -- Three sets

-- Premises
variable (hA_nonempty : Set.Nonempty A)  -- A is nonempty
variable (hAB : ∀ x, x ∈ A → x ∈ B)      -- ∀x∈A, x∈B (i.e., A ⊆ B)
variable (hBC : ∀ x, x ∈ B → x ∈ C)      -- ∀x∈B, x∈C (i.e., B ⊆ C)

-- Conclusion
example (x : α) (hx : x ∈ A) : x ∈ C := by
  -- Since x ∈ A, we have x ∈ B
  have hxB : x ∈ B := hAB x hx
  -- Since x ∈ B, we have x ∈ C
  exact hBC x hxB
```

</td>
</tr>
</table>

Litex automatically handles transitive set membership through its built-in reasoning, recognizing the logical chain from set inclusion facts.

Lean requires explicit application of the inclusion hypotheses and manual construction of intermediate facts. The proof structure is clear but requires explicit steps for each logical inference.

---

## Example 10: Membership in Set Builders with Domain-Restricted Propositions

**Task**: Prove that `17` belongs to the set `{x N: x % 17 = 0, $p(x)}` where `p` is a proposition with domain restriction `{z Z: z < 100}`, and `p` is derived from another proposition `q` with domain `{y Q: y > 0}` through a universal rule.

This example demonstrates how Litex and Lean handle propositions with domain restrictions (subsets as domains) and the complexity of type conversions between different number systems.

<table>
<tr>
<td width="50%">

**Litex**

```litex
have a R = 17
prop p(x {z Z: z < 100})
prop q(x {y Q: y > 0})
know $q(17)
know forall x Z: x $in {y Z: y < 20, $q(y)} => $p(x)
a $in {x N: x % 17 = 0, $p(x)}
```

</td>
<td width="50%">

**Lean**

```lean
import Mathlib.Data.Int.Basic
import Mathlib.Data.Rat.Basic

-- Define constant R
def R : ℤ := 17

-- 1. Define predicates with range restrictions (Subtypes)
-- The domain of p is {z : ℤ | z < 100}
def DomainP := {z : ℤ // z < 100}
variable (p : DomainP → Prop)

-- The domain of q is {y : ℚ | y > 0}
def DomainQ := {y : ℚ // y > 0}
variable (q : DomainQ → Prop)

-- 2. know q(17)
-- Here we need to prove 17 > 0 to construct an element of DomainQ
axiom q_17 : q ⟨17, by norm_num⟩

-- 3. know ∀ x ∈ ℤ: x ∈ {y ∈ ℤ : y < 20, q(y)} => p(x)
-- Here we need to handle type conversions: x must satisfy x > 0 to pass to q, and x < 100 to pass to p
axiom p_rule : ∀ (x : ℤ), 
  (h_range : x < 20) → 
  (h_pos : x > (0 : ℚ)) → 
  q ⟨x, h_pos⟩ → 
  p ⟨x, by linarith⟩

-- 4. a ∈ {x ∈ ℕ : x % 17 = 0, p(x)}
-- a is a natural number satisfying both conditions
structure InSetA (a : ℕ) : Prop where
  mod_17 : a % 17 = 0
  -- Similarly, here we need to prove a < 100 to pass a to p
  h_lt_100 : (a : ℤ) < 100
  prop_p : p ⟨(a : ℤ), h_lt_100⟩

-- Declare that a belongs to this set
variable (a : ℕ)
variable (ha : InSetA p a)
```

</td>
</tr>
</table>

Litex automatically handles domain restrictions, type conversions, and verification of all conditions, making complex scenarios involving multiple constraints and type systems more manageable. The convenience of Litex's automatic handling is especially evident in more complex examples like this one.

Lean requires explicit definition of subtypes (`DomainP`, `DomainQ`) to represent domain-restricted propositions. Each type conversion (ℕ → ℤ → ℚ) must be explicit, and domain conditions must be proven manually. For `q(17)`, we must explicitly prove `17 > 0` to construct the subtype element. The universal rule requires explicit handling of all type conversions and domain conditions. The membership condition requires defining a custom structure `InSetA` with explicit proofs of all conditions.

---

## Summary

Since Lean's kernel can only provide built-in functionality for type theory (its foundation), it cannot provide built-in functionality for set theory. Consequently, users must manually implement set-theoretic operations and proofs. 

It is understandable why Lean's expression of set theory is more complex than Litex's. Lean is built on type theory as its foundational axiom system. Type theory is a more abstract mathematical theory than set theory (type theory can derive set theory, but set theory cannot derive type theory). Naturally, Lean's support for set theory will be less direct than Litex, which takes set theory as its foundation.

Mathematics has many different axiomatic systems, and choosing different foundational axiom systems as the basis for a formal language results in vastly different user experiences. The choice of foundation fundamentally shapes how users express mathematical concepts, what operations are built-in versus requiring manual implementation, and the overall learning curve and accessibility of the language. 

This design makes Lean easier to maintain and more general, but means that Lean's expression of set theory—the most fundamental mathematical theory taught in schools—is significantly more complex than Litex's. The high barrier to entry in Lean creates a highly professional community, but limits accessibility. In contrast, Litex's lower barrier to entry, built on familiar set theory, aims to democratize formal mathematics while maintaining rigor.

In the meantime, Lean's extensive standard library (Mathlib) is a significant strength, and all of Litex contributors show great respect for the Lean community and the work of the Lean developers. Wish the Lean community a bright future and Litex will continuously learn and collaborate with the Lean community.