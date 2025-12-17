# Litex vs Lean: Set Theory Examples

This document compares Litex and Lean in expressing set-theoretic statements through side-by-side code examples. Our goal is not to criticize Lean, but to propose complementary ideas where Lean may be less intuitive, particularly in set theory. We explore alternative design choices that prioritize accessibility while maintaining rigor.

---

## Example 1: Simple Set Membership Proof

**Task**: Prove that `1` is an element of the set `{1, 2}`.

### Litex Solution

In Litex, this is straightforward and intuitive:

```litex
1 $in {1, 2}
```

That's it! Litex automatically verifies this statement. The syntax directly mirrors mathematical notation, and the kernel handles the verification automatically.

### Lean Solution

In Lean, proving this simple fact requires significantly more code:

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

**Why Litex is better**: Litex automatically verifies set membership in one line, while Lean requires imports, explicit definitions, and proof tactics.

---

## Example 2: Sets Containing Sets

**Task**: Define a set containing sets as elements: `{{}, {1, 2}}`, and prove that `{1, 2}` is an element of this set.

### Litex Solution

Litex handles this naturally, as sets are objects and can be elements of other sets:

```litex
{1, 2} $in {{}, {1, 2}}
```

### Lean Solution

In Lean, this becomes complex because Lean requires explicit type information. You need to work with a specific type system:

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

**Why Litex is better**: Litex's set-theoretic foundation naturally supports sets containing sets, while Lean requires explicit type definitions and complex type hierarchies.

---

## Example 4: Disjunction from Set Membership

**Task**: If `x` is an element of `{1, 2}`, then `x = 1` or `x = 2`.

### Litex Solution

```litex
have x {1, 2}
x = 1 or x = 2
```

Litex automatically derives this disjunction from set membership. The kernel recognizes that membership in a finite enumerated set implies equality to one of its elements.

### Lean Solution

In Lean, this requires explicit proof steps:

```lean
import Mathlib.Data.Finset.Basic

variable (x : ℕ)

example (h : x ∈ ({1, 2} : Finset ℕ)) : x = 1 ∨ x = 2 := by
  simp [Finset.mem_insert, Finset.mem_singleton] at h
  cases h with
  | inl h1 => left; exact h1
  | inr h2 => right; exact h2
```

Or using tactics:

```lean
example (h : x ∈ ({1, 2} : Finset ℕ)) : x = 1 ∨ x = 2 := by
  simp [Finset.mem_insert, Finset.mem_singleton] at h
  tauto
```

**Why Litex is better**: Litex automatically derives disjunctions from set membership, while Lean requires explicit proof tactics and case analysis.

---

## Example 5: Properties from Intensional Set Membership

**Task**: If `x` is an element of `{x R: x > 0}`, then `x > 0`.

### Litex Solution

```litex
have x {x R: x > 0}
x > 0
```

Litex automatically derives this property. The kernel recognizes that membership in an intensional set (defined by a condition) implies that condition.

### Lean Solution

In Lean, this requires explicit proof steps:

```lean
import Mathlib.Data.Set.Basic

variable (x : ℝ)

example (h : x ∈ {y : ℝ | y > 0}) : x > 0 := by
  simp [Set.mem_setOf_eq] at h
  exact h
```

Or more verbosely:

```lean
example (h : x ∈ {y : ℝ | y > 0}) : x > 0 := by
  rw [Set.mem_setOf_eq] at h
  assumption
```

**Why Litex is better**: Litex automatically derives properties from intensional set membership, while Lean requires explicit rewriting and proof tactics for this fundamental mathematical pattern.

---

## Summary

Since Lean's kernel can only provide built-in functionality for type theory (its foundation), it cannot provide built-in functionality for set theory. Consequently, users must manually implement set-theoretic operations and proofs. 

It is understandable why Lean's expression of set theory is more complex than Litex's. Lean is built on type theory as its foundational axiom system. Type theory is a more abstract mathematical theory than set theory (type theory can derive set theory, but set theory cannot derive type theory). Naturally, Lean's support for set theory will be less direct than Litex, which takes set theory as its foundation.

Mathematics has many different axiomatic systems, and choosing different foundational axiom systems as the basis for a formal language results in vastly different user experiences. The choice of foundation fundamentally shapes how users express mathematical concepts, what operations are built-in versus requiring manual implementation, and the overall learning curve and accessibility of the language. 

This design makes Lean easier to maintain and more general, but means that Lean's expression of set theory—the most fundamental mathematical theory taught in schools—is significantly more complex than Litex's. The high barrier to entry in Lean creates a highly professional community, but limits accessibility. In contrast, Litex's lower barrier to entry, built on familiar set theory, aims to democratize formal mathematics while maintaining rigor.

In the meantime, Lean's extensive standard library (Mathlib) is a significant strength, and all of Litex contributors show great respect for the Lean community and the work of the Lean developers. Wish the Lean community a bright future and Litex will continuously learn and collaborate with the Lean community.