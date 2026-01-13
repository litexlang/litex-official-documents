# Litex From A Mathematician's Perspective

## Why Set Theory?

The foundation of mathematics is its most crucial component. The Bourbaki school constructed the mathematical edifice—encompassing analysis, algebra, and topology—upon set theory. Meanwhile, Grothendieck and others advocated category theory as a superior foundation.

Litex chooses set theory for its accessibility. Fundamental mathematical structures are naturally defined in terms of sets:

- **A group** is an ordered pair (G, ·), where G is a _set_ and · is a binary operation on G such that: (a·b)·c = a·(b·c) for all a,b,c ∈ G; there exists e ∈ G with a·e = e·a = a for all a ∈ G; and for each a ∈ G there exists b ∈ G with a·b = b·a = e.

```litex
prop is_group(s set, mul fn(s,s)s, inv fn(s)s, e s):
    forall a, b, c s: mul(mul(a, b), c) = mul(a, mul(b, c))
    forall a s: mul(a, e) = a, a = mul(e, a)
    forall a s: inv(a) \mul a = a \mul inv(a), a \mul inv(a) = e

# prove (Z, +, negate, 0) is a group
forall a, b, c Z: (a + b) + c = a + (b + c)
forall a Z: a + 0 = a, a = 0 + a
forall a Z: negate(a) + a = a + negate(a), a + negate(a) = 0
forall a Z: negate(a) = -a, -a $in Z, negate(a) $in Z

$is_group(Z, +, negate, 0)
```

- **A topological space** is an ordered pair (X, T), where X is a _set_ and T is a collection of subsets of X such that: ∅, X ∈ T; the union of any subcollection of T is in T; and the intersection of any two elements of T is in T.

```litex
prop is_topological_space(s set, open_sets power_set(s)):
    {} $in open_sets
    s $in open_sets
    forall x, y open_sets: x \intersect y $in open_sets
    forall u power_set(open_sets): cup(u) $in open_sets
```

- **A metric space** is a _set_ X equipped with a function d: X × X → R such that: d(x,y) ≥ 0; d(x,x) = 0; d(x,y) = d(y,x); and d(x,z) ≤ d(x,y) + d(y,z) for all x,y,z ∈ X.

```litex
prop is_metric_space(s set, d fn(s, s) R):
    forall x, y s: d(x, y) >= 0, d(x, y) = d(y, x)
    forall x s: d(x, x) = 0
    forall x, y, z s: d(x, z) <= d(x, y) + d(y ,z)
```

While category theory excels in fields like algebraic geometry, set theory remains the dominant language across analysis, algebra, and topology. Mathematical education—from calculus and linear algebra to probability and combinatorics—is predominantly expressed through set theory. Mainstream formal languages like Lean and Isabelle adopt the categorical/functional programming paradigm, yet most mathematicians think in terms of sets. Litex aligns with this natural mode of mathematical thought.