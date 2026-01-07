# Litex From A Mathematician's Perspective

## Why Set Theory?

The foundation of mathematics is its most crucial component. The Bourbaki school constructed the mathematical edifice—encompassing analysis, algebra, and topology—upon set theory. Meanwhile, Grothendieck and others advocated category theory as a superior foundation.

Litex chooses set theory for its accessibility. Fundamental mathematical structures are naturally defined in terms of sets:

- **A group** is an ordered pair (G, ·), where G is a _set_ and · is a binary operation on G such that: (a·b)·c = a·(b·c) for all a,b,c ∈ G; there exists e ∈ G with a·e = e·a = a for all a ∈ G; and for each a ∈ G there exists b ∈ G with a·b = b·a = e.
- **A topological space** is an ordered pair (X, T), where X is a _set_ and T is a collection of subsets of X such that: ∅, X ∈ T; the union of any subcollection of T is in T; and the intersection of any two elements of T is in T.
- **A metric space** is a _set_ X equipped with a function d: X × X → R such that: d(x,y) ≥ 0; d(x,x) = 0; d(x,y) = d(y,x); and d(x,z) ≤ d(x,y) + d(y,z) for all x,y,z ∈ X.
- **A vector space** over a field F is a _set_ V with operations +: V × V → V and ·: F × V → V such that: (V,+) is an abelian group; and scalar multiplication satisfies a·(u+v) = a·u + a·v, (a+b)·v = a·v + b·v, (ab)·v = a·(b·v), and 1·v = v for all a,b ∈ F and u,v ∈ V. 

While category theory excels in fields like algebraic geometry, set theory remains the dominant language across analysis, algebra, and topology. Mathematical education—from calculus and linear algebra to probability and combinatorics—is predominantly expressed through set theory. Mainstream formal languages like Lean and Isabelle adopt the categorical/functional programming paradigm, yet most mathematicians think in terms of sets. Litex aligns with this natural mode of mathematical thought.