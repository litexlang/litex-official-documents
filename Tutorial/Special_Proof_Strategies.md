# Special Proof Strategies

In mathematics, most proofs are direct, proceeding step by step from assumptions to conclusions. However, many important results also require other proof strategies:

*Proof by Contradiction* – Assume the opposite of what you want to prove, and show that this leads to a contradiction.

*Proof by Cases* – Divide the situation into several possible cases, prove the statement in each case, and conclude that it holds universally. For example, when 1. we know `or($p(x), $q(x))`, 2. we can prove when `$p(x)` is true, `$r(x)` is also true. 3. we can prove when `$q(x)` is true, `$r(x)` is also true. With this, we can prove `$r(x)` is always true.

*Proof by Induction* – Establish a base case, then show that if the statement holds for one step, it also holds for the next, covering all natural numbers. This is called `principle of mathematical induction`. Technically, it is an axiom schema: it is a template for producing an infinite number of axioms.

*Proof over a Finite Set* – Suppose `s` is a finite set, we want to prove `forall x s => $p(x)`. We can simply check each element `x` in `s` one by one whether `$p(x)` holds. This is different from an infinite set: a computer cannot iterate over infinitely many elements in finite time and check whether `$p(x)` holds for each element.

Without these methods, we cannot prove many important theorems. For example, we cannot prove the irrationality of sqrt(2) without proof by contradiction.

We will explore these methods in detail in the following sections.