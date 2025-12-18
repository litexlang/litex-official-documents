## Litex to ZFC Axioms Cheat Sheet

_If people do not believe that mathematics is simple, it is only because they do not realize how complicated life is._

_- John von Neumann_

---

Zermelo-Fraenkel set theory with the Axiom of Choice (ZFC) serves as the foundation of modern mathematics. Many of its core concepts—sets, elements, membership, and subsets—are familiar to anyone who has studied high-school mathematics. This document demonstrates how Litex implements the ZFC axioms, providing a direct mapping between Litex's syntax and the fundamental principles that underpin virtually all of mathematics.

1. Axiom of extensionality: `forall x, y set: x = y <=> forall z: z $in x <=> z $in y`

**Explanation**: This axiom defines what it means for two sets to be equal: two sets are equal if and only if they contain exactly the same elements. This is fundamental because it tells us that a set is completely determined by its elements—the order and repetition of elements don't matter. For example, `{1, 2}` and `{2, 1}` are the same set, and `{1, 1, 2}` is also the same set as `{1, 2}`.

**Litex implementation**: The `equal_set` proposition is a built-in that checks if two sets are equal by verifying that all elements of the first set are in the second set and all elements of the second set are in the first set.

Builtin implementation of axiom of extensionality (pseudo code):

```
know imply equal_set(x, y set):
    x = y

know:
    forall x, y set:
        forall a x:
            a $in y
        forall a y:
            a $in x
        =>:
            $equal_set(x, y)
```

```litex
forall x, y set:
    forall a x:
        a $in y
    forall a y:
        a $in x
    <=>:
        $equal_set(x, y)
        x = y
```

**Example explanation**: This example demonstrates that to prove two sets are equal, we need to show that every element of the first set belongs to the second, and vice versa. The `$equal_set` proposition encapsulates this check, and when it holds, we can conclude that the sets are equal.

2. Axiom of regularity: every nonempty set A has an element Y that is disjoint from the set A, i.e. for all items z in Y, z is not in A; for all items z in A, z is not in Y.

**Explanation**: This axiom prevents pathological sets like sets that contain themselves (e.g., `A = {A}`). It ensures that every nonempty set has at least one element that is "minimal" in the sense that it doesn't share any elements with the original set. This axiom is crucial for avoiding paradoxes and ensures that the membership relation is well-founded, meaning there are no infinite descending chains of membership.

**Litex implementation**: The `$axiom_of_regularity` proposition provides a witness element Y that is disjoint from the given set A.

```litex
have A nonempty_set

have Y st $axiom_of_regularity(A)

forall z A: not z $in Y
forall z Y: not z $in A
```

**Example explanation**: This demonstrates that for any nonempty set A, we can find an element Y such that Y and A have no elements in common. This property is used in proofs by contradiction and ensures the well-foundedness of the set membership relation.

3. Axiom schema of specification

**Explanation**: This axiom allows us to construct subsets by specifying a property that elements must satisfy. Given a set and a property (expressed as a formula), we can form the subset of all elements that satisfy that property. This is the mathematical foundation for set builder notation, which is one of the most common ways to define sets in mathematics.

**Important restriction**: The axiom schema of specification can only construct subsets of existing sets. It does not allow constructing sets of the form `{x set: $P(x)}` from all sets, as this would lead to Russell's paradox (consider the set of all sets that don't contain themselves).

**Litex implementation**: Subsets are constructed using set builder notation. For example, the positive integers can be constructed as `{x Z: x > 0}`. In general, the subset of a set z obeying a formula P(x) is constructed as `{x z: $P(x)}`.

Example:

```litex
forall x {x R: x > 0}:
    x > -1
```

**Example explanation**: This example shows that if x is a positive real number (i.e., x belongs to the set `{x R: x > 0}`), then x is also greater than -1. This demonstrates how set builder notation allows us to work with subsets defined by properties, and how properties of the defining condition automatically apply to all elements of the constructed set.

4. Axiom of pairing: for any two sets A and B, there exists a set {A, B} that contains exactly A and B. Generally, given any finite number of sets A1, A2, ..., An, there exists a set {A1, A2, ..., An} that contains exactly A1, A2, ..., An.

**Explanation**: This axiom guarantees that we can always form a set containing any finite collection of sets. It's the foundation for constructing finite sets by enumeration. Without this axiom, we couldn't even guarantee that `{1, 2}` exists as a set. This axiom is essential for building up mathematics from the ground up, as it allows us to create sets step by step.

**Litex implementation**: In Litex, you can directly construct finite sets using curly braces, and the pairing axiom (extended to finite collections) ensures these sets exist.

Example: We have a set contains and only contains two elements 1 and 2.

```litex
have a set = {1, 2}
```

**Example explanation**: This simple example demonstrates the pairing axiom in action. We can directly declare that a set exists containing exactly the elements 1 and 2. This is the most basic way to construct finite sets in Litex.

5. Axiom of union: for any set x, there exists a set Union(x) that contains all elements of the elements of x.

**Explanation**: This axiom allows us to "flatten" a collection of sets. If you have a set whose elements are themselves sets, the union axiom guarantees that there exists a set containing all elements that belong to any of those sets. For example, if `x = {{1, 2}, {3, 4}}`, then `cup(x) = {1, 2, 3, 4}`. This is fundamental for operations like taking the union of multiple sets, which is one of the most common set operations in mathematics.

**Litex implementation**: The `cup` function implements the union operation. The proposition `$cup_contains_all_items` ensures that if an element z belongs to some set y that is an element of x, then z belongs to `cup(x)`.

Builtin implementation of union axiom (pseudo code):

```
fn cup(x set) set
know imply cup_contains_all_items(x set, y x, z y):
    z $in cup(x)
exist_prop y x st cup_witness_item(x set, z cup(x)):
	z $in y
```

```litex
forall A, B set:
    A != B
    =>:
        A $in {A, B}
        forall x A:
            $cup_contains_all_items({A, B}, A, x)
            x $in cup({A, B})
```

```litex
forall x R:
    $cup_contains_all_items(R, x)
    forall y x:
        y $in cup(R)
```

**Example explanation**: This example shows that if R is a set whose elements are themselves sets, then any element y that belongs to any element x of R will also belong to the union `cup(R)`. This demonstrates how the union operation collects all elements from all member sets into a single set.

6. Axiom schema of replacement: the image of a set under any definable function will also fall inside a set.

**Explanation**: This axiom states that if you have a function f and apply it to all elements of a set, the collection of all outputs (the image of the set under f) is itself a set. This is crucial for many mathematical constructions, as it allows us to transform sets through functions while staying within the realm of sets. For example, if we have the set of natural numbers N and the function f(x) = 2x, then the set of even numbers {2, 4, 6, ...} exists as a set.

**Litex implementation**: The `image_set` function computes the image of a set under a function. The proposition `$exist_preimage` checks whether an element in the codomain has a preimage in the domain.

Builtin implementation of replacement axiom (pseudo code):

```
exist_prop x s1 st exist_preimage(s1, s2 set, y s2, f fn(s1)s2):
    f(x) = y

fn image_set(s1, s2 set, f fn(s1)s2) set

know:
    forall s1, s2 set, f fn(s1)s2, y image_set(s1, s2, f):
        $exist_preimage(s1, s2, y, f)

    forall s1, s2 set, f fn(s1)s2, y s2:
        $exist_preimage(s1, s2, y, f)
        =>:
            y $in image_set(s1, s2, f)

	forall s1, s2 set, f fn(s1)s2:
		image_set(s1, s2, f) $subset_of s2
```

```litex
have fn f(x R) R = x + 1
forall y R:
    f(y - 1) = (y - 1) + 1 = y
    exist y - 1 st $exist_preimage(R, R, y, f)
    $exist_preimage(R, R, y, f)

prove R = image_set(R, R, f):
    image_set(R, R, f) $subset_of R
    forall x image_set(R, R, f):
        x $in R

    forall x R:
        $exist_preimage(R, R, x, f)
        x $in image_set(R, R, f)

    $equal_set(R, image_set(R, R, f))
```

**Example explanation**: This example demonstrates the replacement axiom by showing that the image of the real numbers R under the function f(x) = x + 1 is again R. The proof shows that every real number y has a preimage (namely y - 1), so the image set contains all of R. This illustrates how functions can be used to construct new sets from existing ones.

7. Axiom of infinity: there exists an infinite set.

**Explanation**: This axiom guarantees that infinite sets exist. Without it, we could only work with finite sets, which would be insufficient for most of mathematics. The natural numbers, integers, rationals, and reals all require the existence of infinite sets. Von Neumann's construction uses this axiom to build the natural numbers as an infinite set with a well-defined structure.

**Litex implementation**: The keyword `N` in Litex is the built-in set of natural numbers, which is constructed using the axiom of infinity. Statements like `0 $in N` and `1 $in N` are true by definition.

Besides `N`, Litex also builds in the following built-in axiom. You can use it to define your own N, or build connection between your own N and N.

```
exist_prop x set st axiom_of_infinity():
	{} $in x
	forall y x:
		union(y, {y}) $in x
```

8. Axiom of power set: for any set x, there exists a set Power(x) that contains all subsets of x.

**Explanation**: This axiom states that for any set, the collection of all its subsets forms a set (called the power set). This is fundamental for many areas of mathematics, including topology, measure theory, and logic. For example, if `x = {1, 2}`, then `power_set(x) = {{}, {1}, {2}, {1, 2}}`. The power set is always strictly larger than the original set (by Cantor's theorem), which is why this axiom is essential for constructing larger infinite sets.

**Litex implementation**: The `power_set` function returns the set of all subsets. The axiom ensures that if y is a subset of x, then y belongs to `power_set(x)`, and conversely, every element of `power_set(x)` is a subset of x.

Builtin implementation of power set axiom (pseudo code):
```
fn power_set(x set) set
know:
	forall x set, y power_set(x):
		y $subset_of x
	forall x set, y set:
		y $subset_of x
		=>:
			y $in power_set(x)
```

```litex
forall x, y set:
    x $subset_of y
    =>:
        x $in power_set(y)
```

**Example explanation**: This example shows that if x is a subset of y, then x automatically belongs to the power set of y. This is the fundamental property of power sets: they contain exactly all subsets of the original set.

9. Axiom of choice (well-ordering principle): every set can be well-ordered. For any set X, there exists a function f from X to the union of the members of X, called a "choice function", such that forall Y $in X, one has f(Y) $in Y.

**Explanation**: The Axiom of Choice is perhaps the most controversial of the ZFC axioms, though it is now widely accepted. It states that given any collection of nonempty sets, we can choose one element from each set simultaneously, even if there are infinitely many sets and no explicit rule for making the choices. This axiom is equivalent to several important mathematical statements, including Zorn's Lemma and the well-ordering principle. It's essential for many proofs in analysis, topology, and algebra, but it also leads to some counterintuitive results (like the Banach-Tarski paradox).

**Litex implementation**: The `choice` function implements the choice function. Given a set x whose elements are themselves sets, `choice(x)` is a function that selects one element from each member of x.

Builtin implementation of axiom of choice (pseudo code):

```
fn choice(x set) fn(x) cup(x)
know imply axiom_of_choice(x set):
	forall y x:
		choice(x)(y) $in y
```

```litex
$axiom_of_choice(R)
forall x R:
    choice(R)(x) $in x
    choice(R)(x) $in cup(R)
```

**Example explanation**: This example demonstrates the Axiom of Choice in action. If R is a set whose elements are themselves sets, then `choice(R)` is a function that, for each element x in R, selects an element from x. The example shows that `choice(R)(x)` belongs to both x (the set it was chosen from) and to `cup(R)` (the union of all sets in R). This illustrates how the choice function allows us to simultaneously select elements from each member of a collection of sets.