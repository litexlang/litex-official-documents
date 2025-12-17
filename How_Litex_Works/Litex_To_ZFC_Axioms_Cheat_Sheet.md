## Litex to ZFC Axioms Cheat Sheet

_If people do not believe that mathematics is simple, it is only because they do not realize how complicated life is._

_- John von Neumann_

---

1. Axiom of extensionality: `forall x, y set: x = y <=> forall z: z $in x <=> z $in y`

Litex example: equal_set is a built-in proposition that checks if two sets are equal by checking if all elements of the first set are in the second set and all elements of the second set are in the first set.

```litex
forall x, y set:
    forall a x:
        a $in y
    forall a y:
        a $in x
    <=>:
        $equal_set(x, y)
```

2. Axiom of regularity: every nonempty set A has an element Y that is disjoint from the set A, i.e. for all items z in Y, z is not in A; for all items z in A, z is not in Y.

```litex
have A nonempty_set

have Y st $axiom_of_regularity(A)

forall z A: not z $in Y
forall z Y: not z $in A
```

3. Axiom schema of specification

Subsets are commonly constructed using set builder notation. For example, the positive integers can be constructed as {x Z: x > 0}. In general, the subset of a set z obeying a formula P(x) is constructed as {x z: $P(x)}. Note that the axiom schema of specification can only construct subsets and does not allow the construction of entities of more general form {x set: $P(x)}. (This restriction is necessary to avoid Russell's paradox.)

Example:

```litex
forall x {x R: x > 0}:
    x > -1
```

4. Axiom of pairing: for any two sets A and B, there exists a set {A, B} that contains exactly A and B. Generally, given any finite number of sets A1, A2, ..., An, there exists a set {A1, A2, ..., An} that contains exactly A1, A2, ..., An.

Example: We have a set contains and only contains two elements 1 and 2.

```litex
have a set = {1, 2}
```

5. Axiom of union: for any set x, there exists a set Union(x) that contains all elements of the elements of x.

```litex
forall x set, y union_of_items(x): y $subset_of x
forall x, y set: y $subset_of x => y $in union_of_items(x)
```

6. 