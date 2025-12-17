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

6. Axiom schema of replacement: the image of a set under any definable function will also fall inside a set.

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

7. Axiom of infinity: there exists an infinite set.

Von Neumann uses axiom of infinity to construct the natural numbers. Keyword N in Litex is the built-in set of natural numbers, where `0 $in N` and `1 $in N` ... are true.

8. Axiom of power set: for any set x, there exists a set Power(x) that contains all subsets of x.

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

9. Axiom of choice (well-ordering principle): every set can be well-ordered. For any set X, there exists a function f from X to the union of the members of X, called a "choice function", such that forall Y $in X, one has f(Y) $in Y.

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