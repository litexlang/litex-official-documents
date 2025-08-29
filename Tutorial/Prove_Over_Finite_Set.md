# Prove Over Finite Set: Things are easy when they are finite

If a set is finite, then to prove that forall x in this set some property holds, we can simply check each element one by one. In this way, unlike the general case of infinite sets, the conclusion can be obtained by directly traversing all the elements in the set.

Litex uses keyword `prove_over_finite_set` to support proving over finite set.

```
prove_over_finite_set:
	universal_fact
    prove:
        statement1
        statement2
        ...
```

The sets in universal fact header must be finite.

For example, we want to prove that forall x in the set {1, 2, 3}, x is less than 4.

```litex
let s set:
    s := {1, 2, 3}

prove_over_finite_set:
    forall x s:
        x > 0
    prove:
        x > 0
```

Empty set, which is the very special case of finite set, is also supported. As you can see, any factual statement is true on items in empty set, since there is no item in empty set.

```litex
let s2 set:
    s2 := {}

# any factual statement is true on empty set
prove_over_finite_set:
    forall x s2:
        x > 0
        x < 0
    prove:
        x < 0
```

You can pass multiple sets to `prove_over_finite_set` to prove a universal fact over multiple sets. These sets must all be finite.

```litex
let s3, s4 set:
    s3 := {1, 2, 3}
    s4 := {1, 2, 3}

prove_over_finite_set:
    forall x s3, y s4:
        x * y >= 1
    prove:
        x * y >= 1
```