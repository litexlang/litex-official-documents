# Have Object In Nonempty Set

## Description

Have Object In Nonempty Set is a statement that defines a new object in the environment. The existence of the object is guaranteed by the fact that it is gotten from a nonempty set.

## Syntax

```
have object1 nonempty_set1, object2 nonempty_set2, ...
```

Although keyword `set`, `finite_set`, `nonempty_set` are not keywords (i.e. they are syntax sugar for `is_set`, `is_finite_set`, `is_nonempty_set`), we can still `have` objects from them.

```
have object1 set
have object2 finite_set
have object3 nonempty_set
```

## Examples

```litex
have x R, y Z, z N, a set, b finite_set, c nonempty_set
have e c # c is nonempty, so we can have an element e from c
```

## Semantics

Execution of this statement has the following effects:
1. Verify that the set is nonempty.
2. Define the object in the environment.
3. Memorize the fact that the object is in that nonempty set.

## Notes

1. Keywords `R`, `Z`, `N`, `Q`, `N_pos` etc. are built-in nonempty sets.
2. We use `witness_nonempty` to verify a set is nonempty.