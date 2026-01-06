# Existential Factual Statement

_The beginning is the most important part of the work._

_-— Plato_

## Introduction

In this section, we'll explore existential factual statements in Litex. You'll learn how to define existential factual statements and how to use them in Litex. By the end of this section, you'll be able to use existential factual statements in Litex to express mathematical statements.

## Definition

Syntax:

```
exist param1 set1, param2 set2, ... st $predicate_name(...)
```

Here param1, param2, ... are free objects which are not bound by the existential statement.

```litex
prop p(x, y R)

know forall x R: exist z R st $p(x, z)

exist z R st $p(1, z)
```

Here `exist z R st $p(1, z)` matches `forall x R: exist z R st $p(x, z)`, so it is true.

## Use Existential Factual Statement To Define Objects

The existential factual statement can be used to define a new object with existential promise.

```litex
prop p(x, y R)

know forall x R: exist z R st $p(x, z)

have z R st $p(1, z)
```

Here `have z R st $p(1, z)` works by 1. check related existential fact `exist z R st $p(1, z)`, 2. define a new object `z` with the property `z $in R` and `$p(1, z)`.

Since `exist z R st $p(1, z)` is true, `have z R st $p(1, z)` works.

You may want to write objects satisfy many properties at once, for example: `exist x R st x > 0, x < 10`. But since you can just write one property at a time, you can not do so. A way to get around this is using set builder `exist x R st x $in {z R: 0 < z, z < 10}`.

```litex
know forall x, y R: x < y => exist z R st z $in {t R: x < z, z < y}
have z R st z $in {t R: 1 < t, t < 2}

# Since `know forall x, y R: x < y => $is_nonempty_set({t R: x < t, t < y})`, you can write this:
have a {t R: 1 < t, t < 2}
```

## Prove Existence of an object

Litex uses keyword `prove_exist` to prove existence of an object

Syntax:

```
prove_exist obj1, obj2 ...: exist_obj1 set1, exist_obj2 set2 ... st $predicate(...):
    prove_statement1
    ...
```

Here we want to prove `exist_obj1 set1, exist_obj2 set2 ... st $predicate(...)` and we want to show `obj1, obj2 ...` are exactly objects that satisfies 1. `obj1 $in set1`, `obj2 $in set2` ... 2. By replacing exist_obj1, exist_obj2 ... with obj1, obj2 ... the predicate is valid. When there is no prove statement, you can skip that part

Example:

```litex
prove_exist 1: x N st x > 0:
    1 > 0

# short form
prove_exist 1: x N st x > 0
```

Here when x = 1, we have `1 $in N` and `1 > 0`. After execution, `exist x N st x > 0` is inferred.

## Relation between Existential Factual Statement and Nonempty Set

In many ways, existential factual statements is equivalent to a set is a nonempty set

```litex
{x R: x > 0} $is_nonempty_with_item 1
prove_exist 1 : x R st x > 0
```


