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

## Functionality of Existential Factual Statement

The existential factual statement can be used to define a new object with existential promise.

```litex
prop p(x, y R)

know forall x R: exist z R st $p(x, z)

have z R st $p(1, z)
```

Here `have z R st $p(1, z)` works by 1. check related existential fact `exist z R st $p(1, z)`, 2. define a new object `z` with the property `z $in R` and `$p(1, z)`.

Since `exist z R st $p(1, z)` is true, `have z R st $p(1, z)` works.