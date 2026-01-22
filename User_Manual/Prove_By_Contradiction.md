# Prove By Contradiction

## Description

`contra` is a proof strategy that proves a statement by assuming its negation and deriving a contradiction.

## Syntax

There are two ways to use `contra`

1. Short version

```
contra reversible_fact:
    statement1
    statement2
    ...
    statementN
    impossible reversible_fact
```

2. Long version

```
claim:
    reversible_fact
    contra:
        statement1
        statement2
        ...
        statementN
        impossible reversible_fact
```

A reversible fact is a fact that can be reversed. In Litex, a `forall` fact can not be negated because of Litex's design, and you should use the equivalent `exist ...` to represent the negation of a `forall` fact. A specific fact, such as `x = 1`, `not y > 0`, `exist a N_pos st a < 0`, can be reversed. An `or` fact, such as `x = 1 or x = 2`, can also be reversed.

## Example

```litex
prop p(x R)
prop q(x R)
know forall x R: $p(x) => $q(x)
know not $q(17)

# short version
prove_contra not $p(17):
    $q(17)
    impossible not $q(17)

# long version
claim:
    not $p(17)
    contra:
        $q(17)
        impossible not $q(17)
```

## Semantics

Execution of this statement has the following effects:
1. We assume the negation of the reversible fact is true in the local environment.
2. All statements in the `contra` block are assumed to be true in the local environment.
3. If the `impossible` statement is true in the local environment, and its negation is also true in the local environment, then a contradiction is found.
4. The local environment is released and the reversible fact is true.

## Notes

1. `contra` is the companion to logical keyword `not`.