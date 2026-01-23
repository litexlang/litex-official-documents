# Let_Object_In_Set

## Description

`let` is a statement used to declare objects or variables in the environment **without** checking their existence. It allows the user to introduce symbols and assume arbitrary properties about them, which is useful for setting up hypothetical scenarios or algebraic manipulations.

## Syntax

There are two common forms:

1. **Simple Declaration**
```
let var1 set1, var2 set2, ...
```

2. **Declaration with Conditions**
```
let var1 set1, var2 set2: condition1 condition2 ...
```

## Examples

```litex
# Basic assumption
let x R, y Z

# Assumption with properties
let n N:
    n > 10
    n % 2 = 0

# System of equations (Assumption)
let a, b R:
    a + b = 5
    a - b = 1
```

## Semantics
Execution of this statement has the following effects:

1.Defines the specified symbols in the local environment.
2.Associates the specified sets (types) with these symbols.
3.Does not verify if such objects actually exist (unlike have).
4.Assumes all attached conditions (facts) are true for these symbols in the current context.

## Notes
Because let does not check existence, it is possible to declare contradictory objects (e.g., let x R: x > 0, x < 0). This is allowed for purposes like Proof by Contradiction, but should be used carefully in normal contexts.

If you need to guarantee that the object exists (e.g., ensuring a set is not empty before picking an element), use have instead.