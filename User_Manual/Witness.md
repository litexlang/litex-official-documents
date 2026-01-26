# Witness Statement

## Description

The `witness` statement is the standard way to prove an existential proposition (`exist ...`). It allows you to provide a specific object (or objects) that satisfy the required condition "Such That" (`st`). 

## Syntax

```
witness object: existential statesment
```

## Examples
```litex
claim: 
    exist x N st x > 5
    prove:
        witness 6 : x N st x > 5
```

## Semantics
1. The specific values provided are substituted into the existential claim.

2. The proof goal shifts from "Does there exist an x?" to "Does this specific witness satisfy the condition?".

3. The system checks if the provided objects belong to the required sets defined in the exist statement.