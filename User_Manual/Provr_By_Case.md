# Proof By Case 

## Description

`cases` is a proof strategy used when a problem needs to be broken down into distinct logical scenarios. It verifies that a conclusion holds in **all** possible scenarios derived from a disjunction (OR) statement.

## Syntax
```
cases: 
    =>:
        conlusion

    case condition_A: proof_steps_for_A ... conclusion

    case condition_B: proof_steps_for_B ... conclusion
```

## Examples

```litex
claim:
            forall x R: (x + 3)^2 = 121 => x = 8 or x = -14
            prove:
                (x + 3)^2 = 121
                x + 3 = sqrt(121) or x + 3 = -sqrt(121)
                11 = sqrt(121)
                cases:
                    =>:
                        x = 8 or x = -14
                    case x + 3 = 11:
                        x + 3 = 11
                        x = (x + 3) - 3 = 11 - 3 = 8
                    case x + 3 = -11:
                        x + 3 = -11
                        x = (x + 3) - 3 = -11 - 3 = -14
```
## Semantics
Execution of this statement has the following effects:

1.Validates that the cases statement (the disjunction) covers the necessary logical space (or is a known fact).

2.In each block, assumes the specific condition is true.

3.Verifies that all case blocks reach the same required conclusion or state.

Notes
Often used with the or keyword.

If any single case fails to prove the target, the entire statement fails