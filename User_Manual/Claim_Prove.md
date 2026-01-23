# Claim and Prove

## Description

The `claim` and `prove` block is the core structure for verifying mathematical statements in Litex. It explicitly states a goal (`claim`) and then provides a sequence of steps (`prove`) to reach that goal.

## Syntax
```
claim: 
    fact_to_check 
    prove: prove_steps
```

## Examples

```litex
# Simple algebraic proof
have x R
claim:
    x + x = 2 * x
    prove:
        x + x = 1 * x + 1 * x
        1 * x + 1 * x = (1 + 1) * x
        (1 + 1) * x = 2 * x

# Logical proof
claim:
    forall a R: a > 10 => a > 0
    prove:
        a > 10
        10 > 0
        a > 0
```

## Semantics
Execution of this statement has the following effects:
1.The system checks if the final state of the prove block implies or matches the claim.

2.If the verification succeeds, the fact_to_check becomes a known fact in the outer environment.

## Notes

In the prove block, you can use have, let, witness, and other statements to construct the logic path.