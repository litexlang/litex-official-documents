# Proof By Induction

## Description

The `induc` statement triggers a proof by mathematical induction. It is typically used for claims involving natural numbers (`N`) or inductively defined structures. 

## Syntax

```litex
induc variable_name



prop P(n N)
# ... definitions of P ...
know:
    forall n N_pos: n >= 1, $P(n) => $  P(n+1)
    $   P(1)
claim:
    forall n N_pos: 
            =>:
             $P(n)
    prove:
        induc(n)
        case n=1: 
                $P(1)
        case n > 1:
                know P(n-1) # Induction Hypothesis
                $P(n)
                       