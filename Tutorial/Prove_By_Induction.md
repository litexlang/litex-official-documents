# Prove by Induction: The Power of Recursion

## The Core Idea

Mathematical induction is like a line of dominoes:

* First, you show that the very first domino falls (**base case**).
* Then, you show that whenever one domino falls, it will push the next one down (**induction step**).
* Therefore, all the dominoes will eventually fall, meaning the statement is true for every case.

## Two Key Steps

1. **Base Case**
   Prove the statement for the first number (often $n = 0$ or $n = 1$).

2. **Induction Step**
   Assume the statement is true for some number $n = k$ (this is the **induction hypothesis**).
   Then prove it must also be true for $n = k+1$.

## Why It Works

Once both steps are done, you’ve shown the statement works for the first case, and that the truth passes from each number to the next. 

It is so simple that people often overlook it; yet it is actually a mathematical axiom, without which the whole tower of mathematics would collapse.

Litex uses keyword `prove_by_induction` to support proving by induction.

```
prove_by_induction(specific_fact, the_object_you_want_to_iterate_over, induction_begin_from_positive_index)
```

For example, there is a proposition `p(x, n)` that is true for `n = 2` and when `p` is true for `n`, it is also true for `n+1` if `n >= 2`. We want to prove that `p(x, n)` is true for all `n >= 2`.

```litex
prop p(x R, n N_pos)

let x R

know:
    forall n N_pos: n >= 2, $p(x, n) => $p(x, n+1)
    $p(x, 2)

prove_by_induction($p(x, n), n, 2)

forall n N_pos: n >= 2 => $p(x,n)
```