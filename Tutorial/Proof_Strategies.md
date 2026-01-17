# Proof Strategies

_I suppose it is tempting, if the only tool you have is a hammer, to treat everything as if it were a nail._

_— Abraham Maslow_

The most fundamental way to prove a statement in Litex, or math in general, is `match and substitution`. It is a very simple and intuitive method. However, there are other ways to prove a statement in Litex. People use them unconsciously all the time, too. Just like different tools are for different mechanical tasks, different proof strategies are for different proof tasks. One should never force himself to use a hammer when a screwdriver is more suitable.

*Proof In Each Case* – Assume the opposite of what you want to prove, and show that this leads to a contradiction.

*Proof by Cases* – Divide the situation into several possible cases, prove the statement in each case, and conclude that it holds universally. For example, when 1. we know `$p(x) or $q(x)`, 2. we can prove when `$p(x)` is true, `$r(x)` is also true. 3. we can prove when `$q(x)` is true, `$r(x)` is also true. With this, we can prove `$r(x)` is always true.

*Proof by Induction* – Establish a base case, then show that if the statement holds for one step, it also holds for the next, covering all natural numbers. This is called `principle of mathematical induction`. Technically, it is an axiom schema: it is a template for producing an infinite number of axioms.

*Proof by Enumeration* – Suppose `s` is a finite set, e.g. `s = {1,2,3}`, we want to prove `forall x s => x > 0`. We can simply check each element `x` in `s` one by one whether `x > 0` holds. This is different from an infinite set: a computer cannot iterate over infinitely many elements in finite time and check whether `x > 0` holds for each element. Actually, Functionality of `enum` can be covered by `cases`, but `enum` is more concise and readable.

*Proof in Range* - Given two integers `a <= b` and a set which is subset of `{x Z | a <= x < b}`, we prove iteratively over each integer `x` in that set whether some properties hold.

*Functionality Enhancement: 

We will explore these methods in detail in the following sections.

## Prove by Contradiction: A coin cannot be heads and tails at the same time.

In math, one common way to prove a statement is to prove its negation is false. This method is called `Prove by Contradiction`.

```
# short version
prove_contra fact_you_want_to_prove:
    statement1
    ...
    final_statement

# multiple lines version
claim:
    fact_you_want_to_prove
    prove_contra:
        statement1
        ...
        final_statement
```

`prove_contra` should always be used in `claim` block. In the environment of `prove_contra`, `not fact_you_want_to_prove` is assumed to be true. To make the process of proving by contradiction works, the `final_statement` should be a fact that is both true and false. After that, the assumption `not fact_you_want_to_prove` is false and `fact_you_want_to_prove` is true.

For example:

```litex
prop g(x R)
prop s(x R)
prop q(x R)

know:
    forall x R: $g(x) => $s(x)
    forall x R: $s(x) => $q(x)
    not $q(17)

# short version
prove_contra not $g(17):
    $s(17)
    $q(17)

claim:
    not $g(17)
    prove_contra:
        $s(17)
        $q(17)
```

In this case, since `g(x)` leads to `s(x)` leads to `q(x)`, when `not q(x)` is true, `g(x)` can not be true.

## Example

Here is a classic example, prove sqrt(2) is irrational using Proof by Contradiction:

```litex
# prove sqrt(2) is irrational
# 证明 sqrt(2) 是无理数

fn logBase(x, y N) N:
    dom:
        x != 0

know forall x, y, z N => logBase(z, x^y) = y * logBase(z, x), logBase(z, x*y) = logBase(z, x) + logBase(z, y)

know forall x N: x != 0 => logBase(x, x) = 1

prove_contra not sqrt(2) $in Q:
    sqrt(2) > 0
    have x, y st $Q_pos_in_frac(sqrt(2))
    
    x = sqrt(2) * y
    x ^ 2 = (sqrt(2) ^ 2) * (y ^ 2)
    sqrt(2) ^ 2 = 2
    x ^ 2 = 2 * (y ^ 2)

    logBase(2, x ^ 2) = logBase(2, 2 * (y ^ 2))     
    logBase(2, x ^ 2) = 2 * logBase(2, x)
    logBase(2, y ^ 2) = 2 * logBase(2, y)

    logBase(2, 2 * (y ^ 2)) = logBase(2, 2) + logBase(2, y ^ 2)
    logBase(2, 2) = 1
    logBase(2, 2 * (y ^ 2)) = 1 + logBase(2, y ^ 2)

    logBase(2, x ^ 2) = 1 + 2 * logBase(2, y)
    2 * logBase(2, x) = 1 + 2 * logBase(2, y)

    =:
        0
        (2 * logBase(2, x)) % 2            
        (1 + 2 * logBase(2, y)) % 2
        
    =:
        (1 % 2 + (2 * logBase(2, y)) % 2) % 2
        (1 + 2 * logBase(2, y)) % 2
        (1 % 2 + (2 * logBase(2, y)) % 2) % 2
        (1 + 0) % 2
        1
    0 = 1
```

## Prove by Induction: The Power of Recursion

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

Litex uses keyword `prove_induc` to support proving by induction.

```
prove_induc(specific_fact, the_object_you_want_to_iterate_over, induction_begin_from_positive_index)
```

For example, there is a proposition `p(x, n)` that is true for `n = 2` and when `p` is true for `n`, it is also true for `n+1` if `n >= 2`. We want to prove that `p(x, n)` is true for all `n >= 2`.

```litex
prop p(x R, n N_pos)

let x R

know:
    forall n N_pos: n >= 2, $p(x, n) => $p(x, n+1)
    $p(x, 2)

prove_induc($p(x, n), n, 2)

forall n N_pos: n >= 2 => $p(x,n)
```

## Prove by Cases: Divide and Conquer in Proofs

**Proof by cases** is a reasoning method where we split the problem into a finite number of mutually exclusive scenarios (cases). If the statement to be proved holds in *every* case, then it holds in general.

This method relies on the logical principle of **disjunction elimination**:

* If we know that one of several possibilities (\$p \lor q \lor \dots\$) must be true,
* and we can show that the desired conclusion follows from each possibility individually,
* then the conclusion is universally valid.

In practice, this means:

1. Identify the possible cases that cover all situations.
2. Prove the claim separately under the assumption of each case.
3. Combine the results to conclude that the claim holds overall.

This approach is especially useful when direct reasoning is difficult, but the problem naturally breaks into distinct scenarios — for example, proving a property of an integer by considering the cases “even” and “odd.”

The syntax is:

```
prove_cases:
    =>:
        then_facts
    case condition1:
        proof1
    ...
    case conditionN:
        proofN
```

condition1 or condition2 or ... or conditionN is must be true. We prove `then_facts` in each case after running the proof steps in each proof section.


Here is an example:

```litex
know forall x R: x > 0 => x^2 > 0

claim:
    forall a R => a^2 >= 0
    prove:
        prove_cases:
            =>:
                a^2 >= 0
            case a > 0:
                a * a = a ^ 2
                a ^ 2 > 0
                a ^ 2 >= 0
            case a = 0:
                a * a = 0 ^ 2 = 0
                a ^ 2 >= 0
            case a < 0:
                a * a = a ^ 2
                a ^ 2 > 0
                a ^ 2 >= 0
```

In this example, we use the known fact `forall x R: x > 0 => x^2 > 0` to prove `forall a R => a^2 >= 0`. We split the case into `a > 0`, `a = 0`, and `a < 0`. And we prove `a^2 >= 0` in each case.

Here is another example: solve the quadratic equation `x^2 + 2 * a * x + b = 0` when `a^2 - b >= 0`. We want to prove that `x = -a + sqrt(a^2 - b) or x = -a - sqrt(a^2 - b)`.

```litex
claim:
    forall a, b, x R:
        x^2 + 2 * a * x + b = 0
        a^2 - b >= 0
        =>:
            x = -a + sqrt(a^2 - b) or x = -a - sqrt(a^2 - b)
    prove:
        sqrt(a^2 - b) * sqrt(a^2 - b) = sqrt(a^2 - b) ^ 2 = a^2 - b
        (x + a - sqrt(a^2 - b)) * (x + a + sqrt(a^2 - b)) = x ^ 2 + 2 * a * x + a^2 - sqrt(a^2 - b) ^ 2 = x ^ 2 + 2 * a * x + a^2 - (a^2 - b) = x ^ 2 + 2 * a * x + b = 0
        $product_is_0_then_at_least_one_factor_is_0(x + a - sqrt(a^2 - b), x + a + sqrt(a^2 - b))
        
        prove_in_each_case:
            x + a + sqrt(a^2 - b) = 0 or x + a - sqrt(a^2 - b) = 0
            =>:
                x = -a + sqrt(a^2 - b) or x = -a - sqrt(a^2 - b)
            prove:
                x + a + sqrt(a^2 - b) + (-a - sqrt(a^2 - b)) = 0 + (-a - sqrt(a^2 - b))
                x = 0 + (-a - sqrt(a^2 - b))
                x = -a - sqrt(a^2 - b) 
            prove:
                x + a - sqrt(a^2 - b) + (-a + sqrt(a^2 - b)) = 0 + (-a + sqrt(a^2 - b))
                x = 0 + (-a + sqrt(a^2 - b))
                x = -a + sqrt(a^2 - b)
```

We prove triangle inequality by proving in each case.

```litex
claim:
    forall x, y R:
        abs(x + y) <= abs(x) + abs(y)
    prove:
        prove_in_each_case:
            or:
                x >= 0
                x < 0
            =>:
                abs(x + y) <= abs(x) + abs(y)
            prove:
                x >= 0
                prove_in_each_case:
                    or:
                        y >= 0
                        y < 0
                    =>:
                        abs(x + y) <= abs(x) + abs(y)
                    prove:
                        y >= 0
                        abs(x) = x
                        abs(y) = y
                        x + y >= 0
                        abs(x + y) = x + y
                        abs(x + y) = abs(x) + abs(y)
                        abs(x + y) <= abs(x) + abs(y)
                    prove:
                        y < 0
                        abs(x) = x
                        abs(y) = -y
                        prove_in_each_case:
                            or:
                                x + y >= 0
                                x + y < 0
                            =>:
                                abs(x + y) <= abs(x) + abs(y)
                            prove:
                                x + y >= 0
                                abs(x + y) = x + y
                                y < 0
                                x + y < x
                                x + y <= x
                                -y > 0
                                y < 0
                                x + (-y) > x
                                x < x + (-y)
                                x + y < x
                                x + y <= x + (-y)
                                abs(x + y) <= abs(x) + abs(y)
                            prove:
                                x + y < 0
                                abs(x + y) = -(x + y) = -x - y
                                x >= 0
                                -x <= 0
                                -x - y <= 0 -y
                                -x - y <= -y
                                -y <= x + (-y)
                                -x - y <= x + (-y)
                                abs(x + y) <= abs(x) + abs(y)
            prove:
                x < 0
                prove_in_each_case:
                    or:
                        y >= 0
                        y < 0
                    =>:
                        abs(x + y) <= abs(x) + abs(y)
                    prove:
                        y >= 0
                        abs(x) = -x
                        abs(y) = y
                        prove_in_each_case:
                            or:
                                x + y >= 0
                                x + y < 0
                            =>:
                                abs(x + y) <= abs(x) + abs(y)
                            prove:
                                x + y >= 0
                                abs(x + y) = x + y
                                x < 0
                                x + y < y
                                x + y <= y
                                -x > 0
                                -x >= 0
                                (-x) + y > y
                                x + y < y
                                x + y <= y
                                x + y <= (-x) + y
                                abs(x + y) <= abs(x) + abs(y)
                            prove:
                                x + y < 0
                                abs(x + y) = -(x + y) = -x - y
                                y >= 0
                                -y <= 0
                                -x - y <= -x
                                -x - y <= (-x) + y
                                abs(x + y) <= abs(x) + abs(y)
                    prove:
                        y < 0
                        abs(x) = -x
                        abs(y) = -y
                        x + y < y
                        y < 0
                        x + y < 0
                        abs(x + y) = -(x + y) = -x - y
                        abs(x + y) = -x + (-y) = abs(x) + abs(y)
                        abs(x + y) <= abs(x) + abs(y)

```

# Prove by Enumeration

If a set is finite, then to prove that forall x in this set some property holds, we can simply check each element one by one. In this way, unlike the general case of infinite sets, the conclusion can be obtained by directly traversing all the elements in the set.

Litex uses keyword `prove_enum` to support proving over finite set.

```
prove_enum(x_name, set_name)
    ... # domain facts
    =>:
        ... # then facts
    prove:
        ...
```

The sets in universal fact header must be finite.

For example, we want to prove that forall x in the set {1, 2, 3}, x is less than 4. Litex iterates over `x = 1`, `x = 2`, `x = 3` to see whether the `then` facts (e.g. In this case, the `x > 0` in `forall x s => x > 0`) is true or not.

There can be no domain facts, no prove sections, or both.

```litex
have s set = {1, 2, 3}

prove_enum(x s):
    x > 0 # then facts
```

Empty set, which is the very special case of finite set, is also supported. As you can see, any factual statement is true on items in empty set, since there is no item in empty set.

```litex
have s set = {}

# any factual statement is true on empty set
prove_enum(x s):
    x > 0
    x < 0
```

## Prove For In Range

Given a set which is the subset of a consecutive integers range, we can prove a universal fact over this set by iteratively proving over each integer in this set.

```
prove_for variable_name range_type(lower, upper):
    dom:
        ...
    =>:
        ... # then facts
    prove:
        ...
``` 

For example, we want to prove that forall x in the range {1, 2, 3}, x is less than 4.

```litex
prove_for i range(5, 8):
    i = 5 or i = 6 or i = 7

prove forall x Z: x = 5 or x = 6 or x = 7 => x >= 5, x < 8:
    prove_cases:
        =>:
            x >= 5
            x < 8
        case x = 5:
            do_nothing
        case x = 6:
            do_nothing
        case x = 7:
            do_nothing
```

## Prove_imply

**Purpose**: After proving an implication, whenever the proposition holds in the future, the `then` facts of the implication are automatically stored and available. In the normal case, you would know a `forall` statement, and that `forall` would be used to prove related `then` facts. However, if a particular `then` fact is frequently needed, manually writing it each time becomes tedious. This feature automates that process.

When you use `prove_imply`, you're telling Litex: "Whenever this proposition is true, automatically remember these consequences." This eliminates the need to repeatedly apply the same implication manually.

```litex
prop p(x R):
    x > 2

forall x R: $p(x) => x > 0

let x R: $p(x)

x > 0 # verified by forall x R: $p(x) => x > 0

forall x R: $p(x) => x > 0, 1 / x > 0 

1 / x > 0 # verified forall x R: $p(x) => x > 0, 1 / x > 0
```

```litex
prop p(x R):
    x > 2

prove_imply $p(x):
    =>:
        x > 0
    prove:
        x > 2
        x > 0

prove_imply $p(x) => 1 / x > 0:
    x > 2
    x > 0

let x R: $p(x)

x > 0 # verified by x > 0, generated by prove_imply $p(x) => x > 0

forall x R: $p(x) => x > 0, 1 / x > 0 # verified by x > 0, generated by prove_imply $p(x) => 1 / x > 0
```

This can be extremely useful. However, do not use it too much, because if you bind too many facts to a proposition, it will be very memory-consuming.