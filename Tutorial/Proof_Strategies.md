# Proof Strategies

_I suppose it is tempting, if the only tool you have is a hammer, to treat everything as if it were a nail._

_— Abraham Maslow_

The most fundamental way to prove a statement in Litex, or math in general, is `match and substitution`. It is a very simple and intuitive method. However, there are other ways to prove a statement in Litex. People use them unconsciously all the time, too. Just like different tools are for different mechanical tasks, different proof strategies are for different proof tasks. One should never force himself to use a hammer when a screwdriver is more suitable.

*Proof by Contradiction* – Assume the opposite of what you want to prove, and show that this leads to a contradiction.

*Proof by Cases* – Divide the situation into several possible cases, prove the statement in each case, and conclude that it holds universally. For example, when 1. we know `or($p(x), $q(x))`, 2. we can prove when `$p(x)` is true, `$r(x)` is also true. 3. we can prove when `$q(x)` is true, `$r(x)` is also true. With this, we can prove `$r(x)` is always true.

*Proof by Induction* – Establish a base case, then show that if the statement holds for one step, it also holds for the next, covering all natural numbers. This is called `principle of mathematical induction`. Technically, it is an axiom schema: it is a template for producing an infinite number of axioms.

*Proof over a Finite Set* – Suppose `s` is a finite set, we want to prove `forall x s => $p(x)`. We can simply check each element `x` in `s` one by one whether `$p(x)` holds. This is different from an infinite set: a computer cannot iterate over infinitely many elements in finite time and check whether `$p(x)` holds for each element.

*Proof in Range* - Given two integers `a <= b`, we prove iteratively over each integer `x` in the range `[a, b]` whether some properties hold.

We will explore these methods in detail in the following sections.

## Prove by Contradiction: A coin cannot be heads and tails at the same time.

In math, one common way to prove a statement is to prove its negation is false. This method is called `Prove by Contradiction`.

```
claim:
    fact_you_want_to_prove
    prove_by_contradiction:
        statement1
        ...
        final_statement
```

`prove_by_contradiction` should always be used in `claim` block. In the environment of `prove_by_contradiction`, `not fact_you_want_to_prove` is assumed to be true. To make the process of proving by contradiction works, the `final_statement` should be a fact that is both true and false. After that, the assumption `not fact_you_want_to_prove` is false and `fact_you_want_to_prove` is true.

For example:

```litex
prop g(x R)
prop s(x R)
prop q(x R)

know:
    forall x R: $g(x) => $s(x)
    forall x R: $s(x) => $q(x)
    not $q(17)

claim:
    not $g(17)
    prove_by_contradiction:
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

claim:
    not sqrt(2) $in Q
    prove_by_contradiction:
        sqrt(2) > 0
        have x, y st $rational_positive_number_representation_in_fraction(sqrt(2))
        
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
prove_in_each_case:
    or(fact1, fact2, ..., factN)
    =>:
        then_fact
    prove:
        # assume fact1 is true, prove then_fact
    prove:
        # assume fact2 is true, prove then_fact
    ...
    prove:
        # assume factN is true, prove then_fact
```

If `or(fact1, fact2, ..., factN)` is true, and each `prove` section, where the nth fact in `or` statement, proves `then_fact`, then ¸`then_fact` is always true.

For example

```litex
let weekdays set
prop is_monday(x weekdays)
prop is_tuesday(x weekdays)
prop is_wednesday(x weekdays)
prop is_thursday(x weekdays)
prop is_friday(x weekdays)
prop is_saturday(x weekdays)
prop is_sunday(x weekdays)
know forall x weekdays => or($is_monday(x), $is_tuesday(x), $is_wednesday(x), $is_thursday(x), $is_friday(x), $is_saturday(x), $is_sunday(x))

prop stay_at_home_doctor_wear_his_uniform(x weekdays)
know:
    forall x weekdays: $is_monday(x) => $stay_at_home_doctor_wear_his_uniform(x)
    forall x weekdays: $is_tuesday(x) => $stay_at_home_doctor_wear_his_uniform(x)
    forall x weekdays: $is_wednesday(x) => $stay_at_home_doctor_wear_his_uniform(x)
    forall x weekdays: $is_thursday(x) => $stay_at_home_doctor_wear_his_uniform(x)
    forall x weekdays: $is_friday(x) => $stay_at_home_doctor_wear_his_uniform(x)
    forall x weekdays: $is_saturday(x) => $stay_at_home_doctor_wear_his_uniform(x)
    forall x weekdays: $is_sunday(x) => $stay_at_home_doctor_wear_his_uniform(x)

prop stay_at_home_doctor_always_wear_his_uniform():
    forall x weekdays => $stay_at_home_doctor_wear_his_uniform(x)

claim:
    forall x weekdays => $stay_at_home_doctor_wear_his_uniform(x)
    prove:
        prove_in_each_case:
            or($is_monday(x), $is_tuesday(x), $is_wednesday(x), $is_thursday(x), $is_friday(x), $is_saturday(x), $is_sunday(x))
            =>:
                $stay_at_home_doctor_wear_his_uniform(x)
            prove:
                $is_monday(x)
            prove:
                $is_tuesday(x)
            prove:
                $is_wednesday(x)
            prove:
                $is_thursday(x)
            prove:
                $is_friday(x)
            prove:
                $is_saturday(x)
            prove:
                $is_sunday(x)

$stay_at_home_doctor_always_wear_his_uniform()
```

In example, we know any item in `weekdays` is either satisfies `is_monday`, `is_tuesday`, `is_wednesday`, `is_thursday`, `is_friday`, `is_saturday`, or `is_sunday`. And we know the stay at home doctor wears his uniform on each of these days. Therefore, we can conclude that the stay at home doctor wears his uniform on any day.

Here is another example:

```litex
know forall x R: x > 0 => x^2 > 0

claim:
    forall a R => a^2 >= 0
    prove:
        prove_in_each_case:
            or:
                a > 0
                a = 0
                a < 0
            =>:
                a^2 >= 0
            prove:
                a * a = a ^ 2
                a ^ 2 > 0
                a ^ 2 >= 0
            prove:
                =(0, 0^2, a ^ 2, a * a)
                0 >= 0
                a^2 >= 0
            prove:
                a ^ 2 = (-a) ^ 2
                -a > 0
                (-a) ^ 2 > 0
                (-a) ^ 2 >= 0
```

In this example, we use the known fact `forall x R: x > 0 => x^2 > 0` to prove `forall a R => a^2 >= 0`. We split the case into `a > 0`, `a = 0`, and `a < 0`. And we prove `a^2 >= 0` in each case.

# Prove Over Finite Set: Things are easy when they are finite

If a set is finite, then to prove that forall x in this set some property holds, we can simply check each element one by one. In this way, unlike the general case of infinite sets, the conclusion can be obtained by directly traversing all the elements in the set.

Litex uses keyword `prove_over_finite_set` to support proving over finite set.

```
prove_over_finite_set:
	universal_fact
```

The sets in universal fact header must be finite.

For example, we want to prove that forall x in the set {1, 2, 3}, x is less than 4. Litex iterates over `x = 1`, `x = 2`, `x = 3` to see whether the `then` facts (e.g. In this case, the `x > 0` in `forall x s => x > 0`) is true or not.

```litex
let s set:
    s := {1, 2, 3}

prove_over_finite_set:
    forall x s:
        x > 0
```

Empty set, which is the very special case of finite set, is also supported. As you can see, any factual statement is true on items in empty set, since there is no item in empty set.

```litex
have set s := {}

# any factual statement is true on empty set
prove_over_finite_set:
    forall x s:
        x > 0
        x < 0
```

You can pass multiple sets to `prove_over_finite_set` to prove a universal fact over multiple sets. These sets must all be finite.

```litex
let s3, s4 set:
    s3 := {1, 2, 3}
    s4 := {1, 2, 3}

prove_over_finite_set:
    forall x s3, y s4:
        x * y >= 1
```

Sometimes, the `then` facts are not immediately true. In this case, you can use `prove` section to prove them.

```
prove_over_finite_set:
    universal_fact
    prove:
        ...
    prove:
        ...
```

The number of `prove` sections here are the same as the number of sets in the universal fact header. The `prove` sections are executed in the order of the sets in the universal fact header.

For example

```litex
let s1 set, s2 set:
    s1 := {1, 2}
    s2 := {3, 4}

prove_over_finite_set:
    forall x s1, y s2:
        x * y >= 1
    prove:
        1 * 3 >= 1
    prove:
        1 * 4 >= 1
    prove:
        2 * 3 >= 1
    prove:
        2 * 4 >= 1
```

## Prove in Range: Iteratively Prove Over a Range of Integers

For some factual statements, especially those involving computation, it’s impossible to have a truly general theorem that directly tells us what every specific case looks like.
For example, if you want to prove that a given number is prime, the only possible way might be to go through all smaller numbers and test them one by one—there’s simply no alternative to checking each case directly.
The same applies to facts like proving that the positive divisors of a given number are exactly certain numbers (for instance, given 81, its divisors are exactly 1, 3, 9, 27, and 81).

In this case, we can use `prove_in_range` to prove the statement.

```
prove_in_range(a, b, x):
    domFacts_of_x
    =>:
        then_facts
    prove:
        prove_facts
```

It iterates over [a, b) (a < b), i.e. x = a, x = a+1, ..., x = b-1 to check

1. whether `domFacts_of_x` are true for `x`. If one domain fact can not be proved, it checks whether that the reverse of that domain fact is true. If both it and reverse of it is unknown, the check fails.
2. When all domain facts are proved to be true, it checks whether `prove_facts` are true for `x`. If one `prove_fact` can not be proved, the check fails.
3. If both `domFacts_of_x` and `prove_facts` are true for `x`, it checks whether `then_facts` are true for `x`. If one `then_fact` can not be proved, the check fails.
4. After that, when x is equal to the current value, everything is true.

```litex
prove_in_range(1, 10, x):
    x % 2 = 0
    =>:
        x >= 1
        x < 10
        x % 2 = 0
    prove:
        x >= 1
        x < 10
        x % 2 = 0


prove_in_range(1, 10, x):
    x >= 1
    x < 10
    prove:
        x >= 1
        x < 10

prove_in_range(1, 10, x):
    x % 2 = 0
    =>:
        x >= 1
        x < 10
        x % 2 = 0

prove_in_range(1, 10, x):
    x >= 1
```

Notice prove section and domain section are optional.