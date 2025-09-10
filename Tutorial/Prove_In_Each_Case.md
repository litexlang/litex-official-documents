# Prove by Cases: Divide and Conquer in Proofs

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