# Function Template: The Blueprint of Functions

Before we dive into function template, we need to know what we are doing when we are declaring a new function using `fn`. We begin with an example:

```litex
fn f(x R, y N) R:
    x > y
    =>:
        f(x, y) = x - y
```

1. The name of this function is `f`
2. The parameters `x, y` must be in `R` and `N`, and further ore the fact that `x > y` must be true. In all, the domain of parameters is `x $in R, y $in N, x > y`
3. The return value of this function is in `R`, and the fact that `f(x, y) = x - y` is by definition be true.

Can we generalize the above assumptions over a function? Yes, we can. We can define a set of functions that has such domain with return value satisfying the above facts. `fn_template` (Function Template) allows you to do so.

Function template can be very helpful, especially when we are defining multiple functions with similar structure. For example, we want to define the set of all finite positive sequences (a sequence is a function from natural numbers to some set) with at least 10 items. Obviously, there are infinitely many functions that satisfy those requirements. We can do this by defining a function template.



A function template in Litex looks like this:

```
fn_template T(template-parameter-parameter-set-pairs):
    dom:
        template_dom_fact_1
        ...
    fn (function-parameter-parameter-set-pairs) the_set_where_the_return_value_of_this_function_belongs_to:
        dom_fact_1
        dom_fact_2
        ...
        =>:
            then_fact_1
            then_fact_2
            ...
```

You might be wondering, what does a function in a function template actually means. For example, what does `f $in T(parameters)` mean? It means:

1. The domain of f is superset of the domain of the `fn` under declaration of T: the domain of `f` satisfies function-parameter-parameter-set-pairs, and dom_fact_1, dom_fact_2, ...

2. When restricted on the domain of the `fn` under declaration of T, the function f satisfies all the then facts in `fn`: `f` satisfies `then_fact_1`, `then_fact_2`, ... and the return value is in set `the_set_where_the_return_value_of_this_function_belongs_to`

For example, we define the set of all finite positive sequences with at least 10 items. 

<!-- TODO：有严重的bug，需要修复 -->

```litex
fn_template finite_positive_sequence_with_at_least_10_items(length N_pos):
    dom:
        length >= 10
    fn (n N_pos) R:
        n <= length
        =>:
            finite_positive_sequence(n) > 0

let f finite_positive_sequence_with_at_least_10_items(12)
```

The `f` here is equivalent to `f` defined here.

```litex
fn f(n N_pos) R:
    n <= 12
    =>:
        f(n) > 0
```

When there is no further template parameter requirements, you can hide the template parameter set pairs. For example:

## Return Set Inference

A function can return a function. For example, the addition of two functions return a new function. Litex checks the return set of the function to be a set, and checks whether you can indeed pass parameters to the returned function.

```litex
prove:
    have has_very_special_meanings nonempty_set

    fn_template T7(t R):
        t >= 16
        fn (z R) has_very_special_meanings:
        	dom:
                z >= t

    fn_template T6(t R):
        fn (z R) T7(t)

    fn_template T5(t R):
        fn (z R) T6(t)

    fn_template T4(t R):
        fn (z R) T5(t)

    fn_template T3(t R):
        fn (z R) T4(t)

    fn_template T2(t R):
        fn (z R) T3(t)

    fn_template T(t R):
        fn (z R) T2(t)

    fn w(x R) T(16)

    have b, z, d, g, s, m R

    w(b)(z)(d)(g)(s)(m)(m)(17) $in has_very_special_meanings
```