# Function Template: The Blueprint of Functions

A definition of a function has the following parts: 1. function name 2. parameters and the sets they belong to 3. domain facts of these parameters 4. the properties that the function satisfy. 5. the return value of this function belongs to what set.

For example

```litex
fn f(x R, y N) R:
    x > y
    =>:
        f(x, y) = x - y
```

1. The name of this function is `f`
2. The parameters `x, y` must be in `R` and `N`,
3. domain fact `x > y` must be true for parameters `x, y`.
4. The fact that `f(x, y) = x - y` is by definition true.
5. The return value of this function is in `R`, 

Apparently, there are countless functions with domain `x $in R, y $in R, x > y`, with property `f(x ,y) = x - y`, `f(x ,y) $in R`. `fn_template` allows to declare a set of functions with certain properties.

For example

```litex
fn_template sequence_of_real_numbers():
    fn (n N) R
```

Here we have defined a set of functions. All of these functions take a natural parameter and return a real number. In mathematics, sequences are very common. For example, sometimes we define a linear sequence a[n] = n, a constant sequence a[n] = c, or the Fibonacci sequence a[n+2] = a[n+1] + a[n]. In fact, these sequences are simply functions whose input is a natural number and whose output is a real number. We say `a $in sequence_of_real_numbers()` to say sequence `a` take a natural parameter and return a real number.

How about defining a sequence of integers, a sequence of rational numbers, a sequence of real numbers, a sequence of happy baby characters?

```litex
fn_template integer_sequence():
	fn (n N) Z
fn_template rational_sequence():
	fn (n N) Q
fn_template real_sequence():
	fn (n N) R

have happy_baby_characters nonempty_set

fn_template happy_baby_characters_sequence():
	fn (n N) happy_baby_characters 

let a integer_sequence(), b rational_sequence(), c real_sequence(), d happy_baby_characters_sequence()
```

They all looks similar, don't they? Litex allows you to define them in a very short form.

```litex
fn_template sequence(s set):
	fn (n N) s

let a sequence(Z), b sequence(Q), c sequence(R), d sequence(happy_baby_characters_sequence)
```

In this case template parameter `s` of `sequence` definition, replaces the `Z` of `integer_sequence` definition, `Q` of `rational_sequence` definition, `R` of `real_sequence()` definition. So `sequence(Z)` is equivalent to `integer_sequence()`.

Generally, a function template definition in Litex looks like this:

```
fn_template T(template_parameter1 template_parameter1_set, ...):
    dom: # domain of template parameters
        template_dom_fact_1
        ...
    fn (parameter1 set1, parameter2 set2...) fn_return_value_set:
        # domain of this function
        dom_fact_1
        dom_fact_2
        ...
        =>:
            then_fact_1
            then_fact_2
            ...
```

What does `f $in T(template_parameters)` mean? It means:

0. template_parameters must satisfy domain of template parameters.

1. The domain of f is superset of the domain of the `fn` under declaration of T: the domain of `f` has parameters `parameter1 set1, parameter2 set2...` with domain dom_fact_1, dom_fact_2, ...

2. When restricted on the domain of the `fn` under declaration of T, the function f satisfies all the then facts in `fn`: `f` satisfies `then_fact_1`, `then_fact_2`, ... and the return value is in set `fn_return_value_set`

Function template can be very helpful, especially when we are defining multiple functions with similar structure. For example, we want to define the set of all finite positive sequences (a sequence is a function from natural numbers to some set) with at least 10 items. Obviously, there are infinitely many functions that satisfy those requirements. We can do this by defining a function template.

For example, we define the set of all finite positive sequences with at least 10 items. 

```litex
fn_template finite_positive_sequence_with_at_least_10_items(length N_pos):
    dom:
        length >= 10
    fn (n N_pos) R:
        n <= length
        =>:
            finite_positive_sequence_with_at_least_10_items(n) > 0

# length = 12, 12 >= 10 so everything is fine.
let f finite_positive_sequence_with_at_least_10_items(12)

f(9) > 0

# f(-1) > 0 #Error: -1 $in N_pos is not true

# f(17) > 0 #Error: 17 <= 12 is not true
```

Notice `12 >= 10` must be true so that `finite_positive_sequence_with_at_least_10_items(12)` is valid. `f(9) > 0` is true because `f $in $finite_positive_sequence_with_at_least_10_items(12)` and all functions in finite_positive_sequence_with_at_least_10_items(12) can take parameter `n` with properties `n $in N_pos, n <= 12` and return a function with property `

The `f` here is equivalent to `f` defined here.

```litex
fn f(n N_pos) R:
    n <= 12
    =>:
p        f(n) > 0
```

<!-- TODO: Return Set Inference --> 

## Return Set Inference

A function can return a function. For example, the addition of two functions return a new function. Litex checks the return set of the function to be a set, and checks whether you can indeed pass parameters to the returned function.

```litex
fn_template T0():
    fn (x R, y R) R

fn_template T1():
    fn (x R) T0()

let a T1()

a(1)(2,3) $in R
```

`a` is a function that satisfies the function template `T1()`, i.e. You can define `a` like `fn a(x R) T0()`. a(1) is a function which satisfies the function template `T0()`, because `a` takes `x = 1` as parameter and returns a function which satisfies the function template `T0()`, so a(1) is a function in form `fn (x R, y R) R`. Since `a(1)` takes 2 real parameters and return a real number, `a(1)(2,3) $in R` is true.

Notice how useful the above functionality is. You can define a function that takes a function as parameter and returns a function. This is very common in mathematics.  

```litex
have has_very_special_meanings nonempty_set

fn_template T3():
    fn (x R) has_very_special_meanings

fn_template T2():
    fn (x R, y R, z R, m R) T3()

fn_template T1():
    fn (x R) T2()

fn_template T0():
    fn (x R) T1()

fn w(x R) T0()

have b, z, d, g, s, m R

w(b)(z)(d)(g, s, m, m)(17) $in has_very_special_meanings
```

As you can see, you can make the chain of function calls arbitrarily long and complicated.

```litex
have has_very_special_meanings nonempty_set
prop very_special(x has_very_special_meanings)

fn_template T3(n R):
    dom:
        n < 10
    fn (x R) has_very_special_meanings

fn_template T2(n R):
    dom:
        n $in N_pos
    fn (x R, y R, z R, m R) T3(n)

fn_template T1(n R):
    dom:
        n $in N
    fn (x R) T2(n)

fn_template T0(n R):
    dom:
        n >= 1
    fn (x R) T1(n)

fn w(x R) T0(1)

have b, z, d, g, s, m R

w(b)(z)(d)(g, s, m, m)(17) $in has_very_special_meanings
```

`w` is in template `T0(1)`, so `w(b)` is in template `T1(1)`, so `w(b)(z)` is in template `T2(1)`, so `w(b)(z)(d)` is in template `T3(1)`, so `w(b)(z)(d)(g, s, m, m)` is in template `T4(1)`. 1 satisfies `n >= 1` so that `T0(1)` is valid. 1 satisfies `n $in N`, so that `T1(1)` is valid. 1 satisfies `n $in N_pos`, so that `T2(1)` is valid. 1 satisfies `n < 10`, so that `T3(1)` is valid. 