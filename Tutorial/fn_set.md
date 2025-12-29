# Function Set: The Blueprint of Functions

_Meaning lies as much in the mind of the reader as in the Haiku._

_— Douglas R. Hofstadter_

Function sets are one the most powerful features in Litex, inspired by template (generic programming) in C++. They are the blueprint of functions. Introduction of function set makes sequence, matrix, product of sets, and some of the most widely used concepts in math easy to define in Litex.

You can think of a function set as a power set. For example, fn(R)R, which contains all functions from R to R, is equivalent to set R^{R}.

## What is a Function Set?

A definition of a function has the following parts: 1. function name 2. parameters and the sets they belong to 3. domain facts of these parameters 4. the properties that the function satisfy. 5. the return value of this function belongs to what set.

For example

```litex
have fn f(x R, y N) R = x - y
```

1. The name of this function is `f`
2. The parameters `x, y` must be in `R` and `N`,
3. domain fact `x > y` must be true for parameters `x, y`.
4. The fact that `f(x, y) = x - y` is by definition true.
5. The return value of this function is in `R`, 

Apparently, there are countless functions with domain `x $in R, y $in R, x > y`, with have property `f(x ,y) = x - y`, `f(x ,y) $in R`. `fn_set` allows to declare a set of functions with certain properties.

For example

```litex
have fn_set sequence_of_real_numbers():
    fn (n N) R
```

Here we have defined a set of functions. All of these functions take a natural parameter and return a real number. In mathematics, sequences are very common. For example, sometimes we define a linear sequence a[n] = n, a constant sequence a[n] = c, or the Fibonacci sequence a[n+2] = a[n+1] + a[n]. In fact, these sequences are simply functions whose input is a natural number and whose output is a real number. We say `a $in sequence_of_real_numbers()` to say sequence `a` take a natural parameter and return a real number.

How about defining a sequence of integers, a sequence of rational numbers, a sequence of real numbers, a sequence of happy baby characters?

```litex
have fn_set integer_sequence():
	fn (n N) Z
have fn_set rational_sequence():
	fn (n N) Q
have fn_set real_sequence():
	fn (n N) R

have happy_baby_characters nonempty_set

have fn_set happy_baby_characters_sequence():
	fn (n N) happy_baby_characters 

let a integer_sequence(), b rational_sequence(), c real_sequence(), d happy_baby_characters_sequence()
```

They all looks similar, don't they? Litex allows you to define them in a very short form.

```litex
have fn_set sequence(s set):
	fn (n N) s

let a sequence(Z), b sequence(Q), c sequence(R)
```

In this case set parameter `s` of `sequence` definition, replaces the `Z` of `integer_sequence` definition, `Q` of `rational_sequence` definition, `R` of `real_sequence()` definition. So `sequence(Z)` is equivalent to `integer_sequence()`.

Generally, a function set definition in Litex looks like this:

```
have fn_set T(set_parameter1 set_parameter1_set, ...):
    dom: # domain of set parameters
        set_dom_fact_1
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

What does `f $in T(set_parameters)` mean? It means:

0. set_parameters must satisfy domain of set parameters.

1. The domain of f is superset of the domain of the `fn` under declaration of T: the domain of `f` has parameters `parameter1 set1, parameter2 set2...` with domain dom_fact_1, dom_fact_2, ...

2. When restricted on the domain of the `fn` under declaration of T, the function f satisfies all the then facts in `fn`: `f` satisfies `then_fact_1`, `then_fact_2`, ... and the return value is in set `fn_return_value_set`

Function set can be very helpful, especially when we are defining multiple functions with similar structure. For example, we want to define the set of all finite positive sequences (a sequence is a function from natural numbers to some set) with at least 10 items. Obviously, there are infinitely many functions that satisfy those requirements. We can do this by defining a function set.

For example, we define the set of all finite positive sequences with at least 10 items. 

```litex
have fn_set finite_positive_sequence_with_at_least_10_items(length N_pos):
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
let fn f(n N_pos) R:
    n <= 12
    =>:
        f(n) > 0
```

<!-- TODO: Return Set Inference --> 

## Return Set Inference

A function can return a function. For example, the addition of two functions return a new function. Litex checks the return set of the function to be a set, and checks whether you can indeed pass parameters to the returned function.

```litex
have fn_set T0():
    fn (x R, y R) R

have fn_set T1():
    fn (x R) T0()

let a T1()

a(1)(2,3) $in R
```

`a` is a function that satisfies the function set `T1()`, i.e. You can define `a` like `fn a(x R) T0()`. a(1) is a function which satisfies the function set `T0()`, because `a` takes `x = 1` as parameter and returns a function which satisfies the function set `T0()`, so a(1) is a function in form `fn (x R, y R) R`. Since `a(1)` takes 2 real parameters and return a real number, `a(1)(2,3) $in R` is true.

Notice how useful the above functionality is. You can define a function that takes a function as parameter and returns a function. This is very common in mathematics.  

```litex
have has_very_special_meanings nonempty_set

have fn_set T3():
    fn (x R) has_very_special_meanings

have fn_set T2():
    fn (x R, y R, z R, m R) T3()

have fn_set T1():
    fn (x R) T2()

have fn_set T0():
    fn (x R) T1()

fn w(x R) T0()

have b, z, d, g, s, m R

w(b)(z)(d)(g, s, m, m)(17) $in has_very_special_meanings
```

As you can see, you can make the chain of function calls arbitrarily long and complicated.

```litex
have has_very_special_meanings nonempty_set
prop very_special(x has_very_special_meanings)

have fn_set T3(n R):
    dom:
        n < 10
    fn (x R) has_very_special_meanings

have fn_set T2(n R):
    dom:
        n $in N_pos
    fn (x R, y R, z R, m R) T3(n)

have fn_set T1(n R):
    dom:
        n $in N
    fn (x R) T2(n)

have fn_set T0(n R):
    dom:
        n >= 1
    fn (x R) T1(n)

fn w(x R) T0(1)

have b, z, d, g, s, m R

w(b)(z)(d)(g, s, m, m)(17) $in has_very_special_meanings
```

`w` is in set `T0(1)`, so `w(b)` is in set `T1(1)`, so `w(b)(z)` is in set `T2(1)`, so `w(b)(z)(d)` is in set `T3(1)`, so `w(b)(z)(d)(g, s, m, m)` is in set `T4(1)`. 1 satisfies `n >= 1` so that `T0(1)` is valid. 1 satisfies `n $in N`, so that `T1(1)` is valid. 1 satisfies `n $in N_pos`, so that `T2(1)` is valid. 1 satisfies `n < 10`, so that `T3(1)` is valid. 


## Sequence

Function sets are the blueprint of functions. This is a rather abstract concept. A very common example is sequence. Since sequences and finite-length sequences are everywhere in math, Litex provides built-in keyword `seq`, `finite_seq` to represent sequences. They are declared in this way:

```
have fn_set seq(s set):
	fn (n N_pos) s

have fn_set finite_seq(s set, n N_pos):
    fn (x N_pos) s:
    	dom:
        	x <= n
```

Let's take a look at a simple example:

```litex
let a seq(R), b seq(R), c seq(R), d seq(R):
    forall n N => a(n) = n
    forall n N => b(n) = n * n
    forall n N => c(n) = n * n * n
    forall n N => d(n) = n * n * n * n

a(1) = 1
b(3) = 3 * 3 = 9
c(3) = 3 * 3 * 3 = 27
d(3) = 3 * 3 * 3 * 3 = 81
```

Here we have defined four sequences `a`, `b`, `c`, `d` which are all in the set `R`. We have also defined the domain of each sequence.

## Matrix

Matrices are another common application of function sets. A matrix can be thought of as a function that takes two indices (row and column) and returns a value. Using function sets, we can define matrices of any size:

```litex
have fn_set matrix(m N_pos, n N_pos):
    fn (i N_pos, j N_pos) R:
        dom:
            i <= m
            j <= n

let x matrix(3, 3)

x(2,2) = x(2,2)
```

Here, `matrix(m, n)` defines the set of all m×n matrices (functions from pairs of positive integers `(i, j)` where `i ≤ m` and `j ≤ n` to real numbers). When we declare `x matrix(3, 3)`, we're saying that `x` is a 3×3 matrix, and we can access its elements using `x(i, j)` where `1 ≤ i ≤ 3` and `1 ≤ j ≤ 3`.

## Sequence and Prove By Induction

When studying sequences, mathematical induction is often the most natural proof technique. Since sequences are defined step by step along the natural numbers, many of their properties are expressed in terms of the relationship between consecutive terms. This makes induction especially suitable for proving results such as general formulas and summation identities. Below, we use the formula for the sum of an arithmetic progression as an example, showing how sequences and induction work hand in hand in Litex.

The next example wants to prove the formula for the sum of an arithmetic progression:

$$
S_n = \frac{n}{2} (2a_1 + (n-1)d)
$$

where $a_1$ is the first term and $d$ is the common difference.


Here is the builtin implementation of sequence related stuffs:

```
have fn_set seq(s set):
	fn (n N_pos) s

have fn_set finite_seq(s set, n N_pos):
    fn (x N_pos) s:
    	dom:
        	x <= n

fn finite_seq_sum(n N_pos, a finite_seq(R, n), k N) R:
    dom:
        k <= n

know:
    forall n N_pos, a finite_seq(R, n), k N: k < n => finite_seq_sum(n, a, k+1) = finite_seq_sum(n, a, k) + a(k+1)
    forall n N_pos, a finite_seq(R, n) => finite_seq_sum(n, a, 1) = a(1)

fn finite_seq_product(n N_pos, a finite_seq(R, n), k N) R:
    dom:
        k < n

know:
    forall n N_pos, a finite_seq(R, n), k N: k < n => finite_seq_product(n, a, k+1) = finite_seq_product(n, a, k) * a(k+1)
    forall n N_pos, a finite_seq(R, n) => finite_seq_product(n, a, 1) = a(1)
```

Now you have a sequence of numbers, which are {1, 2, 3}. You can use `finite_seq_sum` to get the sum of the sequence.

```litex
let a finite_seq(R, 3):
    a(1) = 1
    a(2) = 2
    a(3) = 3
finite_seq_sum(3, a, 3) = finite_seq_sum(3, a, 2) + a(3) = finite_seq_sum(3, a, 2) + a(3) = finite_seq_sum(3, a, 1) + a(2) + a(3) = a(1) + a(2) + a(3) = 1 + 2 + 3 = 6
```

## Anonymous Function Set

The following two examples are equivalent:

```litex
have fn_set from_N_to_N():
    fn (n N) N

let f from_N_to_N()
```

```litex
let f fn(N) N
```

## Function Set is a set

```litex
have a set = {x fn(R)R: x(0) = 0}
let b a
b $in fn(R)R 
b(0) = 0

prop is_fib(f fn(N_pos) N):
    f(1) = 1
    f(2) = 1
    forall n N_pos: n >= 3 => f(n) = f(n - 1) + f(n - 2)

have F set = { f fn(N_pos) N: $is_fib(f) }
let f F
f $in fn(N_pos) N
$is_fib(f)
f(1) = 1
f(2) = 1
f(3) = f(1) + f(2) = 2
```

have `fn_set` is a subset of a power set. And `fn(R)R` is actually equal to `R^{R}`.

Essentially, `fn(X)Y` can be thought of as a "function" that takes sets as input—if we view `fn` itself as a function, its input parameters are sets. Typically, we don't allow a function's parameter type to be a set, which is why `fn` is a special keyword designed have specifically to handle sets. `fn_set` allows users to define their own functions similar to `fn`, making it convenient to write multivariate functions and impose type requirements on the input sets.