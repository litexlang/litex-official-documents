# Function: The Glue of Symbols

_Function: a mathematical correspondence that assigns exactly one element of one set to each element of the same or another set_

_— Merriam-Webster Dictionary_

---

## Section 1: Understanding Functions in Litex

### Introduction

In this section, we'll explore the fundamental concept of functions in Litex. You'll learn that functions in Litex are fundamentally different from functions in programming languages—they are symbolic constructors, not executable code. By the end of this section, you'll understand why Litex doesn't compute function values and how functions work as "glue" that binds symbols together under certain restrictions (arguments must satisfy the domain of the function).

* In **programming languages** (e.g. Python, Lean), a function is a block of executable code that performs computation or side effects.
* In **mathematics**, a function is not executable code. Instead, it is a **symbolic constructor** that builds a new symbol from input symbols. You can think of it as *glue* that binds objects together to form a new object.

## Section 2: Built-in Functions

### Introduction

Litex provides built-in functions for common arithmetic operations. These functions come with their standard mathematical properties already built into the kernel, so you can use them immediately without defining them yourself.

### From Natural Language to Litex

In mathematics, we use operations like:
- "One plus one equals two"
- "Two times three equals six"
- "x squared plus two x plus one"

In Litex, these become:

```litex
1 + 1 = 2
2 * 3 = 6
have x R
x^2 + 2*x + 1 = (x + 1)^2
```

**Natural Language**: "Addition, multiplication, exponentiation" → **Litex**: `+`, `*`, `^` → **Meaning**: Built-in functions with known properties

### Detailed Explanation

`+`, `-`, `*`, `/`, `^`, `%` are built-in functions. Their daily properties are already in the Litex kernel. You can use them directly without any declaration:

```litex
1 + 1 = 2
2 * (1 + 1) = 3 + 1
have x, y, z R
(x + 1) ^ 2 = x ^ 2 + 2 * x + 1
(x + y) * (x + z) = x ^ 2 + x * y + x * z + y * z
x + z = z + x
```

These built-in functions follow standard mathematical properties:
- Commutative laws: `a + b = b + a`, `a * b = b * a`
- Associative laws: `(a + b) + c = a + (b + c)`, `(a * b) * c = a * (b * c)`
- Distributive laws: `a * (b + c) = a * b + a * c`

### Litex Code and Natural Language Correspondence

| Natural Language | Litex Code | Meaning |
|-----------------|------------|---------|
| "Add two numbers" | `a + b` | Built-in addition |
| "Multiply two numbers" | `a * b` | Built-in multiplication |
| "x to the power of 2" | `x^2` | Built-in exponentiation |
| "x plus y equals y plus x" | `x + y = y + x` | Commutative property |

### Summary

- Litex provides built-in arithmetic functions: `+`, `-`, `*`, `/`, `^`, `%`
- These functions come with standard mathematical properties
- No declaration needed—use them directly
- Besides built-in functions, Litex allows you to define your own functions

### Litex Syntax Reference

**Built-in arithmetic operators**:
- `+` : addition
- `-` : subtraction
- `*` : multiplication
- `/` : division
- `%` : modulo
- `^` : exponentiation

### Exercises

1. Write Litex code expressing that addition is commutative.
2. Verify the distributive law `a * (b + c) = a * b + a * c` in Litex.
3. Use built-in functions to express `(x + 1)^2 = x^2 + 2*x + 1`.

### Bonus: Why Built-in Functions?

Built-in functions are provided because they are so fundamental to mathematics that they appear everywhere. By building them into the kernel, Litex ensures they are always available and their properties are always known, making proofs more natural and efficient.

---

### Introduction

In programming, defining a function only requires writing a block of code. In mathematics, however, *declaring a new function must come with a proof of its existence*. Otherwise, the declaration is unsafe and could lead to contradictions. This section teaches you how to define functions with existence guarantees using `have fn`.

**Important**: In Litex, **function existence must be explicitly declared**. You cannot use a function without first proving or declaring its existence. This is fundamentally different from programming languages where functions are automatically available once defined.

### From Natural Language to Litex

In mathematics, we might say:
- "Define a function g such that g(x) = x"
- "Prove there exists a function h such that h(x) > 1 for all x > 0"
- "Define f(x) = x squared"

In Litex:

```litex
have fn g(x R) R = x

have fn:
    h(x R) R:
        x > 0
        =>:
            h(x) > 1
    prove:
        100 > 1
    = 100

have fn s(x R) R = x^2
```

**Natural Language**: "Define a function with existence proof" → **Litex**: `have fn ...` → **Meaning**: Function with guaranteed existence

### Detailed Explanation

When declaring a new object with existence guarantee, we use `have` keyword. When declaring a function with existence guarantee, we use `have fn` keyword.

There are several ways to define functions with `have fn`:

#### Method 1: Define by Equality (Simplest)

In daily math, when we want to define a function, we just write `g(x) = x` or `s(x) = x^2` or `q(x) = x^2 + 1` etc. In Litex, we can do the same thing:

```litex
have fn g(x R) R = x
have fn s(x R) R = x^2
have fn q(x R) R = x^2 + 1
```

These are equivalent to:

```litex
have fn:
    g(x R) R:
        g(x) = x
    prove:
        x = x
    = x

have fn:
    s(x R) R:
        s(x) = x^2
    prove:
        x^2 = x^2
    = x^2

have fn:
    q(x R) R:
        q(x) = x^2 + 1
    prove:
        x^2 + 1 = x^2 + 1
    = x^2 + 1
```

#### Method 2: Define with Proof

When you need to prove a function exists with specific properties:

```litex
have fn:
    a(x R) R:
        x > 0
        =>:
            a(x) > 0
    prove:
        x > 0
    = x
```

Explanation:
* In the `prove` section, the parameters of the function (here `x`) are assumed to satisfy the domain condition (`x > 0`).
* We must then provide an object that lies in the return set and satisfies all the conclusions (`a(x) > 0`).
* If we define `a(x) = x`, then `a(x) > 0` holds whenever `x > 0`.
* Writing `have x` ensures the existence of such a function.

#### Method 3: Define with Explicit Return Value

You can also use `=` to specify the return value directly:

```litex
have fn:
    h(x R) R:
        x > 0
        =>:
            h(x) > 1
    prove:
        100 > 1
    = 100
```

This defines `h(x) = 100` for all `x > 0`, which satisfies `h(x) > 1`.

#### Method 4: Case-by-Case Definition

You can define functions differently for different cases:

```litex
have fn:
    p(x R) R:
        x > 0
        =>:
            p(x) > x
    case 100 > x:
        do_nothing
    = 100
    case not 100 > x:
        x + 1 > x
    = x + 1
```

This defines:
- When `100 > x`: `p(x) = 100`
- When `not 100 > x` (i.e., `x >= 100`): `p(x) = x + 1`

Both cases satisfy `p(x) > x`.

You can also use the shorthand:

```litex
have fn f(x R) R =:
    case x > 0 : x
    case x <= 0 : 0

f(2) = 2
f(-1) = 0
```

### Key Difference: Function Existence vs. Other Existence

Proving other things' existence can only use `exist_prop`. However, function existence can be proven by **specifying a value for each element in the domain** that satisfies the conditions.

For example, `have fn f(x R) R = x` proves the existence of a function with domain R and range R, because we specify that each `f(x)` equals `x`, and `x` is in R.

### Litex Code and Natural Language Correspondence

| Natural Language | Litex Code | Meaning |
|-----------------|------------|---------|
| "Define g(x) = x" | `have fn g(x R) R = x` | Function with guaranteed existence |
| "Prove h exists with h(x) > 1" | `have fn: h(x R) R: x > 0 => h(x) > 1; prove: 100 > 1; = 100` | Existence proof |
| "Define f case by case" | `have fn f(x R) R =: case x > 0 = x; case x <= 0 = 0` | Conditional definition |

### Summary

- `have fn` defines functions with existence guarantees
- Simplest form: `have fn f(x set) return_set = expression`
- Can prove existence by providing values satisfying conditions
- Can define functions case-by-case
- Function existence is proven by specifying values, not just asserting existence
- **Function existence must be declared before use**: Unlike programming languages, you cannot use a function in Litex without first declaring its existence with `have fn` or `let fn`

### Litex Syntax Reference

**Simple definition**:
```
have fn function_name(param set) return_set = expression
```

**With proof**:
```
have fn:
    function_name(param set) return_set:
        domain_condition
        =>:
            conclusion
    prove:
        proof_statement
    have object_satisfying_conclusion
```

**With explicit return**:
```
have fn:
    function_name(param set) return_set:
        domain_condition
        =>:
            conclusion
    prove:
        proof_statement
    = return_value
```

**Case-by-case**:
```
have fn function_name(param set) return_set =:
    case condition1 = value1
    case condition2 = value2
```

### Exercises

1. Define a function `square` that takes a real number and returns its square, using `have fn`.
2. Define a function `positive` that takes a positive real number and returns a number greater than 1.
3. Define a function `sign` that returns 1 for positive numbers, -1 for negative numbers, and 0 for zero.

### Bonus: Why Prove Function Existence?

In mathematics, declaring a function without proving its existence can lead to contradictions. For example, if we could declare "a function f such that f(x) > f(x)" without proof, we'd have a contradiction. `have fn` ensures that functions we use are well-defined and exist, making our proofs safe and sound.

**Key Principle**: In Litex, **all functions must have their existence declared** before they can be used. Built-in functions (like `+`, `-`, `*`) have their existence guaranteed by the kernel. Custom functions must be declared with either `have fn` (with existence proof) or `let fn` (without existence proof, for assumed functions).

---

## Section 4: Defining Functions with `let fn`

### Introduction

In this section, you'll learn how to define your own functions using the `let fn` keyword. This method introduces a function symbol with certain properties **without proving its existence**. It's useful when you want to work with functions whose existence is assumed or will be proven later.

**Important**: `let fn` does **not** guarantee function existence. It only introduces a function symbol with properties. For functions whose existence must be guaranteed, use `have fn` (covered in the previous section). However, **you still must declare the function with `let fn` before using it**—Litex requires explicit function declarations.

### From Natural Language to Litex

In mathematics, we might say:
- "Let f be a function from real numbers to real numbers"
- "Define the square root function such that sqrt(x) squared equals x"
- "f maps positive numbers to positive numbers"

In Litex:

```litex
let fn f(x R) R

let fn square_root(x R) R:
    x >= 0
    =>:
        square_root(x) * square_root(x) = x

let fn g(x R) R:
    x > 0
    =>:
        f(x) > 0
```

**Natural Language**: "Define a function f" → **Litex**: `let fn f(x R) R: ...` → **Meaning**: Introduces a function symbol with properties

### Detailed Explanation

Sometimes we simply want to introduce a function symbol with certain properties, without proving existence. For example, the square root function:

```litex
let fn square_root(x R) R:
    dom:
        x >= 0
    =>:
        square_root(x) * square_root(x) = x

forall x R:
    x >= 0
    =>:
        square_root(x) $in R
        square_root(x) * square_root(x) = x
```

⚠️ **Note:** This style of definition does not guarantee that such a function exists. For safety, Litex will later support `set_defined_by_replacement`, which ensures existence.

Here's what each part means:

* `fn` introduces a new function.
* `square_root` is its name.
* `(x R)` specifies the parameter `x` belongs to `R`.
* The last `R` specifies the *range* of the function.
* `dom` specifies domain restrictions (`x >= 0`).
* The `=>` section states the properties the function satisfies.

So, `square_root(-1)` is invalid, since `-1` does not satisfy the domain.

When writing `fn` to declare a function, facts about that function are known without verification:

**Important**: You should not refer to the function itself in domain facts. For example, don't do this:

```
let fn f(x R) R:
    f(x) > 0  # ❌ Don't do this
    =>:
        ...
```

### Compact Styles of Function Definition

Litex encourages short, clean definitions. For example, we can omit `dom` explicitly:

```litex
let fn square_root(x R) R:
    x >= 0
    =>:
        square_root(x) * square_root(x) = x
```

Or even inline:

```litex
let fn square_root(x R) R: x >= 0 => square_root(x) * square_root(x) = x
```

Other shorthand examples:

```litex
let fn f(x R) R
let fn f2(x R) R: x > 0
let fn f3(x R) R => f3(x) > 0
let fn f4(x R) R: x > 0 => f4(x) > 0
```

Equivalent to the expanded forms:

```litex
let fn f(x R) R
let fn f2(x R) R:
    dom:
        x > 0
let fn f3(x R) R:
    f3(x) > 0
let fn f4(x R) R:
    x > 0
    =>:
        f4(x) > 0
```

### Litex Code and Natural Language Correspondence

| Natural Language | Litex Code | Meaning |
|-----------------|------------|---------|
| "Define a function f" | `let fn f(x R) R` | Introduces function symbol |
| "f has domain x > 0" | `let fn f(x R) R: x > 0` | Specifies domain restriction |
| "f(x) > 0 for all x > 0" | `let fn f(x R) R: x > 0 => f(x) > 0` | Defines function property |

### Summary

- Use `fn` to define functions without proving existence
- Functions can have domain restrictions and properties
- Compact syntax allows omitting `dom` keyword
- Functions can be defined inline or in expanded form
- Domain facts must not refer to the function itself

### Litex Syntax Reference

**Basic function definition**:
```
let fn function_name(param set) return_set
```

**With domain restriction**:
```
let fn function_name(param set) return_set:
    domain_condition
```

**With properties**:
```
let fn function_name(param set) return_set:
    domain_condition
    =>:
        property1
        property2
```

**Inline form**:
```
let fn function_name(param set) return_set: domain_condition => property
```

### Exercises

1. Define a function `double` that takes a real number and returns its double.
2. Define a function `abs` (absolute value) with domain all real numbers and property `abs(x) >= 0`.
3. Define a function `reciprocal` with domain `x != 0` and property `reciprocal(x) * x = 1`.

### Bonus: When to Use `fn`

Use `fn` when:
- The function's existence is assumed (like square root in standard mathematics)
- You're working with functions whose existence will be proven later
- You want to introduce a function symbol quickly without proof

Remember: `let fn` doesn't guarantee existence. For functions whose existence must be proven, use `have fn` (covered in the previous section). However, **both `let fn` and `have fn` are required declarations**—you cannot use a function in Litex without first declaring it.

---

## Section 5: Calling Functions

### Introduction

This section covers how to call functions in Litex. You'll learn that function calls look exactly like in mathematics, but with a crucial difference: Litex does not execute functions. Understanding this difference is essential for working correctly with functions in Litex.

### From Natural Language to Litex

In mathematics, we say:
- "The square root of 4"
- "f of 2"
- "Apply function g to x"

In Litex:

```
$square_root(4)
$f(2)
$g(x)
```

**Natural Language**: "Call function f with argument x" → **Litex**: `f(x)` → **Meaning**: Constructs a symbol according to function definition

### Detailed Explanation

Function calls in Litex look exactly like in mathematics:

```litex
let fn square_root(x R) R:
    x >= 0
    =>:
        square_root(x) * square_root(x) = x

square_root(4) $in R
```

⚠️ **Critical Understanding: Litex Does Not Execute Functions**

This is fundamentally different from programming languages where functions execute and return computed values.

### Parameters Must Satisfy Domain

You should not pass parameters which do not satisfy the domain of the function. For example:

```
let fn f(x R) R:
    x > 0
    =>:
        f(x) > 0

f(-1) > 0  # ❌ Error!
```

### Using Functions with Different Types

You can define functions for any types, not just numbers:

```litex
have cartoon_characters nonempty_set, oddie_bird, carmela_bird cartoon_characters
let fn fuse_characters(x, y cartoon_characters) cartoon_characters

# You can not add two cartoon characters, because + takes real numbers as parameters.
# oddie_bird + carmela_bird = oddie_bird + carmela_bird

fuse_characters(oddie_bird, carmela_bird) $in cartoon_characters
```

You cannot write `oddie_bird + carmela_bird`, because `+` takes real numbers as parameters. You can call `fuse_characters(oddie_bird, carmela_bird)` to get a new cartoon character because it is defined as a function that takes cartoon characters as parameters.

### Litex Code and Natural Language Correspondence

| Natural Language | Litex Code | Meaning |
|-----------------|------------|---------|
| "The square root of 4" | `square_root(4)` | Symbol satisfying square_root definition |
| "f of 2" | `f(2)` | Symbol constructed by function f |
| "sqrt(4) equals 2" | `sqrt(4) = 2` | Equality holds by definition, not computation |

### Summary

- Function calls look like mathematics: `f(x)`
- Litex does not execute functions—they construct symbols
- `sqrt(4) = 2` holds because 2 satisfies the definition, not because of computation
- Most functions cannot be computed to specific values
- Parameters must satisfy the function's domain conditions
- Functions can work with any types, not just numbers

### Litex Syntax Reference

**Function call**: `function_name(argument1, argument2, ...)`

**Domain check**: Parameters must satisfy domain conditions, or an error occurs.

**Key point**: Functions don't compute—they construct symbols according to their definitions.

### Exercises

1. Define a function `double` and call it with argument 5. What can you say about `double(5)`?
2. Why does `sqrt(4) = 2` hold in Litex? Explain without mentioning computation.
3. What happens if you call a function with a parameter that doesn't satisfy its domain?

### Bonus: The Philosophy of Non-Computation

The fact that Litex doesn't compute functions is not a limitation—it's a feature. In mathematics, we reason about functions based on their properties, not their computed values. Most mathematical functions (like `sqrt(2)`, `sin(x)`, `log(x)`) don't have exact decimal representations anyway. By focusing on properties rather than computation, Litex aligns with mathematical thinking and enables reasoning about functions that cannot be computed.

---


### Example: Defining Image of a Function

Here's a more complex example using function templates to define the range (image) of a function:

```litex
exist_prop x s1 st exist_preimage(s1, s2 set, f fn(s1) s2, y s2):
    f(x) = y

fn range_of_fn(s1 set, s2 set, f fn(s1) s2) set:
    forall y range_of_fn(s1, s2, f):
        $exist_preimage(s1, s2, f, y)
    forall y s2:
        $exist_preimage(s1, s2, f, y)
        =>:
            y $in range_of_fn(s1, s2, f)

know:
    forall s1 set, s2 set, f fn(s1) s2, y s2:
        $exist_preimage(s1, s2, f, y)
        =>:
            y $in range_of_fn(s1, s2, f)

have fn id_R(x R) R = x

# prove 10 is in the range of id_R
exist 10 st $exist_preimage(R, R, id_R, 10)
$exist_preimage(R, R, id_R, 10)
10 $in range_of_fn(R, R, id_R)

# prove all elements in R are in the range of id_R
forall x R:
    exist x st $exist_preimage(R, R, id_R, x)
    $exist_preimage(R, R, id_R, x)
    x $in range_of_fn(R, R, id_R)
```

## Example: Inverse Function

```litex
prop is_inverse_fn(X, Y set, f fn(X)Y, g fn(Y)X):
    forall x X:
        g(f(x)) = x
    forall y Y:
        f(g(y)) = y

prove:
    have fn f(x R) R = 2 * x
    have fn g(x R) R = x / 2

    forall x R: f(g(x)) = f(x / 2) = 2 * (x / 2) = x
    forall y R: g(f(y)) = g(2 * y) = (2 * y) / 2 = y

    $is_inverse_fn(R, R, f, g)

exist_prop g fn(Y)X st has_inverse_fn(X, Y set, f fn(X)Y):
    $is_inverse_fn(X, Y, f, g)

# 单射是有反函数的
prop is_injective(X, Y set, f fn(X)Y):
    forall x1 X, x2 X:
        f(x1) = f(x2)
        =>:
            x1 = x2

exist_prop x X st item_has_preimage(X, Y set, f fn(X)Y, y Y):
    f(x) = y

claim:
    forall X, Y set, f fn(X)Y:
        $is_injective(X, Y, f)
        forall y Y:
            $item_has_preimage(X, Y, f, y)
        =>:
            $has_inverse_fn(X, Y, f)
    prove:
        have fn:
            g(y Y) X:
                f(g(y)) = y
            prove:
                have x st $item_has_preimage(X, Y, f, y)
                f(x) = y
            = x
        
        forall y Y:
            f(g(y)) = y # by definition of g

        forall x X:
            f(g(f(x))) = f(x)
            g(f(x)) = x # $is_inverse_fn(X, Y, f)

        $is_inverse_fn(X, Y, f, g)
        exist g st $has_inverse_fn(X, Y, f)
```

### Exercises

1. Create a function template for sequences and use it to define a function that squares natural numbers less than 5.
2. Explain why functions can be treated as objects in Litex.
3. Create a template for functions that take two parameters and use it to define a specific function.

### Bonus: Functions as First-Class Objects

In Litex, functions are first-class objects—they can be passed as parameters, returned from other functions, and created dynamically. This is similar to functional programming languages, but in Litex, functions remain symbolic constructors rather than executable code. This design allows for powerful abstractions while maintaining the mathematical nature of functions.

---

## Wrap-Up

Functions in Litex are fundamentally different from functions in programming languages:

✨ **In short:**
* In **programming**, a function executes.
* In **Litex**, a function is a **symbolic constructor**, a piece of glue that builds new symbols from old ones.
* To define functions safely, one must ensure existence, either by proof or by replacement.

We've covered:
- **Understanding Functions**: Functions are symbolic constructors, not executable code
- **Built-in Functions**: Arithmetic operators with known properties
- **Defining with `fn`**: Introducing function symbols without existence proof
- **Defining with `have fn`**: Functions with existence guarantees
- **Calling Functions**: How to use functions and why they don't compute
- **Function Templates**: Creating functions dynamically from templates

Remember: When you write `sqrt(4) = 2`, this holds because `2` satisfies the definition of `sqrt`, not because Litex computed `sqrt(4)`. Most functions cannot be computed to specific values—they are symbols satisfying certain properties.

---

## Summary: Methods for Proving Function Existence

The following table summarizes all methods for proving function existence in Litex:

| Method | Syntax | When to Use | Example |
|--------|--------|-------------|---------|
| **1. Equality Definition** | `have fn f(param set) return_set = expression` | When the function can be defined by a simple expression | `have fn g(x R) R = x` |
| **2. Proof with Object** | `have fn: f(param set) return_set: domain => conclusion; prove: ...; have object` | When you need to prove existence by providing an object | `have fn: a(x R) R: x > 0 => a(x) > 0; prove: x > 0; have x` |
| **3. Proof with Explicit Value** | `have fn: f(param set) return_set: domain => conclusion; prove: ...; = value` | When you want to explicitly specify the return value | `have fn: h(x R) R: x > 0 => h(x) > 1; prove: 100 > 1; = 100` |
| **4. Case-by-Case (Simple)** | `have fn f(param set) return_set =: case condition1 = value1; case condition2 = value2` | When the function has different definitions for different cases | `have fn f(x R) R =: case x > 0 = x; case x <= 0 = 0` |
| **5. Case-by-Case (Full)** | `have fn: f(param set) return_set: domain => conclusion; case cond1: ... = value1; case cond2: ... = value2` | When cases need proof steps before specifying values | `have fn: p(x R) R: x > 0 => p(x) > x; case 100 > x: do_nothing = 100; case not 100 > x: x + 1 > x = x + 1` |

**Key Principle**: Function existence is proven by **specifying a value for each element in the domain** that satisfies the function's conditions. This is different from proving other objects' existence, which uses `exist_prop`.

**Note**: Using `fn` (without `have`) does not prove existence—it only introduces a function symbol with properties. Use `have fn` when you need to guarantee existence.

---

## Bonus: Function In Math is very different from Function in Programming

From the perspective of set theory, a function is a binary relation, i.e., a mapping from one set to another. The function type `fn(R, R) R` is essentially defined as a mapping from `cart(R, R)` to `R`. From this, we can see two key differences: 1. Functions in mathematics are not always "computable"—for example, if a real number is irrational, no computer can compute it exactly. 2. If a function's domain is an infinite set like $R^{\infty}$, then the function has "infinitely many" parameters, which is fundamentally different from the concept of functions in computer programming.

Example: How to define a function that adds two positive real numbers by 1. function takes one parameter, which is a pair of real numbers. 2. function takes two parameters, which are two real numbers.

Example: Use set builder as function template set.

```litex
have fn f(x {y R: y > 0}) {z R: z > -1} = x
f(1) = 1
```

```litex
have s set = {x cart(R, R): x[1] > 0, x[2] > 0}
forall x s: x $in cart(R, R), x[1] $in R, x[2] $in R
have fn add_2_pos(x s) R = x[1] + x[2]

have fn:
    add_2_pos2(x, y R) R:
        dom:
            x > 0
            y > 0
        =>:
            add_2_pos2(x, y) = x + y
    
    prove:
        do_nothing

    = x + y

forall x s:
    add_2_pos(x) = x[1] + x[2]
    x[1] > 0
    x[2] > 0
    add_2_pos2(x[1], x[2]) = x[1] + x[2]
```

Example: How to prove that the sequence 1/n converges to 0.

```litex
exist_prop M N_pos st abs_less_than(epsilon R):
    dom:
        epsilon > 0
    <=>:
        1 / M < epsilon

know forall epsilon R: epsilon > 0 => $abs_less_than(epsilon)

exist_prop M N_pos st converge_to(s fn(N_pos)R, x R, epsilon R):
    dom:
        epsilon > 0
    <=>:
        forall n N_pos:
            n > M
            =>:
                abs(s(n) - x) < epsilon

have fn f(n N_pos) R = 1/n

prove forall epsilon R: epsilon > 0 => $converge_to(f, 0, epsilon):
    have M st $abs_less_than(epsilon)
    forall n N_pos:
        n > M
        =>:
            1 / n > 0 # make sure abs(1/n) = 1/n
            1 / M > 0
            abs(1 / n - 0) = abs(1/n) = 1 / n = abs(f(n) - 0)
            abs(1 / M - 0) = abs(1/M) = 1 / M
            1 / M < epsilon
            1 / n < 1 / M
            1 / n < epsilon # < is transitive
            abs(f(n) - 0) < epsilon
            
    exist M st $converge_to(f, 0, epsilon)
```

However, in Litex, we still treat `fn(R, R) R` and `fn(cart(R, R)) R` as different. The latter takes only one parameter, while the former takes two. Of course, these two types of functions can easily be shown to be equivalent. For example, `fn f(x R, y R) R` and `fn g(x cart(R, R)) R` are equivalent if for any `x cart(R, R)`, we have `g(x) = f(coord(x, cart(R, R), 1), coord(x, cart(R, R), 2))`.
