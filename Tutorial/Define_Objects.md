# Objects: Nouns of Logic

_Objects are typically noun phrases. Objects normally follow the verb in a clause._

_— Cambridge Dictionary_

## Define Objects

Any factual statement consists of a verb and nouns. For example, `2 > 1` involves verb `>` and nouns `2` and `1`. In math, such verbs are called proposition predicates, and such nouns are called objects.

We must have objects to work with before we can process them. However, we cannot introduce nouns arbitrarily like we can introduce predicates. For example, we cannot arbitrarily extract an object from an empty set, nor can we introduce something that is both positive and negative at the same time. Therefore, we need to prove the existence of objects. This is very different from programming in Python or C, where we can declare an object directly and use it directly.

When programming, say in Python, we are so familiar with declaring an object directly and using it directly. For example:

```python
x = 1
print(x)
```

However, in math, we are not allowed to use an object directly without proving its existence. For example, many new-comers of Litex may try to write the following code:

```litex
have x N = 2
```

This works and you have defined a new object `x` with the property `x $in N` and `x = 2`.

However, if you try to write the following code:

```
have x N: x = 2.5
```

This will not work, because there is no object `x` in `N` (the set of natural numbers) that equals to 2.5.

## Define a new object from a nonempty set

Syntax:

```
have object_name nonempty_set_name
```

For example:

```litex
have x R # x is defined to be in the set of real numbers
have a {1, 2, 3} # a is defined to be in {1, 2, 3}
have f fn(R)R # f is a function from R to R
```

As long as `$is_nonempty_set(nonempty_set_name)` is true, then you can do that.

## Define a new object from a nonempty set and specifying its equality

Syntax:

```
have object_name nonempty_set_name = equal_to
```

For example:

```litex
have x R = 17.17
have y N = 0
```

## Define a new function

### Specifying its value

Syntax:

```
have fn function_name(p1 set1, p2 set2 ...) return_set = equal_to
```

Example:

```litex
have fn f(x R, y R) R = x + y
```

### Specifying its value in each case

```
have fn function_name(p1 set1, p2 set2 ...) return_set =:
    case fact1: value_in_case1
    ...
```

Example:

```litex
have fn g(x R) R =:
        case x = 2: 3
        case x != 2: 4 
```

### Specify its value in detailed way with proofs

This is helpful when you can not write the specific form of the value, but you can prove the existence of that value


Example

```litex
    have fn:
        h(x R) R:
            x > 0
            =>:
                h(x) > 1
        prove:
            do_nothing
        = 100
```

Now you defined a function called h, which has domain `x $in R`, `x > 0`, and has property `h(x) > 1` and `h(x) $in R`. You need to prove its existence. Your proof procedure is `do_nothing`. And after your proof, you specify the value of `h(x)` to be 100. It is easy to see that when `h(x) = 100`, the properties of function are all satisfied.

Example with case by case

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

Now you defined a function called h, which has domain `x $in R`, `x > 0`, and has property `h(x) > 1` and `h(x) $in R`. You need to prove its existence. You prove case by case. When `100 > x`, you prove nothing and specify the value of `p(x)` to be 100. When `not 100 > x`, you prove `x + 1 > x` and specify the value of `p(x)` to be `x + 1`.