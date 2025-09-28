```litex
"""
Basics
"""

forall x R, a R, b R:
    a + x = b
    =>:
        a + x - a = b - a
        x = b - a

forall x R, a R, b R:
    a != 0
    a * x = b
    =>:
        a * x / a = b / a
        x = b / a

know:
    forall a R, b R:
        b  >  a
        =>:
            b - a > 0

    forall a R, b R:
        b > a
        =>:
            b >= a 
            b != a

    forall a R, b R:
        b < a
        =>:
            a > b

exist_prop x Z st is_divisible_by(b Z, a Z):
    a * x = b

prop is_smallest_element_of(x N, s set):
    dom:
        forall y s:
            y $in Z
        x $in s
    <=>:
        forall y s:
            y >= x

exist_prop x obj st non_empty(s set):
    x $in s

know @exist x N st exist_smallest_element_of(s set):
    dom:
        $non_empty(s)
        forall y s:
            y $in Z
    <=>:
        x $in s
        $is_smallest_element_of(x, s)
    
know forall x Z, y Z => x * y $in Z, x + y $in Z, x - y $in Z

know forall x N, y N => x + y $in N, x * y $in N

know forall x N, y N => x + y $in N, x * y $in N


 """
Chapter 1
"""

# Handy builtin rules are there for verifying basic properties of real numbers.
prove:
    let x R, y R, z R
    (x + y) + z = x + (y + z)
    x + y = y + x
    0 + x = x
    (x*y)*z = x*(y*z)
    x*y = y*x
    1*x = x
    x*(y+z) = x*y + x*z

know:
    forall a Z, b Z:
        a - b $in Z
        a + b $in Z
        a * b $in Z

    forall a Q, b Q:
        a - b $in Q
        a + b $in Q
        a * b $in Q

    forall a Q, b Q:
        a != 0
        =>:
            b / a $in Q

"""
Chapter 2
"""

# Lemma 2.1

# TODO: THIS CLAIM CAN BE PROVED
know @exist q Z st exist_largest_multiple_of(d Z, a Z):
    <=>:
        a >= d * q
        d*(q+1) > a

# Theorem 2.1

# TODO: THIS CLAIM CAN BE PROVED
know @exist m N st nonempty_set_of_integers_closed_under_addition_has_elements_divisible_by_a_common_divisor(s set):
    dom:
        $non_empty(s)
        forall x s:
            x $in Z
    <=>:
        forall x s:
            x $in Z
            $is_divisible_by(m, x)

# Corollary 2.1
# Specialized case

# Define integral linear combination of two integers

exist_prop c Z, d Z st is_linear_combination_of_two_integers(x Z, a Z, b Z):
    x = c * a + d * b

## 可能可以给用户一个语法糖，让他们能更轻松地让下面这两个定义合并

fn set_of_integer_linear_combination_of_two_integers(a Z, b Z) set:
    forall x set_of_integer_linear_combination_of_two_integers(a, b):
        x $in Z
        $is_linear_combination_of_two_integers(x, a, b)

know:
    forall x Z, a Z, b Z:
        $is_linear_combination_of_two_integers(x, a, b)
        =>:
            x $in set_of_integer_linear_combination_of_two_integers(a, b)

fn set_of_multiples_of(d N) set:
    forall x set_of_multiples_of(d):
        x $in Z
        x $is_divisible_by d

know:
    forall x Z, d N:
        x $is_divisible_by d
        =>:
            x $in set_of_multiples_of(d)

know:
    forall x Z, d N:
        x $in set_of_multiples_of(d)
        =>:
            x $is_divisible_by d

# Corollary itself

# 存在唯一性所以用fn
# 事实上这就是gcd的定义
# Definition 1 at page 7
fn gcd(a Z, b Z) N:
    set_of_multiples_of(gcd(a, b)) = set_of_integer_linear_combination_of_two_integers(a, b)
    
# Corollary 2.2
# Specialized case

know forall a Z, b Z, d Z: d != 0, a $is_divisible_by d, b $is_divisible_by d => gcd(a, b) $is_divisible_by d

"""
Chapter 3
"""

# Definition 3.1
prop relatively_prime(a Z, b Z):
    gcd(a, b) = 1

exist_prop c Z, d Z st exist_relatively_prime(a Z, b Z):
    a * c + b * d = 1

# Theorem 3.1
know:
    forall a Z, b Z:
        gcd(a, b) = 1
        <=>:
            $exist_relatively_prime(a, b)

# Corollary 3.1
know:
    forall a Z, b Z:
        dom:
            a != 0
            b != 0
        =>:
            a / gcd(a, b) $in Z
            b / gcd(a, b) $in Z
            gcd(a / gcd(a, b), b / gcd(a, b)) = 1

# facts that are not mentioned but still used
know:
    forall a Z, b Z, d Z:
        a $is_divisible_by d
        b $is_divisible_by d
        =>:
            a + b $is_divisible_by d
            a - b $is_divisible_by d
            a * b $is_divisible_by d

# Theorem 3.2
know:
    forall a Z, b Z, d Z:
        gcd(a, d) = 1
        a*b $is_divisible_by d
        =>:
            b $is_divisible_by d

# Corollary 3.1
know:
    forall a Z, b Z, d Z:
        gcd(a, b) = 1
        gcd(a, d) = 1
        =>:
            gcd(a, b*d) = 1


```
