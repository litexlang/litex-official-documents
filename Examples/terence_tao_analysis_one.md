```litex
# Chapter 2: Starting from the beginning: the natural numbers

# This file formalizes natural numbers axioms in chapter 2 of Analysis I, with explanations and examples.

# Axiom 2.1 0 is a natural number.

# The fact that literals are symbols for natural numbers within the set of natural numbers is built-in.
# N, Z, Q, R, C are built-in sets: the set of natural numbers, integers, rational numbers, real numbers, and complex numbers. Some of their properties are built-in, but Litex is flexible enough to allow the user to define and derive their own properties without any problem.

# factual expressions are typically written as $propName(objects). There are 3 handy exceptions: 1. builtin keywords like =, > are written as daily life math 2. If the proposition requires one and only one object, it can be written as "object $propName" 3. If the proposition requires two objects, it can be written as "object1 $propName object2".

0 $in N # This is a factual statement. Its output is true.

# Axiom 2.2 If n is a natural number, then the successor of n is also a natural number.
know forall x N => x + 1 $in N

# examples: the followings are true factual statements.
0 + 1 = 1
3 $in N
4 != 0
2 != 6

# Axiom 2.3 0 is not the successor of any natural number.
know forall x N => 0 != x + 1

# Axiom 2.4 If two natural numbers are equal, iff their successors are equal.
know:
    forall x N, y N:
        x != y
        <=>:
            x + 1 != y + 1

# Axiom 2.5 Principle of mathematical induction.
# prove_by_induction is a built-in function that takes a predicate and a natural number and returns true if the predicate is true for all natural numbers up to and including the natural number.
# The user actually can use "prove_by_induction" + "there exists the smallest natural number" to prove the principle of mathematical induction. In this case, he does not need to use the builtin keyword "prove_by_induction" to use "prove_by_induction" to prove correctness of a statement.

# define a random proposition
prop random_proposition(n N)

# know it satisfies the condition of the principle of mathematical induction
know:
    $random_proposition(1)
    forall n N_pos:
        n >= 1
        $random_proposition(n)
        =>:
            $random_proposition(n + 1)

# use "prove_by_math_induction" to prove random_proposition is true for all natural numbers larger than 0
prove_by_induction($random_proposition(n), n, 1)

# verify: $random_proposition(n) is true for all n N
forall n N_pos:
    n >= 1
    =>:
        $random_proposition(n)

# Assumption 2.6 There exists a number system N. Set N is built-in.

# Proposition 2.1.16 Recursive definition. The definition of recursion in this book is sort of confusing and informal because f(n)(a_{n}) is defined by a_{n}, but what is a_{n}? A sequence is not a set, because there might exists equal elements in a sequence. If a sequence is a function from N to N, then why do we need a function f(n) to define a function from N to N to make sure f(n)(a_{n}) = a_{n}? a_{n} itself is already that function which satisfies the condition a_{n} = a_{n}.

# Since addition and multiplication is so common in math, their basic properties are builtin in Litex. For example, Litex automatically checks equality of two polynomials by builtin expansion and combination.

# Addition of natural numbers.
forall x N, y N:
    (x + y) + 1 = (x + 1) + y

forall x N:
    0 + x = x

# Addition is commutative
forall x N, y N:
    x + y = y + x

# Addition is associative
forall x N, y N, z N:
    (x + y) + z = x + (y + z)

# Definition 2.2.1: a is positive if a != 0.
prop is_positive_natural_number(n N):
    n != 0

# Proposition 2.2.8: If a is positive, b is natural number, then a + b is positive.
know forall a N, b N: a != 0 => a + b != 0

# Corollary 2.2.9: If a and b are natural numbers such that a + b = 0, then a = 0 and b = 0.
know forall a N, b N: a + b = 0 => a = 0, b = 0

# Lemma 2.2.10: If a is positive, then there exists exactly one natural number b such that b + 1 = a.
know forall a N => (a - 1) + 1 = a

# Proposition 2.2.11: If n and m are natural numbers. We say n is greater than or equal to m, written n >= m, if n = m + k for some natural number k. We say n is strictly greater than m, written n > m, if n >= m and n != m.

# Definition 2.3.1 multiplication of natural numbers.
know forall x N => 0 * x = 0

forall x N, y N:
    (x + 1) * y = x * y + y

# Multiplication is commutative
forall x N, y N:
    x * y = y * x

# Multiplication is associative
forall x N, y N, z N:
    (x * y) * z = x * (y * z)

# Distributive law
forall x N, y N, z N:
    x * (y + z) = x * y + x * z

# 0 is the multiplicative identity
know forall x N => 0 * x = 0

# 1 is the multiplicative identity
know forall x N => 1 * x = x


# Chapter 3: Set theory

# This file formalizes set theory axioms in chapter 3 of Analysis I, with explanations and examples.

# Axiom 3.1 If A is a set, then A is an object. In particular, given two sets A and B, it is meaningful to ask whether A in B.
# "in" and "set" are built-in keywords. They behave in Litex just like how they behave in daily math (naive set theory).
# "obj" is a built-in keyword in Litex for declaring objects. Also, anything declared object (things that are not declared as prop or exist_prop) is an object (writes xxx $in obj). obj itself is not obj.
# The word "object" every now and then in Analysis I without any definition. It sort to reveals that explanations of basic elements in math are still missing in this book (or maybe in math world in general). The keyword "obj" in Litex is really something aligns with the word "object" means in math with Litex creators's understanding.

know forall s set => s $in obj

# Definition 3.1.4: Set A is equal to set B, written A = B, if and only if every element of A is an element of B and every element of B is an element of A.
know:
    forall A , B set:
        A = B
        <=>:
            forall x A:
                x $in B
            forall x B:
                x $in A

# Axiom 3.2: There exists a set which contains no elements
know @exist empty_set set st exist_empty_set():
    =>:
        forall x obj:
            not $in(x, empty_set)

# Axiom 3.3: a is an object, then there exists a set A such that A contains and only contains a. If a and b are objects, then there exists a set A such that A contains and only contains a and b.
know @exist s set st exist_set_contains_and_only_contains_obj(a obj):
    =>:
        forall x s:
            x = a
        a $in s

# Axiom 3.4: Definition of union of two sets.
fn union(A, B set) set:
    forall x A:
        x $in union(A, B)
    forall x B:
        x $in union(A, B)
    forall x union(A, B):
        or:
            x $in A
            x $in B

# Definition of subset.
prop is_subset_of(A, B set):
    forall x A:
        x $in B

# Axiom 3.5: Axiom of specification. If A is a set and P is a property, then there exists a set B such that B contains and only contains the elements of A that satisfy P.
# In Litex you can specify a set very flexibly.
prove:
    let s2 set # define a random set
    prop property_of_s2_items(x s2) # define a property of the elements of s2
    
    # TODO: Litex will provide the user a syntax sugar for defining a set by a property. Now we use the idea of "if and only if" to define a set by a property.
    let s set: # define s = {x in s2| property_of_s2_items(x) is true}
        s $is_subset_of s2
        forall x s:
            $property_of_s2_items(x)
        forall x s2:
            $property_of_s2_items(x)
            =>:
                x $in s
    
# TODO: Axiom 3.6 solves the problem of exist and only exist. But it is second-order logic. Since early versions of Litex does not support second-order logic for user, Litex will make it as built-in. The reason why early versions of Litex does not support second-order logic is that most math is based on first-order logic and the creator does not want to make it too complex for user. Second-order-logic is still a "match and substitute" logic (but, first order logic only match and substitute objects inside parameter list of a proposition, second order logic can match and substitute the name of that proposition.), but in order to keep the language simple, Litex needs another set of language features to make it independent from the main logic of "first-order logic" which is the default logic of Litex (the new system is similar to first-order logic, but you have to give a name to any universal fact with proposition as parameter because ordinary universal fact can not take proposition as parameter). Implementing and designing it is a matter of time, not something fundamental.
# Designing a proper syntax and semantics is tricky. Unlike another piece of logic, prove by math induction, which is a second-order logic, axiom of replacement is not that easy to implement. The inventor could implement it now, but he refuses to do so until he finds a way to make it more user-friendly. For the time being, the user can by default assume axiom of replacement is true and declare new sets whose existence is guaranteed by axiom of replacement. Again this is a matter of time, not something fundamental.

# Axiom 3.7: There exists a set N whose elements have properties defined in chapter 2.
# N is built-in in Litex. Most of the properties of N are also built-in. The user can also define his own properties of N easily.

# Axiom 3.8 is wrong because it leads to Russell's paradox.

# Axiom 3.9 (Regularity) If A is a non-empty set, then there is at least one element of A that is either not a set, or is disjoint from A
prop is_disjoint_from(A obj, B set):
    A $in set
    forall x A:
        not $in(x, B)

exist_prop x A st any_nonempty_set_has_item_that_is_not_a_set_or_is_disjoint_from_A(A set):
    or:
        not $in(x, set) # "x is a set" is written as $in(x, set)
        $is_disjoint_from(x, A)

# Axiom 3.10 (Power set axiom) Let X and Y be sets. Then there exists a set denoted by Y^{X} which contains all functions from X to Y



# Axiom 3.11 (Union axiom) Let X be a set. Then there exists a set denoted by union(X) which contains all elements of the elements of X.
fn union_of_set_in_sets(X set) set:
    forall x X:
        x $in set
    =>:
        x $in union_of_set_in_sets(X)

# Chapter 4: Integers and rationals

# This file formalizes integers and rationals axioms in chapter 4 of Analysis I, with explanations and examples.

# Keyword Z is a built-in set in Litex. Here are some basic built-in properties of Z.

Z $in set # Z is a set
1 $in Z
-1 $in Z
forall x N:
    x $in Z

# The following properties about Z are true for real numbers. Since integers are real numbers by builtin-rules automatically, the following facts are all true.

forall x, y, a, b Z: # this is syntax sugar for forall x Z, y Z, a Z, b Z:
    x - y + a - b = (x + a) - (y + b)

forall x, y Z:
    x - y = x + (-y)

forall x Z:
    x + (-x) = 0

forall x Z: # 0 is the additive identity
    x * 0 = 0

# associative law for addition
forall x, y, z Z:
    (x + y) + z = x + (y + z)

# associative law for multiplication
forall x, y, z Z:
    (x * y) * z = x * (y * z)

# distributive law
forall x Z, y Z, z Z:
    x * (y + z) = x * y + x * z

# 0 is the additive identity
forall x Z:
    x + 0 = x

# 1 is the multiplicative identity
forall x Z:
    x * 1 = x

know forall x N: x > 0 => not $in(-x, N)

exist_prop x N st given_int_is_reverse_of_nat(y Z):
    x + y = 0

# Lemma 4.1.5: Every integer is either a natural number or the negative of a natural number.
know forall x Z => x $in N or $given_int_is_reverse_of_nat(x)

# Use Lemma 4.1.5 to prove that -1 is not a natural number and there is a natural number t such that t + (-1) = 0

not $in(-1, N)
$given_int_is_reverse_of_nat(-1)
have t st $given_int_is_reverse_of_nat(-1)
t + (-1) = 0

# The rationals

know forall x2, y2 R: x2 != 0, y2 != 0 => x2 * y2 != 0

# proved by builtin rules for *, +, -, /
forall a2, b2, c2, d2 R:
    b2 != 0
    d2 != 0
    =>:
        b2 * d2 != 0
        a2 / b2 + c2 / d2 = (a2 * d2 + b2 * c2) / (b2 * d2)

forall a, b Q:
    a + b = b + a
    a * b = b * a

forall a, b, c Q:
    (a + b) + c = a + (b + c)
    (a * b) * c = a * (b * c)
    a * (b + c) = a * b + a * c
    (a + b) * c = a * c + b * c

forall a Q:
    a + 0 = 0 + a
    a = a + 0
    a + (-a) = 0
    a * 1 = 1 * a

forall a Q:
    a != 0
    =>:
        a / a = 1
```
