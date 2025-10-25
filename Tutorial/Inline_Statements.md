# Inline Statements

_Design and programming are human activities; forget that and all is lost._

_-- Bjarne Stroustrup_

In the previous sections, we are exploring how to map mathematical expressions to Litex statements. You can see Litex is a very intuitive language because it maps mathematical concepts directly to Litex statements.

People are always more receptive to things they’re familiar with. That’s why Litex adopts Python-style syntax, using line breaks to structure code. This not only keeps the code organized but also lowers the learning curve for users.

However, in daily writing, people are also very familiar with writing statements in a single paragraph. Using Python-style syntax can sometimes make code occupy excessively many lines. So Litex provides a way to write statements in a single line.

When you find yourself writing a sequence of statements in a single line one after another, when you are writing a specific fact, follow it with `,`; when you are writing a `forall` statement, follow it with `;`. When it is the last statement, the `,` or `;` is optional.

## Forall

Inline forall statement ends with `;` to separate itself from the next statement. When the whole line ends with that forall statement, the `;` is optional (If you are careful, write `;` every time to avoid confusion). When `forall` is inside another statement, the `;` is required. As you can see, inline version saves a lot of lines.

The `then` keyword is replaced by `=>` and `iff` is replaced by `<=>`. Domain Facts follow the `:` symbol. When you are writing inline `forall`, all facts that appear in the `forall` fact must also be written in inline format. When there is no extra domain facts, you can hide the `:` symbol and write `=>` directly.

```litex
forall => 1 + 1 = 2
forall => 1 + 1 = 2;
forall:
    1 + 1 = 2
```

```litex
forall : 1 > 0 => 1 > 0
forall:
    1 > 0
    =>:
        1 > 0
```

```litex
forall => 1 + 1 = 2 <=> 1 + 1 = 2
forall:
    =>:
        1 + 1 = 2
    <=>:
        1 + 1 = 2
```

```litex
forall x R => x $in R
forall x R:
    x $in R

forall x R => x > 0 <=> x > 0
forall x R:
    =>:
        x > 0
    <=>:
        x > 0
```

```litex
forall x R: x > 0 => x > 0 <=> x > 0
forall x R:
    dom:
        x > 0
    =>:
        x > 0
    <=>:
        x > 0
```

```litex
forall x R: forall y R: y > 0 => y > 0 <=> y > 0; x > 0 => x > 0
forall x R:
    forall y R:
        dom:
            y > 0
        =>:
            y > 0
        <=>:
            y > 0
    x > 0
    =>:
        x > 0

forall x R: forall y R: y > 0 => y > 0 <=> y > 0; x > 0 => forall y R: y > 0 => y > 0 <=> y > 0; x > 0
forall x R:
    forall y R:
        dom:
            y > 0
        =>:
            y > 0
        <=>:
            y > 0
    x > 0
    =>:
        forall y R:
            dom:
                y> 0
            =>:
                y > 0
            <=>:
                y > 0
        x > 0
```

```litex
forall x R: forall y R: y > 0 => y > 0; 1 > 0, forall y R: y > 0 => y > 0; => 1 > 0, forall y R: y > 0 => y > 0; 1 > 0
forall x R:
    forall y R:
        y > 0
        =>:
            y > 0
    1 > 0
    forall y R:
        y > 0
        =>:
            y > 0
    =>:
        1 > 0
        forall y R:
            y > 0
            =>:
                y > 0
        1 > 0
```

The followings are also equivalent.

```litex
prop p(x R)
prop q(x R)
know:
    forall x R:
        $p(x)
        <=>:
            $q(x)

forall x R: $p(x) <=> $q(x)
forall x R: 
    $p(x)
    <=>:
        $q(x)
```

When there is no extra domain facts, `forall params: facts1 <=> facts2` is equivalent as `forall params => facts1 <=> facts2`. The meaning of `forall params : facts1 <=> facts2`, i.e. `when there is no extra domain facts, facts1 is equivalent to facts2`.

## Or, Equal

`or` and `=` can also be written in inline format.

```litex
1 = 1 or 1 = 2
```

```
1 = 1 * 1 = 2 - 1
```

## Function Declaration

`fn` can also be written in inline format. The `then` keyword is replaced by `=>`.

```litex
fn f(x R) R: x > 0 => f(x) > 0
fn f_multi_lines(x R) R:
    x > 0
    =>:
        f_multi_lines(x) > 0
```

```litex
fn g(x R) R => g(x) > 0
fn g_multi_lines(x R) R:
    g_multi_lines(x) > 0
```

```litex
fn k(x N) N: forall y N_pos: x < y => k(x) = 0
fn k_multi_lines(x N) N:
    dom:
        forall y N_pos:
            x < y
            =>:
                k_multi_lines(x) = 0
```

```litex
fn t(x N) N: forall y N_pos: x < y => t(x) = 0; 1 > 0, forall y N_pos: x < y => t(x) = 0; => t(1) = 0
fn t_multi_lines(x N) N:
    forall y N_pos:
        x < y
        =>:
            t_multi_lines(x) = 0
    1 > 0
    forall y N_pos:
        x < y
        =>:
            t_multi_lines(x) = 0
    =>:
        t_multi_lines(1) = 0
```

## Proposition Declaration

The followings are inline version of proposition declaration. The equivalent multiple lines version is below. `iff` in inline version is replaced by `<=>`.

```litex
prop q(x R) <=> x > 0
prop q_multi_lines(x R):
    x > 0

prop p(x , y R): x > 0, y > 0 <=> x + y > 0
prop p_multi_lines(x , y R):
    x > 0
    y > 0
    <=>:
        x + y > 0
```



## Inline Multiple Factual Statements

You can write multiple factual statements in one line. When you find yourself writing a sequence of statements in a single line one after another, when you are writing a specific fact, follow it with `,`; when you are writing a `forall` statement, follow it with `;`. When it is the last statement, the `,` or `;` is optional.

For example, the following line is equivalent to the following multiple lines:

```litex
forall x R:
	x $in R
1 > 0
forall x R:
	x $in R
1 > 0

forall x R => x $in R; 1 > 0, forall x R => x $in R; 1 > 0
```

## Other Statements

Most Litex statements can be written in inline format. Here are some examples:

```litex
let x, y R: x > y
let x_multi_lines, y_multi_lines R:
    x_multi_lines > y_multi_lines

claim:
    1 > 0
    prove:
        1 > 0

claim:
    1 > 0
    prove:
        1 > 0

claim 1 > 0 prove:
    1 > 0
```

```litex
claim:
    forall x R:
        x > 0
        =>:
        	x > 0
    prove:
        x > 0

claim forall y R: y > 0 => y > 0; prove:
    y > 0

# you can omit `prove` here
claim 1 > 0:
    1 > 0

claim:
    1 > 0
    prove_by_contradiction:
        1 > 0

claim 1 > 0 prove_by_contradiction:
    1 > 0

exist_prop x R st exist_R_larger_than_any_positive_number_multi_lines(y R):
    y > 0
    <=>:
        x > y

exist_prop x R st exist_R_larger_than_any_positive_number(y R): y > 0 <=> x > y

prop p(x R)

know $p(1), $p(2), $p(3)
```

### Inline Factual Statements

You can write factual statements in a single line.

The following two examples are equivalent. The inline version is more concise and saves you a lot of lines.

```litex
let a, b, c, d, e, f R:
    a = 1
    b = 2
    c = 3
    d = 4
    e = 5
    f = 6
a = 1
b = 2
c = 3
d = 4
e = 5
f = 6
```

```litex
let a, b, c, d, e, f R: a = 1, b = 2, c = 3, d = 4, e = 5, f = 6
a = 1, b = 2, c = 3, d = 4, e = 5, f = 6
```

Specific facts, existential facts, and universal facts can all be written in inline format. Universal facts should end with `;` and specific facts should end with `,`.

```litex
1 + 1 = 2, forall x R: x > 0 => x > 0; exist 2 st $item_exists_in(R), 0 * 18 = 0
```

### Conclusion

Simplicity is the number one design principle of Litex. Inline statements are a great example of this principle. Simplicity makes Litex a pleasure to use.