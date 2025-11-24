# Set Theory: The Solid Foundation of Modern Mathematics

_From the paradise that Cantor created for us, no one shall be be able to expel us._

_— David Hilbert_

## A Little Bit of History

The birth of set theory in the late 19th century marked one of the most dramatic revolutions in the history of mathematics—a revolution that would ultimately provide mathematics with its unshakeable foundation. Georg Cantor, the visionary architect of this mathematical paradise, faced fierce resistance and personal attacks from the mathematical establishment of his time, with his revolutionary ideas about infinite sets being dismissed as "a disease from which mathematics will have to recover."

Yet, through decades of relentless pursuit of mathematical truth, Cantor's once-controversial theories about the infinite would eventually be recognized as the bedrock upon which all of modern mathematics rests.

Just as the history of natural science has shown time and again, the most profound truths are often the easiest to grasp. Everyone can understand the syllogism, yet it is almost the entire foundation of mathematical reasoning. Set theory, at its advanced levels, can become very difficult, but one of its great virtues is that we don’t need to master the deepest parts. It is enough to learn just what is necessary to handle everyday mathematics. In fact, when it comes to writing Litex, all the set theory you need can be learned in just five minutes.

## Set Theory in Litex

Modern math is built upon set theory. In Litex, to ensure correctness and be more aligned with modern math, when the user wants to declare a new object, he must say which set it belongs to.

```litex
have a N, b Q, c R
let e N, f Q, g R
```

The keyword `set` is useless, unless there is a proposition that works together with it. In our case, as how math works, it is the keyword `in`.

```litex
have a N
a $in N
```

Actually, `have a N` has two effects: 1. declare an object `a` in current environment (context). 2. assume `a` is in set `N`, similar to `know a $in N`.

As `in` serves many use cases in math, it also serves many use cases in Litex.

1. serves as companion to `set`.

```litex
have a N
a $in N
```

2. A function satisfy a function template also uses the keyword `in`.

```litex
fn_template self_defined_seq(s set):
    fn (n N) s

fn f(n N) R

f $in self_defined_seq(R)
```

3. As parameter condition for everything: function, proposition, etc.

It is easy to introduce wrong facts if we do not have `set` requirement of things that might receive parameters. For example, it is strange to pass a set object to `+` (e.g. It is strange to say `empty_set + empty_set` ). It's also strange to say `2 $in 1` because 1 is not a set. To solve such ambiguity, we use `in` to require the parameter to be in a set at definition time.

(It sort of has the same functionality as `type` in programming languages like C, Java, TypeScript, etc. The user can only pass parameters that satisfy certain conditions to a function, proposition, etc.)

## In

`in` is a built-in proposition in Litex. It is used when you want to claim an object is in a set. Since `in` facts are everywhere, Litex allows you to omit it in most cases. For example:

```litex
let n N
n $in N
```

`let n N` here has two effects:

1. Declare an object in current environment (context). For example, object `n` now exists in current environment. You can use it later.

2. Assume `n` is in set `N`. It has the same effect as `know n $in N`.

```litex
forall x N:
    x $in N
```

`x N` in `forall x N` is the same as `x $in N`.

```litex
fn f(x N) N
```

`x N` in `fn f(x N) N` means the parameter `x` that is passed to `f` is must satisfy `x $in N`, i.e. The domain of the first parameter `x` is subset of `N`.

```litex
prop p(x N)
```

`x N` in `prop p(x N)` means the parameter `x` that is passed to `p` is must satisfy `x $in N`, i.e. The domain of the first parameter `x` is subset of `N`.

As you can see, `in` is everywhere, in explicit and implicit ways.

Examples of not in special sets:

```litex 
# Examples of not in N (natural numbers)
not -1 $in N
not 3.5 $in N
not (-1 * 1) $in N
not (2 + 3.5) $in N
not (-2) $in N

# Examples of not in Z (integers)
not 3.5 $in Z
not 2.7 $in Z
not (1 + 0.5) $in Z
not (3 / 2) $in Z

# Examples of not in N_pos (positive integers)
not -1 $in N_pos
not -2 $in N_pos
not 0 $in N_pos
not 3.5 $in N_pos
not (-1 * 1) $in N_pos
not (2 - 3) $in N_pos
not (1 - 1) $in N_pos
```