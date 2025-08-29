## Named Universal Fact

It is often we want to use a universal fact to check a specific fact. And we find that there are more parameters in the universal fact than the specific fact. For example:

```litex
know forall a, b, c R: a < b, b < c => a < c
let a, b, c R: a < b, b < c
# a < c # This does not work!
```

We can not prove `a < c` since we do not know which `b` is used by `forall a, b, c R: a < b, b < c => a < c` to prove `a < c`.

It turns out we can give a name to the forall statement by defining a new proposition.

```litex
prop transitivity_of_less(a, b, c R):
    a < b
    b < c
    <=>:
        a < c
know forall a, b, c R: a < b, b < c => $transitivity_of_less(a, b, c)

let a, b, c R: a < b, b < c
$transitivity_of_less(a, b, c)
a < c
```

However, this is not the best way to do it. Litex provides you a short way to do it.

```litex
know @transitivity_of_less(a, b, c R):
    a < b
    b < c
    =>:
        a < c
```

The above example means:

```litex
prop transitivity_of_less(a, b, c R):
    a < b
    b < c

know forall a, b, c R: $transitivity_of_less(a, b, c) => a < c
know forall a, b, c R: a < b, b < c => a < c
```

Named universal fact can be used in the following situations:

1. follow keyword `know`: 

```
know @name(parameter1 set1, parameter2 set2, ...):
	fact1
	fact2
	...
    =>:
        then_fact1
        then_fact2
        ...
```

It means

```
prop name(parameter1 set1, parameter2 set2, ...):
	fact1
	fact2
	...

know forall parameter1 set1, parameter2 set2, ...:
    $name(parameter1, parameter2, ...)
    =>:
        then_fact1
        then_fact2
        ...
```

2. follow keyword `claim`:

```
claim:
    @propName(parameter1 set1, parameter2 set2, ...):
        fact1
        fact2
        ...
        =>:
            then_fact1
            then_fact2
            ...
    prove:
        ...
```

```
prop propName(parameter1 set1, parameter2 set2, ...):
	fact1
	fact2
	...

claim:
    forall parameter1 set1, parameter2 set2, ...:
        $propName(parameter1, parameter2, ...)
        =>:
            then_fact1
            then_fact2
            ...
    prove:
    	...
```

3. use directly

```
@propName(parameter1 set1, parameter2 set2, ...):
	fact1
	fact2
	...
    =>:
        then_fact1
        then_fact2
        ...
```

```
prop propName(parameter1 set1, parameter2 set2, ...):
	fact1
	fact2
	...

forall parameter1 set1, parameter2 set2, ...:
    $propName(parameter1, parameter2, ...)
    =>:
        then_fact1
        then_fact2
        ...
```

Sometimes, a proposition has transitive properties. For example, being colleagues is a transitive relation.

```litex
have people nonempty_set
have oddie_bird, hippo_dog, thin_penguin people
prop are_colleagues(x, y people)
know @are_colleagues_transitive(x, y, z people):
    $are_colleagues(x, y)
    $are_colleagues(y, z)
    =>:
    	$are_colleagues(x, z)
know:
    $are_colleagues(oddie_bird, hippo_dog)
    $are_colleagues(hippo_dog, thin_penguin)
$are_colleagues_transitive(oddie_bird, hippo_dog, thin_penguin)
$are_colleagues(oddie_bird, thin_penguin)
```

## Proposition vs Named Universal Fact

As you can see, `know` a named universal fact has the effect of defining a proposition and knowing it is always true for all parameters. So when you want to define a proposition and what to assume it is always true for all parameters, you can use `know` a named universal fact. When you just want to define a proposition, you can use `prop` keyword. Fundamentally, the behavior of `know @` can be reproduced by `prop` and `know` together, but Litex introduces this `@` syntax to help you write code more efficiently.