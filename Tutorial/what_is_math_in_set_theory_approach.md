# What is Math? In a Set Theory Approach

## Historical Background

Mathematics is a field characterized by its precision and the absence of ambiguity. The birth of set theory in the late 19th century marked one of the most dramatic revolutions in the history of mathematics—a revolution that would ultimately provide mathematics with its unshakeable foundation. Georg Cantor, the visionary architect of this mathematical paradise, faced fierce resistance and personal attacks from the mathematical establishment of his time, with his revolutionary ideas about infinite sets being dismissed as "a disease from which mathematics will have to recover."

Yet, through decades of relentless pursuit of mathematical truth, Cantor's once-controversial theories about the infinite would eventually be recognized as the bedrock upon which all of modern mathematics rests.

Just as the history of natural science has shown time and again, the most profound truths are often the easiest to grasp. Everyone can understand the syllogism, yet it is almost the entire foundation of mathematical reasoning. Set theory, at its advanced levels, can become very difficult, but one of its great virtues is that we don't need to master the deepest parts. It is enough to learn just what is necessary to handle everyday mathematics. In fact, when it comes to writing Litex, all the set theory you need can be learned in just five minutes.

Zermelo–Fraenkel set theory, named after mathematicians Ernst Zermelo and Abraham Fraenkel, is an axiomatic system proposed in the early twentieth century to formulate a theory of sets free of paradoxes such as Russell's paradox. Today, Zermelo–Fraenkel set theory with the historically controversial axiom of choice (AC) included has become the standard form of axiomatic set theory and serves as the most common foundation of mathematics. When the axiom of choice is included, the system is abbreviated as ZFC (where C stands for "choice"), while ZF refers to Zermelo–Fraenkel set theory without the axiom of choice.

Informally, Zermelo–Fraenkel set theory aims to formalize a single primitive notion: that of a hereditary well-founded set. In this framework, all entities in the universe of discourse are such sets. Consequently, the axioms of Zermelo–Fraenkel set theory refer only to pure sets and prevent its models from containing urelements—elements that are not themselves sets. Additionally, proper classes—collections of mathematical objects defined by a shared property that are too large to be sets—can only be treated indirectly. 

Litex chooses set theory as its foundation precisely because it is the most accessible to ordinary people. If you need a more powerful axiomatic system than set theory, you can turn to other, more abstract formal languages such as Lean, Coq, and Isabelle, which are built on type theory and other advanced foundations. But for most people and most mathematical tasks, set theory provides the perfect balance of simplicity and power.

## Example

Everything in math can be represented as a set. For example, this is the strict definition of a circle:

```litex
(1, 0) $in {x cart(R, R): x[1] * x[1] + x[2] * x[2] = 1}
```

## Builtin Set Theory Features

```
## Set theory 

### cup

# check item in cup
know imply check_item_in_cup(x set, x_item x, cup_x_item x_item):
	cup_x_item $in cup(x)

# when item in cup, it has properties
know forall x set, cup_x_item cup(x) => exist x_item x st cup_x_item $in x_item
	
### cap

# check item in cap
know:
	forall x set, item set:
		forall x_item x:
			item $in x_item
		=>:
			item $in cap(x)

# when item in cap, it has properties
know imply item_in_cap_implies(x set, item cap(x)):
	forall x_item x:
		item $in x_item

### union

# check item in union
know:
	forall item, x, y set: item $in x or item $in y => item $in union(x, y)

# when item in union, it has properties
know imply item_in_union_implies(z set, x, y set):
	z $in union(x, y)
	=>:
		z $in x or z $in y

### intersect

# check item in intersect
know:
	forall item, x, y set: item $in x, item $in y => item $in intersect(x, y)

# when item in intersect, it has properties
know imply item_in_intersect_implies(z set, x, y set):
	z $in intersect(x, y)
	=>:
		z $in x
		z $in y

### power set

# check item in power_set
know:
	forall x set, y set:
		y $subset_of x
		=>:
			y $in power_set(x)

# when item in power set, it has properties
know:
	forall x set, y power_set(x):
		y $subset_of x

### set minus

# check item in set minus
know:
	forall item, x, y set:
		item $in x
		not item $in y
		=>:
			item $in set_minus(x, y)

# when item in set minus, it has properties
know imply item_in_set_minus_implies(x, y set, item set_minus(x, y)):
	item $in x
	not item $in y

### set diff

know:
	forall x, y set:
		set_diff(x, y) = set_minus(x, y) \union set_minus(y, x)
```

```litex
# cup example
prove:
    have a, b nonempty_set
    know a != b
    have c set = {a, b}
    have a_item a, b_item b

    $check_item_in_cup(c, a, a_item)
    a_item $in cup(c)

    forall cup_c_item cup(c) => exist c_item c st $in(cup_c_item, c_item)

# cap example
prove:
    have a, b nonempty_set
    have item set
    know:
        a != b 
        item $in a
        item $in b

    have c set = {a, b}
    
    prove_enum c_item c:
        item $in c_item

    item $in cap(c)
    
    $item_in_cap_implies(c, item)
    item $in cap(c)

# union example
prove:
    have x, y set
    have item set
    know item $in x
    
    item $in x or item $in y
    item $in union(x, y)
    
    $item_in_union_implies(item, x, y)
    item $in union(x, y)
    item $in x or item $in y

# intersect example
prove:
    have x, y set
    have item set
    know item $in x
    know item $in y
    
    item $in x, item $in y
    item $in intersect(x, y)
    
    $item_in_intersect_implies(item, x, y)
    item $in intersect(x, y)
    item $in x
    item $in y

# power_set example
prove:
    have x set
    have y set
    know y $subset_of x
    
    y $subset_of x
    y $in power_set(x)
    
    forall x_set set, y_set power_set(x_set):
        y_set $subset_of x_set

# set_minus example
prove:
    have x, y set
    have item set
    know item $in x
    know not item $in y
    
    item $in x
    not item $in y
    item $in set_minus(x, y)
    
    $item_in_set_minus_implies(x, y, item)
    item $in set_minus(x, y)
    item $in x
    not item $in y

# set_diff example
prove:
    have x, y set
    set_diff(x, y) = set_minus(x, y) \union set_minus(y, x)

```