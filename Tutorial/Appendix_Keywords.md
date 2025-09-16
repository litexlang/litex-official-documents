# Appendix: Keywords: Everything Happens Around Them

_Design and programming are human activities; forget that and all is lost._

_-- Bjarne Stroustrup_

The keywords in Litex are almost identical in meaning and usage to the commonly used ones in mathematics. This makes writing in Litex a very pleasant experience.

| Keyword | Meaning |
|---------|---------|
| `let` | Define an object without checking its existence. |
| `prop` | Define a proposition. The verbs of logic. |
| `know` | Establish a fact |
| `forall` | Universal quantification |
| `exist` | Existential quantification |
| `have` | Introduce an object with checking its existence. |
| `exist_prop` | Existential quantification with a proposition |
| `or` | Disjunction |
| `not` | Negation |
| `fn` | Define a function without checking its existence |
| `fn_template` | Define a class of functions |
| `set` | set: a collection of objects |
| `in` | membership of an object in a set |
| `dom` | domain of a proposition, function, function template, etc. |
| `len`  | length of a set |
| `finite_set` | a set with a finite number of elements |
| `prove` | open a local environment to write some statements without affecting the global environment |
| `claim` | claim a factual statement, prove it here |
| `prove_by_contradiction` | prove by contradiction |
| `prove_in_each_case` | prove by case analysis |
| `prove_by_induction` | prove by mathematical induction |
| `prove_over_finite_set` | prove a universal statement by iterating over a finite set |
| `import` | import a file or directory |
| `exist_in` | exist a object in a set |
| `set_defined_by_replacement` | define a set by a axiom of replacement |
| `obj_exist_as_preimage_of_prop` | exist a object as the preimage of a proposition |
| `obj_exist_as_preimage_of_fn` | exist a object as the preimage of a function |
| `N` `N_pos` `Z` `Q` `R` `C` `obj` | builtin sets: natural numbers, positive natural numbers, integers, rational numbers, real numbers, complex numbers, objects |
| `clear` | clear all facts |
| `set_product` | a product of sets |
| `proj` | a projection of a set product |
| `lift` | Point-wise lifting of an operator |

Although these keywords are rarely defined strictly in math textbooks, they are used everyday and everywhere. Litex creator can not find strict definition for keywords like `proposition`, `is`, `in` etc (actually, the word `definition` is also a vague word). He tried his best to make the meaning of these keywords as close to the meaning in our daily math expression, along with his own ideas and understanding, so that Litex is both intuitive and strict.