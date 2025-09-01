# Everyday Math in Litex: Whatever everyday mathematics needs to express, Litex provides. No more, no less.

Mathematics is a difficult discipline. But the basic building blocks of forming a reasoning (or of mathematics as a whole) are not actually complicated. For example, modern mathematics is based on the ZFC axioms, which consist of only nine axioms. From these nine, we can derive the entire edifice of mathematics we are familiar with. 

It is truly remarkable that such a vast structure can be built from so few tools. And precisely because these basic units of mathematics are easy to understand, everyone—from elementary school students to professional mathematicians—possesses some fundamental reasoning ability.

The goal of Litex is to write reasoning (or mathematics in general) as code. Since no matter how complex a piece of reasoning (or mathematics) is, it is always built from a set of basic units, what Litex needs to do is simply provide these fundamental building blocks. Below is how everyday mathematical expressions correspond to their Litex formulations.

---

### **Basics**

* Numbers (e.g. `0`, `-17.17`)
* Arithmetic (e.g. `1 + 1 = 2`)
* Basic facts (e.g. `1 > 0`)
* Sets (keywords: `set`, `nonempty_set`, `R` for real numbers, `N` for natural numbers, etc.)

---

### **Objects**

* Definitions of objects

  * Keyword: `have`, `let`
  * Example: `have a N = 1` defines a new object `a` in set `N` with value `1`

---

### **Facts**

* Defining propositions

  * Keywords: `prop`, `exist_prop`
  * Example: `prop larger_than(x, y) <=> x > y`
* Specific facts (e.g. `1 $in R`, `2 > 0`)
* Universal facts (e.g. `forall x N => x >= 0`)
* Existential facts (e.g. `exist 1 st $exist_in(R)`)

---

### **Functions**

* Function definitions

  * Keywords: `fn`, `have fn`
  * Example: `have fn f(x R) R = x`
* Function templates

  * Keyword: `fn_template`
  * Example: `fn_template sequence(s set): fn (n N) s` defines a series of objects in set `s`

---

### **Special Proof Methods**

* `prove_by_contradiction`
* `prove_in_each_case`
* `prove_by_induction`
* `prove_over_finite_set`

---

### **Others**

* Assumptions or declaring facts without proof

  * Keyword: `know`
* Claiming a fact

  * Keyword: `claim`
* Package management

  * Keyword: `import`
* Clearing all facts

  * Keyword: `clear`
