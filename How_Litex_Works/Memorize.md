# Memorize

_Be fixed on the vision, be flexible on the journey._

_- Jeff Bezos_

When Litex needs to store a fact into the environment, it first checks that all symbols mentioned in the fact are properly defined. Then, depending on the type of fact, the system routes it to different storage mechanisms. For equality facts like "x equals y", the system maintains equivalence classes using a shared pointer structure, which automatically establishes transitive relationships—if a equals b and b equals c, then a equals c is implicitly known. For regular facts, the system organizes them by property name and fact type into separate collections, allowing efficient lookup and retrieval. When facts appear within logical expressions like "A or B", the system remembers not just the facts themselves but also their positions within those expressions. Similarly, when facts are part of universal statements like "for all x, if P(x) then Q(x)", the system tracks which facts belong to which universal statements. After storing a fact, the system automatically triggers inference processes that may derive new facts based on the stored information. These derived facts are then recursively stored using the same mechanism, creating a cascading effect where one fact can lead to many others being discovered and stored. This layered storage approach ensures that facts can be efficiently retrieved, queried, and used for logical reasoning while maintaining clear relationships between different types of information.

Memorization is the mechanism by which Litex stores verified facts in its knowledge base for future use. This is conceptually the simplest of the four operations, but it's crucial for efficiency—without memorization, Litex would need to re-derive every fact from scratch each time it's needed.

**How facts are organized**

Facts are stored and organized by their predicates. Litex maintains separate dictionaries for different types of facts:

1. **Specific facts**: These are facts about particular objects, such as `$p(a)`. When a specific fact like `$p(a)` is memorized, it is added to a list associated with the predicate `p` in the specific fact dictionary. This allows Litex to quickly look up all known instances where predicate `p` is true.

2. **Universal facts (forall facts)**: These are facts that apply to all elements of a set, such as `forall x R: $p(x)`. When such a fact is memorized, it is stored in the forall fact dictionary, again organized by predicate. For example, if we have `forall x R: $p(x), $q(1, x)`, then:
   - `forall x R: $p(x)` is stored in `map["p"]` in the forall fact dictionary
   - `forall x R: $q(1, x)` is stored in `map["q"]` in the forall fact dictionary

**Special handling of equality**

Equality facts require special handling because of the mathematical properties of equality: transitivity (if `a = b` and `b = c`, then `a = c`) and symmetry (if `a = b`, then `b = a`). Rather than storing each equality fact separately, Litex maintains equivalence classes—groups of expressions that are known to be equal to each other.

**Example: How equality equivalence classes work**

Suppose we know the following facts:
- `a = f(b) = 2 * t`
- `g(x)(1) = 10 / 7`

Initially, Litex creates two separate equivalence classes:
- Class 1: `{a, f(b), 2 * t}` (all known to be equal)
- Class 2: `{g(x)(1), 10 / 7}` (all known to be equal)

Now, if we learn a new fact `a = 10 / 7`, Litex recognizes that this connects the two equivalence classes. It merges them into a single class:
- Merged class: `{a, f(b), 2 * t, g(x)(1), 10 / 7}`

**Using equivalence classes for verification**

When you later ask Litex to verify `20 / 14 = a`, Litex:
1. Looks up the equivalence class containing `a`
2. Checks if any expression in that class can be proven equal to `20 / 14`
3. The Litex kernel can perform symbolic computation to determine that `20 / 14 = 10 / 7` (by simplifying the fraction)
4. Since `10 / 7` is in the same equivalence class as `a`, Litex concludes that `20 / 14 = a` is true
5. At this point, `20 / 14` is also added to the equivalence class

This approach makes equality verification very efficient, as Litex only needs to check one equivalence class rather than comparing against every known equality fact individually.
