<!-- ## Summary

1. **Axiom of Pairing**  
   For any sets \(u,v\), there exists a set \(\{u,v\}\).

```litex
have a, b set
have set s = {a, b}
```

2. **Axiom of Power Set**  
   For any set \(X\), there exists a set \(\mathcal{P}(X)\) containing all subsets of \(X\).

```litex
fn power_set(X set) set

know forall X set: forall s set: s $is_subset_of X => s $in power_set(X) <=> forall x power_set(X): x $is_subset_of X
```

3. **Axiom of Union**  
   For any family of sets \(F\), there exists a set \(\bigcup F\) containing all elements of elements of \(F\).

```litex
fn union_of_family(F set) set:
    forall x F:
        x $in set
    =>:
        forall x union_of_family(F):
            x $in F
        forall x F:
            x $is_subset_of union_of_family(F)
            
```

4. **Axiom Schema of Separation**  
   Properties can be used to separate subsets from sets.

```litex
have s set
prop p(x s)
have set s = {x s: $p(x)}
```

## ZFC Axioms and Peano Axioms

### ZFC Axiom System (Zermelo-Fraenkel Set Theory with Choice)

The ZFC axiom system is the foundation of modern mathematics and consists of the following 10 axioms:

#### 1. Axiom of Extensionality

**Mathematical notation**:
$$\forall A, B \text{ set}: A = B \iff (\forall x, x \in A \iff x \in B)$$

Two sets are equal if and only if they have the same elements.

#### 2. Axiom of Empty Set

**Mathematical notation**:
$$\exists \emptyset \text{ set}: \forall x, x \not\in \emptyset$$

There exists a set that contains no elements.

#### 3. Axiom of Pairing

**Mathematical notation**:
$$\forall a, b \text{ obj}: \exists \{a,b\} \text{ set}: \forall y, (y \in \{a,b\} \iff (y = a \lor y = b))$$

For any two objects $a$ and $b$, there exists a set containing exactly $a$ and $b$.

#### 4. Axiom of Union

**Mathematical notation**:
$$\forall A \text{ set}: \exists \bigcup A \text{ set}: \forall x, (x \in \bigcup A \iff (\exists S \in A, x \in S))$$

For any set $A$ (whose elements are themselves sets), there exists a set $\bigcup A$ containing all elements of all sets in $A$.

#### 5. Axiom of Power Set

**Mathematical notation**:
$$\forall X \text{ set}: \exists \mathcal{P}(X) \text{ set}: \forall S, (S \in \mathcal{P}(X) \iff S \subseteq X)$$

For any set $X$, there exists a set $\mathcal{P}(X)$ containing all subsets of $X$.

#### 6. Axiom Schema of Separation

**Mathematical notation**:
$$\forall A \text{ set}, \forall P: \exists \{x \in A : P(x)\} \text{ set}: \forall y, (y \in \{x \in A : P(x)\} \iff (y \in A \land P(y)))$$

For any set $A$ and property $P$, there exists a set containing all elements of $A$ that satisfy $P$.

#### 7. Axiom Schema of Replacement

**Mathematical notation**:
$$\forall F \text{ function}, \forall A \text{ set}: \exists F(A) \text{ set}: \forall y, (y \in F(A) \iff (\exists x \in A, y = F(x)))$$

For any function $F$ and set $A$, there exists a set containing the image of $F$ on $A$.

#### 8. Axiom of Infinity

**Mathematical notation**:
$$\exists I \text{ set}: (\emptyset \in I \land (\forall x \in I, x \cup \{x\} \in I))$$

There exists a set containing the natural numbers.

#### 9. Axiom of Regularity / Foundation

**Mathematical notation**:
$$\forall A \text{ set}: (A \neq \emptyset \implies (\exists x \in A, \forall y \in A, y \not\in x))$$

Every non-empty set contains an element that is disjoint from it.

#### 10. Axiom of Choice

**Mathematical notation**:
$$\forall F \text{ non-empty family of sets}: \exists f \text{ choice function}: (\forall A \in F, f(A) \in A)$$

For any non-empty family of sets, there exists a choice function.

---

### Peano Axioms

The Peano axiom system defines the fundamental properties of natural numbers:

#### 1. 0 is a natural number

**Mathematical notation**:
$$0 \in \mathbf{N}$$

#### 2. Successor Axiom

**Mathematical notation**:
$$\forall n \in \mathbf{N}, n++ \in \mathbf{N}$$

If $n$ is a natural number, then $n++$ (the successor of $n$) is also a natural number.

#### 3. 0 is not the successor of any number

**Mathematical notation**:
$$\forall n \in \mathbf{N}, n++ \neq 0$$

#### 4. Injectivity of Successor

**Mathematical notation**:
$$\forall n, m \in \mathbf{N}, (n++ = m++ \implies n = m)$$

Different natural numbers have different successors. Equivalently, if two natural numbers have the same successor, then they are equal.

#### 5. Induction Axiom

**Mathematical notation**:
$$\forall P: (P(0) \land (\forall n \in \mathbf{N}, P(n) \implies P(n++))) \implies (\forall n \in \mathbf{N}, P(n))$$

If a property $P$ satisfies:
- $P(0)$ holds
- For any natural number $n$, if $P(n)$ holds, then $P(n++)$ also holds

Then $P(n)$ holds for all natural numbers $n$.

---

### Notes

- **ZFC Axiom System**: ZFC is Zermelo-Fraenkel set theory with the axiom of choice, and is the foundation of modern mathematics. All mathematical objects can be defined within the ZFC framework.
- **Peano Axioms**: The Peano axioms define the fundamental properties of natural numbers and are the foundation of arithmetic. The existence of the set of natural numbers $\mathbf{N}$ is guaranteed by the axiom of infinity in ZFC.
- **Correspondence in Litex**: Litex directly supports these axioms through built-in keywords (such as `set`, `$in`, `N`, etc.) and syntax (such as `{x A: P(x)}`), making mathematical expression more natural and intuitive. -->
