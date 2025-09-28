```litex
"""
algorithm.lix

Goal:
Formalize mathematical definition of algorithm from the book "The Art of Computer Programming" chapter 1.

Here is the definition of algorithm from the book:

So far our discussion of algorithms has been rather imprecise, and a mathematically oriented reader is justified in thinking that the preceding commentary makes a very shaky foundation on which to erect any theory about algorithms.
We therefore close this section with a brief indication of one method by which the concept of algorithm can be firmly grounded in terms of mathematical set theory. Let us formally define a computational method to be a quadruple (Q, I, S, f), in which Q is a set containing subsets I and S, and f is a function from Q into itself. Furthermore f should leave & point-wise fixed; that is, f(g) should equal a for al elements q of S. The four quantities Q, I, S, f are intended to represent respectively the states of the computation, the input, the output, and the computational rule. Each input x in the set I defines a computational sequence, x0, x1, x2,..., as follows:
x0 = x and x_{k+1} = f(x_k) for k≥0.
The computational sequence is said to terminate in k steps if k is the smallest
integer for which x_k is in S, and in this case it is said to produce the output x_k from x. (Note that if x_k is in S, so x_{k+1}, because x_{k+1} = x_k in such a case.) Some computational sequences may never terminate; an algorithm is a computational method that terminates in finitely many steps for all x in I.

"""


# Definition of computational sequence
fn comp_seq(D set, f fn(D)D) fn(D, N)D:
    forall x D, n N:
        comp_seq(D, f)(x,n+1) = f(comp_seq(D, f)(x, n))
    comp_seq(D, f)(x, 0) = x

# Definition of end of computational sequence
exist_prop n N st exist_end_of_comp_seq(D set, x D, f fn(D,N)D):
    f(x, n) = f(x, n+1)

# Definition of algorithm
prop is_algorithm(D set, I set, f fn(D)D):
    forall x I: # i.e. I is subset of D
        x $in D
    <=>:
        forall x I:
            $exist_end_of_comp_seq(D, x, comp_seq(D, f))

# We prove $is_algorithm(R, R, f(x) = x)

fn f(x R)R:
    f(x) = x


claim:
    forall x R:
        $exist_end_of_comp_seq(R, x, comp_seq(R, f))
    prove:
        comp_seq(R, f) $in fn(R, N)R
        comp_seq(R, f)(x, 0) = x
        comp_seq(R, f)(x, 0 + 1) = f(comp_seq(R, f)(x, 0))
        comp_seq(R, f)(x, 0 + 1) = f(x)
        f(x) = x
        comp_seq(R, f)(x, 0 + 1) = x
        comp_seq(R, f)(x, 0) = comp_seq(R, f)(x, 1)
        exist 0 st $exist_end_of_comp_seq(R, x, comp_seq(R, f))

$is_algorithm(R, R, f)


"""
Here is a Litex for Curious Lean Users4 code.
"""

"""
structure ComputationalMethod where
  Q : Type
  I : Set Q
  S : Set Q
  f : Q → Q
  f_fixed : ∀ q ∈ S, f q = q

namespace ComputationalMethod

def comp_sequence (cm : ComputationalMethod) (x : cm.Q) : ℕ → cm.Q
  | 0 => x
  | n + 1 => cm.f (comp_sequence x n)

def TerminatesIn (cm : ComputationalMethod) (x : cm.Q) (k : ℕ) : Prop :=
  comp_sequence cm x k ∈ cm.S ∧
  ∀ i < k, comp_sequence cm x i ∉ cm.S

def IsAlgorithm (cm : ComputationalMethod) : Prop :=
  ∀ x ∈ cm.I, ∃ k, TerminatesIn cm x k

end ComputationalMethod

open ComputationalMethod

def IdMethod : ComputationalMethod :=
{ Q := ℝ,
  I := Set.univ,
  S := Set.univ,
  f := id,
  f_fixed := by intros q h; rfl }

example : IsAlgorithm IdMethod :=
by
  intros x hx
  use 0
  unfold TerminatesIn comp_sequence
  constructor
  · simp
    exact Set.mem_univ _
  · 
    intros i hi
    exact False.elim (Nat.not_lt_zero _ hi)

"""

"""
Comments:
It only takes only 10 lines to formalize the definition of algorithm, which is marvelous.
"""
```
