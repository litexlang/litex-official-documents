# Sequence

Since sequences and finite-length sequences are everywhere in math, Litex provides built-in keyword `seq`, `finite_seq` to represent sequences. They are declared in this way:

```
fn_template seq(s set):
	fn (n N) s

fn_template finite_seq(s set, n N_pos):
    fn (x N) s:
    	dom:
        	x < n
```

Let's take a look at a simple example:

```litex
let a seq(R), b seq(R), c seq(R), d seq(R):
    forall n N => a(n) = n
    forall n N => b(n) = n * n
    forall n N => c(n) = n * n * n
    forall n N => d(n) = n * n * n * n

a(1) = 1
=(b(3), 3 * 3, 9)
=(c(3), 3 * 3 * 3, 27)
=(d(3), 3 * 3 * 3 * 3, 81)
```

Here we have defined four sequences `a`, `b`, `c`, `d` which are all in the set `R`. We have also defined the domain of each sequence.

## Sequence and Prove By Induction

When studying sequences, mathematical induction is often the most natural proof technique. Since sequences are defined step by step along the natural numbers, many of their properties are expressed in terms of the relationship between consecutive terms. This makes induction especially suitable for proving results such as general formulas and summation identities. Below, we use the formula for the sum of an arithmetic progression as an example, showing how sequences and induction work hand in hand in Litex.

The next example wants to prove the formula for the sum of an arithmetic progression:

$$
S_n = \frac{n}{2} (2a_1 + (n-1)d)
$$

where $a_1$ is the first term and $d$ is the common difference.

```litex
prop is_arithmetic_progression(a seq(R), d R):
    forall k N_pos => a(k+1) = a(1) + k * d
    forall k N_pos => a(k+1) = a(k) + d

fn sum_of_first_n_numbers(a seq(R), n N_pos) R
know:
    forall a seq(R), n N_pos:
        sum_of_first_n_numbers(a, n+1) = sum_of_first_n_numbers(a, n) + a(n+1)
    forall a seq(R):
        sum_of_first_n_numbers(a, 1) = a(1)

claim:
    forall a seq(R), n N_pos, d R:
        $is_arithmetic_progression(a, d)
        =>:
            sum_of_first_n_numbers(a, n) = n * (2 * a(1) + (n-1) * d) / 2
    prove:
    	=:
            sum_of_first_n_numbers(a, 1)
            a(1)
            1 * (2 * a(1) + (1-1) * d) / 2
        
        claim:
            forall k N_pos:
                sum_of_first_n_numbers(a, k) = k * (2 * a(1) + (k-1) * d) / 2
                =>:
                    sum_of_first_n_numbers(a, k+1) = (k+1) * (2 * a(1) + (k+1 - 1) * d) / 2
            prove:
                a(k+1) = a(k) + d
                =:
                    sum_of_first_n_numbers(a, k+1)
                    sum_of_first_n_numbers(a, k) + a(k+1)
                    k * (2 * a(1) + (k-1) * d) / 2 + (a(1) + k * d)
                    (k+1) * (2 * a(1) + (k+1 - 1) * d) / 2

        prove_by_induction(sum_of_first_n_numbers(a, k) = k * (2 * a(1) + (k-1) * d) / 2, k, 1)
        n >= 1
        sum_of_first_n_numbers(a, n) = n * (2 * a(1) + (n-1) * d) / 2
```