# Sequence

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