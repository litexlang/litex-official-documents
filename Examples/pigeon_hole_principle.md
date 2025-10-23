```litex
"""
1. 过程：N_pos 是正整数
2. 如果对于 fn(N_pos)N_pos 即从正整数到正整数的函数，我用数归法来证明如果 forall x <= n + 1, f(x) <= n 那么存在 a, b 让 f(a) = f(b)， a != b, a,b <= n + 1

exist_prop a, b N_pos st exist_items_in_the_same_box(f fn(N_pos)N_pos, n N_pos):
    f(a) = f(b)
    a != b
    a <= n + 1
    b <= n + 1

# 条件错了。
claim:
    forall f fn(N_pos) N_pos:
        forall x N_pos, n N_pos: x <= n + 1 => f(x) <= n
        =>:
            $exist_items_in_the_same_box(f, 1)
    prove:
        f(1) <= 1
        f(1) = 1 or f(1) < 1 # definition of <=
        f(1) >= 1 # definition of N_pos
        not f(1) < 1 # x >= y <=> not x < y
        f(1) = 1 # not f(1) < 1 and f(1) = 1 or f(1) < 1

        f(2) <= 1
        f(2) = 1 or f(2) < 1
        f(2) >= 1
        not f(2) < 1
        f(2) = 1

        exist 1, 2 st $exist_items_in_the_same_box(f, 1)

claim:
    forall f fn(N_pos) N_pos:
    	forall x N_pos, n N_pos: x <= n + 1 => f(x) <= n 
        =>:
            forall m N_pos: $exist_items_in_the_same_box(f, m) => $exist_items_in_the_same_box(f, m+1)
    prove:
        claim:
            forall m N_pos: $exist_items_in_the_same_box(f, m) => $exist_items_in_the_same_box(f, m+1)
            prove:
                claim:
                    not $exist_items_in_the_same_box(f, m+1)
                    prove_by_contradiction:
                        know not $exist_items_in_the_same_box(f, m)
                        $exist_items_in_the_same_box(f, m)

claim:
    forall f fn(N_pos) N_pos:
        forall x N_pos, n N_pos: x <= n + 1 => f(x) <= n
        =>:
            forall n N_pos => $exist_items_in_the_same_box(f, n)
    prove:
        $exist_items_in_the_same_box(f, 1)
        prove_by_induction($exist_items_in_the_same_box(f, n), n, 1)

"""
```
