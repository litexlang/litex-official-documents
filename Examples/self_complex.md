```litex
let self_complex set
fn sc(x, y R) self_complex # sc means self_complex
fn sc_add(x, y self_complex) self_complex
fn sc_mul(x, y self_complex) self_complex
fn sc_div(x, y self_complex) self_complex
fn sc_sub(x, y self_complex) self_complex
fn sc_neg(x self_complex) self_complex
fn sc_abs(x self_complex) R
fn sc_conj(x self_complex) self_complex

know:
    forall x, y, a, b R:
    	sc(x, y) \sc_add sc(a, b) = sc(x + a, y + b)
        sc(x, y) \sc_mul sc(a, b) = sc(x * a - y * b, x * b + y * a)
        sc(x, y) \sc_sub sc(a, b) = sc(x - a, y - b)
    forall x, y R:
        sc_neg(sc(x, y)) = sc(-x, -y)
        sc_conj(sc(x, y)) = sc(x, -y)
        sc_abs(sc(x, y)) = (x * x + y * y) ^ (1/2)
    forall x, y, a, b R:
        or:
            a != 0
            b != 0
        =>:
        	sc(x, y) \sc_div sc(a, b) = sc((x * a + y * b) / (a * a + b * b), (y * a - x * b) / (a * a + b * b))
    	
prove:
	sc(1, 2) \sc_add sc(3, 4) = sc(1 + 3, 2 + 4)
    sc(1, 2) \sc_add sc(3, 4) = sc(4, 6)
    sc(1, 2) \sc_mul sc(3, 4) = sc(1 * 3 - 2 * 4, 1 * 4 + 2 * 3)
    sc(1, 2) \sc_mul sc(3, 4) = sc(-5, 10)
    sc(1, 2) \sc_sub sc(3, 4) = sc(1 - 3, 2 - 4)
    sc(1, 2) \sc_sub sc(3, 4) = sc(-2, -2)
    sc_neg(sc(1, 2)) = sc(-1, -2)
    sc_conj(sc(1, 2)) = sc(1, -2)
    sc_abs(sc(1, 2)) = (1 * 1 + 2 * 2) ^ (1/2)
    sc_abs(sc(1, 2)) = 5 ^ (1/2)
```
