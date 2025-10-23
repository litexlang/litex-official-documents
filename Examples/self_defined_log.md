```litex
prove:
    fn self_log(b, x R) R: 
        dom:
            b > 0  
            b != 1    
            x > 0  
        =>:
            b  \pow  self_log(b, x) = x

    know forall a, b, c R: a > 0 => (a \pow b) * (a \pow c) = a  \pow  (b+c)

    know @p(a, b, c R): a > 0, a != 1, a  \pow  b = a  \pow  c => b = c

    claim:
        forall b, x, y R:
            b > 0
            b != 1
            x > 0
            y > 0
            =>:
                self_log(b,x * y) = self_log(b,x) + self_log(b,y)

        prove:
            x*y > 0
            b != 0
            b  \pow  self_log(b, x*y) = x*y
            b  \pow  self_log(b, x) = x
            b  \pow  self_log(b, y) = y
            b  \pow  self_log(b, x*y) = (b  \pow  self_log(b, x)) * (b  \pow  self_log(b, y))
            (b  \pow  self_log(b, x)) * (b  \pow  self_log(b, y)) = b  \pow  (self_log(b, x) + self_log(b, y))
            b  \pow  self_log(b, x*y) = b  \pow  (self_log(b, x) + self_log(b, y))
            $p(b, self_log(b, x*y), self_log(b, x) + self_log(b, y))
            self_log(b, x*y) = self_log(b, x) + self_log(b, y)
```
