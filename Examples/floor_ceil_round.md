```litex
fn self_floor(x R) Z:
    forall y Z:
        y <= x
        =>:
            y <= self_floor(x)
know forall x R, y Z: x - y < 1 => self_floor(x) = y

fn self_ceil(x R) Z:
    forall y Z:
        y >= x
        =>:
            y >= self_ceil(x)
know forall x R, y Z: y - x < 1 => self_ceil(x) = y

fn self_round(x R) Z:
    if:
        x - self_floor(x) < 0.5
        =>:
            self_round(x) = self_floor(x)
    if:
        x - self_floor(x) >= 0.5
        =>:
            self_round(x) = self_ceil(x)

know forall x R, y Z: x - y < 0.5 or y - x < 0.5 => self_round(x) = y
know forall x R, y Z: x - y = 0.5, y >= x => self_round(x) = y

prove:
    self_floor(1) = 1
    self_floor(1.2) = 1
    self_floor(1.8) = 1
    self_floor(1.5) = 1

    self_ceil(1) = 1
    self_ceil(1.2) = 2
    self_ceil(1.8) = 2
    self_ceil(1.5) = 2

    self_round(1) = 1
    self_round(1.2) = 1
    self_round(1.8) = 2
    self_round(1.5) = 2
```
