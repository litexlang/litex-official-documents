# Appendix: Litex Kernel Implementation

2025.9.28 This file is under construction. There are many things to write about and I am still figuring out a systematic way to write about it. For now, there are just some notes here.

1. You can write forall under forall under forall, in other words, the depth of forall is limited to two levels. For example You can not write the following code:

```
# The domain fact is too deep: the maximum depth of the whole forall is 2 and thus the depth of the domain fact is 1
forall x R:
    forall y R:
        forall z R:
            x = y + z
    =>:
        x = y + z
```

The correct way to write it is:

```litex
forall x, y, z R:
    x = y + z
    =>:
        x = y + z
```

```
# The then fact is too deep: the maximum depth of the whole forall is 2 and thus the depth of the domain fact is 1
forall x R:
    forall y R:
        forall z R:
            x $in R
            y $in R
            z $in R
```

The correct way to write it is:
```litex
forall x, y, z R:
    x $in R
    y $in R
    z $in R
```

The reason why we must restrict the depth of forall is that proving a one-layer forall fact is computationally expensive: O(N). When the depth is two layers, the computational complexity is O(N^2). When the depth is three layers, the computational complexity is O(N^3). And so on. Therefore, we must restrict the depth of forall to two layers to avoid computational explosion.

To avoid too deep forall, you can put all the related parameters in the outmost layer of forall. For example:
```litex
forall x, y, z R:
    x $in R
    y $in R
    z $in R
```

instead of:
```litex
forall x R, y R:
    forall z R:
        x $in R
        y $in R
        z $in R
```

2. There is no infinite verification loop in Litex

For example, consider the following code:

```litex
prop p(x R)
prop q(x R)
know forall x R => $p(x) <=> $q(x)
$p(1)
```

Since Litex searches related facts using `match and substitution`, it finds that if we can prove $q(1) is true then $p(1) is true. So we prove $q(1). Then we find that if we can prove $p(1) is true then $q(1) is true. So we prove $p(1). This is a loop. It happens when two facts are equivalent.

This won't happen in Litex. Litex just searches 2 rounds of related `forall` facts. So even if we have a loop, it will end after 2 rounds. (Number 2 is equal to the depth of maximum `forall` depth, this is not a coincidence, it's by design.)