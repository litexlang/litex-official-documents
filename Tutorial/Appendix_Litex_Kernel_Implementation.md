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

2. 