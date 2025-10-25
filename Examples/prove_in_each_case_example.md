```litex
claim:
    forall x1, x2, sum R:
        (x1 + 3)^2 = 121
        (x2 + 3)^2 = 121
        x1 > x2
        sum = x1 + x2
        =>:
            sum = -6
    prove:
        claim:
            forall x R: (x + 3)^2 = 121 => x = 8 or x = -14
            prove:
                (x + 3)^2 = 121
                x + 3 = sqrt(121) or x + 3 = -sqrt(121)
                11 = sqrt(121)
                prove_in_each_case:
                    x + 3 = 11 or x + 3 = -11
                    =>:
                        x = 8 or x = -14
                    prove:
                        x + 3 = 11
                        x = (x + 3) - 3 = 11 - 3 = 8
                    prove:
                        x + 3 = -11
                        x = (x + 3) - 3 = -11 - 3 = -14

        x1 = 8 or x1 = -14
        x2 = 8 or x2 = -14

        claim:
            not x2 = 8
            prove_by_contradiction:
                prove_in_each_case:
                    x1 = 8 or x1 = -14
                    =>:
                        not x1 > x2
                    prove:
                        not x1 > x2
                    prove:
                        not x1 > x2
                x1 > x2
        x2 = -14
        
        claim:
            not x1 = -14
            prove_by_contradiction:
                not x1 > x2
        x1 = 8


        x1 + x2 = 8 + (-14) = -6 = sum
```
