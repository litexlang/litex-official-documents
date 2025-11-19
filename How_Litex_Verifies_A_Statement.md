# How Litex Verifies a Statement

```
      +--------------------------------------------------------------+
      |  Start to verify a factual statement:                        |
      |  e.g., check 1 + 1 = 2, check Socrates is mortal             |
      +--------------------------------------------------------------+
                                   |
                                   v
      +--------------------------------------------------------------+
      |  Is it related to numbers?                                   |
      |  If yes, compute it. e.g., 1 + 1 = 2                         |
      +--------------------------------------------------------------+
              | Yes ✓                                | No ✗
              v                                       v
      +---------------------------+        +----------------------------------+
      | Verification Success! ✓😊 |        | Can it be proven using          |
      +---------------------------+        | known specific facts?            |
                                           | e.g., if a = 1, then a = 1       |
                                           +----------------------------------+
                                                     |
                                        Yes ✓      | No ✗
                                          v         v
                             +---------------------------+
                             | Verification Success! ✓😊 |
                             +---------------------------+
                                                       |
                                                       v
                                           +----------------------------------+
                                           | Can it be proven using           |
                                           | known universal facts?           |
                                           | e.g., all men mortal +           |
                                           | Socrates is a man → mortal       |
                                           +----------------------------------+
                                                     |
                                        Yes ✓      | No ✗
                                          v         v
                             +---------------------------+
                             | Verification Success! ✓😊 |
                             +---------------------------+
                                                       |
                                                       v
                                           +----------------------------------+
                                           | Does it have special properties? |
                                           | (transitive/commutative/...)     |
                                           | If so, rewrite and check again   |
                                           +----------------------------------+
                                                     |
                                        Yes ✓      | No ✗
                                          |         |
      <-----------------------------------|         |
        (rewrite and back to top)                   |
                                                    |
                                                    v
                            +---------------------------+
                            | Verification Failed ☹️✗   |
                            +---------------------------+
      
```

