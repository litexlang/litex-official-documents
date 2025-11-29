# Update 2025-10-20

1. CCF Ant Group Competition
2. Major Kernel Updates
    1. `or` is now infix notation, which better aligns with human and AI intuition: `a = 1 or a = 2` instead of `or(a = 1, a = 2)`
    2. `prove_is_transitive_prop` allows props with transitivity to let the kernel directly use transitivity to prove related facts without manual writing: for example, `let a R: a > 2 \n a > 1` automatically holds
    3. Symbol = value allows values to exist as symbol assignments. If facts related to the symbol cannot be proven, the kernel automatically extracts the symbol's value to prove related facts; example: `let a R: a = 2 \n a > 1`
    4. Fixed the long-standing whitespace issue on Windows systems
3. Machine Heart SOTA reported on Litex: https://mp.weixin.qq.com/s/WWaVIPhzpUZCxcOAR29LTg?scene=1&click_id=1
4. Dataset continues to grow: https://huggingface.co/litexlang
5. Welcome everyone to register for the AI For Formal Language competition jointly organized by Ant Digital Technology and the China Computer Federation, and compete using Litex as the base language: https://www.xir.cn/competitions/1143. The prizes are very generous, and Litex users will receive additional rewards even with average performance. Interested friends please register before November 2nd!