# Update 2025-10-20

## Competition Announcement

Welcome everyone to register for the AI For Formal Language competition jointly organized by Ant Digital Technology and the China Computer Federation, and compete using Litex as the base language: https://www.xir.cn/competitions/1143. The prizes are very generous, and Litex users will receive additional rewards even with average performance. Interested friends please register before November 2nd!

## Major Kernel Updates

1. **`or` is now infix notation**, which better aligns with human and AI intuition: `a = 1 or a = 2` instead of `or(a = 1, a = 2)`
2. **`prove_trans_prop`** allows props with transitivity to let the kernel directly use transitivity to prove related facts without manual writing: for example, `let a R: a > 2 \n a > 1` automatically holds
3. **Symbol = value** allows values to exist as symbol assignments. If facts related to the symbol cannot be proven, the kernel automatically extracts the symbol's value to prove related facts; example: `let a R: a = 2 \n a > 1`
4. **Fixed the long-standing whitespace issue** on Windows systems

## Website Updates

The Litex website has been updated with a clearer and more beautiful design. Welcome everyone to check it out: https://litexlang.com/

## Weekly Updates

1. **Website AI Q&A feature**: Added an AI Q&A feature on the website to help users learn and use Litex more easily.
2. **Kernel bug fixes**: Fixed matching and replacement issues with global and local naming conflicts, made function sets also be sets, and ensured built-in axiom sets cannot contain themselves.
3. **Tutorial improvements**: Updated unclear parts in the tutorial.
4. **Upcoming pipeline feature**: Expected to launch next week - a kernel pipeline that shows which rules Litex uses when proving a fact. This will lay the groundwork for further establishing Litex's theoretical foundation.

## Media Coverage

Machine Heart SOTA reported on Litex: https://mp.weixin.qq.com/s/WWaVIPhzpUZCxcOAR29LTg?scene=1&click_id=1

## Dataset

Dataset continues to grow: https://huggingface.co/litexlang

---

Finally, sincere thanks to all friends who care about and support Litex. Your support is our greatest motivation to move forward!
