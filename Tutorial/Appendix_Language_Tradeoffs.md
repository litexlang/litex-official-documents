# Appendix: Language Tradeoffs

Simplicity over Generality: Litex focuses more on simplicity of the language, so that more people can learn to use it. Currently, Litex has built-in support for naive set theory and first-order logic, which is enough for most daily math. If adding certain features (such as higher-order logic) would compromise Litex’s simplicity, we would rather leave them out. 

*Simplicity is the single most important consideration in the design of Litex. It is more important than any other features like generality, elegance, efficiency, etc.*

Community-Driven Fast Development over Careful Design: Litex follows the 'worse is better' development model, because this is the most effective way for software to gain impact. We care more about building the community and iterating quickly based on community feedback. Developing at a much faster pace than usual means more features and a better user experience, but it inevitably comes at the cost of some instability.

Pragmatic over Idealistic: We would rather add features that are useful for daily math than features that are useful for theoretical math which is understood by only a few people on earth. We never seek to make Litex a perfect language, but a language that is good enough for most use cases.