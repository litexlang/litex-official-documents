# Appendix: Language Tradeoffs

Simplicity over Generality: Litex focuses more on simplicity of the language, so that more people can learn to use it. Currently, Litex has built-in support for naive set theory and first-order logic, which is enough for most daily math. If adding certain features (such as higher-order logic) would compromise Litex’s simplicity, we would rather leave them out. 

*Simplicity is the single most important consideration in the design of Litex. It is more important than any other features like generality, elegance, efficiency, etc.*

Community-Driven Fast Development over Careful Design: Litex follows the 'worse is better' development model, because this is the most effective way for software to gain impact. We care more about building the community and iterating quickly based on community feedback. No matter how good a feature is, if it cannot be implemented quickly or is not widely requested by the community, we won’t consider it.

*Bugs won't make Litex obsolete. What truly kills a software is the lack of users and supporters.*

Pragmatic over Idealistic: We would rather add features that are useful for daily math than features that are useful for theoretical math which is understood by only a few people on earth. That's why Litex is ended with tex: we want to make it a wide-spread pragmatic language which solves real problems just like tex.

*We are not aiming for a perfect language, but a language that is good enough for most use cases, that evolves at a fast pace.*