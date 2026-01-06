# Tips

_Conceptual integrity is the most important consideration in system design._

_- The Mythical Man-Month_

1. Since the verification process is based on match-and-substitution, it's highly recommended to maintain consistent writing style. This allows Litex's kernel to perform optimally and facilitates matching. Don't use different notations for logically equivalent facts. For example, if you choose to use `a < b`, don't occasionally use `b > a`. If `f = g`, stick to using either `f` or `g` consistently, rather than switching between them.