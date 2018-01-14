..
  ::
  {-# OPTIONS --allow-unsolved-metas #-}

  module 02-dependent.Indexed where

================================================================
Indexed functional programming
================================================================

.. TODO: Ahman NbE in Presheafs

* Tagless interpreters (_essential_)
    - Ref.: ["A type-correct, stack-safe, provably correct expression compiler in Epigram", Wright \& McKinna](http://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.105.4086&rep=rep1&type=pdf)
    - Ref.: ["Strongly Typed Term Representations in Coq", Benton et al.](http://sf.snu.ac.kr/gil.hur/publications/typedsyntaxfull.pdf)
* Typed CPS transform or typed defunctionalization) (_essential_)
    - Ref.: ["Certified Type-Preserving Compiler from Lambda Calculus to Assembly Language", Chlipala](http://adam.chlipala.net/papers/CtpcPLDI07/CtpcPLDI07.pdf)
    - Ref.: ["Parametric Higher-Order Abstract Syntax for Mechanized Semantics", Chlipala](http://adam.chlipala.net/papers/PhoasICFP08/PhoasICFP08.pdf)
* Indexed monads
    - Ref.: ["Kleisli arrows of outrageous fortune", McBride](https://personal.cis.strath.ac.uk/conor.mcbride/Kleisli.pdf)


Takeaways:
  * You are _familiar_ with the construction of denotational models in type theory
  * You are _able_ to define an inductive family that captures exactly some structural invariant
  * You are _able_ to write a dependently-typed program
  * You _may_ be _familiar_ with normalization-by-evaluation proof for the simply-typed calculus

.. Local Variables:
.. mode: agda2
.. End:
