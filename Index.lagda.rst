================================================================
MPRI 2.4 : Dependently-typed Functional Programming
================================================================

..
  Make sure that everything compiles::

  open import 00-agda.Warmup
  open import 01-effectful.Monad
  open import 02-dependent.Indexed
  open import 03-total.Recursion
  open import 04-generic.Desc
  open import 05-open.Problems

This course is organized as follows:

.. toctree::
   :maxdepth: 1

   00-agda/Warmup
   01-effectful/Monad
   02-dependent/Indexed
   03-total/Recursion
   04-generic/Desc
   05-open/Problems

************************************************
Build
************************************************

You will need 
  * Agda (tested with version 2.5.3)
  * Sphinx (tested with version 1.6.4)

Type:

    ``make html``

which will produce the lecture notes in ``build/html/index.html``.

************************************************
Contributing
************************************************

Feel free to submit a PR if you spot any typo, have comments or think
of any way to improve the material. For instance, if some resource
available on the web were useful to you during this course, please add
a link to this resource where you see fit.

I also welcome alternative implementations in other dependently-typed
(or almost) languages (OCaml or Haskell with GADTs, vanilla Coq,
Coq/Equations, etc.).

I am also eager to replace references to papers behind paywalls by
freely accessible (but legal and stable) links. Please keep the `doi`_
links in comments nonetheless.

************************************************
Author
************************************************

The lecture notes have been written by `Pierre-Évariste Dagand`_.

************************************************
License
************************************************

These lecture notes are available under an `MIT License`_.


.. References:

.. _`doi`: https://www.doi.org/
.. _`Pierre-Évariste Dagand`: https://pages.lip6.fr/Pierre-Evariste.Dagand/
.. _`MIT License`: https://tldrlegal.com/license/mit-license

.. Local Variables:
.. mode: agda2
.. End:
