================================================================
MPRI 2.4 : Dependently-typed Functional Programming
================================================================

.. BEGIN HIDE

**WARNING: This is the "Teacher" edition of MPRI24-DTP.**
**If you're an MPRI student, you should not be here but** `there <https://gitlab.inria.fr/fpottier/mpri-2.4-public/blob/master/>`_.

.. END HIDE

-------------------------

..
  Make sure that everything compiles::

  open import 00-agda.Warmup
  open import 01-effectful.Monad
  open import 02-dependent.Indexed
  open import 03-total.Recursion
  open import 04-generic.Desc
  open import 05-open.Problems

.. BEGIN HIDE

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
Using the lecture notes
************************************************

This course is organized in 5 lectures, meant to be presented in slots
of 2h30 each. The first lecture includes an example-driven
introduction to Agda, which culminates with the presentation of `The
Evolution of a Typechecker
<https://github.com/pedagand/typechecker-evolution>`_ serving as a
fast-paced transition from functional programming to idiomatic,
dependently-typed programming. Each lecture consists in a literate
Agda file, which exists in 4 forms:

  teacher version:
    It contains a complete & type-checked program, including exercises
    and their corrections. These are the files contained in this
    repository.

  student version:
    It contains a mostly complete program, at the exception of
    exercises, which are left as holes in the development. These are
    the files contained in the `MPRI repository
    <https://gitlab.inria.fr/fpottier/mpri-2.4-public/blob/master/>`_.

  student printable version:
    It is the same as the "student version", only processed by Sphinx
    into a pdf file.

  teaching version:
    During class, we collectively reconstruct the desired
    program. Therefore, we start from a stripped-down variant of the
    student version where some essential definitions have been replaced
    by holes. Exercises are left as homework.

The *student version* is obtained from the *teacher version* thanks to
the (dependently-untyped) ``studentize.py`` script. For example,

.. TODO: update instructions

.. code-block:: shell

    studentize.py 01-effectful/Monad.lagda.rst

will produce the student version in
``01-effectful/Monad.student.lagda.rst``. Beware that, due to Agda's
reliance on filenames for identifying modules, this file must be
renamed ``Monad.lagda.rst`` (in an other directory) to be usable by
Agda.

The *teacher version* is obtained from the *student version* and a
corresponding patch. Teaching patches are stored in the ``./teaching``
directory. To produce the teaching version of the lectures, type:

.. code-block:: shell

    cd teaching; make all

As a result of this command, the directory ``./teaching`` mirrors the
root directory: to each ``.lagda.rst`` of the source corresponds a
teaching variant of the same name in ``./teaching``.


************************************************
Build the lecture notes
************************************************

You will need 
  * Agda (tested with version 2.6.0.1)
  * Agda standard library (tested with version 1.1)
  * Sphinx (tested with version 1.8.5)

Type:

.. code-block:: shell

    make html
    make latexpdf

which will produce the lecture notes in ``build/html/index.html`` for
the HTML version and ``build/latex/*.pdf`` for the pdf versions.

.. END HIDE

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

The lecture notes have been written by `Pierre-Évariste Dagand`_,
shakily standing on the shoulders of giants.

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
