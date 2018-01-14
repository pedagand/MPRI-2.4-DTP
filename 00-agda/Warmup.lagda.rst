================================================================
Warming up
================================================================

Cheatsheets:
  - `Install Agda`_
  - `Retrieve the Agda Standard Library <https://github.com/agda/agda-stdlib/archive/v0.14.tar.gz>`_
  - `Setup the Standard Library`_
  - Get used to the `Emacs mode`_
  - RTF `Agda Manual`_ if necessary

************************************************
Agda in a Nutshell
************************************************

First, check that the Agda mode is properly configured in your Emacs
session: if it does, you should see ``(Agda)`` in the status bar of this
buffer. You can try to manually load it by typing

    ``M-x agda2-mode``

To check that Agda is properly configured, load this buffer by typing

    ``C-c C-l``

If everything works fine, then the following definition should color
itself properly::

    data World : Set where
      hello : World

and the status bar of this buffer should become ``(Agda:Checked)``.

We use the Agda Standard Library, which is developed separately from
the core language and must therefore be installed independantly. The
previous step may have failed, indicating an error here::

    open import Data.Nat
    open import Relation.Binary.PropositionalEquality

    foo : 0 ≡ 0
    foo = refl

If so, then there is something wrong with your setup of the standard
library. You can look at the buffer ``*agda2*`` to get some info about
the internal state of the Agda mode, which might help you in
troubleshooting any issue you encounter during the setup:

    ``C-x b *agda2*``

At this point, everything should be in working order.

************************************************
Motivating example: evolution of a type-checker
************************************************

To understand the dynamics and idiosyncrasies of an Agda programmer,
we suggest that you study the Git history of the mock project
`Evolution of a Typechecker`_. Use 

    ``git log --graph --all`` 

to begin your exploration with a bird-eye view of the project.

.. References:

.. _`Install Agda`: http://agda.readthedocs.io/en/v2.5.3/getting-started/installation.html
.. _`Configure the Standard Library`: http://agda.readthedocs.io/en/v2.5.2/tools/package-system.html#example-using-the-standard-library
.. _`Emacs mode`: http://agda.readthedocs.io/en/latest/tools/emacs-mode.html
.. _`Agda manual`: https://agda.readthedocs.io/en/v2.5.3/
.. _`Evolution of a Typechecker`: https://github.com/pedagand/typechecker-evolution
.. TODO: any other useful resources for setting things up?

.. Local Variables:
.. mode: agda2
.. End:
