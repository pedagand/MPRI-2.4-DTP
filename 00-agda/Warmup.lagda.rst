..
  ::
  module 00-agda.Warmup where

================================================================
Warming up
================================================================

These lecture notes have been prepared with Agda (version 2.5.4.1) and
the Agda standard library (version 0.17). These are readily available
in Debian buster and Ubuntu disco, for example.

Cheatsheets:
  - `Install Agda`_
  - `Retrieve the Agda Standard Library <https://github.com/agda/agda-stdlib/archive/v0.17.tar.gz>`_
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
Type theory in a nutshell
************************************************

.. TODO: write in LaTeX?

For pen-and-paper reasoning, the core of type theory can be summarized
by the following typing rules and notational devices. This also sets
the scene for our future interactions with Agda, which nicely follows
established pen-and-paper notations.

There is a type for types (and let's not talk about stratification):

.. code-block:: none

   -------------
   Γ ⊢ Set ∈ Set

Π-types extend function types ("dependent functions") where the value
of the argument can be used to define the return type:

.. code-block:: none

   Γ ⊢ A ∈ Set
   Γ, a : A ⊢ B ∈ Set
   ---------------------
   Γ ⊢ (a : A) → B ∈ Set

   Γ, x : A ⊢ b ∈ B[x/a]
   ------------------------
   Γ ⊢ λ x. b ∈ (a : A) → B

   Γ ⊢ f ∈ (a : A) → B
   Γ ⊢ s ∈ A
   -------------------
   Γ ⊢ f s ∈ B[a/s]

When ``a`` is free in ``B``, we may simplify ``(a : A) → B`` into ``A
→ B``: this is indeed a standard issue function type. When the type of
``a`` can be inferred from context, we may write ``∀ a → B`` instead
of ``(a : A) → B``. A `telescope` is a sequence of Π-types is written
``(a₁ : A₁)(a₂ : A₂)...(aₙ : Aₙ) → B``, dispensing with the
intermediate arrows.

Σ-types extend product types ("dependent pairs") where the value of
the first component refines the type of the second component:

.. code-block:: none

   Γ ⊢ A ∈ Set
   Γ, a : A ⊢ B ∈ Set
   ---------------------
   Γ ⊢ (a : A) × B ∈ Set

   Γ ⊢ t₁ ∈ A
   Γ ⊢ t₂ ∈ B[t₁/a]
   ---------------------------
   Γ ⊢ (t₁ , t₂) ∈ (a : A) × B

   Γ ⊢ p ∈ (a : A) × B
   -------------------
   Γ ⊢ π₁ p ∈ A

   Γ ⊢ p ∈ (a : A) × B
   -------------------
   Γ ⊢ π₂ p ∈ B[π₁ p/a]

When ``a`` is free in ``B``, we may simplify ``(a : A) × B`` into ``A
× B``: this is indeed a standard issue product type. When the type of
``a`` can be inferred from context, we may write ``∃ a → B`` instead
of ``(a : A) × B``. Again, a sequence of Σ-types is written ``(a₁ :
A₁)(a₂ : A₂)...(aₙ : Aₙ) × B``, dispensing with the intermediate
products.

Since computation can occur at the type-level, we have to consider
types up to conversion:

.. code-block:: none

   Γ ⊢ t ∈ S
   S ≡ T        
   ---------
   Γ ⊢ t ∈ T


************************************************
Motivating example: evolution of a type-checker
************************************************

To understand the dynamics and idiosyncrasies of an Agda programmer,
we suggest that you study the Git history of the mock project
`Evolution of a Typechecker`_. Use 

    ``git log --graph --all`` 

to begin your exploration with a bird-eye view of the project.

.. References:

.. _`Install Agda`: https://agda.readthedocs.io/en/v2.5.4.1/getting-started/installation.html
.. _`Setup the Standard Library`: https://agda.readthedocs.io/en/v2.5.4.1/tools/package-system.html#example-using-the-standard-library
.. _`Emacs mode`: http://agda.readthedocs.io/en/v2.5.4.1/tools/emacs-mode.html
.. _`Agda manual`: https://agda.readthedocs.io/en/v2.5.4.1/
.. _`Evolution of a Typechecker`: https://github.com/pedagand/typechecker-evolution
.. TODO: any other useful resources for setting things up?

.. Local Variables:
.. mode: agda2
.. End:
