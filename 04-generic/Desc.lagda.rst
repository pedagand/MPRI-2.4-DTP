..
  ::
  {-# OPTIONS --allow-unsolved-metas --type-in-type #-}

  module 04-generic.Desc where

================================================================
Generic functional programming
================================================================

Extensional vs. intensional generic programming:
  - extensional: meta-level support for accessing structures
    (intuition: type-classes)
  - intensional: internalized code & interpretation
    (intuition: universe)

Extensional side of this lecture:
  - (Lecture 1: Monad, MonadFail)
  - Monoid
  - Functor
  - Applicative
  - Foldable
  - Traversable
  - Want more? `Typeclassopedia`_!

.. BEGIN HIDE
  missing:
   - Monad transformers,
   - MonadFix,
   - Semigroup,
   - Alternative,
   - MonadPlus,
   - Category,
   - Arrow,
   - Comonad

.. TODO: resurrect Xavier's applicative examples?
.. END HIDE

Intensional side of this lecture:
  - reflecting inductive types
  - internalized generic programming (over inductive types)

Vision: `Generic programming is just programming <https://doi.org/10.1145/1863543.1863547>`_
  - Program with structure, one way (extensional) or another (intensional)
  - Reflect the programming language in itself, one way (type-classes) or another (universe)

Takeaways:
  - you will be *able* to spot the following structures: Monoid, Functor, Applicative, Monad, Foldable, Traversable
  - you will be *able* to generalize a program to exploit any of the above structures
  - you will be *able* to program in/with a universe of descriptions
  - you will be *familiar* with Naperian functors
  - you will be *familiar* with the notion of universe
  - you will be *familiar* with "instance arguments"/"type classes"

************************************************
Extensional Generic Programming
************************************************

..
  ::
  module Naperian where
    open import Function

    open import Data.Unit
    open import Data.Bool
    open import Data.Sum hiding (map)
    open import Data.Product hiding (map)
    open import Data.Nat
    open import Data.Fin hiding (_+_)
    open import Data.List
      hiding (map ; replicate ; zipWith ; foldr ; sum ; lookup ; tabulate)

    open import Relation.Binary.PropositionalEquality

    infixr 5 _∷_
    infixl 4 _<*>-Vec_



Following Gibbons' `APLicative Programming Naperian Functors`_, we are
going to study the algebraic structure of "array-oriented programming
language", à la APL (or any of its descendant, such as J). In effect,
we shall build a *deep embedding* of a (small) subset of APL in Agda.


To do so, we will need a datastructure to represent multi-dimensional
arrays, keeping track of (all of) their dimensions. We ought to be
able to define:

.. code-block:: agda

      -- 3-elements vectors:
      v123 = C (S (1 ∷ 2 ∷ 3 ∷ []))
      v456 = C (S (4 ∷ 5 ∷ 6 ∷ []))

      -- 2x2 matrices:
      v12-34 = C (C (S (((1 ∷ 2 ∷ []) ∷
                        ((3 ∷ 4 ∷ []) ∷ [])))))

      v56-78 = C (C (S (((5 ∷ 6 ∷ []) ∷
                        ((7 ∷ 8 ∷ []) ∷ [])))))

      -- 3x3 matrix:
      v123-456-789 = C (C (S ((1 ∷ 2 ∷ 3 ∷ []) ∷
                              (4 ∷ 5 ∷ 6 ∷ []) ∷
                              (7 ∷ 8 ∷ 9 ∷ []) ∷ [])))

      -- 3x2 matrix:
      v12-45-78 = C (C (S ((1 ∷ 2 ∷ []) ∷
                           (4 ∷ 5 ∷ []) ∷
                           (7 ∷ 8 ∷ []) ∷ [])))

      -- 2x3 matrix:
      v123-456 = C (C (S ((1 ∷ 2 ∷ 3 ∷ []) ∷
                         ((4 ∷ 5 ∷ 6 ∷ []) ∷ []))))

      -- 2x2x2 matrix:
      v1234-5678 = C (C (C (S (((1 ∷ 2 ∷ []) ∷
                               ((3 ∷ 4 ∷ []) ∷ [])) ∷
                              (((5 ∷ 6 ∷ []) ∷
                               ((7 ∷ 8 ∷ []) ∷ [])) ∷ [])))))

Exploiting add-hoc polymorphism, we want to be able to apply unary
operations pointwise to every element of a matrix, whatever its size:

.. code-block:: agda

      square (S 3) ≡ S 9
      square v123 ≡ C (S (1 ∷ 4 ∷ 9 ∷ []))
      square v123-456-789
        ≡ C (C (S ((1 ∷  4 ∷  9 ∷ []) ∷
                  (16 ∷ 25 ∷ 36 ∷ []) ∷
                  (49 ∷ 64 ∷ 81 ∷ []) ∷ [])))
      square v12-45-78
        ≡ C (C (S(( 1 ∷  4 ∷ []) ∷
                  (16 ∷ 25 ∷ []) ∷
                  (49 ∷ 64 ∷ []) ∷ [])))
      square v1234-5678
        ≡ C (C (C (S (((1  ∷  4 ∷ []) ∷
                      ((9  ∷ 16 ∷ []) ∷ [])) ∷
                     (((25 ∷ 36 ∷ []) ∷
                      ((49 ∷ 64 ∷ []) ∷ [])) ∷ [])))))

And similarly for n-ary operations, when the arguments are
"compatible" (we will define and refine the notion of compatibility
later):

.. code-block:: agda

      (_+_ <$> v123 ⊛ v456)
        ≡ C (S (5 ∷ 7 ∷ 9 ∷ []))

      (_+_ <$> v12-34 ⊛ v56-78)
        ≡ C (C (S (( 6 ∷  8 ∷ []) ∷
                  ((10 ∷ 12 ∷ []) ∷ []))))

We should be able to process a matrix "per row", perhaps in a stateful
manner:

 .. code-block:: agda

      sum v123 ≡ S 6
      sum v123-456 ≡ C (S (6 ∷ 15 ∷ []))

      sums v123 ≡ C (S (1 ∷ 3 ∷ 6 ∷ []))

      sums v123-456 ≡ C (C (S ((1 ∷ 3 ∷  6 ∷ []) ∷
                               (4 ∷ 9 ∷ 15 ∷ []) ∷ [])))

Or "per column", using the *reranking* operator ```¹``, which amounts
to pre- and post-composing the desired operation with a transposition:

 .. code-block:: agda

      sums `¹ v123-456 ≡ C (C (S ((1 ∷ 2 ∷ 3 ∷ []) ∷
                                  (5 ∷ 7 ∷ 9 ∷ []) ∷ [])))


--------------------------------
Functor
--------------------------------

To represent vectors, we need a notion of arrays of a given size::

    data Vec (A : Set) : ℕ → Set where
      []  : Vec A zero
      _∷_ : ∀ {n} (x : A) (xs : Vec A n) → Vec A (suc n)

    vec : ℕ → Set → Set
    vec n A = Vec A n

Applying an operation pointwise to every elements of a vector is
exactly what ``map`` does::

    map-Vec : ∀ {n}{A B : Set} → (A → B) → vec n A → vec n B
    map-Vec f [] = []
    map-Vec f (x ∷ xs) = f x ∷ map-Vec f xs

This would allow us to lift the operation ``square`` on numbers to
apply on vectors of numbers.

A function of type ``Set → Set`` having a ``map`` is called a `functor <https://wiki.haskell.org/Typeclassopedia#Functor>`_::

    record Functor (F : Set → Set) : Set₁ where
      infixl 4 _<$>_ _<$_

      field
        _<$>_ : ∀ {A B} → (A → B) → F A → F B

      _<$_ : ∀ {A B} → A → F B → F A
      x <$ y = const x <$> y

    open Functor ⦃...⦄
    instance
      VecFunctor : ∀ {n} → Functor (vec n)
      _<$>_ {{ VecFunctor {n} }} = map-Vec

..
  ::

    module Example-vec-functor where
      v123 : Vec ℕ 3
      v123 = 1 ∷ 2 ∷ 3 ∷ []

      v456 : Vec ℕ 3
      v456 = 4 ∷ 5 ∷ 6 ∷ []

      test1 : ((λ x → 3 + x) <$> v123) ≡ v456
      test1 = refl


It ought to abide by the functorial laws::

    record IsFunctor (F : Set → Set){{_ : Functor F}} : Set₁ where
      field
        id-<$> : ∀ {A} (x : F A) →
                    (id <$> x) ≡ x
        ∘-<$> : ∀ {A B C} (x : F A)(f : A → B)(g : B → C) →
                    ((g ∘ f) <$> x) ≡ (g <$> (f <$> x))

**Exercise (difficulty: 1)** Prove the functor law for ``vec``.

Another (arbitrary) example of functor is the following::

    data Pair (A : Set) : Set where
      P : A → A → Pair A

    instance
      PairFunctor : Functor Pair
      _<$>_ {{PairFunctor}} f (P x y) = P (f x) (f y)

**Exercise (difficulty: 1)** Prove the functor law for ``Pair``.

**Exercise (difficulty: 1)** Show that lists define a functor.

.. BEGIN HIDE
  ::
    instance
      ListFunctor : Functor List
      _<$>_ {{ListFunctor}} f [] = []
      _<$>_ {{ListFunctor}} f (x ∷ xs) = f x ∷ (f <$> xs)
.. END HIDE

**Exercise (difficulty: 1)** We define::

    record Arrow (A : Set)(B : Set) : Set where
      constructor ar
      field
        apply : A → B

Let ``A : Set``. Is ``Arrow A : Set → Set`` an endofunctor on ``Set``?

.. BEGIN HIDE
  ::
    ArrowFunctor : ∀ {A} → Functor (Arrow A)
    _<$>_ {{ArrowFunctor}} f (ar g) = ar (f ∘ g)
.. END HIDE


**Exercise (difficulty: 1)** We define::

    record CoArrow (B : Set)(A : Set) : Set where
      constructor co
      field
        apply : A → B

Let ``B : Set``. Is ``CoArrow B : Set → Set`` an endofunctor on
``Set``?

**Exercise (difficulty: 3)** Constructively prove your above answer.

.. BEGIN HIDE
  ::
    open import Data.Empty

    pf-CoArrow-not-Functor : Functor (CoArrow ⊥) → ⊥
    pf-CoArrow-not-Functor F = CoArrow.apply (f <$>F x) tt
        where open Functor F renaming (_<$>_ to _<$>F_)
              f : ⊥ → ⊤
              f _ = tt
              x : CoArrow ⊥ ⊥
              x = co λ falso → falso
.. END HIDE

--------------------------------
Applicative
--------------------------------

To lift n-ary operation ``f`` over two vectors of same size, we merely
need a (total!) ``zipWith``::

    zipWith-Vec : ∀ {n} {A B C : Set} →
              (A → B → C) → vec n A → vec n B → vec n C
    zipWith-Vec f [] [] = []
    zipWith-Vec f (x ∷ xs) (y ∷ ys) = f x y ∷ zipWith-Vec f xs ys

However, ``zipWith`` can be obtained from two more primitive
operations and the functoriality of vectors::

    replicate-Vec : ∀ {n} {A : Set} → A → vec n A
    replicate-Vec {n = zero}  x = []
    replicate-Vec {n = suc n} x = x ∷ replicate-Vec x

    _<*>-Vec_ : ∀ {n} {A B : Set} → vec n (A → B) → vec n A → vec n B
    []       <*>-Vec []       = []
    (f ∷ fs) <*>-Vec (x ∷ xs) = f x ∷ (fs <*>-Vec xs)

    zipWith-Vec' : ∀ {n} {A B C : Set} →
              (A → B → C) → vec n A → vec n B → vec n C
    zipWith-Vec' f xs ys = f <$> xs <*>-Vec ys

A functor equipped with these two operations is an `applicative
functor <https://wiki.haskell.org/Typeclassopedia#Applicative>`_::

    record Applicative (F : Set → Set) : Set₁ where
      infixl 4 _⊛_ _<⊛_ _⊛>_
      infix  4 _⊗_

      field
        pure : ∀ {A} → A → F A
        _⊛_  : ∀ {A B} → F (A → B) → F A → F B
        overlap {{super}} : Functor F

      zipWith : ∀ {A B C} → (A → B → C) → F A → F B → F C
      zipWith f x y = f <$> x ⊛ y

      _<⊛_ : ∀ {A B} → F A → F B → F A
      a <⊛ b = const <$> a ⊛ b

      _⊛>_ : ∀ {A B} → F A → F B → F B
      a ⊛> b = (const id) <$> a ⊛ b

      _⊗_ : ∀ {A B} → F A → F B → F (A × B)
      x ⊗ y = (_,_) <$> x ⊛ y

      replicate : ∀ {A} → A → F A
      replicate = pure

    open Applicative ⦃...⦄
    instance
      VecApplicative : ∀ {n} → Applicative (vec n)
      pure {{VecApplicative}} = replicate-Vec
      _⊛_ {{VecApplicative}} = _<*>-Vec_

..
  ::
    module Example-vec-applicative where

      open Example-vec-functor

      v333 : Vec ℕ 3
      v333 = replicate-Vec 3

      test : zipWith _+_ v333 v123 ≡ v456
      test = refl


It ought to abide by the applicative laws::

    record IsApplicative (F : Set → Set){{_ : Applicative F}} : Set₁ where
      field
        pure-id : ∀ {A} (v : F A) →
                      (pure id ⊛ v) ≡ v
        pure-pure : ∀ {A B} (f : A → B)(a : A) →
                      (pure f ⊛ pure a) ≡ pure {F} (f a)
        applicative : ∀ {A B}{u : F (A → B)}{a : A} →
                      (u ⊛ pure a) ≡ (pure (λ f → f a) ⊛ u)
        composition : ∀ {A B C}{u : F (B → C)}{v : F (A → B)}{w : F A} →
                      (u ⊛ (v ⊛ w)) ≡ ((pure (λ g f a → g (f a))) ⊛ u ⊛ v ⊛ w)


**Exercise (difficulty: 1)** Prove the applicative laws for ``vec``.

Pairs are also applicative::

    instance
      PairApplicative : Applicative Pair
      pure {{PairApplicative}} a = P a a
      _⊛_  {{PairApplicative}} (P f g) (P x y) = P (f x) (g y)

**Exercise (difficulty: 1)** Prove the applicative laws for ``Pair``.

..
  ::

    open import Category.Monad
    open import Category.Monad.State


**Remark:** Every monad is an applicative functor (but not
conversely!). So, for example, the ``State`` monad (encountered in
Lecture 1) is an applicative::

    instance
      StateFunctor : ∀ {A : Set} → Functor (State A)
      _<$>_ {{StateFunctor}} f m s = let (x , s') = m s in
                                     f x , s'
      StateApplicative : ∀ {A : Set} → Applicative (State A)
      pure {{StateApplicative}} x s = x , s
      _⊛_  {{StateApplicative}} fs xs s = let (f , s') = fs s in
                                          let (x , s'') = xs s' in
                                          f x , s''

.. BEGIN HIDE
.. TODO: write the instances above (<$>, pure and ⊛) using the monadic operations
.. END HIDE

**Exercise (difficulty: 1)** Write a program that takes a monad (specified with ``return`` and ``>>=``) and produces its underlying applicative.

**Exercise (difficulty: 1)** We define::

    record PPair (A : Set)(B : Set) : Set where
      constructor ⟨_,_⟩
      field
        fst : A
        snd : B

Let ``A : Set``. Is ``PPair A : Set → Set`` an endofunctor on ``Set``? Is it an applicative?

.. BEGIN HIDE
  ::

    PPairFunctor : ∀ {A} → Functor (PPair A)
    _<$>_ {{PPairFunctor}} f ⟨ x , y ⟩ = ⟨ x , f y ⟩

    pf-PPair-not-Applicative : Applicative (PPair ⊥) → ⊥
    pf-PPair-not-Applicative A = PPair.fst x
      where open Applicative A renaming (pure to pure-A)
            x : PPair ⊥ ⊤
            x = pure-A tt
.. END HIDE

**Exercise (difficulty: 2)** We define::

    open import Data.Char hiding (toNat)
    open import Data.Maybe hiding (zipWith)

    record Regexp (A : Set) : Set where
       constructor re
       field
         match : List Char → Maybe A

Show that ``Regexp`` can be equipped with an ``Applicative`` structure
enabling us to parse context-free grammars (ie. regular
expressions). Is it (necessarily) a monad?

.. BEGIN HIDE
.. TODO Provide solution
.. END HIDE


--------------------------------
Naperian
--------------------------------

Let us (temporarily) model an m-by-n matrix as an m-elements vector of
n-elements vectors::

    matrix : ℕ → ℕ → Set → Set
    matrix m n A = vec m (vec n A)

..
  ::
    module Example-matrix where

      m123-456 : matrix 2 3 ℕ
      m123-456 = (1 ∷ 2 ∷ 3 ∷ []) ∷
                 (4 ∷ 5 ∷ 6 ∷ []) ∷ []


To implement transposition (and, therefore, reranking), we need to be
able to *index* into a vector (say, "get the value on row ``i`` and
column ``j``") as well as to be able to *create* a vector as a
function from its indices (say, "define the matrix of value ``f(i,
j)`` at row ``i`` and column ``j``). The first corresponds to a lookup
while the second corresponds to a tabulation::

    lookup-Vec : ∀ {n} {A : Set} → vec n A → Fin n → A
    lookup-Vec (x ∷ xs)  zero = x
    lookup-Vec (x ∷ xs) (suc i) = lookup-Vec xs i

    tabulate-Vec : ∀ {n} {A : Set} → (Fin n → A) → vec n A
    tabulate-Vec {zero}  f = []
    tabulate-Vec {suc n} f = f zero ∷ tabulate-Vec (f ∘ suc)

    transpose-Matrix : ∀ {m n} {A : Set} → matrix m n A → matrix n m A
    transpose-Matrix m = tabulate-Vec (λ i →
                         tabulate-Vec (λ j →
                         lookup-Vec (lookup-Vec m j) i))

..
  ::
    module Example-matrix-tranpose where

      open Example-matrix

      test : transpose-Matrix m123-456
               ≡ (1 ∷ 4 ∷ []) ∷
                 (2 ∷ 5 ∷ []) ∷
                 (3 ∷ 6 ∷ []) ∷ []
      test = refl

A functor such that there exists a set ``Log`` supporting ``lookup``
and ``tabulate`` is called a Naperian functor or a `representable
functor`_::

    record Naperian (F : Set → Set) : Set₁ where
      field
        Log : Set
        lookup : ∀ {A} → F A → (Log → A)
        tabulate : ∀ {A} → (Log → A) → F A
        overlap {{super}} : Functor F

      positions : F Log
      positions = tabulate λ ix → ix

    open Naperian {{...}}

    instance
      VecNaperian : ∀ {n} → Naperian (vec n)
      Log {{VecNaperian {n}}} = Fin n
      lookup {{VecNaperian}} = lookup-Vec
      tabulate {{VecNaperian}} = tabulate-Vec

.. TODO: add `comonad instance <https://stackoverflow.com/questions/12963733/writing-cojoin-or-cobind-for-n-dimensional-grid-type/13100857#13100857>`_


**Exercise (difficulty: 2)** State the Naperian laws and prove them
for vectors.

.. BEGIN HIDE
  ::
    record IsNaperian (F : Set → Set){{F-Naperian : Naperian F}} : Set₁ where
      field
        tabulate-lookup : ∀ {A} (v : F A) →
                            tabulate (lookup v)  ≡ v
        lookup-tabulate : ∀ {A} (f : Log {{F-Naperian}} → A)(l : Log {{F-Naperian}}) →
                            lookup {{F-Naperian}} (tabulate f) l  ≡ f l

    VectorIsNaperian : ∀{n} → IsNaperian (vec n)
    VectorIsNaperian = record { tabulate-lookup = tabulate-lookup
                              ; lookup-tabulate = lookup-tabulate }
      where tabulate-lookup : ∀ {n A} (v : vec n A) →
                            tabulate (lookup v)  ≡ v
            tabulate-lookup [] = refl
            tabulate-lookup (x ∷ v) rewrite tabulate-lookup v = refl

            lookup-tabulate : ∀ {n A} (f : Fin n → A)(l : Fin n) →
                            lookup {{VecNaperian}} (tabulate f) l  ≡ f l
            lookup-tabulate f zero = refl
            lookup-tabulate f (suc l) rewrite lookup-tabulate (λ n → f (suc n)) l = refl
.. END HIDE

**Exercise (difficulty: 1)** Show that a Naperian functor is
necessarily an Applicative functor.

.. BEGIN HIDE
  ::
    Naperian→Applicative :  (F : Set → Set){{_ : Naperian F}} → Applicative F
    pure {{Naperian→Applicative F}} a = tabulate (λ _ → a)
    _⊛_ {{Naperian→Applicative F}} f a = tabulate (λ ix → (lookup f ix) (lookup a ix))
.. END HIDE

**Exercise (difficulty: 2)** Show that Naperian functors deserve their
name: for ``f`` and ``g`` two Naperian functors, define ``Log (f ×
g)`` and ``Log (f ∘ g)`` in terms of ``Log f`` and ``Log g``. Any
other remarkable identities?

.. BEGIN HIDE
  ::

    record Prod (F : Set → Set)(G : Set → Set)(X : Set) : Set where
      constructor ⟨_,_⟩
      field
        fst : F X
        snd : G X

    ProdFunctor : ∀ F G {{_ : Functor F}}{{_ : Functor G}} →
                    Functor (Prod F G)
    _<$>_ {{ProdFunctor F G}} f ⟨ x , y ⟩ = ⟨ f <$> x , f <$> y ⟩

    ProdNaperian : ∀ F G {{_ : Naperian F}}{{_ : Naperian G}} →
                    Naperian (Prod F G)
    Log {{ProdNaperian F G {{F-Naperian}} {{G-Naperian}}}} = Log {{F-Naperian}} ⊎ Log {{G-Naperian}}
    lookup {{ProdNaperian F G}} ⟨ x , y ⟩ ( inj₁ ix) = lookup x ix
    lookup {{ProdNaperian F G}} ⟨ x , y ⟩ ( inj₂ jx) = lookup y jx
    tabulate {{ProdNaperian F G}} f = ⟨ tabulate (λ x → f (inj₁ x)) , tabulate (λ x → f (inj₂ x)) ⟩
    super {{ProdNaperian F G}} = ProdFunctor F G

    data Comp (F : Set → Set)(G : Set → Set)(X : Set) : Set where
      C : F (G X) → Comp F G X

    CompFunctor : ∀ F G {{_ : Functor F}}{{_ : Functor G}} →
                  Functor (Comp F G)
    _<$>_ {{CompFunctor F G {{F-Functor}}{{G-Functor}}}} f (C x) = C ((_<$>_ f) <$> x)

    CompNaperian : ∀ F G {{_ : Naperian F}}{{_ : Naperian G}} →
                   Naperian (Comp F G)
    Log {{CompNaperian F G {{F-Naperian}} {{G-Naperian}}}} = Log {{F-Naperian}} × Log {{G-Naperian}}
    lookup {{CompNaperian F G}} (C x) (ix , jx) = lookup (lookup x ix) jx
    tabulate {{CompNaperian F G}} f = C (tabulate (λ ix → tabulate (λ jx → f (ix , jx))))
    super {{CompNaperian F G}} = CompFunctor F G

.. END HIDE

Pairs are Naperian too::

    instance
      PairNaperian : Naperian Pair
      Log {{PairNaperian}} = Bool
      lookup {{PairNaperian}} (P x y) true = x
      lookup {{PairNaperian}} (P x y) false = y
      tabulate {{PairNaperian}} f = P (f true) (f false)

**Exercise (difficulty: 1)** Give an example of a Functor that is **not** Naperian.

.. BEGIN HIDE

  Any structure that cannot be statically indexed (in a total manner)
  will do the trick. For example, lists or any kind of data-structure
  whose size is unknown at compile-time.

.. END HIDE


Given any pair of Naperian functors, transposition is expressed as
swapping the composition of structures::

    transpose : ∀ {F G : Set → Set}
                  {{_ : Naperian F}}{{_ : Naperian G}} →
                ∀ {A} → F (G A) → G (F A)
    transpose fga = tabulate <$> (tabulate (λ gx fx → lookup (lookup fga fx) gx))

..
  ::

    module Example-matrix-tranpose' where

      open Example-matrix

      test : transpose m123-456
               ≡ (1 ∷ 4 ∷ []) ∷
                 (2 ∷ 5 ∷ []) ∷
                 (3 ∷ 6 ∷ []) ∷ []
      test = refl

      pv123-456 : Pair (vec 3 ℕ)
      pv123-456 = P (1 ∷ 2 ∷ 3 ∷ [])
                    (4 ∷ 5 ∷ 6 ∷ [])

      test2 : transpose pv123-456 ≡ P 1 4 ∷ P 2 5 ∷ P 3 6 ∷ []
      test2 = refl


--------------------------------
Interlude: Monoid
--------------------------------

So far, we have focused our attention onto type constructors
(functions of type ``Set → Set`` ). But sets can be interesting
too. For example, we may be interested in exhibiting the monoidal
structure of a given set::

    record Monoid (A : Set) : Set₁ where
      infixr 6 _<>_
      field
        mempty : A
        _<>_ : A → A → A

    open Monoid ⦃...⦄

    record IsMonoid (A : Set){{_ : Monoid A}} : Set₁ where
      field
        id-left : (a : A) → mempty <> a ≡ a
        id-right : (a : A) → mempty <> a ≡ a
        assoc : (a b c : A) → (a <> b) <> c ≡ a <> (b <> c)

.. BEGIN HIDE
.. TODO: activate?
.. {-# DISPLAY Monoid.mempty _ = mempty #-}
.. {-# DISPLAY Monoid._<>_ _ a b = a <> b #-}
.. END HIDE

Famous monoids include ``(ℕ, 0, _+_)`` and ``(List A, [], _++_)``
(also called the free monoid)::

    instance
      NatMonoid : Monoid ℕ
      mempty {{NatMonoid}} = 0
      _<>_ {{NatMonoid}} = _+_

      ListMonoid : ∀ {A} → Monoid (List A)
      mempty {{ListMonoid}} = []
      _<>_ {{ListMonoid}} xs ys = xs ++ ys

Perhaps less obviously (or, perhaps, too obviously to be noted),
endomorphisms form a monoid ``(A → A, id, _∘_)``::

      EndoMonoid : ∀ {A} → Monoid (A → A)
      mempty {{EndoMonoid}} = id
      _<>_ {{EndoMonoid}} f g = f ∘ g

**Exercise (difficulty: 2)** State the monoid laws and prove them for
the above examples.


--------------------------------
Foldable
--------------------------------

To compute the running ``sum`` over a vector of numbers, we need a
notion of iteration over vectors. In all generality, the left-to-right
iteration over a vector can be implemented as the interpretation into
a given monoid::

    foldMap-Vec : ∀ {n}{A}{W : Set} {{MonW : Monoid W}} → (A → W) → vec n A → W
    foldMap-Vec f [] = mempty
    foldMap-Vec f (x ∷ xs) = f x <> foldMap-Vec f xs

    sumAll-Vec : ∀ {n} → vec n ℕ → ℕ
    sumAll-Vec = foldMap-Vec id

Note that we recover the 70's embodiment of iteration, the ``foldr``,
by exploiting the fact that endomorphisms form a monoid::

    foldr-Vec : ∀ {n}{A B : Set} → (A → B → B) → B → vec n A → B
    foldr-Vec su ze fs = foldMap-Vec su fs ze

Conversely, we can interpret it into the initial model of foldability,
namely lists::

    toList-Vec : ∀ {n A} → vec n A → List A
    toList-Vec = foldMap-Vec (λ a → a ∷ [])

..
  ::
    module Example-sumAll where
      open Example-vec-functor

      test-sum-vec : sumAll-Vec v123 ≡ 6
      test-sum-vec = refl

      test-toList-vec : toList-Vec v123 ≡ 1 ∷ 2 ∷ 3 ∷ []
      test-toList-vec = refl


A functor offering such an iterator is said to be `foldable
<https://wiki.haskell.org/Typeclassopedia#Foldable>`_::

    record Foldable (F : Set → Set) : Set₁ where
      field
        foldMap : ∀ {A}{W : Set} {{MonW : Monoid W}} → (A → W) → F A → W
        overlap {{super}} : Functor F

      foldr : ∀ {A B : Set} → (A → B → B) → B → F A → B
      foldr su ze fs = foldMap su fs ze

      toList : ∀ {A} → F A → List A
      toList = foldMap (λ a → a ∷ [])

    open Foldable {{...}}

    sumAll : ∀ {F} → {{ _ : Foldable F}} → F ℕ → ℕ
    sumAll = foldMap id

    instance
      VecFoldable : ∀ {n} → Foldable (λ A → Vec A n)
      foldMap {{VecFoldable}} = foldMap-Vec

.. BEGIN HIDE
.. TODO add equational theory
.. END HIDE

Pairs are foldable too::

    instance
      PairFoldable : Foldable Pair
      foldMap {{PairFoldable}} f (P a b) = f a <> f b

**Exercise (difficulty: 1)** Show that lists are foldable.

.. BEGIN HIDE
  ::
    instance
      ListFoldable : Foldable List
      foldMap {{ListFoldable}} f [] = mempty
      foldMap {{ListFoldable}} f (x ∷ xs) = f x <> foldMap f xs
.. END HIDE

..
  ::
    module Example-pair-foldable where

      test-toList-pair : toList (P 42 24) ≡ 42 ∷ 24 ∷ []
      test-toList-pair = refl

      test-sum-pair : sumAll (P 42 24) ≡ 66
      test-sum-pair = refl

**Exercise (difficulty: 2)** State the foldable laws and prove them for
the above examples.

--------------------------------
Traversable
--------------------------------

Being foldable enables us to write pure iterators. To compute the
running sum of a vector, we need to perform a stateful
iteration::

    traverse-Vec : ∀ {n F A B} {{_ : Applicative F}} → (A → F B) → vec n A → F (vec n B)
    traverse-Vec f [] = pure []
    traverse-Vec f (x ∷ v) = _∷_ <$> f x ⊛ traverse-Vec f v

    increase : ℕ → State ℕ ℕ
    increase n = λ m → let n' = m + n in n' , n'

    sumsAll-Vec : ∀ {n} → vec n ℕ → vec n ℕ
    sumsAll-Vec xs = proj₁ (traverse-Vec increase xs 0)

..
  ::
    module Example-Traversable where
      open Example-vec-functor

      test-v136 : sumsAll-Vec v123 ≡ 1 ∷ 3 ∷ 6 ∷ []
      test-v136 = refl


**Remark:** Rather than an applicative, we could have asked for a
monad. However, this is needlessly restrictive (remember, every monad
is an applicative): if the side-effects are commutative (and we like
those for `performance reasons <https://doi.org/10.1145/2699681>`_), we
get more freedom with a purely applicative implementation rather than
a monadic one (for the same reason that OCaml is applicative, compiler
writers like under-specifications!).

A functor offering such an iterator is said to be `traversable
<https://wiki.haskell.org/Typeclassopedia#Traversable>`_::

    record Traversable (T : Set → Set) : Set₁ where
      field
        traverse : ∀ {F A B} {{_ : Applicative F}} → (A → F B) → T A → F (T B)
        overlap {{super}} : Foldable T

      sequence :  ∀ {F A} {{_ : Applicative F}} → T (F A) → F (T A)
      sequence = traverse id

    open Traversable ⦃...⦄
    instance
      VectorTraversable : ∀ {n} → Traversable (λ A → Vec A n)
      traverse {{VectorTraversable}} f [] = pure []
      traverse {{VectorTraversable}} f (x ∷ v) = _∷_ <$> f x ⊛ traverse f v

.. BEGIN HIDE
.. TODO add equational theory
.. END HIDE

Surprise, pairs are traversable too::

    instance
      PairTraversable : Traversable Pair
      traverse {{PairTraversable}} f (P x y) = P <$> f x ⊛ f y

**Exercise (difficulty: 2)** State the foldable laws and prove them for
the above examples.

The running sum example can then be implemented for any traversable
structure::

    sumsAll : ∀ {T} {{_ : Traversable T}} → T ℕ → T ℕ
    sumsAll xs = proj₁ (traverse increase xs 0)

..
  ::
    module Example-sumsAll where
      open Example-vec-functor hiding (test1)

      test1 : sumsAll v123 ≡ 1 ∷ 3 ∷ 6 ∷ []
      test1 = refl

      test2 : sumsAll (P 1 2) ≡ P 1 3
      test2 = refl

--------------------------------
Dimension
--------------------------------

To serve as a data container, we thus require for our type constructor
to be both traversable (ie. support effectful iteration) and naperian
(ie. suppport indexing)::

    record Dimension (F : Set → Set) : Set₁ where
      field
        overlap {{super₁}} : Applicative F
        overlap {{super₂}} : Naperian F
        overlap {{super₃}} : Traversable F


      size : ∀ {α} → F α → ℕ
      size as = length (toList as)

    open Dimension ⦃...⦄

As a result of our hard work, pairs and vectors are straightforward
instances::

    instance
      PairDimension : Dimension Pair
      PairDimension = record {}

      VectorDimension : ∀ {n} → Dimension (vec n)
      VectorDimension = record {}

**Remark:** Any dimensionable functor admits a ``size`` operation,
which counts the number of elements stored in the structure. For
vectors, a direct implementation of ``size`` would simply return the
index of the vector (without conversion to list) and for pairs, it is
constantly equal to 2.

**Example: binary vectors** rather than indexing vectors by Peano
numbers, we can index them by binary numbers::

    data Binary : Set where
      zero : Binary
      2× : Binary → Binary
      1+2× : Binary → Binary

    data BVector (A : Set) : Binary → Set where
      single : A → BVector A zero
      join : ∀ {n} → BVector A n → BVector A n → BVector A (2× n)
      1+join : ∀ {n} → A → BVector A n → BVector A n → BVector A (1+2× n)

    bvector : Binary → Set → Set
    bvector b A = BVector A b

**Exercise (difficulty: 2)** Show that binary vectors can be used as a
dimension::

    instance
      BVectorFunctor : ∀ {n} → Functor (bvector n)
      BVectorFunctor = {!!}

      BVectorFoldable : ∀ {n} → Foldable (bvector n)
      BVectorFoldable = {!!}

      BVectorApplicative : ∀ {n} → Applicative (bvector n)
      BVectorApplicative = {!!}

      BVectorNaperian : ∀ {n} → Naperian (bvector n)
      BVectorNaperian = {!!}

      BVectorTraversable : ∀ {n} → Traversable (bvector n)
      BVectorTraversable = {!!}

      BVectorDimension : ∀ {n} → Dimension (bvector n)
      BVectorDimension = record {}

**Remark:** as for vectors, the ``size`` of a binary vector can be
statically deduced from the index::

    bin2nat : Binary → ℕ
    bin2nat zero = 0
    bin2nat (2× b) = 2 * (bin2nat b)
    bin2nat (1+2× b) = 1 + 2 * bin2nat b

**Example: block matrices** This example is taken from `An agda
formalisation of the transitive closure of block matrices`_, in which
block matrices are defined as follows::

    data Shape : Set where
      L  : Shape
      B  : Shape → Shape → Shape

    data M (a : Set) : (rows cols : Shape) → Set where
        One  :  a → M a L L
        Row  :  {c₁ c₂ : Shape} →
                M a L c₁ → M a L c₂ →  M a L (B c₁ c₂)
        Col  :  {r₁ r₂ : Shape} →
                M a r₁ L → M a r₂ L →  M a (B r₁ r₂) L
        Q    :  {r₁ r₂ c₁ c₂ : Shape} →
                M a r₁ c₁ →  M a r₁ c₂ →
                M a r₂ c₁ →  M a r₂ c₂ →
                M a (B r₁ r₂) (B c₁ c₂)

**Exercise (difficulty: 2)** Show that block matrices can be used as a
dimension::

    instance
        MFunctor : ∀ {r c} → Functor (λ A → M A r c)
        MFunctor = {!!}

        MFoldable : ∀ {r c} → Foldable (λ A → M A r c)
        MFoldable = {!!}

        MApplicative : ∀ {r c} → Applicative (λ A → M A r c)
        MApplicative = {!!}

        MNaperian : ∀ {r c} → Naperian (λ A → M A r c)
        MNaperian = {!!}

        MTraversable : ∀ {r c} → Traversable (λ A → M A r c)
        MTraversable = {!!}

        MDimension : ∀ {r c} → Dimension (λ A → M A r c)
        MDimension = record {}

**Exercise (difficulty: 2)** Show that the generic ``size`` operator
defined by ``MDimension`` is equivalent to the following function::

    toNat : Shape  →  ℕ
    toNat L        =  1
    toNat (B l r)  = toNat l + toNat r


Programming solely with the structure offered by dimensions, we can
implement a generic inner product and matrix product::

    inner-product : ∀ {F} → {{_ : Dimension F}} →
                    F ℕ → F ℕ → ℕ
    inner-product xs ys = sumAll (zipWith _*_ xs ys)

    matrix-product : ∀ {F G H} →
                     {{_ : Dimension F}}{{_ : Dimension G}}{{_ : Dimension H}} →
                     F (G ℕ) → G (H ℕ) → F (H ℕ)
    matrix-product {F}{G}{H} {{dimF}} xss yss =
        zipWith (zipWith inner-product) (replicate <$> xss) (replicate (transpose yss))

..
  ::
    module Example-product where
      open Example-vec-functor

      test : inner-product v123 v456 ≡ 32
      test = refl

      test2 : inner-product (P 1 2) (P 4 5) ≡ 14
      test2 = refl

      m12-34-56 : matrix 3 2 ℕ
      m12-34-56 = (1 ∷ 2 ∷ []) ∷
                  (3 ∷ 4 ∷ []) ∷
                  (5 ∷ 6 ∷ []) ∷ []

      m6789-1234 : matrix 2 4 ℕ
      m6789-1234 = (6 ∷ 7 ∷ 8 ∷ 9 ∷ []) ∷
                   (1 ∷ 2 ∷ 3 ∷ 4 ∷ []) ∷ []

      test3 : matrix-product m12-34-56 m6789-1234
              ≡ (8 ∷ 11 ∷ 14 ∷ 17 ∷ []) ∷
                (22 ∷ 29 ∷ 36 ∷ 43 ∷ []) ∷
                (36 ∷ 47 ∷ 58 ∷ 69 ∷ []) ∷ []
      test3 = refl

--------------------------------
Multi-dimensional matrices
--------------------------------

So far, we have mostly equipped vectors with structure (and pretended
that we cared about ``Pair``). To talk about m-by-n matrices, we ended
up defining a custom datatype built from vectors of vectors. In this
section, we are going to generalize matrices both in terms of
dimension (the number of functors composed) and Dimension (the type of
functors that are composed).

This is also were all the unification hell breaks loose. This means
that we are going to introduce apparently useless definitions to guide
the unifier and some manual instanciations here and there.

A high-dimensional matrix is essentially a composition of multiple
Dimension functors. To help the unifier, we are going to reify the
composition (and identity) through custom datatype definitions::

    data Id (A : Set) : Set where
      I : A → Id A

    data Seq (G : Set → Set)(F : Set → Set)(A : Set) : Set where
      S : F (G A) → Seq G F A

Unsurprisingly, the structures we have seen so far are verified by the
identity functor and closed under composition, so we get the expected
instances.

..
  ::

    instance
      IdFunctor : Functor Id
      _<$>_ {{IdFunctor}} f (I x) = I (f x)

      IdApplicative : Applicative Id
      pure {{IdApplicative}} a = I a
      _⊛_  {{IdApplicative}} (I f) (I x) = I (f x)

      IdNaperian : Naperian Id
      Log {{IdNaperian}} = ⊤
      lookup {{IdNaperian}} (I x) tt = x
      tabulate {{IdNaperian}} f = I (f tt)

      IdFoldable : Foldable Id
      foldMap {{IdFoldable}} f (I a) = f a

      IdTraversable : Traversable Id
      traverse {{IdTraversable}} f (I x) = I <$> f x

      IdDimension : Dimension Id
      IdDimension = record {}

      SeqFunctor : ∀ {F G} → {{_ : Functor F}}{{ _ : Functor G}} →
                       Functor (Seq F G)
      _<$>_ {{SeqFunctor}} f (S fga) = S ((_<$>_ f) <$> fga)

      SeqApplicative : ∀ {F G} → {{_ : Applicative F}}{{ _ : Applicative G}} →
                           Applicative (Seq F G)
      pure {{SeqApplicative}} a = S (pure (pure a))
      _⊛_ {{SeqApplicative {F}{G} }} (S fgf) (S fga) = S (_⊛_ <$> fgf ⊛ fga)

      SeqFoldable : ∀ {F G} → {{_ : Foldable F}}{{ _ : Foldable G}} →
                        Foldable (Seq F G)
      foldMap {{SeqFoldable}} rec (S fga) = foldMap (foldMap rec) fga

      SeqTraversable : ∀ {F G} → {{_ : Traversable F}}{{ _ : Traversable G}} →
                           Traversable (Seq F G)
      traverse {{SeqTraversable}} f (S fga) = S <$> traverse (traverse f) fga

      SeqNaperian : ∀ {F G} → {{_ : Naperian F}}{{ _ : Naperian G}} →  Naperian (Seq F G)
      Log {{SeqNaperian {{naperianF}} {{naperianG}} }} = Log {{naperianG}} × Log {{naperianF}}
      lookup {{SeqNaperian}} (S fga) (lf , lg) = lookup (lookup fga lf) lg
      tabulate {{SeqNaperian {{naperianF}}{{naperianG}}}} f = S (tabulate (λ lf → tabulate (λ lg → f (lf , lg))))

      SeqDimension : ∀ {F G} → {{ _ : Dimension F}}{{ _ : Dimension G}} →
                         Dimension (Seq F G)
      SeqDimension = record {}

An hyper-matrix is essentially a list of functors::

    hyper : Set₁
    hyper = List (Set → Set)

which is interpreted as-is in the monoid of endofunctor on ``Set``::

    Hyper : hyper → Set → Set
    Hyper [] A = Id A
    Hyper (F ∷ Fs) A = Seq F (Hyper Fs) A

that is (but this would not play nice with unification):

.. code-block:: agda

    Hyper : hyper → Set → Set
    Hyper Fs A = foldMap {{_}}{{FunctorMonoid}} id Fs A
      where FunctorMonoid : Monoid (Set → Set)
            mempty {{FunctorMonoid}} = Id
            _<>_ {{FunctorMonoid}} = Seq

..
  ::
    module Example-hyper where

``Hyper`` thus provides a uniform way to type high-dimension
matrices::

      v123 : Hyper (vec 3 ∷ []) ℕ
      v123 = S (I (1 ∷ 2 ∷ 3 ∷ []))

      v456 : Hyper (vec 3 ∷ []) ℕ
      v456 = S (I (4 ∷ 5 ∷ 6 ∷ []))

      v123-456-789 : Hyper (vec 3 ∷ vec 3 ∷ []) ℕ
      v123-456-789 = S (S (I ((1 ∷ 2 ∷ 3 ∷ []) ∷
                              (4 ∷ 5 ∷ 6 ∷ []) ∷
                              (7 ∷ 8 ∷ 9 ∷ []) ∷ [])))

      v12-45-78 : Hyper (vec 2 ∷ vec 3 ∷ []) ℕ
      v12-45-78 = S (S (I ((1 ∷ 2 ∷ []) ∷
                           (4 ∷ 5 ∷ []) ∷
                           (7 ∷ 8 ∷ []) ∷ [])))

      m1234 : Hyper (vec 2 ∷ vec 2 ∷ []) ℕ
      m1234 = S (S (I (((1 ∷ 2 ∷ []) ∷
                       ((3 ∷ 4 ∷ []) ∷ [])))))

      m5678 : Hyper (vec 2 ∷ vec 2 ∷ []) ℕ
      m5678 = S (S (I (((5 ∷ 6 ∷ []) ∷
                       ((7 ∷ 8 ∷ []) ∷ [])))))

      v1234-5678 : Hyper (vec 2 ∷ vec 2 ∷ vec 2 ∷ []) ℕ
      v1234-5678 = S (S (S (I (((1 ∷ 2 ∷ []) ∷
                               ((3 ∷ 4 ∷ []) ∷ [])) ∷
                              (((5 ∷ 6 ∷ []) ∷
                               ((7 ∷ 8 ∷ []) ∷ [])) ∷ [])))))

      v123-456 : Hyper (vec 3 ∷ vec 2 ∷ []) ℕ
      v123-456 = S (S (I ((1 ∷ 2 ∷ 3 ∷ []) ∷
                         ((4 ∷ 5 ∷ 6 ∷ []) ∷ []))))


While we can try to *inhabit* an hyper-matrix for **any** list of
functors, we will only be able to *compute* with those when each of
these functors are Dimensions::

    Shapely : List (Set → Set) → Set₁
    Shapely [] = ⊤
    Shapely (F ∷ Fs) = Dimension F × Shapely Fs

.. XXX: guide the unifier to  automatically proof-search witnesses of ``Shapely``
  ::
    instance
      ShapelyNil : Shapely []
      ShapelyNil = tt

      ShapelyCons : ∀ {F Fs} → {{_ : Dimension F}}{{ _ : Shapely Fs}} → Shapely (F ∷ Fs)
      ShapelyCons {{dimF}} {{shapeFs}} = dimF , shapeFs

As a result, a shapely list of functors is itself a dimension.

.. BEGIN HIDE
  ::
    module Exercise-instances where
.. END HIDE

.. BEGIN BLOCK

**Exercise (difficulty: 3)** Show that a shapely hyper-matrix has a dimension::

      HyperFunctor : ∀ {Fs} → Shapely Fs → Functor (Hyper Fs)
      HyperFunctor shapes = {!!}

      HyperApplicative : ∀ {Fs} → Shapely Fs → Applicative (Hyper Fs)
      HyperApplicative shapes = {!!}

      HyperNaperian : ∀ {Fs} → Shapely Fs → Naperian (Hyper Fs)
      HyperNaperian shapes = {!!}

      HyperFoldable : ∀ {Fs} → Shapely Fs → Foldable (Hyper Fs)
      HyperFoldable shapes = {!!}

      HyperTraversable : ∀ {Fs} → Shapely Fs → Traversable (Hyper Fs)
      HyperTraversable shapes = {!!}

      HyperDimension : ∀ {Fs} → Shapely Fs → Dimension (Hyper Fs)
      HyperDimension shapes = {!!}

.. END BLOCK

.. BEGIN HIDE
  ::
    module Solution-instances where

      HyperThing : ∀ {Fs} → Shapely Fs → (Thing : (Set → Set) → Set₁) →
                    {{ _ : Thing Id}} →
                    {{ _ : ∀ {F G} → {{_ : Thing F}}{{ _ : Thing G}} → Thing (Seq F G)}} →
                    (∀ {F} → Dimension F → Thing F) → Thing (Hyper Fs)
      HyperThing {[]} tt Thing {{pscalar}} pdim = pscalar
      HyperThing {F ∷ Fs} (dimF , shapeFs) Thing {{pscalar}}{{pcomp}} pdim =
                let instance recP : Thing (Hyper Fs)
                             recP = HyperThing {Fs} shapeFs Thing {{pscalar}} {{pcomp}} pdim
                             f : Thing F
                             f = pdim dimF
                in pcomp

      HyperFunctor : ∀ {Fs} → Shapely Fs → Functor (Hyper Fs)
      HyperFunctor shapes = HyperThing shapes Functor
                                      (Applicative.super ∘ Dimension.super₁)

      HyperApplicative : ∀ {Fs} → Shapely Fs → Applicative (Hyper Fs)
      HyperApplicative shapes = HyperThing shapes Applicative
                                          (Dimension.super₁)

      HyperNaperian : ∀ {Fs} → Shapely Fs → Naperian (Hyper Fs)
      HyperNaperian shapes = HyperThing shapes Naperian
                                       Dimension.super₂

      HyperFoldable : ∀ {Fs} → Shapely Fs → Foldable (Hyper Fs)
      HyperFoldable shapes = HyperThing shapes Foldable
                                       (Traversable.super ∘ Dimension.super₃)

      HyperTraversable : ∀ {Fs} → Shapely Fs → Traversable (Hyper Fs)
      HyperTraversable shapes = HyperThing shapes Traversable
                                          Dimension.super₃

      HyperDimension : ∀ {Fs} → Shapely Fs → Dimension (Hyper Fs)
      HyperDimension shapes = HyperThing shapes Dimension id

    open Solution-instances

.. END HIDE

As a result, we can define::

    square : ∀ {T} → {{_ : Traversable T}} → T ℕ → T ℕ
    square x = (λ x → x * x) <$> x

and seamlessly apply it to any hyper-matrix.

We can also define the generalized running sum::

    sums : ∀ {F Fs}
             {{_ : Shapely Fs}}{{_ : Dimension F}} →
             Hyper (F ∷ Fs) ℕ → Hyper (F ∷ Fs) ℕ
    sums {{shapeFs}} (S xs) = S (sumsAll <$>H xs)
        where open Functor (HyperFunctor shapeFs) renaming (_<$>_ to _<$>H_)

and apply it to any matrix of dimension at least ``F``.

..
  ::
    module Example-dimension where
        open  Example-hyper

        example1 : square (I 3) ≡ I 9
        example1 = refl

        example2 : square v123 ≡ S (I (1 ∷ 4 ∷ 9 ∷ []))
        example2 = refl


        example3 : square v123-456-789
                   ≡ S (S (I (( 1 ∷  4 ∷  9 ∷ []) ∷
                              (16 ∷ 25 ∷ 36 ∷ []) ∷
                              (49 ∷ 64 ∷ 81 ∷ []) ∷ [])))
        example3 = refl

        example4 : square v12-45-78
                   ≡ S (S (I ((1  ∷  4 ∷ []) ∷
                              (16 ∷ 25 ∷ []) ∷
                              (49 ∷ 64 ∷ []) ∷ [])))
        example4 = refl


        example5 : square v1234-5678
                   ≡ S (S (S (I (((1  ∷  4 ∷ []) ∷
                                 ((9  ∷ 16 ∷ []) ∷ [])) ∷
                               (((25 ∷ 36 ∷ []) ∷
                                ((49 ∷ 64 ∷ []) ∷ [])) ∷ [])))))
        example5 = refl

        example6 : (_+_ <$> v123 ⊛ v456)
                   ≡ S (I (5 ∷ 7 ∷ 9 ∷ []))
        example6 = refl

        example7 : (_+_ <$> m1234 ⊛ m5678)
                   ≡ S (S (I (( 6 ∷  8 ∷ []) ∷
                             ((10 ∷ 12 ∷ []) ∷ []))))
        example7 = refl

        example10 : sums v123
                      ≡ S (I (1 ∷ 3 ∷ 6 ∷ []))
        example10 = refl

        example11 : sums v123-456
                      ≡ S (S (I ((1 ∷ 3 ∷ 6 ∷ []) ∷
                                 (4 ∷ 9 ∷ 15 ∷ []) ∷ [])))
        example11 = refl


We can also iterate over all "rows" of an hyper-matrix, bringing the
dimension down by ``F``::

    reduceBy : ∀ {F Fs A M} →
                 {{_ : Shapely Fs}}{{_ : Monoid M}}{{_ : Dimension F}} →
                 (A → M) → Hyper (F ∷ Fs) A → Hyper Fs M
    reduceBy {{shapeFs}} f (S fga) = (foldMap f) <$>H fga
        where open Functor (HyperFunctor shapeFs) renaming (_<$>_ to _<$>H_)

    sum : ∀ {F Fs} →
            {{_ : Shapely Fs}}{{_ : Dimension F}} →
            Hyper (F ∷ Fs) ℕ → Hyper Fs ℕ
    sum = reduceBy id

..
  ::
    module Example-reduceBy where
        open Example-hyper

        example8 : sum v123 ≡ I 6
        example8 = refl


        example9 : sum v123-456 ≡ S (I (6 ∷ 15 ∷ []))
        example9 = refl

And, finally, we can generalize ``transpose`` to any hyper-matrix and
obtain the reranking operator::

    transpose' : ∀ {A F G Fs} →
                 {{_ : Shapely Fs}}{{_ : Dimension F}}{{_ : Dimension G}} →
                 Hyper (F ∷ G ∷ Fs) A → Hyper (G ∷ F ∷ Fs) A
    transpose' {{shapeFs}} (S (S x)) = S (S (transpose <$>H x))
        where open Functor (HyperFunctor shapeFs) renaming (_<$>_ to _<$>H_)

    _`¹_ : ∀ {A F₁ F₂ Fs G₁ G₂ Gs} →
             {{_ : Shapely Fs}}{{_ : Shapely Gs}} →
             {{_ : Dimension F₁}}{{_ : Dimension F₂}}
             {{_ : Dimension G₁}}{{_ : Dimension G₂}} →
             (Hyper (F₁ ∷ F₂ ∷ Fs) A → Hyper (G₁ ∷ G₂ ∷ Gs) A) →
             Hyper (F₂ ∷ F₁ ∷ Fs) A → Hyper (G₂ ∷ G₁ ∷ Gs) A
    f `¹ m = transpose' (f (transpose' m))

..
  ::

    module test where
        open  Example-hyper

        example12a : transpose' v123-456
                     ≡ S (S (I ((1 ∷ (4 ∷ [])) ∷
                               ((2 ∷ (5 ∷ [])) ∷
                                (3 ∷ (6 ∷ [])) ∷ []))))
        example12a = refl

        example12b : transpose' v1234-5678
                     ≡ S (S (S (I (((1 ∷ (3 ∷ [])) ∷
                                   ((2 ∷ (4 ∷ [])) ∷ [])) ∷
                                  (((5 ∷ (7 ∷ [])) ∷
                                   ((6 ∷ (8 ∷ [])) ∷ [])) ∷ [])))))
        example12b = refl

        example12 : sums `¹ v123-456 ≡ S (S (I ((1 ∷ 2 ∷ 3 ∷ []) ∷
                                                (5 ∷ 7 ∷ 9 ∷ []) ∷ [])))
        example12 = refl

.. BEGIN HIDE
.. TODO: need alignment to automatically  lift the inner value
      example12 : sum `1 v123-456 ≡ S (I (5 ∷ 7 ∷ 9 ∷ []))
      example12 = refl
.. END HIDE

At this stage, we are merely touching upon what Gibbons' talks about
in `APLicative Programming Naperian Functors`_. For instance, when
applying a binary operation, we (that is, applicative) currently ask
for the two argument matrices to be exactly the same. J, on the other
hand, would automatically lift values to match up dimensions. For
example, we would like to able to sum a scalar to a matrix:

.. code-block:: agda

    I 3 + S (I (4 ∷ 5 ∷ 6 ∷ []))
    ≡ S (I (3 ∷ 3 ∷ 3 ∷ [])) + S (I (4 ∷ 5 ∷ 6 ∷ []))
    ≡ S (I (7 ∷ 8 ∷ 9 ∷ []))

    S (I (1 ∷ 2 ∷ 3 ∷ [])) + S (S (I ((4 ∷ 5 ∷ 6 ∷ []) ∷
                                      (7 ∷ 8 ∷ 9 ∷ []) ∷ [])))
    ≡ S (S (I (1 ∷ 2 ∷ 3 ∷ []) ∷
              (1 ∷ 2 ∷ 3 ∷ []) ∷ []))
    + S (S (I ((4 ∷ 5 ∷ 6 ∷ []) ∷
               (7 ∷ 8 ∷ 9 ∷ []) ∷ [])))
    ≡ S (S (I ((5 ∷ 7 ∷ 9 ∷ []) ∷
               (8 ∷ 10 ∷ 12 ∷ []) ∷ [])))


However, this is also at this point that the extensional style starts
to break. To feel that pain, try to translate Gibbons' ``Max``
type-class. As we will see in the last lecture, manipulating an object
of type ``List (Set → Set)`` was a red-herring, it is already quite
surprising that we came this far.


************************************************
Intensional Generic Programming
************************************************
..
  ::
  module Intensional where
    open import Function

    open import Data.Unit
    open import Data.Bool
    open import Data.Product hiding (map)
    open import Data.Sum hiding (map)
    open import Data.Nat
    open import Data.Fin renaming (suc to sucF) hiding (fold)
    open import Data.Vec hiding (map)

    open import Induction

    open import Level renaming (zero to 0ℓ) hiding (suc)

    open import Relation.Binary.PropositionalEquality 
      hiding (subst ; Extensionality)
    open import Axiom.Extensionality.Propositional

    infixr 50 _`×_ _`×'_
    infixr 30 _`+_ _`+'_

In this second part, we apply a type-theoretic concept, a *universe*,
to manipulate some structure of interest. Here, we shall look at
inductive types.

Universes were born around the same time as type theory: they were
introduced by Martin-Löf in `Intuitionistic Type Theory`_. Their
application to generic programming came later with `Universes for
Generic Programs and Proofs in Dependent Type Theory`_.

Following `The Gentle Art of Levitation`_, we shall:
  - code a universe for describing inductive types
  - show that the resulting types admit an induction principle
  - implement a generic datatype construction: the free monad
  - reflect the universe in itself

Vision: "Whereof one cannot speak, thereof one must be silent."

--------------------------------
Descriptions
--------------------------------

In lecture 1, we asked whether we could give a "grammar" for the
functors used to encode the signatures of algebraic effects. As
mentioned then, signatures are essentially the same as datatype
definitions. We shall thus decompose our model of inductive types in,
first, the underlying functor encoding a signature and, second, a
fixpoint of signatures.

The grammar can be understood as taking the closure of all the
operations offering/preserving a functorial structure. Namely, the
identity and constant functors are functors. Then, the pointwise
product of functors is itself a functor while the indexed sum and
product of functors is itself a functor. The *code* of the universe
translates this intuition by describing the *smallest* set closed
under those operations::

    data Desc : Set₁ where
      `X   : Desc
      `K   : Set → Desc
      _`×_ : (D₁ D₂ : Desc) → Desc
      _`+_ : (D₁ D₂ : Desc) → Desc
      `Σ   : (S : Set)(D : S → Desc) → Desc
      `Π   : (S : Set)(D : S → Desc) → Desc

The *interpretation* gives the desired semantics::

    ⟦_⟧ : Desc → Set → Set
    ⟦ `X ⟧ X       = X
    ⟦ `K S ⟧ X     = S
    ⟦ D₁ `× D₂ ⟧ X = ⟦ D₁ ⟧ X × ⟦ D₂ ⟧ X
    ⟦ D₁ `+ D₂ ⟧ X = ⟦ D₁ ⟧ X ⊎ ⟦ D₂ ⟧ X
    ⟦ `Σ S T ⟧ X   = Σ[ s ∈ S ] ⟦ T s ⟧ X
    ⟦ `Π S T ⟧ X   = (s : S) → ⟦ T s ⟧ X

..
  ::
    module Exercise-compose where

**Exercise (difficulty: 2)** Note that we would expect the composition
of two functors to be a functor. Implement composition of descriptions::

      _∘D_ : Desc → Desc → Desc
      D₁ ∘D D₂ = {!!}

      correctness-∘ : ∀ {X D₁ D₂} → ⟦ D₁ ∘D D₂ ⟧ X ≡ ⟦ D₁ ⟧ (⟦ D₂ ⟧ X)
      correctness-∘ = {!!}
        where postulate ext : Extensionality Level.zero Level.zero

.. BEGIN HIDE
  ::
    module Exercise-map where
.. END HIDE

.. BEGIN BLOCK

**Exercise (difficulty: 2)** We claim that our description interpret
to functors. We ought to be able to equip *any* description with a
functorial action::

      map : ∀ {X Y} → (D : Desc)(f : X → Y)(v : ⟦ D ⟧ X) → ⟦ D ⟧ Y
      map = {!!}

and (generically) prove the functor laws::

      proof-map-id : ∀ {X} → (D : Desc)(v : ⟦ D ⟧ X) → map D id v ≡ v
      proof-map-id = {!!}
        where postulate ext : Extensionality Level.zero Level.zero

      proof-map-compos : ∀ {X Y Z}{f : X → Y}{g : Y → Z} →
                         (D : Desc)(v : ⟦ D ⟧ X) →
                         map D (λ x → g (f x)) v ≡ map D g (map D f v)
      proof-map-compos = {!!}
        where postulate ext : Extensionality Level.zero Level.zero

.. END BLOCK

.. BEGIN HIDE
  ::

    map : ∀ {X Y} → (D : Desc)(f : X → Y)(v : ⟦ D ⟧ X) → ⟦ D ⟧ Y
    map `X f x = f x
    map (`K S) f s = s
    map (D₁ `× D₂) f (xs₁ , xs₂) = map D₁ f xs₁ , map D₂ f xs₂
    map (D₁ `+ D₂) f (inj₁ xs₁) = inj₁ (map D₁ f xs₁)
    map (D₁ `+ D₂) f (inj₂ xs₂) = inj₂ (map D₂ f xs₂)
    map (`Σ S T) f (a , xs) = a , map (T a) f xs
    map (`Π S T) f k = λ x → map (T x) f (k x)

    proof-map-id : ∀ {X} → (D : Desc)(v : ⟦ D ⟧ X) → map D id v ≡ v
    proof-map-id `X v = refl
    proof-map-id (`K S) v = refl
    proof-map-id (D₁ `× D₂) (xs₁ , xs₂)
      rewrite proof-map-id D₁ xs₁
           |  proof-map-id D₂ xs₂  = refl
    proof-map-id (D₁ `+ D₂) (inj₁ xs₁)
      rewrite proof-map-id D₁ xs₁ = refl
    proof-map-id (D₁ `+ D₂) (inj₂ xs₂)
      rewrite proof-map-id D₂ xs₂ = refl
    proof-map-id (`Σ S T) (a , b)
      rewrite proof-map-id (T a) b = refl
    proof-map-id (`Π S T) k = ext (λ a → proof-map-id (T a) (k a))
      where postulate ext : Extensionality Level.zero Level.zero

    proof-map-compos : ∀ {X Y Z}{f : X → Y}{g : Y → Z} →
                       (D : Desc)(v : ⟦ D ⟧ X) →
                       map D (λ x → g (f x)) v ≡ map D g (map D f v)
    proof-map-compos `X v = refl
    proof-map-compos (`K K) v = refl
    proof-map-compos {f = f}{g = g} (D₁ `× D₂) (v₁ , v₂)
      rewrite proof-map-compos {f = f}{g} D₁ v₁
            | proof-map-compos {f = f}{g} D₂ v₂ = refl
    proof-map-compos {f = f}{g = g} (D₁ `+ D₂) (inj₁ v₁)
      rewrite proof-map-compos {f = f}{g} D₁ v₁ = refl
    proof-map-compos {f = f}{g = g} (D₁ `+ D₂) (inj₂ v₂)
      rewrite proof-map-compos {f = f}{g} D₂ v₂ = refl
    proof-map-compos {f = f}{g} (`Σ S T) (a , b)
      rewrite proof-map-compos {f = f}{g} (T a) b = refl
    proof-map-compos (`Π S T) k = ext (λ a → proof-map-compos (T a) (k a))
      where postulate ext : Extensionality Level.zero Level.zero

.. END HIDE

--------------------------------
Fixpoint
--------------------------------

The functors captured by our grammar have also the property of being
"strictly-positive". We are therefore allowed to take their fixpoint::

    data μ (D : Desc) : Set where
      ⟨_⟩ : ⟦ D ⟧ (μ D) → μ D

Over this (standard) inductive type, we can implement the traditional
``fold`` operator::

    {-# TERMINATING #-}
    fold : (D : Desc){T : Set} →
           (⟦ D ⟧ T → T) → μ D → T
    fold D α ⟨ x ⟩ = α (map D (fold D α) x)

**Exercise (difficulty: 3)** Convince the termination checker that
``fold`` is indeed terminating. Hint: manually specialize the
partially applied function ``map D (fold D α)`` in a definition
mutually-recursive with ``fold``.

..
  ::
    module Example-Nat where

**Example: natural numbers**:: Natural numbers are thus described as
follows::

      data NatTag : Set where
        `Ze `Su : NatTag

      NatD : Desc
      NatD = `Σ NatTag (λ { `Ze → `K ⊤
                            ; `Su → `X })

      Nat : Set
      Nat = μ NatD

      pattern ze = ⟨ `Ze , tt ⟩
      pattern su n = ⟨ `Su , n ⟩

Using the ``fold``, we can implement addition over these numbers::

      plus : Nat → Nat → Nat
      plus x = fold NatD (λ { (`Ze , tt) → x
                            ; (`Su , rec) → su rec })

      test : plus (su (su ze)) (su (su (su ze)))
             ≡ su (su (su (su (su ze))))
      test = refl

..
  ::
    module Example-List where

**Example: lists**:: Similarly, here are lists::

      data ListTag : Set where
        `Nil `Cons : ListTag

      ListD : Set → Desc
      ListD X = `Σ ListTag (λ { `Nil → `K ⊤
                              ; CCons → `Σ X λ _ → `X })

      List : Set → Set
      List X = μ (ListD X)

      nil : ∀ {X} → List X
      nil = ⟨ `Nil , tt ⟩

      cons : ∀ {X} → X → List X → List X
      cons x t = ⟨ `Cons , x , t ⟩

**Exercise (difficulty: 1)**:: Implement binary trees using descriptions.

.. BEGIN HIDE
  ::
    module Example-Tree where

    data TreeConst : Set where
      `Leaf : TreeConst
      `Node : TreeConst

    TreeD : Set → Desc
    TreeD X = `Σ TreeConst (λ { `Leaf → `K ⊤
                              ; `Node → `K X `× `X `× `X })

    Tree : Set → Set
    Tree X = μ (TreeD X)

    leaf : {X : Set} → Tree X
    leaf = ⟨ `Leaf , tt ⟩

    node : {X : Set} → X → Tree X → Tree X → Tree X
    node x l r = ⟨ `Node , x , l , r ⟩
.. END HIDE

--------------------------------
Induction
--------------------------------

Introducing a ``fold`` to enable recursion over ``μ D`` is
simple(-type)-minded. Being in type theory, we actually want a
recursion principle. We obtain it by instantiating the usual framework
for induction::


    All : ∀{X} → (D : Desc)(P : X → Set) → ⟦ D ⟧ X → Set
    All `X         P x         = P x
    All (`K Z)     P x         = ⊤
    All (D₁ `× D₂) P (d₁ , d₂) = All D₁ P d₁ × All D₂ P d₂
    All (D₁ `+ D₂) P (inj₁ d₁) = All D₁ P d₁
    All (D₁ `+ D₂) P (inj₂ d₂) = All D₂ P d₂
    All (`Σ S T)   P (s , xs)  = All (T s) P xs
    All (`Π S T)   P k         = ∀ s → All (T s) P (k s)

    Rec-μ : ∀ D → RecStruct (μ D) _ _
    Rec-μ D P ⟨ xs ⟩ = All D P xs

    all : ∀ {X P} → (D : Desc) → (rec : (x : X) → P x)(x : ⟦ D ⟧ X) → All D P x
    all `X rec x = rec x
    all (`K S) rec z = tt
    all (D₁ `× D₂) rec (d₁ , d₂) = all D₁ rec d₁ , all D₂ rec d₂
    all (D₁ `+ D₂) rec (inj₁ d₁) = all D₁ rec d₁
    all (D₁ `+ D₂) rec (inj₂ d₂) = all D₂ rec d₂
    all (`Σ S T) rec (s , xs) = all (T s) rec xs
    all (`Π S T) rec k = λ s → all (T s) rec (k s)

    {-# TERMINATING #-}
    rec-μ-builder : ∀{D} → RecursorBuilder (Rec-μ D)
    rec-μ-builder {D} P rec ⟨ xs ⟩ = all D (λ x → rec x (rec-μ-builder P rec x)) xs

    induction : (D : Desc)(P : μ D → Set) →
                ((x : ⟦ D ⟧ (μ D)) → All D P x → P ⟨ x ⟩) →
                (x : μ D) → P x
    induction D P ms xs = build rec-μ-builder P (λ { ⟨ x ⟩ x₁ → ms x x₁ }) xs

**Exercise (difficulty: 3)**:: Convince the termination checker that
induction is terminating, either by implementing ``rec-μ-builder`` in
an obviously terminating manner, or by writing ``induction`` directly
in terms of ``all``.

.. BEGIN HIDE
  ::
    module Induction-Terminating where
      module Elim (D : Desc)
                  (P : μ D → Set)
                  (ms : (x : ⟦ D ⟧ (μ D)) →
                    All D P x → P ⟨ x ⟩) where


        ind : (x : μ D) → P x
        hyps : (D' : Desc)(xs : ⟦ D' ⟧ (μ D)) → All D' P xs

        ind ⟨ xs ⟩ =  ms xs (hyps D xs)

        hyps `X x = ind x
        hyps (`K Z) z = tt
        hyps (D `× D') (d , d') = hyps D d , hyps D' d'
        hyps (D `+ D') (inj₁ d) = hyps D d
        hyps (D `+ D') (inj₂ d) = hyps D' d
        hyps (`Σ S T) (a , b) = hyps (T a) b
        hyps (`Π S T) f = λ s → hyps (T s) (f s)

      ind : (D : Desc)(P : μ D → Set) →
            ( (x : ⟦ D ⟧ (μ D)) → All D P x → P ⟨ x ⟩) →
            (v : μ D) → P v
      ind D P ms x = Elim.ind D P ms x

.. END HIDE

..
  ::
    module Example-Plus where
      open Example-Nat hiding (plus)

Using induction, we can write any dependently-typed programs or proofs
over described inductive types: they have become (mostly, modulo the
fact that we have to go trough the fold/induction principle, which is
not idiomatic Agda) first-class objects.

But we can also take this as a opportunity to understand what we did
earlier, in a simply-typed setting::

      plus[_∶_] : Nat → Nat → Set
      plus[ m ∶ n ] = Nat

      plus : (m n : Nat) → plus[ m ∶ n ]
      plus m = induction NatD (λ n → plus[ m ∶ n ])
               (λ { (`Ze , tt) tt → m
                  ; (`Su , n) rec → su rec } )

--------------------------------
Generic free monad
--------------------------------

Thinking about it, we now have first-class inductive types (modulo
encoding, again). This means that we can craft new datatypes from
existing datatypes. We exercise this possibility by implementing a
generic free monad construction.

In its most brutal form, the free monad construction consists in
grafting an extra constructor containing a value of a provided type,
the elements of the earlier signature being integrated as operations
``op``::

    _*D_ : Desc → Set → Desc
    D *D X = `Σ Bool λ { true → `K X ; false → D }

    Free : Desc → Set → Set
    Free D X = μ (D *D X)

    return : ∀ {D X} → X → Free D X
    return x = ⟨ true , x ⟩

    op : ∀ {D X} → ⟦ D ⟧ (Free D X) → Free D X
    op xs = ⟨ false , xs ⟩

Doing so, the resulting description has a monadic structure, which we
can realize generically::

    subst[_∶_∶_] : ∀ {X Y} → (D : Desc) → Free D X → (X → Free D Y) → Set
    subst[_∶_∶_] {X}{Y} D _ _ = Free D Y

    subst : ∀ {X Y} → (D : Desc) →
            Free D X → (X → Free D Y) → Free D Y
    subst {X}{Y} D mx k =
      induction (D *D X) (λ mx₁ → subst[ D ∶ mx ∶ k ])
        (λ { (true , x) tt → k x
           ; (false , xs) as → ⟨ false , help D xs as ⟩ })
        mx
      where help : ∀ {X Y} D → (ds : ⟦ D ⟧ X) → All D (λ _ → Y) ds → ⟦ D ⟧ Y
            help `X ds as = as
            help (`K x) ds as = ds
            help (D₁ `× D₂) (ds₁ , ds₂) (as₁ , as₂) = help D₁ ds₁ as₁ , help D₂ ds₂ as₂
            help (D₁ `+ D₂) (inj₁ ds₁) as₁ = inj₁ (help D₁ ds₁ as₁)
            help (D₁ `+ D₂) (inj₂ ds₂) as₂ = inj₂ (help D₂ ds₂ as₂)
            help (`Σ S D₁) (s , ds) as = s , help (D₁ s) ds as
            help (`Π S D₁) ds as = λ s → help (D₁ s) (ds s) (as s)

..
  ::
    module Example-Free (A : Set)(B : A → Set) where

      CallD : Desc
      CallD = `Σ A λ a → `Π (B a) λ _ → `X

      RecMon : Set → Set
      RecMon = Free CallD

      call : ∀ {X} → (a : A)(rec : B a → RecMon X) → RecMon X
      call a rec = op (a , rec)

      substR : ∀ {X Y} → RecMon X → (X → RecMon Y) → RecMon Y
      substR = subst CallD

      test : ∀ {a₁ a₂ a₃} →
           (substR (call a₁ return)
                   (λ ba₁ → call a₂ (λ ba₂ → call a₃ return)))
           ≡ (call a₁ λ ba₁ → call a₂ (λ ba₂ → call a₃ return))
      test = refl

**Exercise (difficulty: 4)**:: Prove the monad laws.

.. BEGIN HIDE
.. TODO: add Zipper
.. END HIDE

--------------------------------
Bootstrap
--------------------------------

So far, we have been doing "generic programming" on the one hand
(computing over Desc) and "programming" on the other hand (computing
over anything else, including inhabitants of ``μ D``, for ``D :
Desc``). This may have gone unnoticed (probably because doing anything
with these encodings is blindly painful) but, in a standalone
language, this would mean having two "programming languages" in the
programming language, one for generic programming and the other for
programming.

There may be two solutions to this problem: either we (pragmatically)
make the generic programming language to borrow as much as possible
from the programming language, or we (brutally) collapse the
programming language into the generic programming language. For
obvious reasons (having to do with full employment), we chose the
latter. The key idea consists in noticing that ``Desc`` itself is an
inductive type. As such, it can be described::

    DescD : Desc
    DescD =  `K ⊤
          `+ `K Set
          `+ (`X `× `X)
          `+ (`X `× `X)
          `+ (`Σ Set λ S → `Π S (λ _ → `X))
          `+ (`Σ Set λ S → `Π S (λ _ → `X))

    Desc' : Set₁
    Desc' = μ DescD

    `X' : Desc'
    `X' = ⟨ inj₁ tt ⟩

    `K' : Set → Desc'
    `K' S = ⟨ inj₂ (inj₁ S) ⟩

    _`×'_ : Desc' → Desc' → Desc'
    D₁ `×' D₂ = ⟨ inj₂ (inj₂ (inj₁ (D₁ , D₂) )) ⟩

    _`+'_ : Desc' → Desc' → Desc'
    D₁ `+' D₂ = ⟨ inj₂ (inj₂ (inj₂ (inj₁ (D₁ , D₂) ))) ⟩

    `Σ' : (S : Set)(T : S → Desc') → Desc'
    `Σ' S T = ⟨ inj₂ (inj₂ (inj₂ (inj₂ (inj₁ (S , T))))) ⟩

    `Π' : (S : Set)(T : S → Desc') → Desc'
    `Π' S T = ⟨ inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (S , T))))) ⟩

Note that, aside from the constructor ``⟨_⟩`` of ``μ``, the
constructor of ``Desc'`` only depend on constructors pre-existing in
the type theory (unit, cartesian product, injections into sum): in an
implementation, we can simply take these codes as the *definition*. We
then only need to implement the fixpoint operator and its induction
principle: this provides us with the ability to compute over inductive
types on one hand (programming) but also, in particular, to compute
over Desc since it is described in itself (generic programming).

************************************************
Conclusion
************************************************

We have seen two complementary approaches to generic programming. In
both cases, we have exploited (type-class) or built (universe) a
mechanism that allows us to reify a subset of the programming language
in itself.

Whichever mechanism we chose depends highly on the functionalities
offered by the programming language. For instance, Coq type-classes
are extremely powerful whereas its strict-positive criteria is
extremely obtuse: as a result, the extensional approach works well
whereas the intensional one is nearly impossible.

**Exercises (difficulty: open ended):**
  - Implement Section 6 to 8 of Gibbons' paper (in Coq, probably)
  - Extend ``Desc`` to encode inductive families
  - Extend ``Desc`` to support internal fixpoints (such as ``data Rose A = rose : List (Rose A) → Rose A``)

**Going further, extensionally:**
  - Other examples of `functor-oriented programming <https://news.ycombinator.com/item?id=15440108>`_: `unification-fd <https://github.com/wrengr/unification-fd>`_, `lenses <https://hackage.haskell.org/package/lens>`_
  - Structures in idiomatic Agda: `Agda Prelude`_





.. References (papers):
.. _`APLicative Programming Naperian Functors`: https://doi.org/10.1007/978-3-662-54434-1_21
.. _`An agda formalisation of the transitive closure of block matrices`: https://doi.org/10.1145/2976022.2976025
.. _`Intuitionistic Type Theory`: https://www.worldcat.org/search?q=isbn%3A8870881059
.. _`Universes for Generic Programs and Proofs in Dependent Type Theory`: http://www.cse.chalmers.se/~patrikj/poly/gendt/
.. _`The Gentle Art of Levitation`: https://doi.org/10.1145/1863543.1863547

.. References (online):
.. _`Typeclassopedia`: https://wiki.haskell.org/Typeclassopedia
.. _`representable functor`: https://ncatlab.org/nlab/show/representable+functor
.. _`Agda prelude`: https://github.com/UlfNorell/agda-prelude

.. Local Variables:
.. mode: agda2
.. End:
