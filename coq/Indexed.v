(** *Indexed functional programming *)

Require Ascii String.
From Equations Require Import Equations.
Require FunctionalExtensionality.
Require Import MPRICoq.Monad.

(** **Typing `sprintf` *)
Module sprintf.
  Import Ascii String.
  Open Scope list_scope.
  Open Scope char_scope.
  Open Scope string_scope.

  Inductive format : Type :=
  | digitf (k : format) : format
  | stringf (k : format) : format
  | symbf (c : ascii)(k : format) : format
  | endf : format.

  Fixpoint parse (s : string) : format :=
    match s with
    | String "%" (String "d" tl) => digitf (parse tl)
    | String "%" (String "s" tl) => stringf (parse tl)
    | String "%" (String c tl) | String c tl => symbf c (parse tl)
    | EmptyString => endf
    end.

  Fixpoint format_type (fmt : format) : Type :=
    match fmt with
    | digitf k => nat -> (format_type k)
    | stringf k => string -> (format_type k)
    | symbf c k => (format_type k)
    | endf => string
    end.
  Notation "⟦ fmt ⟧" := (format_type fmt).

  Definition parse_and_type (s : string) :=
    ⟦ (parse s) ⟧.
  Notation "⟦p s ⟧" := (parse_and_type s).

  Fixpoint show_nat (n : nat) : string :=
    match n with
    | O => "O"
    | S n => "S(" ++ (show_nat n) ++ ")"
    end.

  Fixpoint eval (fmt : format) (acc : string) : ⟦ fmt ⟧ :=
    match fmt return ⟦ fmt ⟧ with
    | digitf k => fun n => eval k (acc ++ (show_nat n))
    | stringf k => fun s => eval k (acc ++ s)
    | symbf c k => eval k (acc ++ String c "")
    | endf => acc
    end.

  Definition sprintf (fmt : string) : ⟦p fmt ⟧ :=
    eval (parse fmt) "".

  Example test : sprintf "test %%d & %%s: %d & %s" 2 "hello world!"
                 = "test %d & %s: S(S(O)) & hello world!".
  Proof. reflexivity. Qed.
End sprintf.

(** **Computing normal forms of λ-terms *)
Module NormalForms.

  (** ***Types and terms *)

  Inductive type : Type :=
  | unit : type
  | arrow (t1 t2 : type) : type
  | prod (t1 t2 : type) : type.
  Notation "t1 ⇒ t2" := (arrow t1 t2) (at level 30).
  Notation "t1 × t2" := (prod t1 t2) (at level 30).

  Inductive context : Type :=
  | ϵ : context
  | ext_context (Γ : context) (t : type) : context.
  Notation "Γ ▷ t" := (ext_context Γ t) (at level 40).
  Derive NoConfusion for context.

  Inductive in_env : type -> context -> Type :=
  | here {t Γ} : in_env t (Γ ▷ t)
  | there {t t' Γ} : in_env t Γ -> in_env t (Γ ▷ t').
  Notation "t ∈ Γ" := (in_env t Γ) (at level 50).
  Derive Signature for in_env.

  Reserved Notation "Γ ⊢ t" (at level 50).
  Inductive has_type : context -> type -> Type :=
  | lam {Γ s t} :
      (Γ ▷ s) ⊢ t ->
      Γ ⊢ s ⇒ t
  | var {Γ t} :
      t ∈ Γ ->
      Γ ⊢ t
  | app {Γ s t} :
      Γ ⊢ s ⇒ t -> Γ ⊢ s ->
      Γ ⊢ t
  | tt {Γ} : Γ ⊢ unit
  | pair {Γ a b} :
      Γ ⊢ a -> Γ ⊢ b ->
      Γ ⊢ a × b
  | fst {Γ a b} :
      Γ ⊢ a × b ->
      Γ ⊢ a
  | snd {Γ a b} :
      Γ ⊢ a × b ->
      Γ ⊢ b
  where "Γ ⊢ t" := (has_type Γ t).

  (** ***Interlude: substitution, structurally *)

  Module Fin.
    Inductive fin : nat -> Type :=
    | zero {n : nat} : fin (S n)
    | suc {n : nat} (i : fin n) : fin (S n).
    Derive Signature for fin.

    Fact fin_eq_suc {n} : forall (i j : fin n), suc i = suc j -> i = j.
    Proof.
      intros i j Heq.
      inversion Heq.
      apply Eqdep.EqdepTheory.inj_pair2 in H0. assumption.
    Qed.

    Reserved Notation "x ⊇ y" (at level 50).
    Inductive geq : nat -> nat -> Type :=
    | id {m} : m ⊇ m
    | weak1 {m n} : m ⊇ n -> (S m) ⊇ n
    | weak2 {m n} : m ⊇ n -> (S m) ⊇ (S n)
    where "x ⊇ y" := (geq x y).
    Derive Signature for geq.

    Equations mono_inter {m n : nat} (Hgeq : m ⊇ n) (l : fin n) : fin m :=
      { mono_inter id k := k;
        mono_inter (weak1 wk) v := suc (mono_inter wk v);
        mono_inter (weak2 wk) zero := zero;
        mono_inter (weak2 wk) (suc k) := suc (mono_inter wk k) }.
    Notation "⟦ wk ⟧" := (mono_inter wk).

    (* TODO *)
    (* Lemma lemma_valid : forall m n k l (wk : m ⊇ n), k <= l -> ⟦ wk ⟧ k <= ⟦ wk ⟧ l. *)
  End Fin.

  (** We can adapt this intentional characterization of monotone functions
      to typed embeddings *)
  Reserved Notation "x ⊇ y" (at level 50).
  Inductive geq : context -> context -> Type :=
  | id {Γ} : Γ ⊇ Γ
  | weak1 {Γ Δ t} : Δ ⊇ Γ -> Δ ▷ t ⊇ Γ
  | weak2 {Γ Δ t} : Δ ⊇ Γ -> Δ ▷ t ⊇ Γ ▷ t
  where "x ⊇ y" := (geq x y).

  Equations shift {Γ Δ T}: (Γ ⊇ Δ) -> (T ∈ Δ) -> T ∈ Γ :=
    { shift id v := v;
      shift (weak1 wk) v := there (shift wk v);
      shift (weak2 wk) here := here;
      shift (weak2 wk) (there v) := there (shift wk v) }.

  Equations rename {Γ Δ T}: (Γ ⊇ Δ) -> (Δ ⊢ T) -> Γ ⊢ T :=
    { rename wk (lam t) := lam (rename (weak2 wk) t);
      rename wk (var v) := var (shift wk v);
      rename wk (app f s) := app (rename wk f) (rename wk s);
      rename wk tt := tt;
      rename wk (pair a b) := pair (rename wk a) (rename wk b);
      rename wk (fst p) := fst (rename wk p);
      rename wk (snd p) := snd (rename wk p) }.

  (* Equations sub {Γ Δ t}: (Γ ⊢ t) -> (forall {s}, s ∈ Γ -> Δ ⊢ s) -> Δ ⊢ t := *)
  (*   { sub (lam t) ρ := lam (sub t (fun s H  with H := *)
  (*                                   { | here := var here; *)
  (*                                     | there v := rename (weak1 id) (ρ _ v) }; *)
  (*                                   (* match H in s ∈ Δ ▷ s return Δ ▷ s ⊢ s with *) *)
  (*                                   (* | here => var here *) *)
  (*                                   (* | (there v) => rename (weak1 id) (ρ _ v) *) *)
  (*                                   (* end)); *) *)
  (*     sub (var v) ρ := ρ _ v; *)
  (*     sub (app f s) ρ := app (sub f ρ) (sub s ρ); *)
  (*     sub tt ρ := tt; *)
  (*     sub (pair a b) ρ := pair (sub a ρ) (sub b ρ); *)
  (*     sub (fst p) ρ := fst (sub p ρ); *)
  (*     sub (snd p) ρ := snd (sub p ρ) }. *)

  Definition sub : forall {Γ Δ T}, (Γ ⊢ T) -> (forall {S}, S ∈ Γ -> Δ ⊢ S) -> Δ ⊢ T.
  Proof.
    fix sub 4.
    intros Γ Δ T v ρ.
    destruct v as [? ? ? v|? ? v|? ? ? f x| |? ? ? v1 v2|? ? ? p|? ? ? p].
    - (* lam *) refine (lam (sub _ _ _ v _)).
      intros x Hx. inversion Hx; subst.
      + exact (var here).
      + eapply rename; eauto.
        apply weak1. apply id.
    - (* var *) exact (ρ _ v).
    - (* app *) exact (app (sub _ _ _ f ρ) (sub _ _ _ x ρ)).
    - (* tt *) exact tt.
    - (* pair *) exact (pair (sub _ _ _ v1 ρ) (sub _ _ _ v2 ρ)).
    - (* fst *) exact (fst (sub _ _ _ p ρ)).
    - (* snd *) exact (snd (sub _ _ _ p ρ)).
  Defined.

  Definition sub1 {Γ T1 T2} (v : Γ ▷ T1 ⊢ T2) (s : Γ ⊢ T1) : Γ ⊢ T2.
  Proof.
    eapply sub; eauto.
    intros x Hx. inversion Hx; subst; clear Hx.
    - exact s.
    - exact (var H1).
  Defined.

  (** Some examples to check it computes *)
  Compute (sub1 (fst (var here)) (pair tt tt)).
  Compute (sub1 (pair (var here) (var (there here))) tt).
  Compute (sub1 (lam (var here)) tt).
  Compute (sub1 (lam (var (there here))) tt).

  (* Equations weak_comp {Δ Σ Γ} : (Δ ⊇ Σ) -> (Γ ⊇ Δ) -> Γ ⊇ Σ := *)
  (*   { weak_comp wk id := wk; *)
  (*     weak_comp wk' (weak1 wk) := weak1 (weak_comp wk' wk); *)
  (*     weak_comp id (weak2 wk) := weak2 wk; *)
  (*     weak_comp (weak1 wk') (weak2 wk) := weak1 (weak_comp wk' wk); *)
  (*     weak_comp (weak2 wk') (weak2 wk) := weak2 (weak_comp wk' wk) }. *)
  Definition weak_comp : forall {Δ Σ Γ}, (Δ ⊇ Σ) -> (Γ ⊇ Δ) -> (Γ ⊇ Σ).
  Proof.
    fix weak_comp 5.
    intros Δ Σ Γ wk1 wk2.
    inversion wk2; subst; clear wk2.
    - exact wk1.
    - apply weak1; eauto.
    - inversion wk1; subst; clear wk1.
      + apply weak2; auto.
      + apply weak1; eauto.
      + apply weak2; eauto.
  Defined.
  Notation "x ∘wk y" := (weak_comp x y) (at level 60).

  Lemma comp_right_unit : forall {Γ Δ} (wk : Γ ⊇ Δ), wk ∘wk id = wk.
  Proof. reflexivity. Qed.

  Lemma comp_left_unit : forall {Γ Δ} (wk : Γ ⊇ Δ), id ∘wk wk = wk.
  Proof.
    induction wk; simpl.
    - reflexivity.
    - unfold eq_rec_r, eq_rec, eq_rect; simpl.
      rewrite IHwk. reflexivity.
    - unfold eq_rec_r, eq_rec, eq_rect; simpl.
      reflexivity.
  Qed.

  Lemma comp_assoc : forall {Γ Δ Σ Ω} (wk3 : Γ ⊇ Δ) (wk2 : Δ ⊇ Σ) (wk1 : Σ ⊇ Ω),
      (wk1 ∘wk wk2) ∘wk wk3 = wk1 ∘wk (wk2 ∘wk wk3).
  Proof.
    fix comp_assoc 5.
    intros Γ Δ Σ Ω wk3 wk2 wk1.
    destruct wk1; simpl.
    - repeat rewrite comp_assoc. reflexivity.
    - unfold eq_rec_r, eq_rec, eq_rect; simpl.
      repeat rewrite comp_assoc. reflexivity.
    - admit.
  Admitted.

  (** **Normal forms *)
  Module Model1.

    (** We can represent the equation theory as an inductive family: *)
    (* Reserved Notation "Γ ⊢ T ∋ t ⤳ s" (at level 70). *)
    Inductive βη_norm : forall (Γ : context) (T : type), Γ ⊢ T -> Γ ⊢ T -> Prop :=
    | rule_β : forall{Γ T S}{b : Γ ▷ S ⊢ T}{s : Γ ⊢ S},
        βη_norm Γ T (app (lam b) s) (sub1 b s)
    | rule_η_fun : forall{Γ T S}{f : Γ ⊢ S ⇒ T},
        βη_norm Γ (S ⇒ T) f (lam (app (rename (weak1 id) f) (var here)))
    | rule_η_pair : forall{Γ A B}{p : Γ ⊢ A × B},
        βη_norm Γ (A × B) p (pair (fst p) (snd p)).
    
    Inductive βη_eq : forall (Γ : context) (T : type), Γ ⊢ T -> Γ ⊢ T -> Prop :=
    | inc : forall {Γ T t1 t2},
        βη_norm Γ T t1 t2 ->
        βη_eq Γ T t1 t2
    | refl : forall {Γ T t},
        βη_eq Γ T t t
    | sym : forall {Γ T t1 t2},
        βη_eq Γ T t1 t2 ->
        βη_eq Γ T t2 t1
    | trans : forall {Γ T t1 t2 t3},
        βη_eq Γ T t1 t2 -> βη_eq Γ T t2 t3 ->
        βη_eq Γ T t1 t3
    | struct_lam : forall{Γ S T b b'},
        βη_eq (Γ ▷ S) T b b' ->
        βη_eq Γ (S ⇒ T) (lam b) (lam b')
    | struct_app : forall{Γ S T f f' s s'},
        βη_eq Γ (S ⇒ T) f f' -> βη_eq Γ S s s' ->
        βη_eq Γ T (app f s) (app f' s')
    | struct_pair : forall{Γ A B a a' b b'},
        βη_eq Γ A a a' -> βη_eq Γ B b b' ->
        βη_eq Γ (A × B) (pair a b) (pair a' b')
    | struct_fst : forall{Γ A B p p'},
        βη_eq Γ (A × B) p p' ->
        βη_eq Γ A (fst p) (fst p')
    | struct_snd : forall{Γ A B p p'},
        βη_eq Γ (A × B) p p' ->
        βη_eq Γ B (snd p) (snd p').

    (** ***Compute η-long β-normal forms for the simply typed λ-calculus: *)
    Inductive term : Type :=
    | Lam (v : String.string) (b : term) : term
    | Var (v : String.string) : term
    | App (f s : term) : term
    | Tt : term
    | Pair (a b : term) : term
    | Fst (p : term) : term
    | Snd (p : term) : term.

    Reserved Notation "⟦ T ⟧Type".
    Fixpoint interp_type (T : type) : Type :=
      match T with
      | unit => term
      | T1 ⇒ T2 => ⟦ T1 ⟧Type -> ⟦ T2 ⟧Type
      | T1 × T2 => ⟦ T1 ⟧Type * ⟦ T2 ⟧Type
      end
    where "⟦ T ⟧Type" := (interp_type T).

    Reserved Notation "⟦ Γ ⟧context".
    Fixpoint interp_context (Γ : context) : Type :=
      match Γ with
      | ϵ => Datatypes.unit
      | Γ ▷ T1 => ⟦ Γ ⟧context * ⟦ T1 ⟧Type
      end
    where "⟦ Γ ⟧context" := (interp_context Γ).

    Definition interp_type_context (Γ : context) (T : type) : Type :=
      ⟦ Γ ⟧context -> ⟦ T ⟧Type.
    Notation "Γ ⊩ T" := (interp_type_context Γ T) (at level 50).

    Fixpoint lookup {Γ T} (v : T ∈ Γ) : Γ ⊩ T :=
      match v with
      | here => fun '(_, x) => x
      | there h => fun '(γ, _) => lookup h γ
      end.

    Fixpoint eval {Γ T} (t : Γ ⊢ T) : Γ ⊩ T :=
      match t with
      | var v => fun ρ => lookup v ρ
      | app f s => fun ρ => eval f ρ (eval s ρ)
      | lam b => fun ρ => fun s => eval b (ρ, s)
      | pair a b => fun ρ => (eval a ρ , eval b ρ)
      | fst p => fun ρ => Datatypes.fst (eval p ρ)
      | snd p => fun ρ => Datatypes.snd (eval p ρ)
      | tt => fun _ => Tt
      end.

    (** Let us, for simplicity, assume that we have access to a fresh name
      generator, `gensym` *)
    Axiom gensym : Datatypes.unit -> String.string.

    (** We could then back-translate the objects in the model (`⟦_⟧Type`)
      back to raw terms (through `reify`). However, to do so, one needs to
      inject variables in η-long normal form into the model: this is the
      role of `reflect`: *)
    Equations reify (T : type) : ⟦ T ⟧Type -> term :=
      { reify unit t => t;
        reify (T1 ⇒ T2) t => let freshx := gensym Datatypes.tt in
                            Lam freshx (reify T2 (t (reflect T1 (Var freshx))));
        reify (T1 × T2) (f, s) => Pair (reify T1 f) (reify T2 s)
      } with reflect (T : type) : term -> ⟦ T ⟧Type :=
        { reflect unit t => t;
          reflect (T1 ⇒ T2) t => fun s => reflect T2 (App t (reify T1 s));
          reflect (T1 × T2) t => (reflect T1 (Fst t), reflect T2 (Snd t))
        }.

    (** Given a λ-term, we can thus compute its normal form: *)
    Fixpoint idC (Γ : context) : ⟦ Γ ⟧context :=
      match Γ with
      | ϵ => Datatypes.tt
      | (Γ ▷ T) => (idC Γ, reflect T (Var (gensym Datatypes.tt)))
      end.
    Definition norm {Γ T} Δ := reify T (eval Δ (idC Γ)).

    (** Just like in the previous lecture, we can use it to check whether any two
      terms belong to the same congruence class by comparing their normal forms *)
    Definition term1 : ϵ ⊢ (unit ⇒ unit) ⇒ (unit ⇒ unit) :=
      (* λ s. λ z. s (s z) *)
      lam (lam (app (var (there here)) (app (var (there here)) (var here)))).

    Definition term2 : ϵ ⊢ (unit ⇒ unit) ⇒ (unit ⇒ unit) :=
      (* λ s. (λ r. λ z. r (s z)) (λ x. s x) *)
      lam (app (lam (lam (app (var (there here))
                              (app (var (there (there here))) (var here)))))
               (lam (app (var (there here)) (var here)))).

    Example test_nbe : norm term1 = norm term2.
    Proof. reflexivity. Qed.

    (** For instance, thanks to a suitable model construction, we have
      surjective pairing *)
    Definition term3 : ϵ ⊢ (unit × unit) ⇒ (unit × unit) :=
      (* λ p. p *)
      lam (var here).

    Definition term4 : ϵ ⊢ (unit × unit) ⇒ (unit × unit) :=
      (* λ p. (fst p, snd p) *)
      lam (pair (fst (var here)) (snd (var here))).

    Example test_nbe2 : norm term3 = norm term4.
    Proof. reflexivity. Qed.

    (** However, this implementation is a bit of wishful thinking: we do not
      have a `gensym`! So the following is also true, for the bad reason
      that `gensym` is not actually producing unique names but always the
      same name (itself): *)
    Definition term5 : ϵ ⊢ unit ⇒ (unit ⇒ unit) :=
      (* λ z1 z2. z1 *)
      lam (lam (var (there here))).

    Definition term6 : ϵ ⊢ unit ⇒ (unit ⇒ unit) :=
      (* λ z1 z2. z2 *)
      lam (lam (var here)).

    Example test_nbe3 : norm term5 = norm term6.
    Proof. reflexivity. Qed. (* BUG ! *)
  End Model1.

  (** This might not deter the brave monadic programmer: we can emulate
      `gensym` using a reenactment of the state monad: *)
  Module Fresh.
    Import FunctionalExtensionality.

    Definition Fresh (A : Type) : Type := nat -> (A * nat).
    Definition gensym (tt : Datatypes.unit) : Fresh String.string :=
      fun n => (sprintf.show_nat n, 1 + n).

    Program Instance FreshMonad : Monad Fresh :=
      {
        ret _ x := fun n => (x, n);
        bind _ _ x k := fun n => let (a, n') := x n in k a n'
      }.
    Next Obligation.
      apply functional_extensionality; intro n.
      destruct (x n) as [a n']. reflexivity.
    Qed.
    Next Obligation.
      apply functional_extensionality; intro n.
      destruct (x n) as [a n'].
      destruct (f a n') as [a1 n1].
      reflexivity.
    Qed.

  (** We then simply translate the previous code to a monadic style, a
      computer could do it automatically: *)
    (* Equations reify (T : type) : ⟦ T ⟧Type -> Fresh term := *)
    (*   { reify unit t => ret t; *)
    (*     reify (T1 × T2) (a, b) => *)
    (*     reify T1 a >>= *)
    (*           fun a => reify T2 b >>= *)
    (*                       fun b => ret (Pair a b); *)
    (*     reify (T1 ⇒ T2) f => *)
    (*     gensym Datatypes.tt >>= *)
    (*            fun s => reflect T1 (Var s) >>= *)
    (*                          fun t => reify T2 (f t) >>= *)
    (*                                      fun b => ret (Lam s b) *)
    (*   } with reflect (T : type) : term -> Fresh ⟦ T ⟧Type := *)
    (*     { reflect unit t => ret t; *)
    (*       reflect (T1 × T2) t => *)
    (*       reflect T1 (Fst t) >>= *)
    (*               fun a => reflect T2 (Snd t) >>= *)
    (*                             fun b => ret (a, b); *)
    (*       reflect (T1 ⇒ T2) t => ret (fun s => _) *)
    (*     }. *)
    (* cannot conclude with `reflect T (neu ! reify s)` *)
  End Fresh.

  (** **The Rising Sea *)
  Module Model2.

    Reserved Notation "Γ ⊢Nf T" (at level 50).
    Reserved Notation "Γ ⊢Ne T" (at level 50).
    Inductive has_type_nf (Γ : context) : type -> Type :=
    | Lam {S T} (b : Γ ▷ S ⊢Nf T) : Γ ⊢Nf S ⇒ T
    | Pair {A B} (a : Γ ⊢Nf A) (b : Γ ⊢Nf B) : Γ ⊢Nf A × B
    | Tt : Γ ⊢Nf unit
    | Ground (grnd : Γ ⊢Ne unit) : Γ ⊢Nf unit
    where "Γ ⊢Nf T" := (has_type_nf Γ T)
    with has_type_ne (Γ : context) : type -> Type :=
         | Var {T} (v : T ∈ Γ) : Γ ⊢Ne T
         | App {S T} (f : Γ ⊢Ne S ⇒ T) (s : Γ ⊢Nf S) : Γ ⊢Ne T
         | Fst {A B} (p : Γ ⊢Ne A × B) : Γ ⊢Ne A
         | Snd {A B} (p : Γ ⊢Ne A × B) : Γ ⊢Ne B
    where "Γ ⊢Ne T" := (has_type_ne Γ T).
    Arguments Lam {_ _ _}. Arguments App {_ _ _}.
    Arguments Tt {_}. Arguments Ground {_}. Arguments Var {_ _}.
    Arguments Fst {_ _ _}. Arguments Snd {_ _ _}. Arguments Pair {_ _ _}.

    Reserved Notation "⎣ t ⎦Nf".
    Reserved Notation "⎣ t ⎦Ne".
    Fixpoint nf_to_term {Γ T} (t : Γ ⊢Nf T) : Γ ⊢ T :=
      match t with
      | Lam b => lam ⎣ b ⎦Nf
      | Ground grnd => ⎣ grnd ⎦Ne
      | Pair a b => pair ⎣ a ⎦Nf ⎣ b ⎦Nf
      | Tt => tt
      end
    where "⎣ t ⎦Nf" := (nf_to_term t)
    with ne_to_term {Γ T} (t : Γ ⊢Ne T) : Γ ⊢ T :=
           match t with
           | Var v => var v
           | App f s => app ⎣ f ⎦Ne ⎣ s ⎦Nf
           | Fst p => fst ⎣ p ⎦Ne
           | Snd p => snd ⎣ p ⎦Ne
           end
    where "⎣ t ⎦Ne" := (ne_to_term t).

    Class Sem : Type :=
      { sem_context : context -> Type;
        ren {Γ Δ} : Γ ⊇ Δ -> sem_context Δ -> sem_context Γ
      }.

    Local Set Warnings "-implicits".
    Definition context_and_type (P Q : Sem) : Type :=
      forall {Γ}, @sem_context P Γ -> @sem_context Q Γ.
    Notation "P ⟦⊢⟧ Q" := (context_and_type P Q) (at level 80).

    Fixpoint rename_Nf {Γ Δ T} (wk : Γ ⊇ Δ) (t : Δ ⊢Nf T) : Γ ⊢Nf T :=
      match t with
      | Lam b => Lam (rename_Nf (weak2 wk) b)
      | Ground grnd => Ground (rename_Ne wk grnd)
      | Pair a b => Pair (rename_Nf wk a) (rename_Nf wk b)
      | Tt => Tt
      end
    with rename_Ne {Γ Δ T} (wk : Γ ⊇ Δ) (t : Δ ⊢Ne T) : Γ ⊢Ne T :=
           match t with
           | Var v => Var (shift wk v)
           | App f s => App (rename_Ne wk f) (rename_Nf wk s)
           | Fst p => Fst (rename_Ne wk p)
           | Snd p => Snd (rename_Ne wk p)
           end.

    Instance Nf (T : type) : Sem :=
      { sem_context Γ := Γ ⊢Nf T;
        ren _ _ := rename_Nf }.

    Instance Ne (T : type) : Sem :=
      { sem_context Γ := Γ ⊢Ne T;
        ren _ _ := rename_Ne }.

    (** Following our earlier model, we will interpret the `unit` type as
        the normal forms of type `unit`: *)
    Definition sem_unit : Sem := Nf unit.
    Notation "⟦unit⟧" := sem_unit.

    Definition sem_tt {P} : P ⟦⊢⟧ ⟦unit⟧ := fun _ _ => Tt.
    Notation "⟦tt⟧" := sem_tt.

    (** Similarly, we will interpret the `_×_` type as a product in
        `Sem`, defined in a pointwise manner: *)
    Instance sem_prod (P Q : Sem) : Sem :=
      { sem_context Γ := Datatypes.prod (@sem_context P Γ) (@sem_context Q Γ);
        ren _ _ wk '(x, y) := (@ren P _ _ wk x, @ren Q _ _ wk y) }.
    Notation "P ⟦×⟧ Q" := (sem_prod P Q) (at level 70).

    Definition sem_pair {P Q R} : P ⟦⊢⟧ Q -> P ⟦⊢⟧ R -> P ⟦⊢⟧ Q ⟦×⟧ R :=
      fun a b ρ Γ => (a ρ Γ, b ρ Γ).
    Notation "⟦pair⟧" := sem_pair.

    Definition sem_fst {P Q R} : P ⟦⊢⟧ Q ⟦×⟧ R -> P ⟦⊢⟧ Q :=
      fun p ρ Γ => Datatypes.fst (p ρ Γ).
    Notation "⟦fst⟧" := sem_fst.

    Definition sem_snd {P Q R} : P ⟦⊢⟧ Q ⟦×⟧ R -> P ⟦⊢⟧ R :=
      fun p ρ Γ => Datatypes.snd (p ρ Γ).
    Notation "⟦snd⟧" := sem_snd.

    (** ***Interlude: Yoneda lemma *)
    (* TODO *)

    (** ***Back to the Sea *)
    Instance sem_arrow (P Q : Sem) : Sem :=
      { sem_context Γ := forall {Δ}, Δ ⊇ Γ -> @sem_context P Δ -> @sem_context Q Δ;
        ren _ _ wk1 k _ wk2 := k _ (wk1 ∘wk wk2) }.
    Notation "P ⟦⇒⟧ Q" := (sem_arrow P Q) (at level 70).

    Definition sem_lam {P Q R} : P ⟦×⟧ Q ⟦⊢⟧ R -> P ⟦⊢⟧ Q ⟦⇒⟧ R :=
      fun η _ p _ wk q => η _ (ren wk p , q).
    Notation "⟦lam⟧" := sem_lam.

    Definition sem_app {P Q R} : P ⟦⊢⟧ Q ⟦⇒⟧ R -> P ⟦⊢⟧ Q -> P ⟦⊢⟧ R :=
      fun η μ _ px => η _ px _ id (μ _ px).
    Notation "⟦app⟧" := sem_app.

    (** At this stage, we have enough structure to interpret the types *)
    Reserved Notation "⟦ T ⟧".
    Fixpoint interp_type (T : type) : Sem :=
      match T with
      | unit => ⟦unit⟧
      | T1 ⇒ T2 => ⟦ T1 ⟧ ⟦⇒⟧ ⟦ T2 ⟧
      | T1 × T2 => ⟦ T1 ⟧ ⟦×⟧ ⟦ T2 ⟧
      end
    where "⟦ T ⟧" := (interp_type T).

    (** To interpret contexts, we also need a terminal object: *)
    Instance terminal : Sem :=
      { sem_context _ := Datatypes.unit;
        ren _ _ _ _ := Datatypes.tt }.
    Notation "⟦⊤⟧" := terminal.

    Reserved Notation "⟦ Γ ⟧C".
    Fixpoint interp_context (Γ : context) : Sem :=
      match Γ with
      | ϵ => ⟦⊤⟧
      | Γ ▷ T => ⟦ Γ ⟧C ⟦×⟧ ⟦ T ⟧
      end
    where "⟦ Γ ⟧C" := (interp_context Γ).

    (** As usual, a type in context will be interpreted as a morphism between
        their respective interpretations. The interpreter then takes the
        syntactic object to its semantical counterpart: *)
    Definition sem_has_type (Γ : context) (T : type) : Type :=
      ⟦ Γ ⟧C ⟦⊢⟧ ⟦ T ⟧.
    Notation "Γ ⊩ T" := (sem_has_type Γ T) (at level 80).

    Fixpoint lookup {Γ T} (v : T ∈ Γ) : Γ ⊩ T :=
      match v with
      | here => fun _ '(_, v) => v
      | there x => fun _ '(γ, _) => lookup x _ γ
      end.

    Fixpoint eval {Γ T} (t : Γ ⊢ T) : Γ ⊩ T :=
      match t with
      | lam b => ⟦lam⟧ (eval b)
      | var v => lookup v
      | app f s => ⟦app⟧ (eval f) (eval s)
      | tt => ⟦tt⟧
      | pair a b => ⟦pair⟧ (eval a) (eval b)
      | fst p => ⟦fst⟧ (eval p)
      | snd p => ⟦snd⟧ (eval p)
      end.

    (** Reify and reflect are defined for a given syntactic context, we
        therefore introduce suitable notations: *)

    Definition synt_has_type (Γ : context) (T : type) : Type :=
      @sem_context ⟦T⟧ Γ.
    Notation "[ Γ ]⊩ T" := (synt_has_type Γ T) (at level 80).

    Definition synt_has_context (Γ Δ : context) : Type :=
      @sem_context ⟦Δ⟧C Γ.
    Notation "[ Γ ]⊩C Δ" := (synt_has_context Γ Δ) (at level 80).

    (** The sea has sufficiently risen: we can implement our initial plan,
        using the renaming operator `ren` equipping `Sem` in the function
        case in `reify`: *)

    Fixpoint reify {Γ} (T : type) : [ Γ ]⊩ T -> Γ ⊢Nf T :=
      match T with
      | unit => fun v => v
      | T1 ⇒ T2 =>
        fun f => Lam (reify T2 ((ren (weak1 id) f) _ id (reflect T1 (Var here))))
      | A × B => fun '(a, b) => Pair (reify A a) (reify B b)
      end
    with reflect {Γ} (T : type) : Γ ⊢Ne T -> [ Γ ]⊩ T :=
           match T with
           | unit => Ground
           | T1 ⇒ T2 =>
             fun v _ w s => reflect T2 (App (@ren (Ne _) _ _ w v) (reify T1 s))
           | A × B => fun v => (reflect A (Fst v), reflect B (Snd v))
           end.

    Fixpoint idC (Γ : context) : [ Γ ]⊩C Γ :=
      match Γ with
      | ϵ => Datatypes.tt
      | (Γ ▷ T) => (ren (weak1 id) (idC Γ), reflect T (Var here))
      end.
    Definition reify_id {Γ T} (f : Γ ⊩ T) : Γ ⊢Nf T :=
      reify _ (f _ (idC Γ)).

    Definition norm {Γ T} (t : Γ ⊢ T) : Γ ⊢Nf T :=
      reify_id (eval t).
  End Model2.
End NormalForms.

(** **Optional: Categorical spotting *)
(* TODO *)