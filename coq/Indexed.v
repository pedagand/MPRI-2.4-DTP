(** *Indexed functional programming *)

Require Ascii String.
From Equations Require Import Equations.

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

  Fixpoint showNat (n : nat) : string :=
    match n with
    | O => "O"
    | S n => "S(" ++ (showNat n) ++ ")"
    end.

  Fixpoint eval (fmt : format) (acc : string) : ⟦ fmt ⟧ :=
    match fmt return ⟦ fmt ⟧ with
    | digitf k => fun n => eval k (acc ++ (showNat n))
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

  Inductive in_env : type -> context -> Prop :=
  | here {t Γ} : in_env t (Γ ▷ t)
  | there {t t' Γ} : in_env t Γ -> in_env t (Γ ▷ t').
  Notation "t ∈ Γ" := (in_env t Γ) (at level 50).
  Derive Signature for in_env.

  Reserved Notation "Γ ⊢ t" (at level 50).
  Inductive has_type : context -> type -> Prop :=
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

    (* TODO What ? *)
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

  (* Definition rename_lam {Γ Δ t} : (t ∈ Γ) -> (forall {s}, s ∈ Γ -> Δ ⊢ s) -> Δ ⊢ t. *)
  (* Admitted. *)
  (*   (* rename_lam here _ := var here; *) *)
  (*   (* rename_lam (there v) ρ := rename (weak1 id) (ρ _ v). *) *)

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
End NormalForms.