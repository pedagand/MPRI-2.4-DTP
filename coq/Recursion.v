(** *Total functional programming *)

From TypingFlags Require Import Loader.
From Equations Require Import Equations.
Require Import Coq.Program.Equality.
Require Import MPRICoq.Monad.
Require Import MPRICoq.Indexed.

(** **First order unification *)

Module UnifSpec.
  Import Maybe.

  (** ***Specification: terms *)
  Definition Var := nat.
  Inductive Term : Type :=
  | var (i : Var) : Term
  | leaf : Term
  | fork (s t : Term) : Term.

  Fixpoint sub (ρ : Var -> Term) (t : Term) : Term :=
    match t with
    | var i => ρ i
    | leaf => leaf
    | fork s t => fork (sub ρ s) (sub ρ t)
    end.

  Definition comp_sub (ρ1 ρ2 : Var -> Term) (t : Var) : Term :=
    sub ρ1 (ρ2 t).
  Notation "ρ1 ∘K ρ2" := (comp_sub ρ1 ρ2) (at level 30).

  (** ***Specification: occur-check *)
  Fixpoint diff (x : Var) (y : Var) : Maybe Var :=
    match x, y with
    | O, O => None
    | O, S y => ret y
    | S x, O => ret O
    | S x, S y => (diff x y) >>= fun y' => ret (S y')
    end.
  Notation "x △ y" := (diff x y) (at level 30).

  Fixpoint check (i : Var) (t : Term) : Maybe Term :=
    match t with
    | var j => i △ j >>= fun z => ret (var z)
    | leaf => ret leaf
    | fork f s => check i f >>= fun r1 => check i s >>= fun r2 => ret (fork r1 r2)
    end.

  (** ***Specification: substitution *)
  Inductive Subst : Type :=
  | id : Subst
  | subst (σ : Subst)(i : Var)(t : Term) : Subst.
  Notation "σ :: [ i ↦ t ]" := (subst σ i t) (at level 30).

  Definition substitute (t : Term) (i : Var) : Var -> Term :=
    fun j => match i △ j with
          | None => t
          | Some j' => var j'
          end.

  Reserved Notation "⟦ ρ ⟧".
  Fixpoint apply_subst (ρ : Subst) : Var -> Term :=
    match ρ with
    | id => fun x => var x
    | ρ::[i ↦ t] => fun x => (⟦ρ⟧ ∘K (substitute t i)) x
    end
  where "⟦ ρ ⟧" := (apply_subst ρ).

  (** ***Specification: most-general unifier *)
  Definition flex_flex (x y : Var) : Subst :=
    match x △ y with
    | Some y' => id::[x ↦ var y']
    | None => id
    end.

  Definition flex_rigid x t := check x t >>= fun t' => ret (id::[x ↦ t']).

  (** We will assume thag the program actually terminates, but the Coq's
      termination checker wont be able to prove it; we switch the checker off
      for now *)
  Unset Guard Checking.
  Fixpoint amgu (t1 : Term) (t2 : Term) (σ : Subst) {struct t1} : Maybe Subst :=
    match t1, t2, σ with
    (* Conflicts: *)
    | leaf, (fork _ _), _ => None
    | (fork _ _), leaf, _ => None
    (* Matches: *)
    | leaf, leaf, acc => ret acc
    | (fork s1 t1), (fork s2 t2), acc => amgu s1 s2 acc >>= amgu t1 t2
    (* Variables flex-flex: *)
    | (var x), (var y), id => ret (flex_flex x y)
    (* Variables flex-rigid: *)
    | (var x), t, id => flex_rigid x t
    | t, (var x), id => flex_rigid x t
    | t1, t2, σ::[z ↦ r] => amgu (sub (substitute r z) t1)
                        (sub (substitute r z) t2) σ >>= fun σ => ret (σ::[z ↦ r])
    end.
  Set Guard Checking.

  Definition mgu (s t : Term) : Maybe Subst := amgu s t id.

  Example test1 : mgu (fork (var 0) leaf) (fork (fork leaf leaf) (var 1))
                  = Some (id::[0 ↦ leaf]::[0 ↦ fork leaf leaf]).
  Proof. reflexivity. Qed.

  Example test2 : mgu (fork (var 0) leaf) (fork (fork leaf leaf) (var 3))
                  = Some (id::[2 ↦ leaf]::[0 ↦ (fork leaf leaf)]).
  Proof. reflexivity. Qed.

  Example test3 : mgu (var 0) (fork leaf (var 0))
                  = None.
  Proof. reflexivity. Qed.

  Example test4 : mgu (fork (var 0) leaf) (fork (fork leaf leaf) (var 0))
                  = None.
  Proof. reflexivity. Qed.

  Example test5 : mgu (fork (var 0) (var 1))
                      (fork (fork leaf (var 1)) (fork leaf leaf))
                  = Some (id::[0 ↦ (fork leaf leaf)]::[0 ↦ (fork leaf (var 0))]).
  Proof. reflexivity. Qed.
End UnifSpec.

Module UnifStruct.
  Import Maybe.
  Import NormalForms.Fin.

  (** ***Structurally: terms *)

  (** We now stratify the set of variables, ie. `Var n` contains `n`
      distinct variables: *)
  Definition Var : nat -> Type := fin.

  (** We can thus represent terms with (at most) ``n`` variables: *)
  Inductive Term (n : nat) : Type :=
  | var (i : Var n) : Term n
  | leaf : Term n
  | fork (s t : Term n) : Term n.
  Arguments var {_}. Arguments leaf {_}. Arguments fork {_}.

  Fixpoint sub {m n} (ρ : Var m -> Term n) (t : Term m) : Term n :=
    match t with
    | var i => ρ i
    | leaf => leaf
    | fork s t => fork (sub ρ s) (sub ρ t)
    end.

  Definition comp_sub {m n l}
             (ρ1 : Var m -> Term n) (ρ2 : Var l -> Term m) (t : Var l) : Term n :=
    sub ρ1 (ρ2 t).
  Notation "ρ1 ∘K ρ2" := (comp_sub ρ1 ρ2) (at level 30).

  Fixpoint ren {m n} (ρ : Var m -> Var n) (t : Term m) : Term n :=
    match t with
    | var v => var (ρ v)
    | leaf => leaf
    | fork s t => fork (ren ρ s) (ren ρ t)
    end.

  Definition subst_eq {m n} (f g : Var m -> Term n) : Prop :=
    forall x, f x = g x.
  Notation "f ≗ g" := (subst_eq f g) (at level 80).

  Fixpoint diff {n} (x : Var (S n)) (y : Var (S n)) : Maybe (Var n).
  Proof.
    inversion x; inversion y; subst.
    - exact None.
    - exact (ret i).
    - destruct n.
      + inversion i.
      + exact (ret zero).
    - destruct n.
      + inversion i.
      + exact (diff _ i i0 >>= fun y' => ret (suc y')).
  Defined.
  Notation "x △ y" := (diff x y) (at level 30).

  Fact diff_zero_l : forall {n} (i : Var n), zero △ (suc i) = Some i.
  Proof.
    intros n i.
    destruct i; reflexivity.
  Qed.

  (* Equations inj {n} : Var (S n) -> Var n -> Var (S n) := *)
  (*   { inj zero y := suc y; *)
  (*     inj (suc x) zero := zero; *)
  (*     inj (suc x) (suc y) := suc (inj x y) *)
  (*   }. *)
  Fixpoint inj {n} (x : Var (S n)) (y : Var n) : Var (S n).
  Proof.
    inversion x as [?|? x']; subst; clear x.
    - exact (suc y).
    - inversion y as [?|? y']; subst; clear y.
      + exact zero.
      + exact (suc (inj _ x' y')).
  Defined.
  Notation "inj[ x ]" := (inj x).

  Lemma lemma_inj1 : forall {n : nat} (x : Var (S n)) y z, inj[x] y = inj[x] z -> y = z.
  Proof.
    fix inj1 2.
    intros n x y z Heq.
    dependent destruction x; simpl in Heq; unfold eq_rect_r, eq_rect, eq_sym in *.
    - apply fin_eq_suc in Heq. assumption.
    - dependent destruction y; simpl; dependent destruction z; simpl in *;
        try congruence.
      + apply fin_eq_suc in Heq.
        apply inj1 in Heq. rewrite Heq. reflexivity.
  Qed.

  Lemma lemma_inj2 : forall {n : nat} (x : Var (S n)) y, inj[x] y <> x.
  Proof.
    fix inj2 2.
    intros n x y.
    dependent destruction x; simpl; unfold eq_rect_r, eq_rect, eq_sym.
    - congruence.
    - dependent destruction y.
      + try congruence.
      + intro contra. apply fin_eq_suc in contra.
        congruence.
  Qed.

  Lemma lemma_inj_diff : forall {n : nat} (x y : Var (S n)) (r : Maybe (Var n)),
      x △ y = r -> (x = y /\ r = None) \/ (exists y', y = inj[x] y' /\ r = Some y').
  Proof.
    fix inj_diff 2.
    intros n x y r Hdiff.
    destruct n; dependent destruction x; dependent destruction y; simpl in *;
      unfold eq_rect_r, eq_rect, eq_sym in *;
      try (now (left;auto));
      try (now (inversion x));
      try (now (inversion y)).
    - right. exists y; auto.
    - right. exists zero; auto.
    - destruct (inj_diff _ x y (x △ y)); auto.
      + left. destruct H as [H1 H2].
        rewrite H1. rewrite H2 in Hdiff. auto.
      + right. destruct H as [y' [Hy1 Hy2]].
        rewrite Hy2 in Hdiff.
        exists (suc y'). rewrite Hy1. auto.
  Qed.

  Inductive inj_View {n} (i : Var (S n)) : (Var (S n)) -> Type :=
  | just (k : Var n) : inj_View i (inj[i] k)
  | eq : inj_View i i.

  (** ***Structurally: occur-check *)
  Fixpoint check {n} (i : Var (S n)) (t : Term (S n)) : Maybe (Term n) :=
    match t with
    | var j => i △ j >>= fun k => ret (var k)
    | leaf => ret leaf
    | fork f s => check i f >>= fun r1 => check i s >>= fun r2 => ret (fork r1 r2)
    end.

  Lemma lemma_check : forall {n : nat} x t {t'},
      @check n x t = Some t' -> ren (inj[x]) t' = t.
  Proof.
    fix lemma_check 3.
    intros n x t t' Hcheck.
    destruct t; simpl in *.
    - destruct (x △ i) eqn:Hdiff; try congruence.
      inversion Hcheck; subst; clear Hcheck.
      dependent destruction x; simpl;
        unfold eq_rect_r, eq_rect, eq_sym.
      + admit.
      + admit.
    - inversion Hcheck; subst.
      dependent destruction x; simpl;
        unfold eq_rect_r, eq_rect, eq_sym; reflexivity.
    - destruct (check x t1) eqn:Hcheck1; try congruence.
      destruct (check x t2) eqn:Hcheck2; try congruence.
      apply lemma_check in Hcheck1; apply lemma_check in Hcheck2; simpl in *.
      dependent destruction x; simpl in *;
        unfold eq_rect_r, eq_rect, eq_sym in *; simpl in *;
          inversion Hcheck; subst; reflexivity.
  Admitted.

  (** ***Structurally: single term substitution *)
  Definition substitute {n} (t : Term n) (i : Var (S n)) : Var (S n) -> Term n :=
    fun j => match i △ j with
          | None => t
          | Some j' => var j'
          end.

  Lemma lemma_for_inj : forall {n} (t : Term n) x,
      (fun v => substitute t x (inj[x] v)) ≗ var.
  Proof.
    intros n t x.
    unfold subst_eq. intros v.
    dependent destruction x; simpl in *;
      unfold eq_rect_r, eq_rect, eq_sym in *.
    - unfold substitute. destruct t; simpl; rewrite diff_zero_l; reflexivity.
    - dependent destruction v; simpl in *.
      + reflexivity.
      + unfold substitute; simpl.
        unfold eq_rect_r, eq_rect, eq_sym.
  Admitted.

  (* TODO *)
End UnifStruct.