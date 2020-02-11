(** * Effectful functional programming *)

Require Import Coq.Classes.SetoidClass.
Require FunctionalExtensionality.

(** **Stateful operations *)
Module StateMonad.
  Definition S := nat.

  Inductive ΣState (X : Type) : Type :=
  | get' : unit -> (S -> X) -> ΣState X
  | set' : S -> (unit -> X) -> ΣState X.
  Arguments get' {_}. Arguments set' {_}.

  Definition ΣState_map {V W : Type} (f : (V -> W)) (v : ΣState V) : (ΣState W) :=
    match v with
    | get' _ g => get' tt (fun x => f (g x))
    | set' s g => set' s (fun u => f (g u))
    end.

  Lemma ΣState_map_id : forall {V : Type} (x : ΣState V),
      (ΣState_map (fun xs => xs) x) = x.
  Proof.
    intros V x. destruct x; simpl.
    - destruct u. f_equal.
    - f_equal.
  Qed.

  Lemma ΣState_map_comp : forall {U V W : Type} (f : U -> V)(g : V -> W)(x : ΣState U),
      ΣState_map (fun x => g (f x)) x = ΣState_map g (ΣState_map f x).
  Proof.
    intros U V W f g x. destruct x; auto.
  Qed.

  (** Remark : an equivalent (but more modular) way to obtain the same signature
      is through the following constructs: *)
  Inductive ΣGet (X : Type) : Type :=
  | get'2 : unit -> (S -> X) -> ΣGet X.
  Inductive ΣType (X : Type) : Type :=
  | set'2 : S -> (unit -> X) -> ΣType X.
  Arguments get'2 {_}. Arguments set'2 {_}.

  Inductive ΣGetType (F G : Type -> Type) (X : Type) : Type :=
  | inl : F X -> ΣGetType F G X
  | inr : G X -> ΣGetType F G X.
  Notation " F ⊕ G " := (ΣGetType F G) (at level 20).

  (** *** Free term algebra for state *)

  Inductive StateF (V : Type) : Type :=
  | ret : V -> StateF V
  | op : ΣState (StateF V) -> StateF V.
  Arguments ret {_}. Arguments op {_}.

  Definition get : unit -> StateF S :=
    fun _ => op (get' tt ret).

  Definition set : S -> StateF unit :=
    fun s => op (set' s ret).

  Fixpoint bind {V W : Type} (x : StateF V) (mf : V -> StateF W) : StateF W :=
    match x with
    | ret x => mf x
    | op (get' u f) => op (get' u (fun s => bind (f s) mf))
    | op (set' s f) => op (set' s (fun u => bind (f u) mf))
    end.
  Notation "x >>= y" := (bind x y) (at level 50, left associativity).

  (** At this stage, we can write (but not execute) stateful programs, such as: *)

  Definition test0 : StateF S :=
    get tt >>= fun s => set s >>= fun _ => get tt >>= fun s' => ret s'.
  Definition test1 : StateF S :=
    get tt >>= fun s' => ret s'.
  Definition test2 : StateF S :=
    get tt >>= fun s => set s >>= fun _ => ret s.
  Definition random : StateF nat :=
    get tt >>= fun seed => let n := Nat.modulo (seed * 25 + 17) 65 in
                        set n >>= fun _ => ret n.

  (** *** Monad laws *)

  Lemma bind_left_unit : forall {X Y : Type} (x : X) (k : X -> StateF Y),
      (ret x >>= k) = k x.
  Proof. reflexivity. Qed.

  Import FunctionalExtensionality.

  Lemma bind_right_unit : forall {X : Type} (mx : StateF X),
      mx >>= ret = mx.
  Proof.
    fix bind_right_unit 2.
    intros X mx. destruct mx as [?|x].
    - reflexivity.
    - destruct x; simpl; repeat f_equal;
        apply functional_extensionality; intro x; apply bind_right_unit.
  Qed.

  Lemma bind_compose : forall {X Y Z : Type} (mx : StateF X)(f : X -> StateF Y)(g : Y -> StateF Z),
    ((mx >>= f) >>= g) = (mx >>= fun x => (f x >>= g)).
  Proof.
    fix bind_compose 4.
    intros X Y Z mx f g.
    destruct mx as [?|x]; simpl.
    - reflexivity.
    - destruct x; simpl; repeat f_equal;
        apply functional_extensionality; intro x;
          rewrite <- bind_compose; reflexivity.
  Qed.

  (** *** Equational theory of State *)

  Inductive StateF_red {V : Type} : StateF V -> StateF V -> Prop :=
    | red_get_get (k : S -> S -> StateF V) :
        StateF_red (get tt >>= (fun s => get tt >>= fun s' => k s s'))
                   (get tt >>= fun s => k s s)
    | red_set_set k s1 s2 :
        StateF_red (set s1 >>= (fun _ => set s2 >>= fun _ => k))
                   (set s2 >>= fun _ => k)
    | red_get_set k :
        StateF_red (get tt >>= fun s => set s >>= fun _ => k) k
    | red_set_get k s :
        StateF_red (set s >>= (fun _ => get tt >>= k))
                   (set s >>= fun _ => k s).
  Notation "x ⇝ y" := (StateF_red x y) (at level 70).

  Reserved Notation "x ∼ y" (at level 70).
  Inductive StateF_eq {V : Type} : StateF V -> StateF V -> Prop :=
    | eq_red p q : (p ⇝ q) -> p ∼ q
    | eq_trans p q r : (p ∼ q) -> (q ∼ r) -> (p ∼ r)
    | eq_refl p : p ∼ p
    | eq_sym p q : p ∼ q -> q ∼ p
    | eq_cong {W : Type} (tm : StateF W)(ps qs : W -> StateF V) :
        (forall w, ps w ∼ qs w) -> (tm >>= ps) ∼ (tm >>= qs)
    where "x ∼ y" := (StateF_eq x y).

  Add Parametric Relation {V : Type} : (StateF V) (@StateF_eq V)
      reflexivity proved by eq_refl
      symmetry proved by eq_sym
      transitivity proved by eq_trans
        as StateF_rel.

  Definition prog1 : StateF nat :=
    get tt >>=
        fun x => set (1 + x) >>=
                  fun _ => get tt >>=
                            fun y => set (2 + x) >>=
                                      fun _ => get tt >>=
                                                fun z => set (3 + y) >>=
                                                          fun _ => ret y.

  Definition prog2 : StateF nat :=
    get tt >>= fun x => set (4 + x) >>= fun _ => ret (1 + x).

  Lemma prog_equiv : prog1 ∼ prog2.
  Proof.
    unfold prog1; unfold prog2.
    repeat (etransitivity;
            try (apply eq_cong; intro w; apply eq_red; constructor)).
  Qed.

  (** ** Semantics: `State ≡ StateF/∼` *)

  Definition State (V : Type) := ΣGet (ΣType V).

  (** We have recovered Haskell's `State` monad: *)
  Definition STATE (V : Type) := S -> (S * V).

  (** It remains to substantiate this claim that every stateful program is
      equivalent to a `get` followed by a `set`. We should do so computationally,
      thus inheriting a program computing these normal forms, as well as a proof
      that this program is correct. *)

  (** The first step is to interpret stateful statements into a suitable
      semantic domain which is extensionally quotiented by the theory of State *)
  Fixpoint eval {A : Type} (s : StateF A) : STATE A :=
    match s with
    | ret x => fun s => (s, x)
    | op x => match x with
             | get' _ k => fun s => eval (k s) s
             | set' s' k => fun s => eval (k tt) s'
             end
    end.

  (** The function should satisfy the following unit-proofs: *)
  Lemma test_eval_get : forall {A} (k : S -> StateF A) s,
      eval (get tt >>= k) s = eval (k s) s.
  Proof. reflexivity. Qed.
  Lemma test_eval_set : forall {A} (k : unit -> StateF A) s s',
      eval (set s' >>= k) s = eval (k tt) s'.
  Proof. reflexivity. Qed.

  (** The second step consists in reifying the semantic objects into a desired
      normal form *)
  Definition reify {A : Type} (f : STATE A) : State A :=
    get'2 tt (fun s => set'2 (fst (f s)) (fun _ => (snd (f s)))).

  (** The normalization procedure thus genuinely computes the normal form: *)
  Definition norm {A : Type} (p : StateF A) : State A :=
    reify (eval p).

  Definition denorm {A : Type} (p : State A) : StateF A :=
    let help := (fun p => match p with
                  | set'2 s k => set s >>= fun _ => ret (k tt)
                  end) in
    match p with
    | get'2 _ k => get tt >>= fun s => help (k s)
    end.
  Notation "⎡ p ⎤" := (denorm p) (at level 60).

  (** ***Monads strike back*** *)

  (** Looking closely at the `eval` function, we notice that we map syntactic
      objects to semantics objects. The natural question to ask is whether all
      the structure defined over `StateF A` carries over to `STATE A`, ie. is
      there a semantical counterpart to `ret`, `get`, `set` and `>>=` ? *)

  Definition sem_return {A : Type} (a : A) : STATE A := fun s => (s, a).

  Definition sem_get (_ : unit) : STATE S := fun s => (s, s).

  Definition sem_set (s : S) : STATE unit := fun _ => (s, tt).

  Lemma test_sem_return : forall {X : Type} (x : X), eval (ret x) = sem_return x.
  Proof. reflexivity. Qed.

  Lemma test_sem_get : forall (s : S), eval (get tt) s = sem_get tt s.
  Proof. reflexivity. Qed.

  Lemma test_sem_set : forall s s', eval (set s') s = sem_set s' s.
  Proof. reflexivity. Qed.

  Definition sem_bind {X Y : Type} (mx : STATE X) (k : X -> STATE Y) : STATE Y :=
    fun s => let (x, y) := (mx s) in k y x.
  Notation "x sem->>= k" := (sem_bind x k) (at level 50, left associativity).

  Lemma test_eval_compose : forall {X Y : Type}(mx : StateF X)(k : X -> StateF Y)(s : S),
      eval (mx >>= k) s = (eval mx sem->>= (fun x => eval (k x))) s.
  Proof.
    fix test_eval_compose 3.
    intros X Y mx k s.
    destruct mx as [x|x]; simpl; unfold sem_bind.
    - reflexivity.
    - destruct x; simpl.
      + rewrite test_eval_compose. unfold sem_bind. reflexivity.
      + rewrite test_eval_compose. unfold sem_bind. reflexivity.
  Qed.

  (** ***Soundness and completeness*** *)

  Fact eval_bind_eq : forall {V W : Type} (tm : StateF V) (p q : V -> StateF W),
      (forall w x, eval (p w) x = eval (q w) x) ->
      forall x, eval (tm >>= p) x = eval (tm >>= q) x.
  Proof.
    fix eval_bind_eq 3.
    intros V W tm p q Hev.
    destruct tm as [?|x]; simpl.
    - apply Hev.
    - destruct x; intro x; simpl;
      apply eval_bind_eq; auto.
  Qed.

  Lemma pf_sound : forall {A : Type} (p : StateF A), p ∼ ⎡ norm p ⎤.
  Proof.
    fix pf_sound 2.
    intros A p.
    destruct p as [x|x]; simpl.
    - symmetry. apply eq_red. apply red_get_set.
    - destruct x as [u k | s k]; simpl.
      + destruct u.
        assert (get tt >>= k ∼ get tt >>= (fun s' => ⎡ norm (k s') ⎤)) as Heq.
        { apply eq_cong. intros. apply pf_sound. }
        etransitivity. apply Heq.
        apply eq_red. apply red_get_get.
      + assert (set s >>= k ∼ set s >>= (fun _ => ⎡ norm (k tt) ⎤)) as Heq.
        { apply eq_cong. intros u; destruct u. apply pf_sound. }
        etransitivity. apply Heq.
        etransitivity. apply eq_red. apply red_set_get.
        etransitivity. apply eq_red. apply red_set_set.
        etransitivity. symmetry. apply eq_red. apply red_get_set.
        etransitivity. apply eq_cong.
        { intros w. apply eq_red. apply red_set_set. }
        reflexivity.
  Qed.

  Lemma pf_complete : forall {A : Type} (p q : StateF A),
      p ∼ q -> forall s, eval p s = eval q s.
  Proof.
    intros A p q Hsim.
    induction Hsim.
    - induction H; reflexivity.
    - intro s. rewrite IHHsim1. rewrite IHHsim2. reflexivity.
    - reflexivity.
    - intro s. auto.
    - intro s. apply eval_bind_eq. assumption.
  Qed.

  Theorem sound : forall {V : Type} (p q : StateF V),
      ⎡ norm p ⎤ = ⎡ norm q ⎤ -> p ∼ q.
  Proof.
    intros V p q H.
    etransitivity. apply pf_sound.
    rewrite H. symmetry.
    apply pf_sound.
  Qed.

  Theorem complete : forall {A : Type} (p q : StateF A),
      p ∼ q -> ⎡ norm p ⎤ = ⎡ norm q ⎤.
  Proof.
    intros V p q H.
    unfold norm at 1.
    assert (eval p = eval q) as He.
    - apply functional_extensionality.
      apply pf_complete; auto.
    - rewrite He. reflexivity.
  Qed.

  (** ***Examples*** *)

  Example test01 : test0 ∼ test1.
  Proof. apply sound. reflexivity. Qed.

  Example test12 : test1 ∼ test2.
  Proof. apply sound. reflexivity. Qed.

  Fact eval_compose : forall {V W : Type} (tm : StateF V) (k : V -> StateF W) s,
      eval (tm >>= k) s = eval (k (snd (eval tm s))) (fst (eval tm s)).
  Proof.
    fix eval_compose 3.
    intros V W tm k s.
    destruct tm as [?|x]; simpl.
    - reflexivity.
    - destruct x; apply eval_compose.
  Qed.

  Lemma norm_compose : forall {V W : Type} (tm : StateF W) (ps : W -> StateF V),
      ⎡ norm (tm >>= ps) ⎤ = ⎡ norm (⎡ norm tm ⎤ >>= fun w => ⎡ norm (ps w) ⎤) ⎤.
  Proof.
    intros V W tm ps.
    simpl. repeat f_equal.
    apply functional_extensionality. intros x. f_equal.
    rewrite eval_compose. reflexivity.
  Qed.

  Lemma cong2 : forall {V W : Type} (tm tm' : StateF W) (ps qs : W -> StateF V),
      (tm ∼ tm') ->
      (forall w, ps w ∼ qs w) ->
      (tm >>= ps) ∼ (tm' >>= qs).
  Proof.
    intros V W tm tm' ps qs Htm Hps.
    apply sound.
    rewrite norm_compose.
    apply complete in Htm. rewrite Htm.
    symmetry. rewrite norm_compose.
    repeat f_equal.
    apply functional_extensionality.
    intros x. apply complete. symmetry. apply Hps.
  Qed.

End StateMonad.

(** We will now represent a generic monad with a class *)
Class Monad (m : Type -> Type) : Type :=
  {
    ret {A} : A -> m A;
    bind {A B}: m A -> (A -> m B) -> m B;

    bind_left_unit {X Y} : forall (x : X) (k : X -> m Y), bind (ret x) k = k x;
    bind_right_unit {X} : forall (x : m X), bind x ret = x;
    bind_compose {X Y Z} : forall (x : m X)(f : X -> m Y)(g : Y -> m Z),
        (bind (bind x f) g) = bind x (fun x => bind (f x) g);
  }.
Notation "x >>= f" := (bind x f) (at level 50, left associativity).

(** **Application: the Tick monad TODO *)

(** **More monads *)

(** ***Exception/Error monad *)
Module Exception.
  Parameter E : Type.

  Inductive Exn (X : Type) :=
  | Ok (v : X) : Exn X
  | Ko (e : E) : Exn X.
  Arguments Ok {_}. Arguments Ko {_}.

  Definition raise (e : E) : Exn unit := Ko e.
  Definition catch {A B : Type} (x : Exn A) (k : A -> Exn B) (ke : E -> Exn B) :=
    match x with
    | Ok v => k v
    | Ko e => ke e
    end.
  Notation "x >>= [ k | ke ]" := (catch x k ke) (at level 50, left associativity).

  Program Instance ExceptionMonad : Monad Exn :=
    {
      ret _ v := Ok v;
      bind _ _ x k := match x with
                      | Ok v => k v
                      | Ko e => Ko e
                      end;
    }.
  Next Obligation. destruct x; reflexivity. Qed.
  Next Obligation. destruct x; reflexivity. Qed.

  (* TODO algebraic presentation *)
End Exception.

(** ***Reader/environment monad *)
Module Reader.
  Parameter Env : Type.

  Definition Reader (X : Type) : Type := Env -> X.

  Definition get_env (_ : unit) : Reader Env := fun e => e.

  Definition local {A : Type} (e : Env) (r : Reader A) : Reader A :=
    fun e => r e.

  Program Instance ReaderMonad : Monad Reader :=
    {
      ret _ v := fun _ => v;
      bind _ _ x k := fun e => k (x e) e
    }.

  (* TODO algebraic presentation *)
End Reader.

(** ***Non-determinism monad *)
Module ND.
  Parameter Info : Type.
  Open Scope list_scope.

  Definition Nondet (A : Type) : Type := list A.

  Definition ndfail {X : Type} : Nondet X := nil.

  Definition ndor {X : Type} (mx1 : Nondet X) (mx2 : Nondet X) : Nondet X :=
    List.app mx1 mx2.

  Program Instance NDMonad : Monad Nondet :=
    {
      ret _ x := x::nil;
      bind _ _ x k := List.concat (List.map k x);
    }.
  Next Obligation. apply List.app_nil_r. Qed.
  Next Obligation.
    induction x; simpl.
    - reflexivity.
    - rewrite IHx. reflexivity.
  Qed.
  Next Obligation.
    induction x; simpl.
    - reflexivity.
    - rewrite List.map_app. repeat rewrite List.concat_app.
      rewrite IHx. reflexivity.
  Qed.

  (* TODO algebraic presentation *)

  (** Insert an element `x` at a non-deterministic position of a list `l` *)
  Fixpoint insert {X : Type} (x : X) (l : list X) : Nondet (list X) :=
    match l with
    | nil => ret (x::nil)
    | hd::tl => ndor (ret (x::hd::tl)) (insert x tl >>= (fun l => ret (hd::l)))
    end.

  (** Compute (non-deterministically) a permutation of list `l` *)
  (* TODO *)
End ND.

(* TODO random Monad *)

(** ***Counting/complexity monad *)
Module Count.
  Definition Count (X : Type) : Type := (nat * X).

  Definition count {X : Type} (x : X) : Count X := (1, x).

  Program Instance CountMonad : Monad Count :=
    {
      ret _ x := (0, x);
      bind _ _ '(n , x) k :=
        let (n', y) := k x in (n + n', y);
    }.
  Next Obligation. destruct (k x); reflexivity. Qed.
  Next Obligation.
    destruct x; simpl.
    f_equal. symmetry. apply plus_n_O.
  Qed.
  Next Obligation.
    destruct x; simpl.
    destruct (f x); simpl; destruct (g y); simpl.
    f_equal. rewrite <- PeanoNat.Nat.add_assoc. reflexivity.
  Qed.

  Open Scope list_scope.
  Fixpoint insert (n : nat) (l : list nat) : Count (list nat) :=
    match l with
    | nil => ret (n::nil)
    | hd::tl => count (Nat.leb n hd)
                     >>= (fun is_le =>
                            match is_le with
                            | true => ret (n::hd::tl)
                            | false => (insert n tl)
                                        >>= (fun tl => ret (hd::tl))
                            end)
    end.

  Example insert_ex:
    (insert 4 (2::3::5::6::nil)) = (3, (2::3::4::5::6::nil)).
  Proof. reflexivity. Qed.
End Count.

(** ***Writer/logging monad *)
Module Log.
  Parameter Info : Type.
  Open Scope list_scope.

  Definition Log (X : Type) : Type := list Info * X.

  Definition log (i : Info) : Log unit := ((i::nil), tt).

  Program Instance LogMonad : Monad Log :=
    {
      ret _ x := (nil, x);
      bind _ _ '(log, x) k :=
        let (log', y) := k x in (List.app log log', y);
    }.
  Next Obligation. destruct (k x). reflexivity. Qed.
  Next Obligation.
    destruct x. f_equal. rewrite List.app_nil_r. reflexivity.
  Qed.
  Next Obligation.
    destruct x; simpl. destruct (f x); simpl. destruct (g y); simpl.
    rewrite List.app_assoc. reflexivity.
  Qed.
End Log.

(** ***CPS monad *)
Module CPS.
  Parameter U : Type.

  Definition CPS (X : Type) : Type := (X -> U) -> U.

  Definition call_cc {X : Type} (f : (X -> U) -> CPS X) : CPS X :=
    fun k => f k k.

  Definition throw {X : Type} (k' : X -> U) (mx : CPS X) : CPS X :=
    fun k => mx k'.

  Program Instance CPSMonad : Monad CPS :=
    {
      ret _ x := fun k => k x;
      bind _ _ x k := fun k' => x (fun x => k x k');
    }.
End CPS.