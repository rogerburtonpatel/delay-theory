From Coinduction Require Export all.
From Delay Require Export Utils Core.
Require Import Program.Tactics.
Set Implicit Arguments.
Set Contextual Implicit.
Set Primitive Projections.

Section Termination.
  Context {A : Type}.

Inductive terminatesF (terminates : delay A -> A -> Prop) : delay' A -> A -> Prop :=
  | terminates_now:   forall v, terminatesF terminates (nowF v) v
  | terminates_later: forall d v, terminates d v -> terminatesF terminates (laterF d) v.

Definition terminates_ (terminates : delay A -> A -> Prop) : delay A -> A -> Prop :=
  fun d a => terminatesF terminates (observe d) a.

Lemma terminatesF_mono : Proper (leq ==> leq) terminates_.
Proof.
  monauto.
Qed.

Definition terminates_mon := Build_mon terminatesF_mono.

(* terminates is now observe-based (vs the original [terminates (now v) v]). *)
Inductive terminates : delay A -> A -> Prop :=
| term_now   : forall d v,    observe d = nowF v    -> terminates d v
| term_later : forall d d' v, observe d = laterF d' -> terminates d' v -> terminates d v.

(* equi is now the gfp of the functor [equiF] over [observe]
   (vs the original direct CoInductive [equi]). *)
Inductive equiF (equi : delay A -> delay A -> Prop) : delay' A -> delay' A -> Prop :=
  | equi_terminates: forall x y v, terminates x v -> terminates y v -> equiF equi (observe x) (observe y)
  | equi_later: forall x y, equi x y -> equiF equi (laterF x) (laterF y)
.

Definition equi_ (equi : delay A -> delay A -> Prop) : delay A -> delay A -> Prop :=
  fun d1 d2 => equiF equi (observe d1) (observe d2).

Lemma equiF_mono : Proper (leq ==> leq) equi_.
Proof. monauto. Qed.

Definition equi_mon := Build_mon equiF_mono.

Definition equi := gfp equi_mon.

End Termination.

Notation "x == y" := (equi x y) (at level 70, no associativity).

(* Things we need/would like to be in the coinduction library: *)

Ltac iunfold      := try unfold equi.
Ltac iunfold_in h := try unfold equi in h.

Ltac refold :=
  repeat match goal with
  | |- context[gfp (@equi_mon ?A)]       => fold (@equi A)
  end.
Ltac refold_in h :=
  repeat match type of h with
  | context[gfp (@equi_mon ?A)]       => fold (@equi A) in h
  end.

Ltac to_mon_core :=
  cbn; match goal with
  | |- context[equiF ?R (observe ?t1) (observe ?t2)] =>
      change (equiF R (observe t1) (observe t2)) with (equi_mon R t1 t2)
  | |- context[equiF ?R (?c1 ?a1) (?c2 ?a2)] =>
      change (equiF R (c1 a1) (c2 a2)) with (equi_mon R (go (c1 a1)) (go (c2 a2)))
  | |- context[equiF ?R (?c ?a) (observe ?t2)] =>
      change (equiF R (c a) (observe t2)) with (equi_mon R (go (c a)) t2)
  | |- context[equiF ?R (observe ?t1) (?c ?a)] =>
      change (equiF R (observe t1) (c a)) with (equi_mon R t1 (go (c a)))
  | |- context[terminatesF ?R (observe ?t) ?v] =>
      change (terminatesF R (observe t) v) with (terminates_mon R t v)
  | |- context[terminatesF ?R (?c ?a) ?v] =>
      change (terminatesF R (c a) v) with (terminates_mon R (go (c a)) v)
  end.

Ltac to_mon_in h :=
  cbn; match type of h with
  | context[equiF ?R (observe ?t1) (observe ?t2)] =>
      change (equiF R (observe t1) (observe t2)) with (equi_mon R t1 t2) in h 
  | context[equiF ?R (?c1 ?a1) (?c2 ?a2)] =>
      change (equiF R (c1 a1) (c2 a2)) with (equi_mon R (go (c1 a1)) (go (c2 a2))) in h
  | context[equiF ?R (?c ?a) (observe ?t2)] =>
      change (equiF R (c a) (observe t2)) with (equi_mon R (go (c a)) t2) in h
  | context[equiF ?R (observe ?t1) (?c ?a)] =>
      change (equiF R (observe t1) (c a)) with (equi_mon R t1 (go (c a))) in h 
  | context[terminatesF ?R (observe ?t) ?v] =>
      change (terminatesF R (observe t) v) with (terminates_mon R t v) in h 
  | context[terminatesF ?R (?c ?a) ?v] =>
      change (terminatesF R (c a) v) with (terminates_mon R (go (c a)) v) in h 
  end.

Ltac to_mon :=
  let guard := fresh "guard" in
  assert (guard : True) by constructor;
  intros; to_mon_core; revert_until guard; clear guard.

Ltac step :=
  (match goal with
   | |- context[elem _] => idtac
   | |- _ => iunfold end);
  Delay.Utils.step; try refold.

Tactic Notation "step" "in" ident(h) :=
  iunfold_in h; Delay.Utils.step_in h; repeat red in h; try refold_in h.

Ltac unstep := iunfold; try to_mon; Delay.Utils.unstep; try refold.

Tactic Notation "unstep" "in" ident(h) :=
  iunfold_in h; try to_mon_in h; unstep_in h; try refold_in h.


Tactic Notation "coinduction"
  simple_intropattern(c) simple_intropattern(CIH) :=
  iunfold; coinduction c CIH.

(* /end things we would like to be in the library *)

(** Trivial or useful lemmas about terminates  *)
Lemma T_now {A} (v : A) : terminates (now v) v.
Proof. eapply term_now; reflexivity. Qed.

Lemma T_later {A} (d : delay A) v : terminates d v -> terminates (later d) v.
Proof.
  intro H. eapply term_later. reflexivity. exact H.
Qed.

Lemma terminates_now_val {A} (d : delay A) v w :
  terminates d v -> observe d = nowF w -> v = w.
Proof.
  intros Ht Ho. destruct Ht as [d0 v0 e | d0 d' v0 e Ht'].
  - rewrite e in Ho. inversion Ho. reflexivity.
  - rewrite e in Ho. discriminate.
Qed.

Lemma terminates_obs_eq {A} (a b : delay A) v :
  observe a = observe b -> terminates a v -> terminates b v.
Proof.
  intros Ho Ht. destruct Ht as [d v0 e | d d' v0 e Ht'].
  - eapply term_now. rewrite <- Ho. exact e.
  - eapply term_later. rewrite <- Ho. exact e. exact Ht'.
Qed.

Lemma terminates_later_inv {A} (d d' : delay A) v :
  observe d = laterF d' -> terminates d v -> terminates d' v.
Proof.
  intros Ho Ht. destruct Ht as [d0 v0 e | d0 d0' v0 e Ht'].
  - rewrite Ho in e. discriminate.
  - rewrite Ho in e. inversion e. subst. exact Ht'.
Qed.

Lemma terminates_det {A} : forall (d : delay A) v w,
  terminates d v -> terminates d w -> v = w.
Proof.
  intros d v w Hv. revert w.
  induction Hv as [d v e | d d' v e Hv IH]; intros w Hw;
    destruct Hw as [d0 w0 e0 | d0 d0' w0 e0 Hw0].
  - rewrite e in e0. inversion e0. congruence.
  - rewrite e in e0. discriminate.
  - rewrite e in e0. discriminate.
  - rewrite e in e0. inversion e0. subst. eauto.
Qed.


(** Tour: here we prove a universal property of the chain of equi_mon *)
Global Instance reflexive_equi {A} : forall c : Chain (@equi_mon A),
Reflexive (elem c).
Proof.
  intros c. apply Reflexive_chain; clear c; intros R H.
  red. intros x. icbn.
  destruct (observe x).
  obs_now.
  apply equi_terminates with (v := a).
  apply T_now.
  apply T_now.
  constructor. apply H.
Qed.

(*  *)
Lemma terminates_equi {A} : forall (a : delay A) v,
  terminates a v -> forall b, a == b -> terminates b v.
Proof.
  intros a v Ht. induction Ht as [a v e | a a' v e Ht IH]; intros b Hab;
    step in Hab; inversion Hab as [x y v0 Tx Ty Ex Ey | x y Hxy Ex Ey].
  - assert (terminates x v) as Hxv.
    { eapply term_now. rewrite Ex. exact e. }
    assert (v0 = v) as Hv0.
    { eapply terminates_det. exact Tx. exact Hxv. }
    subst v0.
    eapply terminates_obs_eq. exact Ey. exact Ty.
  - rewrite e in Ex. discriminate.
  - assert (terminates a' v0) as Ha'.
    { eapply terminates_later_inv. 2: exact Tx. rewrite Ex. exact e. }
    assert (v0 = v) as Hv0.
    { eapply terminates_det. exact Ha'. exact Ht. }
    subst v0.
    eapply terminates_obs_eq. exact Ey. exact Ty.
  - assert (a' = x) as Hax.
    { rewrite e in Ex. inversion Ex. reflexivity. }
    subst x.
    eapply term_later. symmetry. exact Ey. apply IH. exact Hxy.
Qed.

Lemma Symmetric_chain {A} : forall (c : Chain (@equi_mon A)),
  forall x y, elem c x y -> elem c y x.
Proof.
  apply (tower (P := fun R => forall x y, R x y -> R y x)).
  - inf_closed_auto.
  - intros c IH a b H. red in H |- *. red in H |- *.
    inversion H; subst; unfold equi_ in *; simpobs.
    + eapply equi_terminates; eauto.
    + eapply equi_later;   eauto.
Qed.

Lemma equi_sym {A} (x y : delay A) : x == y -> y == x.
Proof. apply (Symmetric_chain (chain_gfp (@equi_mon A))). Qed.

Definition equi_comp {A} (x z : delay A) := exists y, x == y /\ y == z.

Lemma equi_trans_comp {A} : forall x z : delay A, equi_comp x z -> x == z.
Proof.
  coinduction c cih.
  intros x z Hc. red in Hc. destruct Hc as [y [Hxy Hyz]].
  pose proof Hxy as Hxy0. pose proof Hyz as Hyz0.
  step in Hxy. step in Hyz.
  inversion Hxy as [x0 y0 v Tx Ty Ex Ey | x0 y0 Hxy' Ex Ey ];
  inversion Hyz as [y1 z1 w Ty2 Tz Ey2 Ez | y1 z1 Hyz' Ey2 Ez ]; subst.
  - assert (terminates x v) as Hx.
    { eapply terminates_obs_eq. exact Ex. exact Tx. }
    assert (terminates z v) as Hz.
    { eapply terminates_equi. eapply terminates_equi. exact Hx. exact Hxy0. exact Hyz0. }
    eapply equi_terminates. exact Hx. exact Hz.
  - assert (terminates x v) as Hx.
    { eapply terminates_obs_eq. exact Ex. exact Tx. }
    assert (terminates z v) as Hz.
    { eapply terminates_equi. eapply terminates_equi. exact Hx. exact Hxy0. exact Hyz0. }
    eapply equi_terminates. exact Hx. exact Hz.
  - assert (terminates z w) as Hz.
    { eapply terminates_obs_eq. exact Ez. exact Tz. }
    assert (terminates x w) as Hx.
    { eapply terminates_equi. eapply terminates_equi. exact Hz.
      apply equi_sym. exact Hyz0. apply equi_sym. exact Hxy0. }
    eapply equi_terminates. exact Hx. exact Hz.
  - assert (y0 = y1) as Hy.
    { congruence. }
    subst y1.
    icbn. 
    rewrite <- Ex, <- Ez. apply equi_later. apply cih.
    exists y0. split. exact Hxy'. exact Hyz'.
Qed.

Lemma equi_trans {A} (x y z : delay A) : x == y -> y == z -> x == z.
Proof. intros Hxy Hyz. apply equi_trans_comp. exists y. split; assumption. Qed.

Lemma equi_refl {A} (x : delay A) : x == x.
Proof. apply (reflexive_equi (chain_gfp (@equi_mon A))). Qed.

Global Instance Equivalence_equi {A} : Equivalence (@equi A).
Proof. constructor. exact equi_refl. exact equi_sym. exact equi_trans. Qed.

Global Instance Proper_equi_equi {A} : Proper (equi ==> equi ==> iff) (@equi A).
Proof.
  intros x x' Hx y y' Hy; split; intro H.
  - eapply equi_trans. eapply equi_trans. apply equi_sym. exact Hx. exact H. exact Hy.
  - eapply equi_trans. eapply equi_trans. exact Hx. exact H. apply equi_sym. exact Hy.
Qed.

Section Strong.
Context {A : Type}.
Inductive seqF (R : delay A -> delay A -> Prop) : delay' A -> delay' A -> Prop :=
| seq_now   : forall v,   seqF R (nowF v)   (nowF v)
| seq_later : forall x y, R x y -> seqF R (laterF x) (laterF y).
Definition seq_ (R : delay A -> delay A -> Prop) d1 d2 := seqF R (observe d1) (observe d2).
Lemma seqF_mono : Proper (leq ==> leq) seq_.
Proof. monauto. Qed.
Definition seq_mon := Build_mon seqF_mono.
Definition seq := gfp seq_mon.
End Strong.
Notation "x ~= y" := (seq x y) (at level 70, no associativity).

Lemma seq_inv {A} (x y : delay A) : x ~= y -> seqF seq (observe x) (observe y).
Proof. intro H. exact (gfp_pfp seq_mon _ _ H). Qed.

Instance seq_refl {A} (x : Chain (@seq_mon A)) : Reflexive (elem x).
Proof.
  tower induction. intros H. intro a. icbn.
  desobs a ah; constructor. apply H.
Qed.

Instance seq_sym {A} : forall (c : Chain (@seq_mon A)), Symmetric (elem c).
Proof.
  intros c.
  tower induction.
  - intros IH a b H. red in H |- *. red in H |- *.
    inversion H; subst; unfold seq_ in *; simpobs; constructor; auto.
Qed.

Lemma seq_symm {A} (x y : delay A) : x ~= y -> y ~= x.
Proof. apply (seq_sym (chain_gfp (@seq_mon A))). Qed.

Lemma seq_obs_eq {A} (x y : delay A) : observe x = observe y -> x ~= y.
Proof.
  intro H. unfold seq. apply (gfp_fp seq_mon).
  icbn. rewrite H.
  destruct (observe y) eqn:E; constructor; apply seq_refl.
Qed.

Lemma seq_equi {A} (x y : delay A) : x ~= y -> x == y.
Proof.
  revert x y. unfold equi. coinduction c cih. intros x y H.
  apply seq_inv in H.
  icbn.
  inversion H as [ v Ex Ey | x' y' Hxy Ex Ey ].
  - to_mon. reflexivity.
  - apply equi_later. apply cih. exact Hxy.
Qed.

Lemma observe_equi {A} (d : delay A) : {| _observe := observe d |} == d.
Proof.
  step. icbn. to_mon. unstep. reflexivity.
Qed.

Lemma terminates_seq {A} : forall (x : delay A) v,
  terminates x v -> forall y, x ~= y -> terminates y v.
Proof.
  intros x v Ht. induction Ht as [x v e | x x' v e Ht IH]; intros y H;
    apply seq_inv in H; rewrite e in H; inversion H; subst.
  - eapply term_now. eauto.
  - eapply term_later. eauto. apply IH. auto.
Qed.

(* Tour: up-to seq *)
Lemma elem_seq_l {A} : forall (c : Chain (@equi_mon A)) x x' y,
  x ~= x' -> elem c x' y -> elem c x y.
Proof.
  intro c. 
  tower induction. 
  - intros IH x x' y Hs H. red in H |- *. red in H |- *.
    pose proof (seq_inv Hs) as Hs'.
    inversion H as [a b v Ta Tb Ea Eb | a b Hab Ea Eb ]; subst.
    + assert (terminates x v) as Hx.
      { eapply terminates_seq. eapply terminates_obs_eq. exact Ea. exact Ta.
        apply seq_symm. exact Hs. }
      assert (terminates y v) as Hy.
      { eapply terminates_obs_eq. exact Eb. exact Tb. }
      eapply equi_terminates. exact Hx. exact Hy.
    + rewrite <- Ea in Hs'.
      inversion Hs' as [ | x0 a0 Hx0 Ex0 Ea0 ]; subst.
      icbn. 
      rewrite <- Ex0, <- Eb. apply equi_later.
      eapply IH. exact Hx0. exact Hab.
Qed.

(* Tour: pretty essential lemma here, proved by coinduction *)
Lemma equi_later_eq {A} : forall d : delay A, later d == d.
Proof.
  (* coinduction: prove stability under `b`, by induction a chain `c` of `b` *)
  coinduction c cih. intros d.
  (* go from `b` to "forced b" (equi_mon to equiF) *)
  icbn. 
  destruct (observe d) as [a | d'] eqn:E.
  - rewrite <- E.
    apply (equi_terminates (x := later d) (y := d) (v := a)).
    + apply T_later. eapply term_now. exact E.
    + eapply term_now. exact E.
  - apply equi_later.
    eapply elem_seq_l with (x' := later d').
    + apply seq_obs_eq.
    (* you get some observe coersions, but not always... *)
      apply E. 
    + apply cih.
Qed.

Lemma equi_char_bwd {A} : forall (x y : delay A),
  (forall v, terminates x v <-> terminates y v) -> x == y.
Proof.
  coinduction c cih. intros x y H.
  destruct (observe x) as [a | x'] eqn:Ex.
  - apply (equi_terminates (x := x) (y := y) (v := a)).
    + eapply term_now. exact Ex.
    + apply H. eapply term_now. exact Ex.
  - destruct (observe y) as [b | y'] eqn:Ey.
    + apply (equi_terminates (x := x) (y := y) (v := b)).
      * apply H. eapply term_now. exact Ey.
      * eapply term_now. exact Ey.
    + icbn. rewrite Ex, Ey.
      apply equi_later. apply cih. intro v. split; intro Ht.
      * eapply terminates_later_inv. exact Ey.
        apply H. eapply term_later. exact Ex. exact Ht.
      * eapply terminates_later_inv. exact Ex.
        apply H. eapply term_later. exact Ey. exact Ht.
Qed.

Lemma equi_char {A} (x y : delay A) :
  x == y <-> (forall v, terminates x v <-> terminates y v).
Proof.
  split.
  - intros Hxy v; split; intro Ht.
    + eapply terminates_equi. exact Ht. exact Hxy.
    + eapply terminates_equi. exact Ht. apply equi_sym. exact Hxy.
  - apply equi_char_bwd.
Qed.

