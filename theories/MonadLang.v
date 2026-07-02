From Delay Require Import Eq Bind.
From Stdlib Require Import Logic.Eqdep.
Set Implicit Arguments.
Set Contextual Implicit.
Set Primitive Projections.

CoInductive mon (A: Type): Type :=
  | Ret: A -> mon A
  | Bind: forall {B: Type}, mon B -> (B -> mon A) -> mon A
  | Later: mon A -> mon A.

Arguments Ret [A].
Arguments Bind [A B].
Arguments Later [A].

CoFixpoint run {A: Type} (m: mon A) : delay A :=
  match m with
  | Ret v => now v
  | Bind (Ret v) f => later (run (f v))
  | Bind (Bind m f) g => later (run (Bind m (fun x => Bind (f x) g)))
  | Bind (Later m) f => later (run (Bind m f))
  | Later m => later (run m)
  end.

  (* simple unfolding lemmas about observe. needed but annoying. *)
Lemma observe_run_Ret {A} (v : A) : observe (run (Ret v)) = nowF v.
Proof. reflexivity. Qed.
Lemma observe_run_Later {A} (m : mon A) : observe (run (Later m)) = laterF (run m).
Proof. reflexivity. Qed.
Lemma observe_run_Bind {A B} (m : mon A) (f : A -> mon B) :
  observe (run (Bind m f)) =
  match m with
  | Ret v     => laterF (run (f v))
  | Bind m' h => laterF (run (Bind m' (fun x => Bind (h x) f)))
  | Later m'  => laterF (run (Bind m' f))
  end.
Proof. destruct m; reflexivity. Qed.
Lemma observe_run_Bind_later {A B} (m : mon A) (f : A -> mon B) :
  exists d', observe (run (Bind m f)) = laterF d'.
Proof. rewrite observe_run_Bind. destruct m; eexists; reflexivity. Qed.

Lemma run_Ret {A} (a : A) : run (Ret a) == now a.
  Proof. apply seq_equi. apply seq_obs_eq. 
(* now under observe, `run` can reduce... *)
  cbn. reflexivity. Qed.

(* we route termination proofs through `evals`, which 
   tells us what monads "evaluate" to. *)
Inductive evals {A} : mon A -> A -> Prop :=
| evals_ret   : forall v, evals (Ret v) v
| evals_later : forall m v, evals m v -> evals (Later m) v
| evals_bind  : forall B (m : mon B) (h : B -> mon A) v w,
    evals m v -> evals (h v) w -> evals (Bind m h) w.

Ltac ev_inv H :=
  inversion H; subst;
  repeat match goal with
  | E : existT _ _ _ = existT _ _ _ |- _ => apply inj_pair2 in E; subst
  end.

Lemma run_bind_compose {A B} : forall (M : mon A) R,
  evals M R -> forall (g : A -> mon B) w,
  terminates (run (g R)) w -> terminates (run (Bind M g)) w.
Proof.
  intros M R Hev. induction Hev; intros g w' Hh.
  (* here we essentially strip of `later`s *)
  - apply (term_later (d' := run (g v))). reflexivity. exact Hh.
  - apply (term_later (d' := run (Bind m g))). reflexivity. apply IHHev. exact Hh.
  - apply (term_later (d' := run (Bind m (fun x => Bind (h x) g)))). reflexivity.
    apply IHHev1.
    apply IHHev2. exact Hh.
Qed.

Lemma run_evals_bwd {A} : forall (M : mon A) R, evals M R -> terminates (run M) R.
Proof.
  intros M R Hev. induction Hev.
  - apply (term_now (v := v)). reflexivity.
  - apply (term_later (d' := run m)). reflexivity. exact IHHev.
  - eapply run_bind_compose. exact Hev1. exact IHHev2.
Qed.

Lemma run_evals_fwd {A} : forall (D : delay A) R, terminates D R ->
  forall (M : mon A), observe D = observe (run M) -> evals M R.
Proof.
  intros D R Ht. induction Ht as [D R e | D D' R e Ht IH]; intros M HD.
  - rewrite e in HD. destruct M as [v0 | C m' k | m'].
    + rewrite observe_run_Ret in HD. injection HD as ->. apply evals_ret.
    + destruct (observe_run_Bind_later m' k) as [d' Hd']. rewrite Hd' in HD. discriminate.
    + rewrite observe_run_Later in HD. discriminate.
  - rewrite e in HD. destruct M as [v0 | C m' k | m'].
    + rewrite observe_run_Ret in HD. discriminate.
    + rewrite (observe_run_Bind m' k) in HD. destruct m' as [v0 | C2 m'' h'' | m''].
      * injection HD as ->.
        eapply evals_bind. apply evals_ret. apply (IH (k v0)). reflexivity.
      * injection HD as ->.
        specialize (IH (Bind m'' (fun x => Bind (h'' x) k)) eq_refl).
        ev_inv IH. ev_inv H4.
        eapply evals_bind. eapply evals_bind. exact H3. eassumption. eassumption.
      * injection HD as ->.
        specialize (IH (Bind m'' k) eq_refl).
        ev_inv IH.
        eapply evals_bind. apply evals_later. exact H3. exact H4.
    + rewrite observe_run_Later in HD. injection HD as ->.
      eapply evals_later. apply (IH m'). reflexivity.
Qed.

Lemma run_evals {A} (M : mon A) v : terminates (run M) v <-> evals M v.
Proof.
  split.
  - intro H. eapply run_evals_fwd. exact H. reflexivity.
  - apply run_evals_bwd.
Qed.

Lemma evals_Bind {A B} (m : mon A) (f : A -> mon B) w :
  evals (Bind m f) w <-> exists v, evals m v /\ evals (f v) w.
Proof.
  split.
  - intro H. ev_inv H. exists v. split. assumption. assumption.
  - intros [v [Hm Hf]]. eapply evals_bind. exact Hm. exact Hf.
Qed.

Lemma terminates_run_Bind {A B} (m : mon A) (f : A -> mon B) w :
  terminates (run (Bind m f)) w <->
  exists v, terminates (run m) v /\ terminates (run (f v)) w.
Proof.
  rewrite run_evals, evals_Bind.
  split.
  - intros [v [H1 H2]]. exists v. split.
    + apply run_evals. exact H1.
    + apply run_evals. exact H2.
  - intros [v [H1 H2]]. exists v. split.
    + apply run_evals. exact H1.
    + apply run_evals. exact H2.
Qed.


Lemma bind_ret_r {A} (X : delay A) : bind X (fun x => now x) == X.
Proof.
  apply equi_char. intro w. rewrite terminates_bind. split.
  - intros [v [HX Hn]]. pose proof (terminates_now_val Hn eq_refl) as Ev. subst v. exact HX.
  - intro HX. exists w. split.
    + exact HX.
    + apply T_now.
Qed.


(* this proof relies on congruence via termination of 
(bind (run m) (λx. run f x))
and (run (Bind m f)) *)
Lemma run_Bind {A B} (m : mon A) (f : A -> mon B) :
  run (Bind m f) == bind (run m) (fun x => run (f x)).
Proof.
  apply equi_char; intro w. 
  rewrite terminates_bind, terminates_run_Bind. reflexivity.
Qed.

(* this proof is just "move a later" *)
Lemma Mon_law_1 {A B} (v : A) (f : A -> mon B) :
  run (Bind (Ret v) f) == run (f v).
Proof.
  step. 
  (* call `run` through `observe` *)
  icbn.
  unstep. 
  rewrite observe_equi.
  apply equi_later_eq.
Qed.

(* this proof relies on up-to bind of equi, which is nontrivial *)
Lemma Mon_law_2 {A} (m : mon A) : run (Bind m (@Ret A)) == run m.
Proof.
  rewrite run_Bind.
  transitivity (bind (run m) (fun x => now x)).
  - apply bind_cong.
    + reflexivity.
    + intro a. apply run_Ret.
  - apply bind_ret_r.
Qed.

(* this proof is just "move a later" *)
Lemma Mon_law_3 {A B C} (m : mon A) (f : A -> mon B) (g : B -> mon C) :
  run (Bind (Bind m f) g) == run (Bind m (fun x => Bind (f x) g)).
Proof.
  step. icbn. unstep. rewrite observe_equi.
  apply equi_later_eq.
Qed.

(* failing proofs from before without `evals` *)
(* The two attempts below show why the non-[evals] route gets stuck. *)

(* Attempt 1: coinduction on run_Bind directly. *)
Lemma run_Bind__coind {A B} (m : mon A) (f : A -> mon B) :
  run (Bind m f) == bind (run m) (fun x => run (f x)).
Proof.
  revert m f. unfold equi. coinduction c cih. intros m f.
  change (equiF (elem c) (observe (run (Bind m f)))
                         (observe (bind (run m) (fun x => run (f x))))).
  destruct m as [v | C m' h | m'].
  - cbn. apply equi_later. apply (reflexive_equi c).
  - rewrite observe_run_Bind, bind_unfold.
    (* stuck: [run (Bind m' h)] does not reduce for abstract [m'], so the RHS
       [match] is stuck; the only way on is [cih] under [bind] (up-to-bind),
       which is unsound for arbitrary chain elements. *)
    (* note that destructing m' gets us back to the same place. *)
Abort.

(* another attempt via equi *)
Lemma terminates_run_Bind__gen {B} :
  forall (D : delay B) w, terminates D w ->
  forall A (m : mon A) (f : A -> mon B), D == run (Bind m f) ->
  exists v, terminates (run m) v /\ terminates (run (f v)) w.
Proof. 
  intros D w Ht. induction Ht as [D w e | D D' w e Ht IH]; intros A m f HD.
  -  
   (* if run m == now w, then terminates (run m) w *)
   (* if terminates (run Bind m f) w, then 
   terminates run m ?v and terminates (run (f v)) w *)
  (* morally this should be true, but we have little information to 
  go off of because of how `terminates` is defined.  *)
  step in HD. rewrite e in HD. 
  remember (nowF w).
  remember (observe (run (Bind m f))).
  induction HD as [D' | D' D'' w'].
  
  easy. 
  - step in HD. rewrite e in HD. destruct m as [v0 | C m' h | m'].
    + rewrite observe_run_Bind in HD. unstep in HD.
        rewrite 2 equi_later_eq in HD.
        exists v0. split.
        * eapply term_now. reflexivity.
        * eapply terminates_equi. exact Ht. exact HD. 
    + unstep in HD. rewrite observe_equi in HD. 
    rewrite equi_later_eq in HD. 
    specialize (IH _ _ _ HD). 
    exact IH .
    + rewrite observe_run_Bind in HD. unstep in HD.
      rewrite 2 equi_later_eq in HD.
      specialize (IH A m' f HD). destruct IH as [v' [Q1 Q2]].
      exists v'. split.
      * eapply term_later. apply observe_run_Later. exact Q1.
      * exact Q2. 
Abort.
