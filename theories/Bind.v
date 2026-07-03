From Delay Require Import Eq.
Set Implicit Arguments.
Set Contextual Implicit.
Set Primitive Projections.

(* Tour 2: *)

(* bind: matches on [observe x] so it reduces for abstract [x]
   (vs the original match on [x]). *)
Definition bind {A B: Type} (x: delay A) (f: A -> delay B) : delay B :=
  (cofix bind (x : delay A) : delay B :=
     go (match observe x with
         | nowF v  => laterF (f v)
         | laterF y => laterF (bind y)
         end)) x.

Lemma bind_unfold {A B} (x : delay A) (f : A -> delay B) :
  observe (bind x f)
  = match observe x with
    | nowF v   => laterF (f v)
    | laterF y => laterF (bind y f)
    end.
Proof. reflexivity. Qed.

Lemma terminates_bind_fwd {A B} (g : A -> delay B) :
  forall (D : delay B) w, terminates D w ->
  forall (X : delay A), observe D = observe (bind X g) ->
  exists v, terminates X v /\ terminates (g v) w.
Proof.
  intros D w Ht. induction Ht as [D w e | D D' w e Ht IH]; intros X HX.
  - rewrite e, bind_unfold in HX. destruct (observe X); discriminate.
  - rewrite e, bind_unfold in HX. destruct (observe X) as [v | y] eqn:EX.
    + injection HX as ->.
      exists v. split.
      * eapply term_now. exact EX.
      * exact Ht.
    + injection HX as ->.
      destruct (IH y eq_refl) as [v [Tyv Tgv]].
      exists v. split.
      * eapply term_later. exact EX. exact Tyv.
      * exact Tgv.
Qed.

Lemma terminates_bind_bwd {A B} (g : A -> delay B) :
  forall X v, terminates X v -> forall w, terminates (g v) w -> terminates (bind X g) w.
Proof.
  intros X v Ht. induction Ht as [X v e | X X' v e Ht IH]; intros w Hgw.
  - eapply term_later. rewrite bind_unfold, e. reflexivity. exact Hgw.
  - eapply term_later. rewrite bind_unfold, e. reflexivity. apply IH. exact Hgw.
Qed.

Lemma terminates_bind {A B} (X : delay A) (g : A -> delay B) w :
  terminates (bind X g) w <-> exists v, terminates X v /\ terminates (g v) w.
Proof.
  split.
  - intro Ht. eapply terminates_bind_fwd. exact Ht. reflexivity.
  - intros [v [HXv Hgw]]. eapply terminates_bind_bwd. exact HXv. exact Hgw.
Qed.

(* notes for Xavier in the comments of these functions. *)


(* up to bind at the chain. 
Note that we must put type quantifier under the [sim] argument of equi_ 
in order for this to work. 
This is a workable solution but somewhat annoying. 
*)
Fail Lemma bind_cong {A B} (x y : delay A) (f g : A -> delay B) (c : Chain equi_mon):
  elem c x y -> (forall a, elem c (f a) (g a)) -> elem c (bind x f) (bind y g).


(* up to bind at the gfp. because equi (the gfp) is type-quantified 
   independently at each instance (not necessarily the same chain, 
   but every chain terminates at the gfp), this works. *)
Lemma bind_cong {A B} (x y : delay A) (f g : A -> delay B) :
  x == y -> (forall a, f a == g a) -> bind x f == bind y g.
Proof.
  intros Hxy Hfg.
  pose proof (proj1 equi_char Hxy) as Hxy'.
  assert (forall a w, terminates (f a) w <-> terminates (g a) w) as Hfg'.
  { intros a. apply (proj1 equi_char). apply Hfg. }
  apply equi_char. intro w. rewrite !terminates_bind. split.
  - intros [v [HX Hf]]. exists v. split.
    + apply (proj1 (Hxy' v)). exact HX.
    + apply (proj1 (Hfg' v w)). exact Hf.
  - intros [v [HX Hf]]. exists v. split.
    + apply (proj2 (Hxy' v)). exact HX.
    + apply (proj2 (Hfg' v w)). exact Hf.
Qed.
