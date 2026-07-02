#[global] Set Warnings "-intuition-auto-with-star".

From Coinduction Require Import all.
Require Import Program.Tactics.

Global Tactic Notation "intros !" := repeat intro.

Lemma pfp_gfp {X} {L : CompleteLattice X} (b : mon X): b (gfp b) <= (gfp b).
Proof. apply b_chain. Qed.

Ltac step := match goal with
    | |- context [gfp ?b] => apply (pfp_gfp b)
    | |- context [elem ?R] => first [apply (b_chain R) | apply (gfp_bchain R)]
    end.

Ltac step_in h :=
  match type of h with
  | context [gfp ?b] => apply (gfp_pfp b) in h
  end.

Ltac unstep :=
  match goal with
  | |- context [gfp ?b] => apply (gfp_pfp b)
  end.

Ltac unstep_in h :=
  match type of h with
  | context [gfp ?b] => apply (pfp_gfp b) in h 
  end.

Ltac apply_leq := match goal with
  | [H : _ <= _ |- _]=> intros; apply H
  | [H : leq _ _ |- _]=> intros; apply H
  end.

Ltac induct_on_premise := match goal with
  | H: context [?rel _] |- context [?rel ] => induction H
  end.

Create HintDb mono.
Global Hint Extern 4 => apply_leq : mono.

Ltac monauto := solve
  [ cbv; intros;
    solve [ induct_on_premise; try econstructor; try apply_leq; eauto ] ]
  || fail "`monauto` could not solve this goal.".

Ltac inf_closed_forall_auto := repeat (apply inf_closed_all; intro).
Ltac inf_closed_impl_auto :=
  repeat (apply inf_closed_impl; [intros!; apply_leq; firstorder|]).
Ltac inf_closed_final_auto :=
  solve [repeat intro; try solve [firstorder]; try apply_leq; firstorder].
Ltac inf_closed_auto :=
  repeat (inf_closed_forall_auto || inf_closed_impl_auto || inf_closed_final_auto).

Ltac clear_old_chain := match goal with
  | c : ?T |- forall _ : ?T, _ => clear c; intro c end.
Ltac tower_induction := apply tower; [inf_closed_auto|clear_old_chain].
Tactic Notation "tower" "induction" := tower_induction.

Ltac icbn := repeat red; cbn.
Ltac icbn_in h := repeat red in h; cbn in h.
Tactic Notation "icbn" "in" ident(h) := icbn_in h.

