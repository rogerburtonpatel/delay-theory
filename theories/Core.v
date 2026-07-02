Set Implicit Arguments.
Set Contextual Implicit.
Set Primitive Projections.

Section Delay.
Context {A : Type}.

(* Tour 1: start here *)

(* delay: an observe-based encoding (vs the original [now]/[later] constructors);
   [now]/[later] are now notations. *)
Variant delayF (delay : Type) : Type :=
  | nowF (a : A)
  | laterF (d : delay)
  .

CoInductive delay : Type := go { _observe : delayF delay }.

End Delay.

Arguments delay _ : clear implicits.
Arguments delayF _ : clear implicits.


(* necessary(?) observe technology, wish we could do better... *)

Notation delay' A := (delayF A (delay A)).

Definition observe {A} (d : delay A) : delay' A := @_observe A d.

Notation now a := (go (nowF a)).
Notation later d := (go (laterF d)).

Ltac simpobs :=
  repeat match goal with
  | H : observe _ = observe _ |- _ => rewrite <- H in *; clear H
  | H : _ = observe _ |- _ => rewrite <- H in *
  | H : observe _ = _ |- _ => rewrite H in *
  | H : _ = _observe _ |- _ => rewrite <- H in *
  | H : _observe _ = _ |- _ => rewrite H in *
  end.

Ltac desobs t H := destruct (observe t) eqn:H.

Ltac obs_now :=
  match goal with |- context [(nowF ?a)] =>
  replace (nowF a) with (observe (now a)) by reflexivity end.
