(** * The delay monad. standalone early prototype (kept as a self-contained
    example; not used by by the rest of the development). *)

CoInductive delay (A: Type) : Type :=
  | now: A -> delay A
  | later: delay A -> delay A.

Arguments now [A].
Arguments later [A].

(** Termination and divergence *)

Inductive terminates {A: Type}: delay A -> A -> Prop :=
  | terminates_now:   forall v, terminates (now v) v
  | terminates_later: forall x v, terminates x v -> terminates (later x) v.

CoInductive diverges {A: Type}: delay A -> Prop :=
  | diverges_later: forall x, diverges x -> diverges (later x).

(** Equitermination *)

Reserved Notation "x == y" (at level 70, no associativity).

CoInductive equi {A: Type}: delay A -> delay A -> Prop :=
  | equi_terminates: forall x y v, terminates x v -> terminates y v -> x == y
  | equi_later: forall x y, x == y -> later x == later y
where "x == y" := (equi x y).

(** The delay monad *)

Definition ret := now.

Definition bind {A B: Type} (x: delay A) (f: A -> delay B) : delay B :=
  let cofix bind x :=
    match x with
    | now v => later (f v)
    | later y => later (bind y)
    end
  in bind x.

(** * The monadic metalanguage *)

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

(** Monadic laws *)

Lemma Mon_law_1: forall (A B: Type) (v: A) (f: A -> mon B),
  run (Bind (Ret v) f) == run (f v). 
Admitted.

Lemma Mon_law_2:
  forall (A: Type) (m: mon A), run (Bind m (@Ret A)) == run m.
Admitted.

Lemma Mon_law_3: forall (A B C: Type) (m: mon A) (f: A -> mon B) (g: B -> mon C),
  run (Bind (Bind m f) g) == run (Bind m (fun x => Bind (f x) g)).
Admitted.

(** The denotation of a [Bind] is the [bind] of the denotations *)

Lemma run_Bind:
forall (A B: Type) (m: mon A) (f: A -> mon B),
  run (Bind m f) == bind (run m) (fun x => run (f x)).
Admitted.
