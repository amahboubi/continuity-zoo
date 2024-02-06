From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
  
(* Borrrowed from Étienne Miquey's formalization of Brede-Herbelin's LICS 21 paper *)

Section Bars.

Implicit Type A : Type.

(* changed EM's cons into rcons *)
Inductive hereditary_closure A (T : seq A -> Type) : seq A -> Type  :=
 |hereditary_self : forall u, T u -> hereditary_closure T u
 |hereditary_sons : forall u,
    (forall (a : A), hereditary_closure T (rcons u a)) ->
    hereditary_closure T u.

Definition inductively_barred A (T : seq A -> Type) :=
  hereditary_closure T nil.

Definition prefix A (a : nat -> A) (u : seq A) :=
  u = map a (iota 0 (size u)).

Definition barred (A : Type) (T : seq A -> Type) :=
  forall a : nat -> A, {u : seq A & prod (prefix a u) (T u)}.

Definition BI_ind A (T : seq A -> Type) := barred T -> inductively_barred T.

End Bars.
