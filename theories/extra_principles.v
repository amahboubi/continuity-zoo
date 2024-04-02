From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
  
(* Borrrowed from Étienne Miquey's formalization of Brede-Herbelin's LICS 21 paper *)

Section Bars.

Implicit Type A : Type.

(* changed EM's cons into rcons *)
Inductive hereditary_closure A (T : seq A -> Prop) : seq A -> Prop  :=
 |hereditary_self : forall u, T u -> hereditary_closure T u
 |hereditary_sons : forall u,
    (forall (a : A), hereditary_closure T (rcons u a)) ->
    hereditary_closure T u.

Definition inductively_barred A (T : seq A -> Prop) :=
  hereditary_closure T nil.

Definition prefix A (a : nat -> A) (u : seq A) :=
  u = map a (iota 0 (size u)).

Definition barred (A : Type) (T : seq A -> Prop) :=
  forall a, exists u, prefix a u /\ T u.

Definition BI_ind A (T : seq A -> Prop) := barred T -> inductively_barred T.

End Bars.

Set Bullet Behavior "Strict Subproofs".

Lemma hereditary_closure_Acc {A} T u : 
  @hereditary_closure A T u -> Acc (fun v u => ~ T u /\ exists a, v = rcons u a) u.
Proof.
  induction 1.
  - econstructor. intros. firstorder.    
  - econstructor. intros. destruct H1. destruct H2. subst.
    eapply H0.
Qed.

Lemma hereditary_closure_rect : forall [A : Type] [T : seq A -> Prop],
(forall u, {T u} + {~ T u}) ->
 forall [P : seq A -> Type],
  (forall u : seq A, T u -> P u) ->
  (forall u : seq A,
   (forall a : A, hereditary_closure T (rcons u a)) ->
   (forall a : A, P (rcons u a)) -> P u) ->
  forall l : seq A, hereditary_closure T l -> P l.
Proof.
  intros A T Hdec P Hself Hsons l Hl % hereditary_closure_Acc.
  enough (P l * hereditary_closure T l) by firstorder.
  induction Hl. rename X into IH. 
  destruct (Hdec x).
  - split. auto. now econstructor.
  - split. 
    + eapply Hsons.
      * intros. eapply IH. eauto.
      * intros. eapply IH; eauto.
    + econstructor 2. intros. eapply IH. eauto.
Qed.