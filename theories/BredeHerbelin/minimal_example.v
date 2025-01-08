From mathcomp Require Import all_ssreflect.
Require Import extra_principles.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(*We present two Lemmas that, although dual of each other, are such that
 one is provable in Coq and the other does not seem so.
 This entails that Theorem 5 of Brede-Herbelin's paper does not hold
 in its dual version. *)

Section MinEx.

Variable B : Type.


(*We present Downarborification, and Upmonotonisation, dual constructions of each other,
  respectively denotated with (down arrow -) and (up arrow +) in Brede-Herbelin's paper. *)

Definition Downarborification (P : list B -> Type) (u : list B) : Type :=
  forall n, P (take n u).

Inductive Upmonotonisation {C} (T : list C -> Type) : list C -> Type :=
| mon l l' : T l -> Upmonotonisation T (l ++ l').

(*pruning and hereditary_closure are two dual constructions on predicates 
 P : list B -> Type*)

CoInductive pruning (P : list B -> Type) : list B -> Type :=
  prune a u : P u -> pruning P (rcons u a) -> pruning P u.


Inductive hereditary_closure (P : list B -> Type) : list B -> Type  :=
 |hereditary_self : forall u, P u -> hereditary_closure P u
 |hereditary_sons : forall u,
    (forall (b : B), hereditary_closure P (rcons u b)) ->
    hereditary_closure P u.

(*The following Lemma appears in the proof of Theorem 5 from Brede-Herbelin's paper.*)


Lemma pruning_arbor P l :
  (P l -> forall n, P (take n l)) ->
  pruning P l ->
  pruning (Downarborification P) l.
Proof.
  intros HP Hprun ; revert l Hprun HP.
  refine (cofix aux l Hprun :=
            match Hprun as H in pruning _ l0
                  return (P l0 -> forall n, P (take n l0)) -> pruning _ l0 with
            | prune b u Hu Hyp => _
            end).
  intros Htake.
  econstructor.
  { intros n.
    now apply Htake.
  }
  apply aux ; [eassumption |].
  intros Hu' n.
  case: (leqP n (size u)) ; intros Hinf.
  { erewrite <- cats1, takel_cat ; [now apply Htake | assumption]. }
  erewrite <- cats1, take_cat.
  erewrite <- (subnSK Hinf).
  apply ltnW, leq_gtF in Hinf ; rewrite Hinf ; cbn ; rewrite cats1.
  now destruct Hyp.
Qed.


(*We now try to prove the dual of the previous Lemma, in order to prove the dual of 
  Theorem 5 from Brede-Herbelin's paper.*)

Lemma test (P : list B -> Type) l :
  (forall n, P (take n l) -> P l) ->
  hereditary_closure (Upmonotonisation P) l ->
  hereditary_closure P l.
Proof.
  intros HP Hered.
  induction Hered as [u Hu | u k IHk].
  { destruct Hu.
    econstructor ; apply (HP (size l)).
    now rewrite take_size_cat.
  }
  econstructor 2 ; intros b ; apply IHk.
  intros n.
  case: (leqP n (size u)) ; intros Hinf.
  2:{ erewrite <- cats1, take_cat.
      erewrite <- (subnSK Hinf).
      now apply ltnW, leq_gtF in Hinf ; rewrite Hinf ; cbn ; rewrite cats1.
  }
  erewrite <- cats1 , takel_cat ; [ | assumption].
  intros Hn ; apply HP in Hn.
  (*There is no way to derive P (u ++ [:: b])) from the hypotheses.*)
Abort.

End MinEx.