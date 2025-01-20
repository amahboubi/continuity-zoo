Require Import Util continuity_zoo_Prop.

Definition DNE := forall P, ~~ P -> P.

Definition Cont Q A R :=
  forall F : (Q -> A) -> R, dialogue_cont F.

Lemma DNS (P : Prop) :
  Cont P False False -> ~~ P -> P.
Proof.
  intros HC H.
  specialize (HC H) as [d Hd].
  destruct d as [f | HH].
  - tauto.
  - tauto.
Qed.

Definition retract_of X Y :=
  exists I : X -> Y,
  exists R : Y -> option X,
    forall x, R (I x) = Some x.

Lemma MP (f : nat -> bool) :
  (forall P, retract_of P nat -> Cont P False False) -> ~~ (exists n, f n = true) -> exists n, f n = true.
Proof.
  cbn. intros HC H.
  specialize (HC ({ n| f n = true})).
  unshelve edestruct HC as [d Hd].
  2:{ red. repeat unshelve eexists.
      - apply proj1_sig.
      - intros n. destruct (f n) eqn:E.
        + apply Some. exists n. exact E.
        + apply None.
      - intros. destruct x. cbn.
        generalize ((exist (fun n : nat => f n = true) x)).
        rewrite e. reflexivity. }
  1:{ intros F. apply H. intros [n Hn].
      apply F. exists n. assumption. }
  destruct d.
  - tauto.
  - destruct s. eauto.
Qed.

From mathcomp Require Import all_ssreflect.
From mathcomp Require Import zify.
Require Import Lia.

Lemma inconsistent :
  Cont nat bool Prop ->  False.
Proof.
  intros HC. red in HC.
  specialize (HC (fun f => forall n, f n = true)). 
  apply dialogue_to_seq_cont in HC.
  apply seq_cont_to_self_modulus_cont in HC as (m & Hm & _).
  specialize (Hm (fun n => true)).
  cbn in Hm.
  specialize (Hm (fun n => n \in (m (fun _ => true)))). 
  cbn in Hm.
  assert (forall n : nat, (n \in m xpredT) = true) as H.
  - rewrite - Hm.
    1: reflexivity.
    clear Hm ; generalize (m xpredT) as l ; clear m.
    admit.
  - have [n [Hinf Hyp]] := @Notallin (m xpredT).
    specialize (H n).
    rewrite Hyp in H.
    now inversion H.
Admitted.
