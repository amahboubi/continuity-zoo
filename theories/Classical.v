Require Import continuity_zoo_Prop.

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
  unshelve specialize (HC ({ n| f n = true})) as [d Hd].
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

