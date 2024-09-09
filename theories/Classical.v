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
  1:{ firstorder. }
  destruct d.
  - tauto.
  - destruct s. eauto.
Qed.

Definition Cont_M Q A R :=
  forall F : (Q -> A) -> R, ex_modulus_cont F.

Lemma DNS' :
  (forall P Q R : Prop, Cont_M P Q R) ->
  (forall P Q : Prop, (P -> Q) \/ (Q -> P)) ->
  forall P, ~~ P -> P.
Proof.
  intros HC HGD P H.
  specialize (HC (~ P) (~~ P) (~~ P)); red in HC.
  unshelve epose proof (HC _). tauto.
  red in H0.
  unshelve epose proof (H0 _). tauto.
  destruct H1 as [L HL]. red in HL.
  destruct L.
  - cbn in *. 


  destruct d as [f | HH].
  - tauto.
  - tauto.
Qed.

Lemma MP' (f : nat -> bool) :
  (forall P, retract_of P nat -> Cont_M P False False) -> ~~ (exists n, f n = true) -> exists n, f n = true.
Proof.
  cbn. intros HC H.
  unshelve specialize (HC ({ n| f n = true})) as [d Hd].
  firstorder.
  2:{ red. repeat unshelve eexists.
      - apply proj1_sig.
      - intros n. destruct (f n) eqn:E.
        + apply Some. exists n. exact E.
        + apply None.
      - intros. destruct x. cbn.
        generalize ((exist (fun n : nat => f n = true) x)).
        rewrite e. reflexivity. }
  1:{ firstorder. }
  destruct d.
  - tauto.
  - destruct s. eauto.
Qed.

