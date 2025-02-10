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
move/(_ (fun f => forall n, f n)).
move/dialogue_to_tree_fun_cont/tree_fun_cont_to_self_modulus_cont => [m [Hm _]].
pose f (n : nat) := true.
pose g (n : nat) := n \in m f.
have /Hm e : [seq f i | i <- m f] = [seq g i | i <- m f].
  by apply/eq_in_map=> /= k hk; rewrite /f /g hk.
suffices : ~ (forall n, g n) by apply; rewrite -e.
suffices [k hk] : exists k : nat, k \notin (m f) by move/(_ k); apply/negP.
have [k [_ hk]]:= Notallin (m f).
by exists k; rewrite hk.
Qed.
