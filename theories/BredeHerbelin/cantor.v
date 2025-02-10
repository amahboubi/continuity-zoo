Require Import Setoid.
From mathcomp Require Import all_ssreflect.


Inductive right_invertible {A B:Type}(f : A->B):Prop :=
| inverse: forall g, (forall b:B, f (g b) = b) -> right_invertible f.


Lemma case_to_false :  forall P : Prop, (P <-> ~P) -> False.
Proof.
  intros P H; apply H.
    - apply <- H.
      intro p.
      apply H; exact p.
    - apply <- H; intro p; apply H; exact p.
Qed.


Theorem cantor :  forall f : nat -> (nat -> bool), ~right_invertible f.
Proof.
  intros f inv.
  destruct inv.
  pose (diag := fun n => negb (f n n)).
  apply case_to_false with (diag (g diag)).
  split.
  - intro I; unfold diag in I.
    rewrite H in I. auto.
    unfold diag.
    intros Hk.
    epose (fze := Bool.andb_negb_l _).
    erewrite I in fze.
    erewrite Hk in fze.
    now inversion fze.
  - intro nI.
    unfold diag in *. rewrite H. auto.
    eapply introN in nI.
    eassumption.
    eapply idP.
Qed.


Theorem Cantor_Prop X (f : (X -> Prop) -> X) :
  ~ (forall x x', f x = f x' -> x = x').
Proof.
  rename f into i. intros HI. pose (p n := forall q, i q = n -> ~ q n).
  enough (Hp : p (i p) <-> ~ p (i p)).
  { clear HI. apply Hp; apply Hp; intros H; now apply Hp. }
  unfold p at 1. split.
  - intros H. apply H. reflexivity.
  - intros H. intros q Hq. apply HI in Hq. subst. apply H.
Qed.

Fact retraction_Lawvere X B :
  (exists f : (X -> B) -> X, exists g,
    forall x, g (f x) = x) ->
  forall I : B -> B, exists b, I b = b.
Proof.
  intros (f & g & H) I.
  pose (h x := I (g x x)).
  exists (g (f h) (f h)).
  enough (g (f h) (f h) = h (f h)) as H1.
  { revert H1. unfold h at 3. congruence. }
  congruence.
Qed.
