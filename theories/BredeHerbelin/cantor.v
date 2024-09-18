Require Import Setoid.

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
