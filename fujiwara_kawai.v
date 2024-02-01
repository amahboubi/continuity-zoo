Require Import List Lia Arith.
Import ListNotations.

Variable A : Type.
Variable a : A.

Implicit Type Y : (nat -> A) -> nat.
Implicit Types α β : nat -> A.
Implicit Types n : nat.
Implicit Types γ : list A -> bool.
Implicit Types s : list A.

Definition pref α n :=
  map α (seq 0 n).

Definition ext s :=
  fun n => nth n s a.

Definition prep_list s α :=
  fun n => nth n s (α (n - length s)).

Infix "⋆" := prep_list (at level 30).

Definition Cont Y :=
  forall α, exists n, forall β, pref α n = pref β n -> Y α = Y β.

Definition ContL {Q O} (Y : (Q -> A) -> O) :=
  forall α : Q -> A, exists m : list Q, forall β : Q -> A, map α m = map β m -> Y α = Y β.

Definition Mod N Y :=
  forall α β, pref α (N α) = pref β (N α) -> Y α = Y β.

Definition ModL {Q O} (N : (Q -> A) -> list Q) (Y : (Q -> A) -> O) :=
  forall (α β : Q -> A), map α (N α) = map β (N α) -> Y α = Y β.

Definition has_continuous_modulus Y :=
  exists N, Cont N /\ Mod N Y.

Definition has_continuous_modulusL {Q O} (Y : (Q -> A) -> O) :=
  exists N, ContL N /\ ModL N Y.

Definition bar γ :=
  forall α, exists n, γ (pref α n) = true.

Definition monotone γ :=
  forall s s', γ s = true -> γ (s ++ s') = true.

Definition securing γ Y :=
  forall s, γ s = true -> forall β, Y (ext s) = Y (s ⋆ β).

Lemma pref_S α n :
  pref α (S n) = pref α n ++ [α n].
Proof.
  unfold pref. replace (S n) with (n + 1) by lia.
  now rewrite seq_app, map_app.
Qed.

Lemma pref_le_eq n m α β :
  pref α m = pref β m ->
  n <= m ->
  pref α n = pref β n.
Proof.
  intros H (k & -> & Hk) % Nat.le_exists_sub.
  unfold pref in H.
  replace (k + n) with (n + k) in * by lia.
  rewrite seq_app, !map_app in H.
  eapply (f_equal (firstn n)) in H.
  rewrite !firstn_app in H.
  rewrite !map_length, seq_length in H.
  rewrite !minus_diag in H.
  rewrite !firstn_O, !app_nil_r in H.
  rewrite !firstn_all2 in H.
  - assumption.
  - rewrite map_length, seq_length. lia.
  - rewrite map_length, seq_length. lia.
Qed.

Lemma pref_le n m α :
  n <= m ->
  pref α n = pref (ext (pref α m)) n.
Proof.
  intros H.
  unfold pref.
  eapply map_ext_in_iff.
  intros k [_ Hk] % in_seq.
  unfold ext.
  erewrite nth_indep.
  rewrite map_nth, seq_nth.
  - reflexivity.
  - lia.
  - rewrite map_length, seq_length. lia.
    Unshelve. exact 0.
Qed.

Lemma L N :
  Cont N -> forall α, exists n, N (ext (pref α n)) < n.
Proof.
  intros H α. destruct (H α) as [n Hn]. 
  exists (1 + n + N α). rewrite <- Hn.
  lia.
  eapply pref_le. lia.
Qed.

Variable Q : Type.
Variable Q_eq_dec : forall n m : Q, {n = m} + {n <> m}.

Definition extL (α : Q -> A) m :=
  fun x => if in_dec Q_eq_dec x m then α x else a.

Variable O : Type.

Variable embed : O -> Q.

Lemma L' (N : (Q -> A) -> O) :
  ContL N -> forall α : Q -> A, exists m, In (embed (N (extL α m))) m.
Proof.
  intros H α. destruct (H α) as [m Hm]. 
  exists (embed (N α) :: m). rewrite <- Hm.
  firstorder.
  generalize (incl_refl m).
  generalize m at 2 4 as m'.
  clear. induction m.
  - reflexivity.
  - cbn. intros. f_equal. 2: eapply IHm; firstorder congruence.
    unfold extL. destruct in_dec; firstorder.
Qed.

Definition extensional Y :=
  forall α β, (forall n, α n = β n) -> Y α = Y β.

Lemma T12 Y :
  has_continuous_modulus Y -> exists N, Mod N Y /\ forall α, exists n, N (ext (pref α n)) < n.
Proof.
  intros (N & HN & HNY).
  exists N. split. 1: assumption.
  apply L. assumption.
Qed.

Lemma pref_length α n :
  length (pref α n) = n.
Proof.
  unfold pref. now rewrite map_length, seq_length.
Qed.

(* Lemma map_ext [A B : Type] (f g : A -> B) : *)
(*   (forall a : A, f a = g a) -> forall l : list A, map f l = map g l. *)


Lemma T23 Y :
  (exists N, Mod N Y /\ forall α, exists n, N (ext (pref α n)) < n) -> exists γ, securing γ Y /\ bar γ /\ extensional Y.
Proof.
  intros (N & HNY & HN).
  pose (γ := fun s => N (ext s) <? length s).
  exists γ. repeat split.
  - intros s Hs β.
    eapply (HNY (ext s) (s ⋆ β)).
    unfold γ in Hs.
    apply Nat.ltb_lt in Hs.
    unfold pref.
    symmetry.
    eapply map_ext_in_iff.
    intros n [_ H] % in_seq. 
    unfold prep_list.
    unfold ext.
    eapply nth_indep.
    lia.
  - unfold γ. intros α.
    destruct (HN α) as [n Hn].
    exists n. rewrite pref_length. now apply Nat.ltb_lt.
  - intros α β H. eapply HNY.
    unfold pref. now eapply map_ext.
Qed.

Require Import ConstructiveEpsilon.

Lemma T34 γ Y :
  securing γ Y -> bar γ -> extensional Y -> exists N, Mod N Y /\ Mod N N.
Proof.
  intros Hsec Hbar Hext.
  assert (exists N, forall α, γ (pref α (N α)) = true /\
                      (forall k : nat, γ (pref α k) = true -> N α <= k)
         ) as [N HN]. {
    unshelve eexists (fun α => proj1_sig (epsilon_smallest
                                (fun n => γ (pref α n) = true)
                                _
                                (Hbar α))).
    - intros n; cbn. clear.
      destruct γ; firstorder congruence.
    - cbn. intros α.
      destruct epsilon_smallest as [n Hn]. cbn.
      assumption.
  }
  exists N. split.
  - intros α β Hpref. red in Hsec.
    destruct (HN α) as [Hα _].
    pose proof (Hsec _ Hα (fun n => α (n + N α))) as H1.
    rewrite Hpref in Hα.
    pose proof (Hsec _ Hα (fun n => β (n + N α))) as H2.
    unfold prep_list in H1, H2.
    rewrite pref_length in H1, H2.
    rewrite <- Hpref in H2 at 1.
    rewrite H1 in H2.
    enough (forall α m, Y α = Y (fun n => nth n (pref α m) (α (n - m + m)))) as E.
    1: now erewrite E, H2, <- E.
    clear - Hext. intros. eapply Hext. intros.
    destruct (lt_dec n m).
    * unfold pref. symmetry. eapply nth_error_nth.
      erewrite map_nth_error. reflexivity.
      erewrite nth_error_nth'.
      2: now rewrite seq_length.
      now rewrite seq_nth. 
    * rewrite nth_overflow.
      + f_equal. lia.
      + rewrite pref_length. lia.
  - intros α β H.
    assert (N α >= N β). {
      eapply HN.
      rewrite <- H. eapply HN.
    }
    enough (~ N α > N β) by lia.
    intros Hcon.
    eapply pref_le_eq with (n := N β) in H.
    2: lia.
    enough (N α <= N β) by lia.
    eapply HN. rewrite H. eapply HN.
    Unshelve. exact 0.
Qed.

Lemma T41 Y :
  (exists N, Mod N Y /\ Mod N N) -> has_continuous_modulus Y.
Proof.
  intros (N & HN & HNY). exists N. split; auto.
  intros α. exists (N α).
  intros. now eapply HNY.
Qed.

Lemma T41L {Q O} (Y : (Q -> A) -> O) :
  (exists N, ModL N Y /\ ModL N N) -> has_continuous_modulusL Y.
Proof.
  intros (N & HN & HNY). exists N. split; auto.
  intros α. exists (N α).
  intros. now eapply HNY.
Qed.

Lemma T14 Y :
  has_continuous_modulus Y ->
  exists N, Mod N Y /\ Mod N N.
Proof.
  intros (N & HN & HNY).
  assert (exists Z, forall α, N (ext (pref α (Z α))) < (Z α) /\
                      forall m, N (ext (pref α m)) < m ->
                           Z α <= m
         ) as [Z HZ]. {
     unshelve eexists (fun α => proj1_sig (epsilon_smallest
                                _
                                _
                                (L N HN α))).
    - cbn. intros n. eapply lt_dec.
    - cbn. intros α.
      destruct epsilon_smallest as [n Hn]. cbn.
      eapply Hn.
  }
  exists Z. split.
  - intros α β Hpref. 
    destruct (HZ α) as [Hα _].
    assert (H12 : forall α m,
                N (ext (pref α m)) < m ->
               Y (ext (pref α m)) = Y (pref α m ⋆ (fun n => α (n + m)))).
    {
      clear - HNY. intros α m Hα.
      eapply HNY.
      rewrite <- pref_le. 2: lia.
      eapply map_ext_in_iff.
      intros k [H _] % in_seq.
      unfold prep_list.
      rewrite pref_length.
      destruct (lt_dec k m).
      * unfold pref. symmetry. eapply nth_error_nth.
        erewrite map_nth_error. reflexivity.
        erewrite nth_error_nth'.
        2: now rewrite seq_length.
        now rewrite seq_nth. 
      * rewrite nth_overflow.
      + f_equal. lia.
      + rewrite pref_length. lia.
    }
    unshelve epose proof (H12 α (Z α) _) as H1. lia.
    unshelve epose proof (H12 β (Z α) _) as H2.
    { rewrite <- Hpref. lia. }
    unfold prep_list in H1, H2.
    rewrite pref_length in H1, H2.
    rewrite <- Hpref in H2 at 1.
    rewrite H1 in H2.
    enough (forall α m, Y α = Y (fun n => nth n (pref α m) (α (n - m + m)))) as E.
    1: now erewrite E, H2, <- E.
    intros. eapply HNY.
    eapply map_ext_in_iff.
    intros k [H _] % in_seq.
    destruct (lt_dec k m).
    * unfold pref. symmetry. eapply nth_error_nth.
      erewrite map_nth_error. reflexivity.
      erewrite nth_error_nth'.
      2: now rewrite seq_length.
      now rewrite seq_nth. 
    * rewrite nth_overflow.
      + f_equal. lia.
      + rewrite pref_length. lia.
  - intros α β H.
    assert (Z α >= Z β). {
      eapply HZ.
      rewrite <- H. eapply HZ.
    }
    enough (~ Z α > Z β) by lia.
    intros Hcon.
    eapply pref_le_eq with (n := Z β) in H.
    2: lia.
    enough (Z α <= Z β) by lia.
    eapply HZ. rewrite H. eapply HZ.
    Unshelve. all: exact 0.
Qed.

Lemma T14L {Q O} (Y : (Q -> A) -> O) :
  has_continuous_modulusL Y ->
  exists N : (Q -> A) -> list Q, ModL N Y /\ ModL N N.
Proof.
  intros (N & HN & HNY).
Abort.
(* here we now need that Q is enumerable. We already need that Q is discrete, so in summary we're just assuming Q to be a datatype.
   Furthermore, for finite Q continuity is boring, because one can always use the full list of Q.
   So: strengthening to lists makes no sense.
 *)
