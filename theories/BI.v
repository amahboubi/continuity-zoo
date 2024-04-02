From mathcomp Require Import all_ssreflect.
Require Import Program.
From Equations Require Import Equations.
Require Import extra_principles.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".

Require Import continuity_zoo_Prop.

Arguments ext_tree {_ _ _}, _ _ _.
Arguments Btree {_ _}, _ _.

Section ContinuousInduction.

Variable O : Type.
Notation I := nat.
Notation A := (seq O).
Implicit Type (F : (I -> O) -> A).

Variable CI : forall F, seq_cont F -> dialogue_cont F.

Definition wf_ext_tree' (tau : ext_tree I O A) :=
  forall alpha : I -> O,
    {n : nat & { a : A & eval_ext_tree tau alpha n = output a}}.

Definition pred_to_ext_tree (P : list O -> bool) : ext_tree I O A :=
  fun l => if P l then output l else ask (size l).

Lemma pred_to_ext_tree_inv1 P l a :
  pred_to_ext_tree P l = output a -> l = a.
Proof.
  unfold pred_to_ext_tree ; intros H.
  case_eq (P l) ; intros Heq ; rewrite Heq in H ; now inversion H.
Qed.

Lemma pred_to_ext_tree_trace_aux
  (P : list O -> bool) (n : nat) (l : list O) (alpha : I -> O) :
      P (l ++ (map alpha (iota (size l) n))) ->
      P (l ++ (map alpha (eval_ext_tree_trace_aux (pred_to_ext_tree P) alpha n l))).
Proof.
  revert l ; induction n ; cbn ; intros l HP ; [assumption |].
  unfold pred_to_ext_tree.
  case_eq (P l) ; cbn ; intros HeqP ; [now rewrite cats0 |].
  rewrite <- cat_rcons ; rewrite <- cat_rcons in HP.
  apply IHn.
  now rewrite size_rcons.
Qed.

Lemma pred_to_ext_tree_trace
  (P : list O -> bool) (n : nat) (alpha : I -> O) :
      P (map alpha (iota 0 n)) ->
      P (map alpha (eval_ext_tree_trace (pred_to_ext_tree P) alpha n)).
Proof.
  now apply pred_to_ext_tree_trace_aux with (l := nil).
Qed.

Lemma barred_pred_wf_ext_tree (P : list O -> bool) :
  barred P -> wf_ext_tree' (pred_to_ext_tree P).
Proof.
  intros H alpha.
  enough (exists n : I, exists a : A, eval_ext_tree (pred_to_ext_tree P) alpha n = output a).
  { admit. }
  specialize (H alpha) as [l [Hpref HP]].
  exists (size l).
  exists (map alpha (eval_ext_tree_trace (pred_to_ext_tree P) alpha (size l))).
  suff: P (map alpha (eval_ext_tree_trace (pred_to_ext_tree P) alpha (size l))).
  { intros H ; unfold pred_to_ext_tree ; unfold prefix in Hpref.
    rewrite eval_ext_tree_map ; now rewrite H. }
  apply pred_to_ext_tree_trace.
  unfold prefix in Hpref ; now rewrite - Hpref.
Admitted.

Definition ext_tree_to_fun (tau : ext_tree I O A) (H : wf_ext_tree' tau) :
  (I -> O) -> A := fun alpha =>  projT1 (projT2 (H alpha)).

Lemma ext_tree_to_fun_seqW tau H :
  seq_cont (@ext_tree_to_fun tau H).
Proof.
  exists tau.
  intros alpha.
  unfold ext_tree_to_fun ; destruct (((H alpha))) as [i [a Ha]] ; cbn.
  now exists i.
Defined.

Fixpoint beval_aux (b : Btree O A) (f : I -> O) (n : nat) {struct b} : A :=
  match b with
  | spit o => o
  | bite k => beval_aux (k (f n)) f (S n)
  end.

Definition beval' b f := beval_aux b f 0.

Lemma beval_ext (b : Btree O A) (f1 f2 : I -> O) :
  (forall x, f1 x = f2 x) -> beval b f1 = beval b f2.
Proof.
  revert f1 f2 ; induction b as [ | k IHk] ; intros * H ; [ reflexivity | ].
  cbn in * ; erewrite  H.
  eapply IHk.
  intros x ; cbn ; now apply H.
Qed.

Lemma beval_beval_aux (b : Btree O A) f k :
  beval b (fun n => f (k + n)) = beval_aux b f k.
Proof.
  revert k f ; induction b as [ | k IHk] ; cbn ; intros ; [reflexivity |].
  specialize (IHk (f k0) (S k0)).
  erewrite <- IHk, <- plus_n_O.
  eapply beval_ext ; cbn.
  intros n ; now erewrite <- plus_n_Sm.
Qed.

Lemma beval_beval' b f : beval b f = beval' b f.
Proof.
  exact (beval_beval_aux b f 0).
Qed.

  (*We define a specific oracle (pref_o l o alpha) that is equal to o for n <= (size l),
   and coincides with alpha everywhere else.*)

Definition pref_o (l : list O) (o : O) (alpha : I -> O) (n : I) :=
  if n <= size l then o else alpha n.

Lemma pref_o_sizel l o : forall alpha, pref_o l o alpha (size l) = o.
Proof.
  intros alpha ; unfold pref_o in *.
  now rewrite leqnn.
Qed.

Lemma pref_o_alpha l o : forall alpha n, size l < n -> pref_o l o alpha n = alpha n.
Proof.
  intros ; unfold pref_o.
  rewrite ltnNge in H ; rewrite (Bool.negb_involutive_reverse (n <= size l)).
  now rewrite H.
Qed.

Lemma pref_o_eval P l l' o : forall alpha n,
    size l < size l' ->
    eval_ext_tree_aux (pred_to_ext_tree P) alpha n l' =
      eval_ext_tree_aux (pred_to_ext_tree P) (pref_o l o alpha) n l'.
Proof.
  intros ; revert l l' o H.
  induction n.
  { cbn ; intros ; reflexivity. }
  intros ; cbn.
  unfold pred_to_ext_tree ; cbn.
  case_eq (P l') ; intros Heq ; [reflexivity |].
  erewrite pref_o_alpha ; [ | eauto].
  eapply IHn.
  erewrite size_rcons ; now eauto.
Qed.

Lemma pref_o_beval b l o n:
  size l < n ->
  forall alpha, beval_aux b (pref_o l o alpha) n =
                  beval_aux b alpha n.
Proof.
  revert l n ; induction b ; intros * Hinf alpha ; [reflexivity |].
  cbn.
  erewrite pref_o_alpha ; [ | assumption].
  eapply H ; now eauto.
Qed.


Proposition CI_BI (P : list O -> bool) :
  barred P -> inductively_barred P.
Proof.
  unfold inductively_barred ; intros HP.
  assert (Hwf:= barred_pred_wf_ext_tree HP) ; clear HP.
  destruct (dialogue_to_btree_cont (CI (ext_tree_to_fun_seqW Hwf))) as [b H].
  assert (ext_tree_to_fun Hwf =1 fun f => beval_aux b f 0) as Hb.
  { intros alpha ; erewrite H ; exact (beval_beval' _ _). }
  clear H.
  revert Hwf Hb.
  unfold ext_tree_to_fun, wf_ext_tree', eval_ext_tree.
  change 0 with (size (@nil O)) ; generalize (@nil O) as l.
  induction b as [ | k IHk].
  { cbn in * ; intros.
    (*Making use of Hwf and Hb, we can extract a uniform n : nat that constitutes
     the maximum number of questions the evaluation of (pred_to_ext_tree P) is
     going to take. We can then conclude by induction on this n.*)
    assert ({n : nat & forall alpha,
                   eval_ext_tree_aux (pred_to_ext_tree P) alpha n l = output a})
      as [n Hyp].
    { exists (size a) ; intros alpha.
      rewrite - (Hb alpha).
      destruct (Hwf alpha) as [n [x Hx]] ; cbn in *.
      assert (Hx' := Hx).
      rewrite eval_ext_tree_map_aux in Hx'.
      eapply pred_to_ext_tree_inv1 in Hx'.
      rewrite <- Hx' at 1.
      rewrite -> size_cat, size_map, PeanoNat.Nat.add_comm.
      eapply eval_ext_tree_monotone.
      now eapply eval_ext_tree_trace_size_eval.
    }
    clear Hb Hwf ; revert l Hyp.
    induction n as [ | n IHn] ; cbn ; intros.
    all: case_eq (P l) ; intros Heq ; [now econstructor |].
    all: unfold pred_to_ext_tree in Hyp ; rewrite Heq in Hyp.
    all:  eapply hereditary_sons ; intros o.
    { specialize (Hyp (fun=> o)) ; now inversion Hyp. }
    change (fun l => if P l then output l else ask (size l))
      with (pred_to_ext_tree P) in Hyp.
    eapply IHn.
    intros alpha.
    rewrite <- (Hyp (pref_o l o alpha)), pref_o_sizel.
    rewrite <- pref_o_eval ; [ | rewrite size_rcons] ; now eauto.
  }
  (*Now comes the recursive case.*)
  cbn in * ; intros.
  case_eq (P l) ; intros eqP.
  { econstructor ; assumption. }
  apply hereditary_sons ; intros o.
  (*We show that the evaluation of pred_to_ext_tree P using
    (pref_o alpha) leads to the same result as when using alpha. *)
  assert (forall alpha,
             {a : A &
                    eval_ext_tree_aux (pred_to_ext_tree P) alpha
                      (projT1 (Hwf (pref_o l o alpha))).-1 (rcons l o) =
                      output a}) as Hyp.
  { intros alpha.
    erewrite (pref_o_eval P (l := l) o) ; [ | erewrite size_rcons ; now eauto].
    clear Hb IHk ; destruct (Hwf (pref_o l o alpha)) as [n Hn].
    destruct Hn as [a Ha].
    destruct n.
    { cbn in * ; unfold pred_to_ext_tree in * ; rewrite eqP in Ha.
      now inversion Ha. }
    unfold pred_to_ext_tree in * ; cbn in * ; rewrite eqP in Ha ; cbn in Ha.
    exists a.
    now erewrite pref_o_sizel in Ha.
  }
  unshelve eapply (IHk o).
  { intros alpha.
    exists (projT1 (Hwf (pref_o l o alpha))).-1.
    now apply Hyp.
  }
  intros alpha ; specialize (Hb (pref_o l o alpha)) ; cbn in *.
  rewrite pref_o_sizel in Hb.
  rewrite size_rcons.
  revert Hb ; generalize (Hyp alpha) ; generalize (Hwf (pref_o l o alpha)).
  clear Hyp Hwf ; intros [n [x Hx]] [y Hy] Hb; cbn in *.
  rewrite - (pref_o_beval _ o (l := l)) ; [ | now eauto].
  rewrite - Hb.
  clear IHk Hb.
  destruct n ; unfold pred_to_ext_tree in * ; cbn in *.
  { rewrite eqP in Hx ; now inversion Hx. }
  rewrite eqP in Hx.
  eapply eval_ext_tree_output_unique ; [eassumption |].
  rewrite pref_o_sizel in Hx.
  pose (H := @pref_o_eval P l (rcons l o) o) ; unfold pred_to_ext_tree in H.
  erewrite <- H in Hx ; [ | erewrite size_rcons ; now eauto].
  eassumption.
Qed.

End ContinuousInduction.

Require Import Brouwer_ext.

Section BarInduction.


  (*The aim of this Section is to prove that Sequential continuity + Bar Induction
   implies Dialogue continuity.*)
Variable BI : forall A T, @BI_ind A T.
Variable O A : Type.
Notation I := nat.
Implicit Type (F : (I -> O) -> A).
Local Notation Bext_tree := (@Bext_tree O A).


Fixpoint Bextree_to_valid (tau : Bext_tree) (l acc : list O) : option A :=
  match l with
  | nil => tau acc
  | cons a q => match tau acc with
                | None => Bextree_to_valid tau q (rcons acc a)
                | Some a => Some a
                end
  end.

Lemma Bextree_to_valid_eq (tau : Bext_tree) k n alpha:
  Bextree_to_valid tau ((map alpha (iota k n))) (map alpha (iota 0 k)) =
    Beval_ext_tree_aux tau alpha n (map alpha (iota 0 k)) k.
Proof.
  revert k ; induction n ; intros ; cbn.
  reflexivity.
  destruct (tau (map alpha (iota 0 k))) ; [reflexivity |].
  erewrite <- map_rcons.
  erewrite iota_rcons.
  now erewrite IHn.
Qed.

Lemma Bextree_to_valid_const (tau : Bext_tree) l1 l2 acc a :
  forall H : Bextree_to_valid tau l1 acc = Some a,
  Bextree_to_valid tau (l1 ++ l2) acc = Some a.
Proof.
  revert l2 acc ; induction l1 ; cbn ; intros.
  1: destruct l2 ; cbn ; [assumption | now rewrite H].
  destruct (tau acc) ; [assumption |].
  now erewrite IHl1.
Qed.

Lemma Bextree_to_valid_id (tau : Bext_tree) l acc  :
  Bextree_to_valid tau (acc ++ l) nil =
    Bextree_to_valid (fun q => Bextree_to_valid tau q nil) l acc.
Proof.
  revert tau acc.
  induction l ; intros ; cbn.
  1: now erewrite List.app_nil_r.
  remember (Bextree_to_valid tau acc [::]) as r ; destruct r.
  + symmetry in Heqr.
    erewrite Bextree_to_valid_const ; try eassumption ; reflexivity.
  + cbn.
    erewrite <- cat_rcons.
    now erewrite IHl.
Qed.

Lemma Bext_tree_to_valid_valid tau f :
  Bvalid_ext_tree (fun l => Bextree_to_valid tau l nil) f.
Proof.
  intros k a H.
  erewrite <- iota_rcons ; cbn.
  erewrite <- cats1.
  erewrite map_cat.
  now eapply Bextree_to_valid_const.
Qed.


Lemma Bseq_cont_to_Bseq_cont_valid F :
  (exists tau : Bext_tree,
           forall alpha, exists n : nat, Beval_ext_tree tau alpha n = Some (F alpha)
   ) ->
  exists tau : Bext_tree,
           (forall alpha, exists n : nat, Beval_ext_tree tau alpha n = Some (F alpha)) /\
             (forall alpha, Bvalid_ext_tree tau alpha).
Proof.
  intros [tau Htau].
  exists (fun l => Bextree_to_valid tau l nil).
  split.
  2: now eapply Bext_tree_to_valid_valid.
  intros alpha ; specialize (Htau alpha) as [n Hn].
  exists n.
  unfold Beval_ext_tree in *.
  change (@nil O) with (map alpha (iota 0 0)).
  rewrite <- Bextree_to_valid_eq.
  erewrite <- Bextree_to_valid_id ; cbn.
  now erewrite Bextree_to_valid_eq .
Qed.

Definition Bvalid_ext_tree2 (tau : Bext_tree) :=
  forall l a,  tau l = Some a -> forall o, tau (rcons l o) = Some a.

Lemma Bvalid_Bvalid2 (tau : Bext_tree) :
  (forall alpha, Bvalid_ext_tree tau alpha) -> Bvalid_ext_tree2 tau.
Proof.
  intros H l a Heq o.
  unfold Bvalid_ext_tree in H.
  specialize (H (from_pref o (rcons l o)) (size l) a).
  unfold from_pref in H.
  do 2 erewrite map_nth_iota0 in H.
  2-4: rewrite size_rcons ; now auto.
  rewrite - (size_rcons l o) take_size in H.
  apply H.
  have aux: forall l o, take (size l) (rcons l o) = l
      by clear ; intros ; induction l ; [reflexivity | cbn ; now rewrite IHl].
  now rewrite aux.
Qed.


Lemma Bseq_cont_valid2_to_dialogue F :
  (exists tau : Bext_tree,
            (forall alpha, exists n : nat, Beval_ext_tree tau alpha n = Some (F alpha)) /\
             (Bvalid_ext_tree2 tau)) ->
  dialogue_cont_Brouwer F.
Proof.
  intros [tau [HF Hvalid]].
  pose (T := fun l => exists a : A, tau l = Some a).
  have Help : barred T.
  { intros alpha.
    specialize (HF alpha) as [n HF].
    unfold prefix ; unfold T.
    unfold Beval_ext_tree in *.
    exists (map alpha (iota 0 (Beval_ext_tree_trace tau alpha n))).
    split.
    1: erewrite size_map ; now erewrite size_iota.
    exists (F alpha).
    unfold Beval_ext_tree in *.
    now erewrite Beval_ext_tree_map_aux in HF.
  }
  eapply BI in Help.
  eapply Sigma1_choice in HF as [HF].
Admitted.

Lemma Bseq_cont_valid_to_dialogue F :
  (exists tau : Bext_tree,
           (forall alpha, exists n : nat, Beval_ext_tree tau alpha n = Some (F alpha)) /\
             (forall alpha, Bvalid_ext_tree tau alpha) ) ->
  dialogue_cont_Brouwer F.
Proof.
  intros [tau [HF Hvalid]].
  eapply Bseq_cont_valid2_to_dialogue.
  exists tau.
  split ; [assumption |].
  now apply Bvalid_Bvalid2.
Qed.

Proposition Bseq_cont_to_Bcont F :
  seq_cont F ->
  dialogue_cont F.
Proof.
  intros H.
  eapply dialogue_cont_Brouwer_to_dialogue_cont.
  eapply Bseq_cont_valid_to_dialogue.
  eapply seq_cont_to_Brouwer in H. destruct H as [b Hb].
  edestruct Bseq_cont_to_Bseq_cont_valid. exists b. eassumption.
  exists x. eassumption.
Qed.

End BarInduction.