From mathcomp Require Import all_ssreflect.
Require Import Program.
From Equations Require Import Equations.
Require Import extra_principles.
Require Import continuity_zoo_Prop.
Require Import Brouwer_ext.
Require Import brede_herbelin.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".


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
  revert l ; induction n as [ | ? IHn]; cbn ; intros l HP ; [assumption |].
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
  barred P -> inhabited (wf_ext_tree' (pred_to_ext_tree P)).
Proof.
  intros H. unfold wf_ext_tree'.
  enough (inhabited (forall alpha : I -> O, {n : I | exists a : A, eval_ext_tree (pred_to_ext_tree P) alpha n = output a})) as Hi.
  { destruct Hi as [Hi]. econstructor.
    intros alpha. destruct (Hi alpha) as [n Hn].
    exists n. destruct eval_ext_tree; eauto. exfalso. now firstorder congruence.
  }
  eapply Delta0_choice.
  {
    intros. destruct eval_ext_tree; firstorder (eauto || congruence).
  }
  intros alpha.
  specialize (H alpha) as [l [Hpref HP]].
  exists (size l).
  exists (map alpha (eval_ext_tree_trace (pred_to_ext_tree P) alpha (size l))).
  suff: P (map alpha (eval_ext_tree_trace (pred_to_ext_tree P) alpha (size l))).
  { intros H ; unfold pred_to_ext_tree ; unfold prefix in Hpref.
    rewrite eval_ext_tree_map ; now rewrite H. }
  apply pred_to_ext_tree_trace.
  unfold prefix in Hpref ; now rewrite - Hpref.
Qed.

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
  revert k f ; induction b as [ | k IHk] ; cbn ; intros k' f; [reflexivity |].
  specialize (IHk (f k') (S k')).
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
  intros alpha n H ; unfold pref_o.
  rewrite ltnNge in H ; rewrite (Bool.negb_involutive_reverse (n <= size l)).
  now rewrite H.
Qed.

Lemma pref_o_eval P l l' o : forall alpha n,
    size l < size l' ->
    eval_ext_tree_aux (pred_to_ext_tree P) alpha n l' =
      eval_ext_tree_aux (pred_to_ext_tree P) (pref_o l o alpha) n l'.
Proof.
  intros alpha n H ; revert l l' o H.
  induction n as [ | ? IHn].
  { cbn ; intros ; reflexivity. }
  intros ? l' ? ?; cbn.
  unfold pred_to_ext_tree ; cbn.
  case_eq (P l') ; intros Heq ; [reflexivity |].
  erewrite pref_o_alpha ; [ | eauto].
  1: eapply IHn.
  erewrite size_rcons ; now eauto.
Qed.

Lemma pref_o_beval b l o n:
  size l < n ->
  forall alpha, beval_aux b (pref_o l o alpha) n =
                  beval_aux b alpha n.
Proof.
  revert l n ; induction b as [ | ? IH] ; intros * Hinf alpha ; [reflexivity |].
  cbn.
  erewrite pref_o_alpha ; [ | assumption].
  eapply IH ; now eauto.
Qed.

Proposition CI_BI (P : list O -> bool) :
  barred P -> inductively_barred P.
Proof.
  unfold inductively_barred ; intros HP.
  assert (Hwf := barred_pred_wf_ext_tree HP); clear HP.
  destruct Hwf as [Hwf].
  destruct (dialogue_to_btree_cont (CI (ext_tree_to_fun_seqW Hwf))) as [b H].
  assert (ext_tree_to_fun Hwf =1 fun f => beval_aux b f 0) as Hb.
  { intros alpha ; erewrite H ; exact (beval_beval' _ _). }
  clear H.
  revert Hwf Hb.
  unfold ext_tree_to_fun, wf_ext_tree', eval_ext_tree.
  change 0 with (size (@nil O)) ; generalize (@nil O) as l.
  induction b as [ a | k IHk].
  { cbn in * ; intros l Hwf Hb.
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
    induction n as [ | n IHn] ; cbn ; intros l Hyp.
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
  1: reflexivity.
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

Lemma Bext_tree_to_valid_valid tau :
  Bvalid_ext_tree (fun l => Bextree_to_valid tau l nil).
Proof.
  intros f k a H.
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
             (Bvalid_ext_tree tau).
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
  Bvalid_ext_tree tau -> Bvalid_ext_tree2 tau.
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

Lemma Beval_ext_tree_output_unique (tau : Brouwer_ext.Bext_tree O A) f l m n1 n2 o1 o2 :
  Beval_ext_tree_aux tau f n1 l m = Some o1 ->
  Beval_ext_tree_aux tau f n2 l m = Some o2 ->
  o1 = o2.
Proof.
  elim: n1 n2 m l => [| n1 ihn1] [ | n2] m l /=.
  all: try by move=> -> [].
  all: case: (tau l) => //; try congruence.
  eapply ihn1.
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
  eapply Delta0_choice in HF as [HF].
  2:{
    intros α n. destruct Beval_ext_tree eqn:E.
    - left. destruct (HF α) as [m].
      f_equal. eapply Beval_ext_tree_output_unique; eauto.
    - firstorder congruence.
  }
  revert Help HF ; unfold inductively_barred, Beval_ext_tree.
  generalize (@nil O) ; intros l Help HF.
  unfold dialogue_cont_Brouwer.
  suff: { b : Btree | forall (alpha : I -> O),
    exists n : I, Beval_ext_tree_aux tau alpha n l 0 = Some (beval b alpha) }.
  { intros [b Hb].
    exists b ; intros alpha; specialize (Hb alpha) as [n Heqn].
    specialize (HF alpha) as [m Heqm].
    unfold Beval_ext_tree in *.
    eapply Beval_ext_tree_output_unique ; eassumption.
  }
  clear HF.
  pattern l.
  eapply hereditary_closure_rect in Help.
  - exact Help.
  - unfold T ; intros u ; destruct (tau u) ; [left ; now exists a | right].
    intros [a Hyp] ; now inversion Hyp.
  - clear l Help.
    intros u Hu ; cbn.
    remember (tau u) as r ; destruct r.
    + exists (spit a) ; intros alpha ; exists 0 ; now cbn.
    + exfalso ; destruct Hu as [a Ha] ; rewrite Ha in Heqr.
      now inversion Heqr.
  - intros u k IHk ; cbn in *.
    unshelve eexists.
    + apply bite ; intros o.
      exact (proj1_sig (IHk o)).
    + cbn.
      intros alpha.
      destruct (IHk (alpha 0)) as [b IHb].
      destruct (IHb (alpha \o succn)) as [n Hn] ; cbn in *.
      exists (S n) ; cbn ; rewrite <- Hn.
      clear -Hvalid.
      remember (tau u) as r ; destruct r.
      * destruct n ; cbn ; [symmetry ; now apply Hvalid |].
        suff: tau (rcons u (alpha 0)) = Some a by (intros Hyp ; now rewrite Hyp).
        now apply Hvalid.
      * generalize 0 ; clear Heqr ; revert alpha u.
        induction n ; [ reflexivity | cbn ; intros alpha u i].
        destruct (tau (rcons u (alpha i))) ; [reflexivity |].
        now eapply IHn.
Qed.

Lemma Bseq_cont_valid_to_dialogue F :
  (exists tau : Bext_tree,
           (forall alpha, exists n : nat, Beval_ext_tree tau alpha n = Some (F alpha)) /\
             Bvalid_ext_tree tau) ->
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
  edestruct Bseq_cont_to_Bseq_cont_valid.
  - exists b. eassumption.
  - exists x. eassumption.
Qed.

End BarInduction.

Section GeneralisedBarInduction.

Variable I : eqType.
Variables O A : Type.
Implicit Type (F : (I -> O) -> A).
Print GBI.
Variable HGBI : forall T, @GBI I O T.

Definition is_fun_list (u : seq (I * O)) :=
  forall i j j', List.In (i, j) u -> List.In (i, j') u -> j = j'.

Lemma is_fun_map (u : seq I) (f : I -> O) :
  is_fun_list [seq (i, f i) | i <- u].
Proof.
  have aux: forall i j, List.In (i, j) [seq (i, f i) | i <- u] -> j = f i.
  { induction u ; intros i j Hij ; [now inversion Hij | cbn in *].
    destruct Hij as [Hyp | Hyp] ; [now inversion Hyp | now apply IHu ].
  }
  intros i j j' Hj Hj'.
  apply aux in Hj, Hj' ; now subst.
Qed.

Lemma is_fun_list_incl (u v : seq (I * O)) :
  is_fun_list v ->
  List.incl u v ->
  is_fun_list u.
Proof.
  intros Hfun Hincl i j j' Hin Hin'.
  apply Hincl in Hin, Hin' ; eapply Hfun ; eassumption.
Qed.

Lemma is_fun_cat_notin_dom (u v : seq (I * O))
  (Hu : is_fun_list u)
  (Hv : is_fun_list v)
  (Hyp : forall i, ~ (List.In i (map fst u)) \/ ~ (List.In i (map fst v))) :
  is_fun_list (u ++ v).
Proof.
  intros i j j' Hinj Hinj'.
  specialize (Hyp i) ; destruct Hyp as [Hnotinu | Hnotinv].
  { suff: List.In (i, j) v.
    { suff: List.In (i, j') v.
      { intros Hinv1 Hinv2 ; apply (Hv i) ; assumption. }
      destruct (List.in_app_or _ _ _ Hinj') ; [ | assumption].
      exfalso ; apply Hnotinu.
      now apply (in_map fst) in H ; cbn in H.
    }
    destruct (List.in_app_or _ _ _ Hinj) ; [ | assumption].
    exfalso ; apply Hnotinu.
    now apply (in_map fst) in H ; cbn in H.
  }
  suff: List.In (i, j) u.
  { suff: List.In (i, j') u.
    { intros Hinu1 Hinu2 ; apply (Hu i) ; assumption. }
    destruct (List.in_app_or _ _ _ Hinj') ; [ assumption | ].
    exfalso ; apply Hnotinv.
    now apply (in_map fst) in H ; cbn in H.
  }
  destruct (List.in_app_or _ _ _ Hinj) ; [ assumption | ].
  exfalso ; apply Hnotinv.
  now apply (in_map fst) in H ; cbn in H.
Qed.
  
  
Lemma is_fun_cons_notin_dom (u : seq (I * O)) (i : I) (o : O)
  (Hu : is_fun_list u)
  (H : ~ (List.In i (map fst u))) :
  is_fun_list ((i,o) :: u).
Proof.
  rewrite - cat1s ; apply is_fun_cat_notin_dom ; [ | assumption | ].
  { intros i' j j' Hinj Hinj' ; cbn in *.
    destruct Hinj as [Heq | ] ; [ inversion Heq ; subst | now exfalso].
    destruct Hinj' as [Heq' | ] ; [ inversion Heq' ; now subst | now exfalso].
  }
  intros i'.
  case: (@eqP I i i') ; [intros Heq ; subst ; now right | intros Hnoteq ; left].
  cbn ; intros [Heq | Hfalse] ; [ now apply Hnoteq | assumption].
Qed.

Lemma is_fun_rcons_notin_dom (u : seq (I * O)) (i : I) (o : O)
  (Hu : is_fun_list u)
  (H : ~ (List.In i (map fst u))) :
  is_fun_list (rcons u (i,o)).
Proof.
  rewrite - cats1 ; apply is_fun_cat_notin_dom ; [ assumption | | ].
  { intros i' j j' Hinj Hinj' ; cbn in *.
    destruct Hinj as [Heq | ] ; [ inversion Heq ; subst | now exfalso].
    destruct Hinj' as [Heq' | ] ; [ inversion Heq' ; now subst | now exfalso].
  }
  intros i'.
  case: (@eqP I i i') ; [intros Heq ; subst ; now left | intros Hnoteq ; right].
  cbn ; intros [Heq | Hfalse] ; [ now apply Hnoteq | assumption].
Qed.  
    


Lemma NoDup_rcons {X : Type} (x : X) (l : seq X) :
  List.NoDup l -> ~ List.In x l -> List.NoDup (rcons l x).
Proof.
  induction 1 as [| a l Hnotina k IHk ]; intros Hnotinx.
  { apply List.NoDup_cons ; [assumption | now econstructor]. }
  rewrite rcons_cons.
  econstructor 2.
  2:{ apply IHk ; intros Hin.
      apply Hnotinx.
      now cbn ; right.
  }
  rewrite <- cats1 ; intros Hin.
  apply List.in_app_or in Hin ; destruct Hin as [Hinl | Hinx] ; [now apply Hnotina |].
  cbn in Hinx ; destruct Hinx as [Heqxq | HFalse] ; [ subst | assumption].
  apply Hnotinx ; now left.
Qed.  

Inductive indbarred_fun_list (T : seq (I * O) -> Prop) : seq (I * O) -> Prop :=
| ieta_fun_list : forall u' u : seq (I * O),
    T u -> List.incl u u' -> is_fun_list u' -> indbarred_fun_list T u'
| ibeta_NoDup : forall (a : I) (v : seq (I * O)),
    ~ List.In a [seq i.1 | i <- v] ->
    (forall b : O, indbarred_fun_list T (v ++ [:: (a, b)])) ->
    indbarred_fun_list T v.



Lemma indbarred_indbarred_fun_list (T : seq (I * O) -> Prop) :
  indbarred T nil ->
  indbarred_fun_list T nil.
Proof.
  have aux: is_fun_list (@nil (I * O)).
  { intros q r r' Hin ; now inversion Hin. }
  revert aux ; generalize (@nil (I * O)) ; intros l Hfun Hyp ; revert Hfun.
  induction Hyp as [u v Hv Hincl | i v Hnotin k IHk ] ; intros.
  { econstructor ; eassumption. }
  econstructor 2 ; [ now apply Hnotin |].
  intros o ; apply IHk.
  rewrite cats1 ; apply is_fun_rcons_notin_dom ; assumption.
Qed.


(*Inductive indbarred_NoDup (T : seq (I * O) -> Prop) : seq (I * O) -> Prop :=
| ieta_NoDup : forall u' u : seq (I * O),
    T u -> List.incl u u' -> List.NoDup (map fst u') -> indbarred_NoDup T u'
| ibeta_NoDup : forall (a : I) (v : seq (I * O)),
    ~ List.In a [seq i.1 | i <- v] ->
    (forall b : O, indbarred_NoDup T (v ++ [:: (a, b)])) -> indbarred_NoDup T v.



Lemma indbarred_indbarred_NoDup (T : seq (I * O) -> Prop) :
  indbarred T nil ->
  indbarred_NoDup T nil.
Proof.
  have aux: List.NoDup (map fst (@nil (I * O))) by (apply List.NoDup_nil).
  revert aux ; generalize (@nil (I * O)) ; intros l HNoDup Hyp ; revert HNoDup.
  induction Hyp as [u v Hv Hincl | i v Hnotin k IHk ] ; intros.
  { econstructor ; eassumption. }
  econstructor 2 ; [ now apply Hnotin |].
  intros o ; apply IHk.
  rewrite cats1.
  rewrite map_rcons ; apply NoDup_rcons ; cbn ; assumption.
Qed.
  
Lemma indbarred_NoDup_indbarred (T : seq (I * O) -> Prop) :
  indbarred_NoDup T nil ->
  indbarred T nil.
Proof.
  generalize (@nil (I * O)) ; intros l ; induction 1.
  { now econstructor ; eassumption. }
  econstructor 2 ; eassumption.
Qed.
*)


Fixpoint eval_list (u : seq (I * O)) (i : I) : option O :=
  match u with
  | nil => None
  | (i', o') :: v => if i == i' then Some o' else eval_list v i
  end.

Fixpoint eval_ext_tree_aux_finapp
  (tau : @ext_tree I O A) (u: seq (I * O)) (n : nat) (l : seq O)
  {struct n} : result :=
  match n with
  | 0 => tau l
  | k.+1 =>
      match tau l with
      | ask q => match eval_list u q with
                 | None => ask q
                 | Some o => eval_ext_tree_aux_finapp tau u k (rcons l o)
                 end
      | output _ => tau l
      end
  end.

Lemma eval_list_In u i o :
  eval_list u i = Some o ->
  List.In (i, o) u.
Proof.
  revert i o ; induction u as [ | [i' o'] v IHv] ; intros i o Heq ; cbn in *.
  { now inversion Heq. }
  case (@eqP I i i') ; [intros Heqi ; subst ; left | intros Hnoteqi].
  { erewrite eq_refl in Heq ; inversion Heq  ; now subst. }
  eapply (introF (b:= i == i') eqP) in Hnoteqi.
  rewrite Hnoteqi in Heq.
  apply IHv in Heq ; now right.
Qed.

  
Lemma In_eval_list u i o :
  is_fun_list u ->
  List.In (i, o) u ->
  eval_list u i = Some o.
Proof.
  revert i o ; induction u as [ | [i' o'] v IHv] ; intros i o Hfun Hin ; cbn in *.
  { now inversion Hin. }
  destruct Hin as [Heq | Hin] ; [inversion Heq ; subst ; now rewrite eq_refl | ].
  case (@eqP I i i') ; [intros Heq ; subst | intros Hnoteq].
  { f_equal.
    eapply Hfun ; [left ; reflexivity | now right ].
  }
  apply IHv ; [ | assumption].
  eapply is_fun_list_incl ; [eassumption | ].
  apply List.incl_tl ; now apply List.incl_refl.
Qed.


Lemma eval_list_In_is_fun u i o :
  is_fun_list u ->
  eval_list u i = Some o ->
  is_fun_list (u ++ [:: (i, o)]).
Proof.
  intros Hfun Heq q a a' Hina Hina'. 
  apply List.in_app_or in Hina, Hina'.
  destruct Hina as [Hina | Heqa].
  2:{ destruct Heqa as [Heqa | Hfalse] ; [ inversion Heqa ; clear Heqa ; subst | now inversion Hfalse].
      destruct Hina' as [Hina' | Heqa']; [ apply In_eval_list in Hina' ; [ | assumption] | ].
      2:{ destruct Heqa' as [Heqa' | Hfalse] ; [ inversion Heqa' ; now subst | now inversion Hfalse]. }
      rewrite Heq in Hina' ; now inversion Hina'.
  }
  destruct Hina' as [Hina' | Heqa'] ; [eapply Hfun ; now eauto | ].
  destruct Heqa' as [Heqa' | Hfalse] ; [ inversion Heqa' ; subst | now inversion Hfalse].
  apply In_eval_list in Hina ; [ | assumption].
  rewrite Heq in Hina ; now inversion Hina.
Qed.  
    
            

Lemma eval_list_notin u q :
  eval_list u q = None ->
  ~ List.In q [seq i.1 | i <- u].
Proof.
  revert q ; induction u as [ | [i' o'] v IHv] ; intros i Heq Hin ; [assumption | ].
  cbn in * ; destruct Hin as [Heq' | Hin] ; [subst | ].
  { rewrite eq_refl in Heq ; now inversion Heq. }
  eapply IHv ; [ | eassumption].
  destruct (i == i') ; [now inversion Heq | assumption].
Qed.

Lemma eval_list_none_fun u q o :
  is_fun_list u ->
  eval_list u q = None ->
  is_fun_list (u ++ [:: (q,o)]).
Proof.
  intros Hfun Hnone ; eapply is_fun_cat_notin_dom ; [assumption | | ].
  -  intros x y y' [Hyp1 | Hyp1] [Hyp2 | Hyp2] ; inversion Hyp1 ; inversion Hyp2 ; now subst.
  - intros i.
    destruct (@eqP I q i) as [Heq | Hnoteq] ; [ subst ; left | ].
    + now apply eval_list_notin.
    + cbn ; right ; intros [Hyp | Hyp] ; now auto. 
Qed.      


Lemma eval_list_notin_cat u v q :
  eval_list u q = None ->
  ~ List.In q [seq i.1 | i <- v] ->
  eval_list (u ++ v) q = None.
Proof.
  revert q v ; induction u as [ | [i o] u IHu] ; intros q v Heq Hnotin.
  - cbn.
    remember (eval_list v q) as aux ; destruct aux as [a | ] ; [ exfalso | reflexivity ].
    suff: List.In (q, a) v ; [intros Hyp | now apply eval_list_In].
    apply Hnotin.
    apply (in_map fst) in Hyp ; now cbn in *.
  - revert Heq ; cbn ; destruct (q == i) ; [now auto | ].
    intros Heq ; now eapply IHu ; eauto.
Qed.

    
Lemma eval_list_monotone (u v : seq (I * O)) (i : I) (o : O) :
  is_fun_list v ->
  List.incl u v ->
  eval_list u i = Some o ->
  eval_list v i = Some o.
Proof.
  intros Hfun Hincl Heq.
  apply In_eval_list ; [assumption | ].
  apply Hincl ; now apply eval_list_In in Heq.
Qed.

Lemma eval_list_incl_none (u v : seq (I * O)) (i : I):
  is_fun_list v ->
  List.incl u v ->
  eval_list v i = None ->
  eval_list u i = None.
Proof.
  intros Hfun Hincl Heq.
  remember (eval_list u i) as aux ; destruct aux as [o | ] ; [ | reflexivity].
  erewrite (eval_list_monotone Hfun Hincl) in Heq ; [eassumption | eauto].
Qed.
  
Lemma eval_ext_tree_aux_finapp_monotone_output_list
  (tau : @ext_tree I O A) (u v: seq (I * O)) (n : nat) (l : seq O) (a : A) :
  is_fun_list v ->
  List.incl u v ->
  eval_ext_tree_aux_finapp tau u n l = output a ->
  eval_ext_tree_aux_finapp tau v n l = output a.
Proof.
  revert u v l a; induction n as [| k IHk] ; intros * Hfun Hincl Heq ; [assumption| ].
  cbn in *.
  remember (tau l) as r ; destruct r as [q | r] ; [ | assumption ].
  remember (eval_list u q) as ev ; destruct ev as [r' | ] ; [| now inversion Heq ].
  erewrite eval_list_monotone ; now eauto.
Qed.

Lemma eval_ext_tree_aux_finapp_monotone_output_fuel
  (tau : @ext_tree I O A) (u: seq (I * O)) (n k : nat) (l : seq O) (a : A) :
  eval_ext_tree_aux_finapp tau u n l = output a ->
  eval_ext_tree_aux_finapp tau u (n + k) l = output a.
Proof.
  revert l ; induction n as [ | n IHn] ; cbn in * ; intros l H.
  1: destruct k ; cbn ; [assumption | now rewrite H].
  destruct (tau l) ; [ | assumption].
  destruct (eval_list u s) ; [ | now inversion H].
  now eapply IHn.
Qed.


Lemma eval_ext_tree_aux_finapp_monotone_ask_list
  (tau : @ext_tree I O A) (u v: seq (I * O)) (n : nat) (l : seq O) (q : I) :
  is_fun_list v ->
  List.incl u v ->
  eval_list v q = None ->
  eval_ext_tree_aux_finapp tau u n l = ask q ->
  eval_ext_tree_aux_finapp tau v n l = ask q.
Proof.
  revert u v l q.
  induction n as [| k IHk] ; intros * Hfun Hincl Hnotin Heq ; [assumption| ].
  cbn in *.
  remember (tau l) as r ; destruct r as [q' | r] ; [ | assumption ].
  remember (eval_list u q') as ev ; destruct ev as [r' | ].
  - erewrite eval_list_monotone ; now eauto.
  - injection Heq ; intros Heq' ; subst.
    remember (eval_list v q) as r' ; destruct r' as [q' | ] ; [ | reflexivity].
    symmetry in Heqr' ; apply eval_list_In, (in_map fst) in Heqr'.
    exfalso ; now inversion Hnotin.
Qed.


Lemma eval_ext_tree_aux_finapp_monotone_ask_list_nomorefuel
  (tau : @ext_tree I O A) (u v: seq (I * O)) (n : nat) (l : seq O) (q : I) (a : O) :
  is_fun_list v ->
  List.incl u v ->
  eval_list u q = Some a ->
  eval_ext_tree_aux_finapp tau u n l = ask q ->
  eval_ext_tree_aux_finapp tau v n l = ask q.
Proof.
  revert u v l q.
  induction n as [| k IHk] ; intros * Hfun Hincl Hnotin Heq ; [assumption| ].
  cbn in *.
  remember (tau l) as r ; destruct r as [q' | r] ; [ | assumption ].
  remember (eval_list u q') as ev ; destruct ev as [r' | ].
  - erewrite eval_list_monotone ; now eauto.
  - injection Heq ; intros Heq' ; subst.
    rewrite Hnotin in Heqev ; now inversion Heqev.
Qed.

Lemma eval_ext_tree_aux_finapp_monotone_ask_fuel
  (tau : @ext_tree I O A) (u : seq (I * O)) (n m : nat) (l : seq O) (q : I) :
  is_fun_list u ->
  eval_list u q = None ->
  eval_ext_tree_aux_finapp tau u n l = ask q ->
  eval_ext_tree_aux_finapp tau u (n + m) l = ask q.
Proof.
  revert u n l q.
  induction n as [| k IHk] ; intros * Hfun Hnotin Heq ; cbn in *.
  - destruct m ; cbn ; [ assumption | now rewrite Heq Hnotin ].
  - destruct (tau l) ; cbn in * ; [ | now inversion Heq ].
    destruct (eval_list u s) ; cbn in * ; [ | assumption].
    now apply IHk.
Qed.

Lemma eval_ext_tree_aux_finapp_one_step_fuel tau u v w l n q a :
  is_fun_list v ->
  is_fun_list w ->
  List.incl u v ->
  List.incl u w ->
  eval_list u q = Some a ->
  eval_ext_tree_aux_finapp tau u n l = ask q ->
  eval_ext_tree_aux_finapp tau v n.+1 l = eval_ext_tree_aux_finapp tau w n.+1 l.
Proof.
  revert u v w l q.
  induction n as [ | n IHn] ; intros * Hfunv Hfunw Hinclv Hinclw Heval Hasku.
  - cbn in *.
    rewrite Hasku.
    now do 2 (erewrite eval_list_monotone ; eauto).
  - cbn in *.
    remember (tau l) as aux ; destruct aux as [i | r] ; subst ; [ | now inversion Hasku].
    remember (eval_list u i) as aux2 ; destruct aux2 as [ o | ].
    2:{ inversion Hasku ; subst.
        rewrite Heval in Heqaux2 ; now inversion Heqaux2.
    }
    now do 2 (erewrite eval_list_monotone ; eauto).
Qed.

Print indbarred_fun_list.

Inductive indbarred_ext_tree (T : seq (I * O) -> Prop) (tau : ext_tree) :
  seq (I * O) -> Prop :=
|  ieta_ext_tree : forall (u' u : seq (I * O)) (r : A),
    T u ->
    List.incl u u' ->
    is_fun_list u' ->
    eval_ext_tree_aux_finapp tau u (size u) nil = output r ->
    eval_ext_tree_aux_finapp tau u' (size u') nil = output r ->
    indbarred_ext_tree T tau u'
| isucc_ext_tree : forall (u : seq (I * O)) (q : I) (a : O),
    is_fun_list u ->
    eval_ext_tree_aux_finapp tau u (size u) nil = ask q ->
    eval_list u q = Some a ->
    indbarred_ext_tree T tau (u ++[:: (q, a)]) ->
    indbarred_ext_tree T tau u
| ibeta_ext_tree : forall (u : seq (I * O)) (q : I),
    is_fun_list u ->
    eval_ext_tree_aux_finapp tau u (size u) nil = ask q ->
    eval_list u q = None ->
    (forall o : O, indbarred_ext_tree T tau (u ++ [:: (q, o)])) ->
    indbarred_ext_tree T tau u.


Print Acc.

Inductive goodRel (tau : ext_tree) : seq (I * O) -> seq (I *O) -> Prop :=
| goodRel_in_dom u i i' o : is_fun_list u ->
                          eval_ext_tree_aux_finapp tau u (size u) nil = ask i ->
                          eval_list u i' = None ->
                          goodRel tau (u ++ [:: (i', o)]) u
| goodRel_notin_dom u i i' o : is_fun_list u ->
                             eval_ext_tree_aux_finapp tau u (size u) nil = ask i ->
                             eval_list u i' = Some o ->
                             goodRel tau (u ++ [:: (i', o)]) u.

Lemma hope (tau : ext_tree) (l : seq (I * O)) :
  indbarred_fun_list
    (fun u => exists n a, eval_ext_tree_aux_finapp tau u n nil = output a) l ->
  Acc (goodRel tau) l.
Proof.
  induction 1 as [v u [n [r Hr]] Hincl Hfun | q v Hnotin _ IHk] ; intros.
  - have aux := eval_ext_tree_aux_finapp_monotone_output_list Hfun Hincl Hr.
    clear u Hr Hincl.
    case (leqP n (size v)).
    { apply (eval_ext_tree_aux_finapp_monotone_output_fuel (size v - n)) in aux.
      intros Hinf ; apply subnK in Hinf.
      rewrite addnC in Hinf ; rewrite Hinf in aux.
      econstructor ; intros u Hu.
      destruct Hu as [u i i' o Hfunu Hask Hnone | u i i' o Hfunu Hask Hsome ].
      1,2: rewrite aux in Hask ; now inversion Hask.
    }
    intros Hinf ; apply leqW in Hinf ; cbn in Hinf ; apply subnK in Hinf.
    rewrite addnC in Hinf ; rewrite - Hinf in aux.
    clear Hinf ; revert r Hfun aux.
    generalize (n - size v) as k ; intros k ; clear n ; revert v.
    induction k as [ | k IHk].
    + intros.
      rewrite addn0 in aux.
      econstructor ; intros u Hu.
      destruct Hu as [ u i i' o Hfunu Hask Hnone | u i i' o Hfunu Hask Hsome ].
      1,2 : rewrite aux in Hask ; now inversion Hask.
    + intros.
      econstructor ; intros u Hu.
      destruct Hu as [u i i' o Hfunu Hask Hnone | u i i' o Hfunu Hask Hsome ].
      * apply (IHk _ r) ; [now apply eval_list_none_fun | ].
        rewrite size_cat addn1 addSn - addnS.
        unshelve eapply (eval_ext_tree_aux_finapp_monotone_output_list _ _ aux).
        -- now apply eval_list_none_fun.
        -- now apply List.incl_appl, List.incl_refl.
      * apply (IHk _ r) ; [ now apply eval_list_In_is_fun | ].
        rewrite size_cat addn1 addSn - addnS.
        unshelve eapply (eval_ext_tree_aux_finapp_monotone_output_list _ _ aux).
        -- now apply eval_list_In_is_fun.
        -- now apply List.incl_appl, List.incl_refl.
  - econstructor ; intros u Hu.
    destruct Hu as [u i i' o Hfunu Hask Hnone | u i i' o Hfunu Hask Hsome ].
Abort.

Unset Elimination Schemes.

Inductive ext_tree_indbarredP (tau : ext_tree) (l: seq (I * O)) : Prop :=
| etree_in : is_fun_list l ->
             ((exists q, eval_ext_tree_aux_finapp tau l (size l) nil = ask q /\
                           eval_list l q = None /\
                           (forall a, ext_tree_indbarredP tau (l ++ [:: (q,a)]))) \/
                
                (exists r, eval_ext_tree_aux_finapp tau l (size l) nil = output r) \/
                
                (exists q a, eval_ext_tree_aux_finapp tau l (size l) nil = ask q /\
                             eval_list l q = Some a /\
                             ext_tree_indbarredP tau (l ++ [:: (q, a)]))) ->
             ext_tree_indbarredP tau l.

Set Elimination Schemes.

Inductive ext_tree_indbarred (tau : ext_tree) (l : seq (I * O)) : Type :=
| ext_tree_eta r : is_fun_list l ->
                   eval_ext_tree_aux_finapp tau l (size l) nil = output r ->
                   ext_tree_indbarred tau l
| ext_tree_succ q a : is_fun_list l ->
                      eval_ext_tree_aux_finapp tau l (size l) nil = ask q ->
                      eval_list l q = Some a ->
                      ext_tree_indbarred tau (l ++ [:: (q, a)]) ->
                      ext_tree_indbarred tau l
| ext_tree_beta q : is_fun_list l ->
                    eval_ext_tree_aux_finapp tau l (size l) nil = ask q ->
                    eval_list l q = None ->
                    (forall a, ext_tree_indbarred tau (l ++ [:: (q,a)])) ->
                      ext_tree_indbarred tau l.

(* econstructor ; [assumption | ].
    right ; left ; exists r.
    eapply eval_ext_tree_aux_finapp_monotone_output_list ; now eauto.
  - econstructor ; [assumption | ].
    right ; right.
    exists q, a ; split ; [ | split ; [eapply eval_list_monotone ; eassumption | ] ].
    2:{ eapply ext_tree_indbarredP_monotone_list ; now eauto. }
    eapply eval_ext_tree_aux_finapp_monotone_ask_list_nomorefuel ; now eauto.
Defined.    *)

Fixpoint ext_tree_indbarredP_rect
  (tau : ext_tree)
  (P : seq (I * O) -> Type)
  (Hout : forall (l : seq (I * O)) (r : A) (Hfun : is_fun_list l)
                 (e : eval_ext_tree_aux_finapp tau l (size l) [::] = output r), 
      P l)
  (Hsucc : forall (l : seq (I * O)) (q : I) (a : O) (Hfun : is_fun_list l)
                 (Heq : eval_ext_tree_aux_finapp tau l (size l) [::] = ask q)
                 (Hnone : eval_list l q = Some a)
                 (e : ext_tree_indbarredP tau (l ++ [:: (q, a)])),
      P (l ++ [:: (q,a) ]) -> P l)
  (Hask : forall (l : seq (I * O)) (q : I) (Hfun : is_fun_list l)
                 (Heq : eval_ext_tree_aux_finapp tau l (size l) [::] = ask q)
                 (Hnone : eval_list l q = None)
                 (e : forall a : O, ext_tree_indbarredP tau (l ++ [:: (q,a)])),
      (forall a : O, P (l ++ [:: (q,a)])) -> P l)
  (l : seq (I * O)) (e : ext_tree_indbarredP tau l) : P l.
Proof.
  destruct e as [Hnodup Hq].
  remember (eval_ext_tree_aux_finapp tau l (size l) [::]) as aux.
  destruct aux as [q | r].
  - remember (eval_list l q) as aux2 ; destruct aux2 as [a | ].
    + suff: ext_tree_indbarredP tau (l ++ [:: (q, a)]).
      { intros Hyp ; eapply Hsucc ; eauto. 
        now apply (ext_tree_indbarredP_rect tau P Hout Hsucc Hask).
      }
      destruct Hq as [[q' [Heq [Hnone Hq']]] | [[r Hr] | [q' [a' [Heq' [Hq' IH]]]]]] ; [ | now inversion Hr |  ].
      * injection Heq ; intros Heqq ; subst.
        rewrite Hnone in Heqaux2 ; now inversion Heqaux2.
      * inversion Heq' ; subst.
        rewrite Hq' in Heqaux2 ; inversion Heqaux2 ; now subst.
    + suff: forall a : O, ext_tree_indbarredP tau (l ++ [:: (q, a)]).
      { intros Hyp.
        eapply (Hask l q Hnodup) ; [now auto | now symmetry | assumption | ] ; intros a.
        apply (ext_tree_indbarredP_rect tau P Hout Hsucc Hask) ; now apply Hyp.
      }
      destruct Hq as [[q' [Heq' Ho]]| [[r Hr] | [q' [a' [Heval [Hsome Hsuc]]]]]] ; [| now inversion Hr | ].
      * inversion Heq' ; subst ; now eapply Ho.
      * exfalso.
        injection Heval ; intros Heq ; subst.
        rewrite Hsome in Heqaux2 ; now inversion Heqaux2.
  - eapply (Hout l r Hnodup).
    destruct Hq as [[q [Heq Ho]]| [[r' Hr] | [q' [a' [Heval _]]]]] ; [ now inversion Heq | | now inversion Heval ].
    inversion Hr ; now subst.
Defined.


Lemma ext_tree_indbarredP_ind
  (tau : ext_tree)
  (P : seq (I * O) -> Prop)
  (Hout : forall (l : seq (I * O)) (r : A) (Hfun : is_fun_list l)
                 (e : eval_ext_tree_aux_finapp tau l (size l) [::] = output r), 
      P l)
  (Hsucc : forall (l : seq (I * O)) (q : I) (a : O) (Hfun : is_fun_list l)
                 (Heq : eval_ext_tree_aux_finapp tau l (size l) [::] = ask q)
                 (Hnone : eval_list l q = Some a)
                 (e : ext_tree_indbarredP tau (l ++ [:: (q, a)])),
      P (l ++ [:: (q,a) ]) -> P l)
  (Hask : forall (l : seq (I * O)) (q : I) (Hfun : is_fun_list l)
                 (Heq : eval_ext_tree_aux_finapp tau l (size l) [::] = ask q)
                 (Hnone : eval_list l q = None)
                 (e : forall a : O, ext_tree_indbarredP tau (l ++ [:: (q,a)])),
      (forall a : O, P (l ++ [:: (q,a)])) -> P l)
  (l : seq (I * O)) (e : ext_tree_indbarredP tau l) : P l.
Proof.
  eapply ext_tree_indbarredP_rect ; eauto.
Qed.  



(*
  (tau : ext_tree)
  (P : forall l : seq (I * O), Type)
       (Hyp : forall (l : seq (I * O)) (q : I) (n : List.NoDup [seq i.1 | i <- l])
          (e : eval_ext_tree_aux_finapp tau l (size l) [::] = ask q)
          (e0 : forall a : O, ext_tree_indbarredP tau ((q, a) :: l)),
        (forall a : O, P ((q, a) :: l)) -> P l)
        (l : seq (I * O)) (e : ext_tree_indbarredP tau l) : P l.
Proof.
  destruct e as [Hnodup Hq].
  remember (eval_ext_tree_aux_finapp tau l (size l) [::]) as aux.
  destruct aux as [q | r].
  - eapply (Hyp l q Hnodup) ; [now auto | | ] ; intros a.
    + destruct Hq as [q' [Heq' Ho]] ; inversion Heq' ; subst.
      now eapply Ho.
    + apply (ext_tree_indbarredP_rect tau P Hyp).
      destruct Hq as [q' [Heq' Ho]] ; inversion Heq' ; subst.
      now apply Ho.
  - exfalso.
    destruct Hq as [q' [Heq' Ho]].
    now inversion Heq'.
Defined.
*)
Lemma ext_tree_indbarred_spec (tau : ext_tree) (l : seq (I * O)) (n : nat) :
  ext_tree_indbarredP tau l ->
  ext_tree_indbarred tau l.
Proof.
  induction 1 as [l a Hnodup Heqa | l q Hnodup Heq ? IHk  | Hsuc].
  - econstructor 1 ; eassumption.
  - econstructor 2 ; eauto. 
  - econstructor 3 ; now eauto.
Qed.

Lemma ext_tree_indbarred_dialogue
  (tau : ext_tree) (Hvalid : valid_ext_tree tau)
  (Hyp : ext_tree_indbarred tau nil) :
  {d : dialogue & forall alpha, exists n, eval_ext_tree tau alpha n = output (deval d alpha)}.
Proof.
  unfold eval_ext_tree.
  revert Hyp ; generalize (@nil (I * O)).
  intros l Hyp ; pattern l.
  induction Hyp.
  - exists (eta r).
    intros alpha ; exists (size l).
    cbn in *.
    admit.
  - assumption.
  - destruct l as [ | [q' o'] v].
    + cbn in *.
      exists (beta q (fun o => projT1 (X o))).
      intros alpha.
      destruct (projT2 (X (alpha q)) alpha) as [n Hn].
      exists n.
      now cbn.
    + exact (X o').
Admitted
              .
(*Lemma indbarred_NoDup_NoDup T l:
  indbarred_NoDup T l ->
  List.NoDup (map fst l).
Proof.
  induction 1 as [ | q v Hnotin k IHk] ; [ assumption | ].
  destruct v as [ | [q' a] v] ; [now econstructor | ].
  specialize (IHk a).
  rewrite map_cat in IHk.
  now apply List.NoDup_remove_1 in IHk ; rewrite -> cats0 in IHk.
Qed.
 *)

Lemma eval_output_indbarredP tau u n r :
  is_fun_list u ->
  eval_ext_tree_aux_finapp tau u n nil = output r ->
  ext_tree_indbarredP tau u.
Proof.
  intros Hfun Hyp.
  case: (leqP n (size u)) ; intros Hinf.
  - apply subnKC in Hinf.
    econstructor ; [assumption | right ; left ].
    exists r ; rewrite - Hinf.
    now apply eval_ext_tree_aux_finapp_monotone_output_fuel.
  - apply leqW in Hinf ; cbn in Hinf ; apply subnKC in Hinf.
    remember (eval_ext_tree_aux_finapp tau u (size u) [::]) as aux ; destruct aux as [q | r'].
    2: econstructor ; [assumption | right ; left ; now exists r'].
    remember (eval_list u q) as aux2 ; destruct aux2 as [ a | ].
    2:{ symmetry in Heqaux ; eapply (eval_ext_tree_aux_finapp_monotone_ask_fuel (n - size u)) in Heqaux ; eauto.
        rewrite Hinf Hyp in Heqaux ; now inversion Heqaux.
    }
    remember (n - size u) as m ; clear Heqm.
    revert n q a u Hfun Hyp Hinf Heqaux Heqaux2 ; induction m as [ | k IHk] ; intros.
    + erewrite <- plus_n_O in Hinf ; subst ; exfalso.
      rewrite Hyp in Heqaux ; now inversion Heqaux.
    + econstructor ; [assumption | ].
      right ; right.
      exists q,a ; split ; [now auto | split ; [now auto | ] ].
      remember (eval_ext_tree_aux_finapp tau (u ++ [:: (q, a)]) (size u + 1) [::]) as aux3.
      destruct aux3 as [q' | r'].
      2:{ econstructor ; [ now apply eval_list_In_is_fun | ].
          right ; left ; exists r' ; now rewrite size_cat. }
      remember (eval_list u q') as aux4.
      destruct aux4 as [a' | ].
      { apply (IHk n q' a') ; eauto.
        * now apply eval_list_In_is_fun.
        * eapply eval_ext_tree_aux_finapp_monotone_output_list ;
            [ now apply eval_list_In_is_fun | | eassumption ].
          now apply List.incl_appl, List.incl_refl.
        * now rewrite <- Hinf, size_cat, <- plus_n_Sm, addn1, plus_Sn_m.
        * now rewrite size_cat.
        * symmetry ; eapply eval_list_monotone ; eauto ; [ now apply eval_list_In_is_fun | ].
          now apply List.incl_appl, List.incl_refl.
      }
      exfalso.
      rewrite <- Hinf, <- plus_n_Sm, <- plus_Sn_m in Hyp.
      erewrite eval_ext_tree_aux_finapp_monotone_ask_fuel in Hyp ; eauto ; [now inversion Hyp | ].
      eapply eval_ext_tree_aux_finapp_monotone_ask_list ; eauto ; [ | now rewrite Heqaux3 addn1].
      apply List.incl_app ; [now apply List.incl_refl | ].
      intros [x y] [Hin | Hfalse] ; [ inversion Hin ; subst | now eauto].
      now apply eval_list_In.
Qed.      


Lemma indbarred_fun_list_fun_list T l:
  indbarred_fun_list T l ->
  is_fun_list l.
Proof.
  induction 1 as [ | q v Hnotin k IHk] ; [ assumption | ].
  destruct v as [ | [q' a] v];  [intros ??? Hin ; now inversion Hin | ].
  specialize (IHk a).
  eapply is_fun_list_incl ; [eassumption | ].
  now apply List.incl_appl, List.incl_refl.
Qed.


Fixpoint ext_tree_indbarredP_monotone tau u v
  (Hu : ext_tree_indbarredP tau u) {struct Hu}:
  is_fun_list v ->
  List.incl u v ->
  ext_tree_indbarredP tau v.
Proof.
  intros Hfunv Hincl.
  destruct Hu as [Hfunu Hyp].
  destruct Hyp as [[q [Heq [Hnone Hq]]]| [[r Hr] | [q [a [Heval [Hsome Hsuc]]]]]].
  - remember (eval_list v q) as aux ; destruct aux as [ a | ].
    + apply (ext_tree_indbarredP_monotone tau _ _ (Hq a) Hfunv).
      apply List.incl_app ; [assumption | ].
      intros [q' o'] [Hyp | Hyp] ; inversion Hyp; subst.
      now apply eval_list_In.
    + suff: forall (a : O) w, List.incl (v ++ [:: (q, a)]) w ->
                              is_fun_list w ->
                              ext_tree_indbarredP tau w.
      2:{ intros a w Hincl' Hfun' ; apply (ext_tree_indbarredP_monotone tau _ _ (Hq a) Hfun').
          eapply List.incl_tran ; [ | eassumption].
          apply List.incl_app ; [now apply List.incl_appl | apply List.incl_appr].
          now apply List.incl_refl.
      }
      intros Hyp.
      case: (leqP (size u) (size v)) ; intros Hinf.
      * apply subnKC in Hinf.
        econstructor ; [assumption | ].
        left ; exists q ; split ; [ | split ; [now auto | ] ].
        2:{ intros a ; apply (Hyp a) ; [now apply List.incl_refl | ].
            rewrite cats1 ; apply is_fun_rcons_notin_dom ; [assumption | ].
            now apply eval_list_notin.
        }
        rewrite - Hinf.
        erewrite (eval_ext_tree_aux_finapp_monotone_ask_fuel (size v - size u)) ; eauto.
        eapply eval_ext_tree_aux_finapp_monotone_ask_list ; now eauto.
      * apply leqW in Hinf ; cbn in Hinf ; apply subnKC in Hinf ; rewrite - Hinf in Heq.
        remember (size u - size v) as n ; clear Heqn.
        revert u v Hinf Hincl Hfunu Hfunv Hnone Hq Heq Heqaux Hyp.
        induction n ; cbn ; intros.
        { rewrite <- plus_n_O in Hinf, Heq.
          econstructor ; [assumption | ].
          left ; exists q ; split ;
            [now eapply eval_ext_tree_aux_finapp_monotone_ask_list ; eauto | ].
          split ; [now eauto | ].
          intros a ; apply (Hyp a) ; [now apply List.incl_refl | ].
          rewrite cats1 ; apply is_fun_rcons_notin_dom ; [assumption | ].
          now apply eval_list_notin.
        }
        remember (eval_ext_tree_aux_finapp tau v (size v) [::]) as auxv ; destruct auxv as [q' | ].
        2:{ eapply eval_ext_tree_aux_finapp_monotone_ask_list in Heq ; eauto.
            symmetry in Heqauxv.
            eapply (eval_ext_tree_aux_finapp_monotone_output_fuel n.+1) in Heqauxv ; eauto.
            rewrite Heq in Heqauxv ; now inversion Heqauxv.
        }
        case: (@eqP I q q') ; [intros Heqq ; subst | intros Hnoteq].
        -- econstructor ; [assumption | ].
           left ; exists q' ; split ; [now auto | split ; [now trivial | ]].
           intros a ; apply (Hyp a) ; [now apply List.incl_refl | ].
           rewrite cats1 ; apply is_fun_rcons_notin_dom ; [assumption | ].
           now apply eval_list_notin.
        -- econstructor ; [assumption | ].
           remember (eval_list v q') as auxv ; destruct auxv as [ a| ].
           { right ; right.
             exists q', a ; split ; [now auto | split ; [now auto | ] ].
             apply (IHn u) ; eauto.
             ++ rewrite size_cat ; cbn ; now rewrite -> addn1, plus_Sn_m, plus_n_Sm.
             ++ now apply List.incl_appl.
             ++ now apply eval_list_In_is_fun.
             ++ now rewrite size_cat ; cbn ; rewrite -> addn1, plus_Sn_m, plus_n_Sm.
             ++ symmetry ; apply eval_list_notin_cat ; [now auto | cbn].
                intros [Heq' | Hfalse] ; [ subst | now inversion Hfalse].
                now apply Hnoteq.
             ++ intros a' w Hincl' Hfunw.
                apply (Hyp a') ; [ | assumption].
                eapply List.incl_tran ; [ | eassumption].
                apply List.incl_app ; [do 2 apply List.incl_appl ; now apply List.incl_refl | ].
                now apply List.incl_appr, List.incl_refl.
           }
           left.
           exists q' ; split ; [now auto | split ; [now auto | ] ].
           intros a.
           eapply (IHn u) ; eauto.
           ++ rewrite size_cat ; cbn ; now rewrite -> addn1, plus_Sn_m, plus_n_Sm.
           ++ now apply List.incl_appl.
           ++ rewrite cats1 ; apply is_fun_rcons_notin_dom ; [assumption | ].
              now apply eval_list_notin.
           ++ now rewrite <- Heq, size_cat, <- plus_n_Sm, <- plus_Sn_m, addn1.
           ++ symmetry ; apply eval_list_notin_cat ; [now auto | cbn].
              intros [Heq' | Hfalse] ; [ subst | now inversion Hfalse].
              now apply Hnoteq.
           ++ intros a' w Hincl' Hfunw.
              apply (Hyp a') ; [ | assumption].
              eapply List.incl_tran ; [ | eassumption].
              apply List.incl_app ; [do 2 apply List.incl_appl ; now apply List.incl_refl | ].
              now apply List.incl_appr, List.incl_refl.
  - eapply eval_output_indbarredP ; [eassumption | ].
    eapply eval_ext_tree_aux_finapp_monotone_output_list ; eassumption.
  - apply (ext_tree_indbarredP_monotone _ _ _ Hsuc Hfunv).
    apply List.incl_app ; [assumption | ].
    intros [x y] [Hin | Hfalse] ; [ inversion Hin ; subst | now inversion Hfalse].
    now apply Hincl, eval_list_In.
Defined.    

Print eval_ext_tree_aux_finapp.

Fixpoint eval_ext_tree_aux_finapp_minimal_list
  (tau : ext_tree (R := A)) (u : seq (I * O)) (n : nat) (l : seq O) {struct n} :
    seq (I * O) :=
  match n, tau l with
  | 0, _ => [::]
  | _, output _ => [::]
  | k.+1, ask q => match eval_list u q with
                   | None => [::]
                   | Some o => (q, o) :: eval_ext_tree_aux_finapp_minimal_list tau u k (rcons l o)
                   end
  end.

Print List.Add.

Lemma Add_rcons {X : Type} (a : X) (l : seq X): List.Add a l (rcons l a).
Admitted.

Lemma Add_cat {X : Type} (a : X) (u v w : seq X) :
  List.Add a u v ->
  List.Add a (u ++ w) (v ++ w).
Admitted.

Lemma Add_diamond {X : Type} (x y : X) (u v w l : seq X) :
  List.Add x u v -> List.Add y v l -> List.Add x w l -> List.Add y u w.
Admitted.


Lemma super (tau : ext_tree) (u v : seq (I * O)) (i : I) (o : O) :
  eval_list u i = None ->
  List.Add (i,o) u v ->
  (ext_tree_indbarredP tau v) ->
  (forall a w, List.Add (i, a) u w ->
               ext_tree_indbarredP tau w) ->
  ext_tree_indbarredP tau u.
Proof.
  intros Hnone Hadd Hv Hyp.
  have Hincl : List.incl u v.
  { intros x Hin ; eapply List.Add_in ; [eassumption | now right]. }
  revert u Hincl Hnone Hadd Hyp.
  induction Hv as [l a Hnodup Heqa | l q o' Hfunl Heq Hsome k IHk |
                    l q Hfunl Heq Hnonel k IHk] ; intros.
  - have Hfunu : is_fun_list u.
    { eapply is_fun_list_incl ; eassumption. } 
    have Heq: (size l = (size u).+1) by (eapply List.Add_length ; eassumption).
    rewrite Heq in Heqa.
    remember (eval_ext_tree_aux_finapp tau u (size u) nil) as aux.
    destruct aux as [q' | r].
    2: econstructor ; [ assumption | right ; left ; now exists r].
    remember (eval_list u q') as aux2 ; destruct aux2 as [a' | ].
    + econstructor ; [assumption | right ; right ; exists q', a' ].
      split ; [now auto | split ; [now auto | ] ].
      remember (eval_ext_tree_aux_finapp tau (u ++ [:: (q', a')]) (size u).+1 [::])
        as aux3.
      destruct aux3 as [q'' | r'].
      2:{ econstructor ; [ now apply eval_list_In_is_fun | ].
          right ; left ; exists r' ; now rewrite size_cat addn1.
      }
      econstructor ; [now apply eval_list_In_is_fun | right ; left ].
      exists a ; rewrite size_cat addn1 - Heqa.
      eapply (eval_ext_tree_aux_finapp_one_step_fuel) ; eauto.
      * now apply eval_list_In_is_fun.
      * now apply List.incl_appl, List.incl_refl.
    + destruct (@eqP I q' i) as [Heq' | Hnoteq] ; [subst | ].
      * econstructor ; [assumption | ].
        left ; exists i ; split ; [auto | split ; [assumption | ] ].
        intros a' ; apply (Hyp a').
        rewrite cats1 ; now apply Add_rcons.
      * exfalso.
        suff: eval_ext_tree_aux_finapp tau l (size u).+1 [::] = ask q'.
        {intros Heq' ; rewrite Heq' in Heqa ; now inversion Heqa. }
        suff: eval_list l q' = None.
        { intros Hnonel.
          rewrite - addn1 ; apply eval_ext_tree_aux_finapp_monotone_ask_fuel ; auto .
          now eapply eval_ext_tree_aux_finapp_monotone_ask_list ; eauto.
        }
        suff: eval_list (u ++ [::(i,o)]) q' = None.
        { intros Hnoneu.
          eapply eval_list_incl_none with (u ++ [:: (i, o)]) ; eauto.
          * now apply eval_list_none_fun.
          * intros x Hinx.
            eapply (List.Add_in Hadd) in Hinx.
            destruct Hinx as [Hl | Hr] ; apply List.in_or_app ; [right | ] ; now left.
        }
        apply eval_list_notin_cat ; [now auto | cbn].
        intros [Heqi | Hfalse] ; auto.
  - have Hfunu : is_fun_list u by (eapply is_fun_list_incl ; eassumption).
    have Heqsize : size l = (size u).+1 by (eapply List.Add_length ; eassumption).
    rewrite Heqsize in Heq.
    remember (eval_ext_tree_aux_finapp tau u (size u) nil) as aux.
    destruct aux as [q' | r].
    2: econstructor ; [ auto | right ; left ; now exists r ].
    remember (eval_list u q') as aux2 ; destruct aux2 as [a | ].
    + econstructor ; [ auto | ].
      right ; right ; exists q',a.
      split ; [now auto | split ; [now auto | ] ].
      remember (eval_ext_tree_aux_finapp tau (u ++[:: (q', a)]) (size (u ++ [:: (q', a)])) nil)
        as aux3.
      destruct aux3 as [q'' | r].
      2: econstructor ; [ now apply eval_list_In_is_fun | right ; left ; now exists r ].
      suff: q'' = q.
      2:{ suff: ask (R:= A) q'' = ask q ; [ intros H ; now inversion H | ].
          rewrite Heqaux3 - Heq size_cat addn1.
          erewrite (eval_ext_tree_aux_finapp_one_step_fuel (u := u) (v := l)) ; eauto.
          * now apply eval_list_In_is_fun.
          * apply List.incl_appl, List.incl_refl.
      }
      intros H ; subst.
      remember (eval_list u q) as aux4 ; destruct aux4 as [a' | ].
      * have auxeq : o' = a'.
        { suff : Some o' = Some a' by (intros H ; now inversion H).
          rewrite - Hsome ; eapply eval_list_monotone ; eauto.
        }
        subst.
        have auxeval : eval_list (u ++ [:: (q', a)]) q = Some a'.
        { eapply eval_list_monotone with u ; [now apply eval_list_In_is_fun | | eauto ].
          now apply List.incl_appl, List.incl_refl.
        }
        econstructor ; [now apply eval_list_In_is_fun | right ; right ].
        exists q, a' ; split ; [auto | split ; [ auto | ] ].
        suff: ext_tree_indbarredP tau (u ++ [::(q,a')]).
        { intros H ; apply (ext_tree_indbarredP_monotone H).
          + apply eval_list_In_is_fun ; [ now apply eval_list_In_is_fun | auto ].
          + apply List.incl_app ; [ | now apply List.incl_appr, List.incl_refl].
            do 2 apply List.incl_appl ; now apply List.incl_refl.
        }
        destruct (@eqP I i q) as [e | n] ; [ subst | ].
        { rewrite - Heqaux4 in Hnone ; now inversion Hnone. }
        unshelve eapply IHk.
        -- apply List.incl_app ; [now apply List.incl_appl | ].
           apply List.incl_appr, List.incl_refl.
        -- apply eval_list_notin_cat ; [assumption | ].
           cbn ; intros [Hfalse | Hfalse] ; [ | now inversion Hfalse].
           now apply n.
        -- now apply Add_cat.
        -- intros o' w Haddw.
           suff: ext_tree_indbarredP tau (u ++ [::(i, o')]).
           { intros H ; unshelve eapply (ext_tree_indbarredP_monotone H).
             + eapply is_fun_list_incl with ((u ++ [:: (q, a')]) ++ [::(i, o')]).
               { apply eval_list_none_fun ; [ now apply eval_list_In_is_fun | ].
                 eapply eval_list_incl_none with u ; eauto.
                 apply List.incl_app ; [now apply List.incl_refl | ].
                 apply List.incl_cons ; [ | now apply List.incl_nil_l].
                 now apply eval_list_In.
               }
               intros y Hiny ; apply (List.Add_in Haddw) in Hiny.
               destruct Hiny as [Hiny | Hiny] ; [subst | ].
               ++ apply List.in_or_app ; right ; now left.
               ++ apply List.in_or_app ; now left.
             + intros x Hin ; eapply List.Add_in ; [eassumption | ].
               destruct (List.in_app_or _ _ _ Hin) as [Hin2 | Hin2] ; [right | ].
               * now apply List.in_or_app ; left.
               * destruct Hin2 as [Hin2 | Hin2] ; inversion Hin2 ; now left.
           }
           eapply (Hyp o').
           rewrite <- cat1s, <- (cats0 u) at 1.
           apply List.Add_app.
      * have auxeval : eval_list (u ++ [:: (q', a)]) q = None.
        { eapply eval_list_incl_none with u ; eauto.
          apply List.incl_app ; [now apply List.incl_refl | ].
          intros x [Hinx | Hinx] ; inversion Hinx.
          now apply eval_list_In.
        }
        econstructor ; [ now apply eval_list_In_is_fun | left].
        exists q ; split ; [ now auto | split ; [ auto | ] ].
        intros a'.
        suff: ext_tree_indbarredP tau (u ++ [::(q, a')]).
        { intros H ; unshelve eapply (ext_tree_indbarredP_monotone H).
          + rewrite cats1 ; apply is_fun_rcons_notin_dom.
            * now apply eval_list_In_is_fun.
            * now apply eval_list_notin.
          + apply List.incl_app ; [ | now apply List.incl_appr,List.incl_refl].
            do 2 apply List.incl_appl ; now apply List.incl_refl.
        }
        destruct (@eqP I q i) as [Heqi | Hnoteq] ; [subst | exfalso ].
        -- apply (Hyp a').
           rewrite cats1 ; now apply Add_rcons.
        -- suff: eval_list l q = None by (intros H ; rewrite H in Hsome ; now inversion Hsome).
           eapply eval_list_incl_none with (u ++ [::(i, o)]).
           ++ now apply eval_list_none_fun.
           ++ intros x Hinx ; eapply (List.Add_in Hadd) in Hinx.
              destruct Hinx as [Hinx | Hinx] ; eapply List.in_or_app ; [| now left].
              right ; now left.
           ++ eapply eval_list_notin_cat ; auto ; cbn.
              intros [Hin | Hin] ; inversion Hin ; now auto.
    + destruct (@eqP I q' i) as [Heqi | Hnoteq] ; [subst | exfalso ].
      * econstructor ; [assumption | left].
        exists i ; split ; [auto | split ; [auto | ] ].
        intros a ; apply (Hyp a).
        rewrite cats1 ; now apply Add_rcons.
      * have auxl : eval_list l q' = None.
        -- eapply eval_list_incl_none with (u ++ [::(i, o)]).
           ++ now apply eval_list_none_fun.
           ++ intros x Hinx ; eapply (List.Add_in Hadd) in Hinx.
              destruct Hinx as [Hinx | Hinx] ; eapply List.in_or_app ; [| now left].
              right ; now left.
           ++ eapply eval_list_notin_cat ; auto ; cbn.
              intros [Hin | Hin] ; inversion Hin ; now auto.
        -- suff: ask (R := A) q = ask q' by
             (intros H ; inversion H ; subst ; rewrite auxl in Hsome ; inversion Hsome).
           rewrite - Heq.
           eapply eval_ext_tree_aux_finapp_monotone_ask_list ; eauto.
           rewrite - addn1 ; now apply eval_ext_tree_aux_finapp_monotone_ask_fuel.
  - have Hfunu : is_fun_list u.
    { eapply is_fun_list_incl ; eassumption. } 
    remember (eval_ext_tree_aux_finapp tau u (size u) nil) as aux.
    destruct aux as [q' | r].
    2: econstructor ; [ assumption | right ; left ; now exists r ].
    remember (eval_list u q') as aux2 ; destruct aux2 as [a | ].
    + econstructor ; [ assumption | ].
      right ; right ; exists q',a.
      split ; [now auto | split ; [now auto | ] ].
      remember (eval_ext_tree_aux_finapp tau (u ++[:: (q', a)]) (size (u ++ [:: (q', a)])) nil)
        as aux3.
      destruct aux3 as [q'' | r].
      2: econstructor ; [now apply eval_list_In_is_fun | right ; left ; now exists r ].
      suff: q'' = q.
      2:{ suff: ask (R := A) q'' = ask q by (intros H ; inversion H).
          have Heqsize: (size l = (size u).+1) by (eapply List.Add_length ; eassumption).
          rewrite Heqaux3 - Heq size_cat addn1 Heqsize.
          eapply eval_ext_tree_aux_finapp_one_step_fuel ; eauto.
          * now apply eval_list_In_is_fun.
          * now apply List.incl_appl, List.incl_refl.
      }
      intros e ; subst.
      have Hnone': eval_list (u ++ [:: (q', a)]) q = None.
      { eapply eval_list_incl_none ; [ | | eassumption ] ; auto.
        eapply List.incl_tran ; [ | exact Hincl].
        apply List.incl_app ; [now apply List.incl_refl | ].
        intros x [Hinx | Hinx] ; inversion Hinx ; now apply eval_list_In.
      }
      econstructor ; [now apply eval_list_In_is_fun | left].
      exists q ; split ; [auto | split ; [auto | ] ].
      intros o'.
      suff: ext_tree_indbarredP tau (u ++ [::(q, o')]).
      { intros H ; unshelve eapply (ext_tree_indbarredP_monotone H).
        + rewrite cats1 ; apply is_fun_rcons_notin_dom.
          * now apply eval_list_In_is_fun.
          * now apply eval_list_notin.
        + apply List.incl_app ; [ | now apply List.incl_appr,List.incl_refl].
          do 2 apply List.incl_appl ; now apply List.incl_refl.
      }
      have Hnoneu: eval_list (u ++ [:: (q, o')]) i = None.
      { apply eval_list_notin_cat ; [assumption | ].
        cbn ; intros [Hfalse | Hfalse] ; [ subst | now inversion Hfalse].
        suff: eval_list l i = Some o.
        { intros H ; rewrite H in Hnonel ; now inversion Hnonel. }
        apply (In_eval_list Hfunl).
        unshelve eapply (List.Add_in Hadd) ; now left.
      }
      eapply (IHk o') ; eauto.
      -- apply List.incl_app ; [now apply List.incl_appl | ].
         apply List.incl_appr, List.incl_refl.
      -- now apply Add_cat.
      -- intros a' w Haddw.
         suff: exists x, List.Add (q,o') x w.
         2:{ eapply List.Add_inv.
             apply (List.Add_in Haddw) ; right ; apply List.in_or_app.
             right ; now left.
         }
         intros [x Haddx].
         eapply (ext_tree_indbarredP_monotone) with x.
         ++ eapply Hyp with a'.
            eapply (@Add_diamond _ _ _ u (u ++ [:: (q, o')]) x w) ; eauto.
            rewrite cats1 ; eapply Add_rcons.
         ++ eapply is_fun_list_incl with ((u ++ [:: (q, o')]) ++ [::(i, a')]).
            { do 2 (apply eval_list_none_fun ; auto).
              eapply eval_list_incl_none ; [ | | eassumption ] ;
                [ now apply eval_list_In_is_fun | ].
              now apply List.incl_appl, List.incl_refl.
            }
            intros y Hiny ; apply (List.Add_in Haddw) in Hiny.
            destruct Hiny as [Hiny | Hiny] ; [subst | ].
            ** apply List.in_or_app ; right ; now left.
            ** apply List.in_or_app ; now left.
         ++ intros y Hin ; eapply List.Add_in ; [eassumption | now right].
    + destruct (@eqP I q' i) as [Heqi | Hnoteq] ; [ subst | ].
      * econstructor ; [assumption | ].
        left ; exists i ; split ; [auto | split ; [ auto | ] ].
        intros o' ; apply (Hyp o').
        rewrite cats1 ; now apply Add_rcons.
      * suff: q' = q ; [intros Heqq ; subst | ].
        -- econstructor ; [assumption | ].
           left ; exists q ; split ; [auto | split ; [ auto | ] ].
           intros o' ; eapply (IHk o').
           ++ apply List.incl_app ; [now apply List.incl_appl | ].
              apply List.incl_appr, List.incl_refl.
           ++ apply eval_list_notin_cat ; [assumption | ].
              cbn ; intros [Heqi | Hfalse] ; now auto.
           ++ now apply Add_cat.
           ++ intros a w Haddw.
              eapply ext_tree_indbarredP_monotone with ((i,a) :: u).
              ** now apply Hyp with a, List.Add_head.
              ** eapply is_fun_list_incl with ((u ++ [:: (q, o')]) ++ [::(i, a)]).
                 { apply eval_list_none_fun ; auto ; [ now apply eval_list_none_fun | ].
                   apply eval_list_notin_cat ; auto ; cbn.
                   intros [Heqi | Hfalse] ; [now subst | now inversion Hfalse].
                 }
                 intros y Hiny ; apply (List.Add_in Haddw) in Hiny.
                 destruct Hiny as [Hiny | Hiny] ; [subst | ].
                 --- apply List.in_or_app ; right ; now left.
                 --- apply List.in_or_app ; now left.
              ** intros x Hinx.
                 eapply (List.Add_in Haddw) ; rewrite - cat_cons.
                 apply List.in_or_app ; now left.
        -- suff: ask (R := A) q = ask q' by (inversion 1).
           erewrite <- Heq, List.Add_length ; eauto.
           eapply eval_ext_tree_aux_finapp_monotone_ask_list ; eauto.
           ++ eapply eval_list_incl_none with ((i,o) :: u).
              ** eapply is_fun_cons_notin_dom ; eauto.
                 now apply eval_list_notin.
              ** intros x Hinx ; now apply (List.Add_in Hadd) in Hinx.
              ** cbn ; erewrite ifN_eq ; [now auto | ].
                 eapply contra_not_neq with (q' = i) ; auto.
           ++ rewrite - addn1.
              eapply eval_ext_tree_aux_finapp_monotone_ask_fuel ; eauto.
Qed.

(*              apply eval_list_In_is_fun ; auto.
              | ].
              intros y Hiny ; apply (List.Add_in Haddw) in Hiny.
              destruct Hiny as [Heqy | Hinu] ; [subst | ].
              
           admit.
      * admit.
    + suff: q' = i.
      * intros e ; subst.
        
      *
           apply List.Add_split in Haddw as [w1 [w2 [Heqw1 Heqw2]]] ; subst.
           suff: ext_tree_indbarredP tau (w1 ++ ((i, a') :: w2)%SEQ)
           
           remember (eval_list u i) as test ; destruct test as [a' | ].
           
           admit.
        -- 
        

        -- suff: o' = o.
           { intros H ; subst.
             econstructor ; [admit | ].
             left.
             exists q ; split ; [auto | split ; [ auto | ] ].
             intros o'.
             suff: ext_tree_indbarredP tau (u ++ [::(q, o')]).
             { intros H ; unshelve eapply (ext_tree_indbarredP_monotone H).
               + admit.
               + apply List.incl_app ; [ | now apply List.incl_appr,List.incl_refl].
                 do 2 apply List.incl_appl ; now apply List.incl_refl.
             }
             apply (Hyp o') ; admit.
           }
           suff: List.In (q,o) l.
           { intros H ; apply (In_eval_list Hfunl) in H ; rewrite H in Hsome.
             now injection Hsome.
           }
           eapply List.Add_in ; [exact Hadd | now left].
        -- econstructor ; [ admit | left].
           exists q ; split ; [ now auto | split ; [now auto | ] ].
           intros a'.
           suff: 
           cbn.
           
           
             eapply IHk.
           
         2:{
        
        
        
      * suff: q = q''.
        { intros Heq' ; subst.
          specialize (IHk i o u (v ++ [::(q'', o')])).
          Print List.Add.
          suff: ext_tree_indbarred
  - subst.
    econstructor ; [assumption | ].
    remember (eval_ext_tree_aux_finapp tau u (size u) [::]) as val.
    destruct val as [q | r].
    2:{ right ; left ; eauto. }
    remember (eval_list u q) as val2 ; destruct val2 as [o' |].
    + symmetry in Heqval, Heqval2.
      suff: List.incl u (u ++ [::(i,o)]).
      * intros Htest.
        right ; right.
        exists q, o' ; split ; [auto | split ; [auto | ] ].
        econstructor.
        { now apply eval_list_In_is_fun. }
        right ; left.
        exists a.
        revert Heqa.
        admit.
      * apply List.incl_appl, List.incl_refl.
    + left.
      exists q.
      split ; [reflexivity | split ; [now auto | ] ].
      remember (eval_list [::(i,o)] q) as aux ; destruct aux as [o' | ].
      { cbn in *.
        destruct (@eqP I q i) as [? | Hnoteq] ; [subst ; assumption | now inversion Heqaux].
      }
      symmetry in Heqaux,Heqval,Heqval2 ; apply eval_list_notin in Heqaux.
      exfalso.
      eapply (eval_ext_tree_aux_finapp_monotone_ask_fuel 1 Hfun Heqval2) in Heqval.
      eapply (eval_ext_tree_aux_finapp_monotone_ask_list) in Heqval ; [ | exact Hnodup | | ].
      * rewrite size_cat Heqval in Heqa ; now inversion Heqa.
      * now apply List.incl_appl, List.incl_refl.
      * now apply eval_list_notin_cat.
  - subst.
    remember (eval_ext_tree_aux_finapp tau u (size u) nil) as aux.
    destruct aux as [q' | r].
    2: econstructor ; [assumption | right ; left ; now exists r ].
    remember (eval_list u q') as aux2 ; destruct aux2 as [a | ].
    + econstructor ; [ assumption | ].
      right ; right ; exists q',a.
      split ; [now auto | split ; [now auto | ] ].
      remember (eval_ext_tree_aux_finapp tau (u ++ [:: (q', a)]) (size (u ++ [:: (q', a)])) nil)
        as aux3.
      destruct aux3 as [q'' | r].
      2: econstructor ; [now apply eval_list_In_is_fun | right ; left ; now exists r ].
      remember (eval_list (u ++ [:: (q', a)]) q'') as aux4 ; destruct aux4 as [a' | ].
      * suff: q = q''.
        { intros Heq' ; subst.
          specialize (IHk i o (u ++ [::(q'', o')])).
          suff: ext_tree_indbarred
          
      
      unshelve eapply IHk.
      

      
    specialize (IHk q o' (u ++ [::(i, o)])).
*)
    
  
Lemma test (tau : ext_tree) (l : seq (I * O)) (o : O) :
  indbarred_fun_list
    (fun u => exists n a, eval_ext_tree_aux_finapp tau u n nil = output a) l ->
  ext_tree_indbarredP tau l.
Proof.
  intros Hyp.
  assert (aux := indbarred_fun_list_fun_list Hyp) ; revert aux.
  induction Hyp as [u v [n [r Hr]] Hincl Hnodup | q v Hnotin _ IHk].
  - intros Hfun ; eapply eval_output_indbarredP ; eauto.
    eapply eval_ext_tree_aux_finapp_monotone_output_list ; now eauto.
  - intros Hfun.
    unshelve eapply super with (v ++ [::(q,o)]) q o.
    + rewrite - (cat0s v) ; apply eval_list_notin_cat; auto.
    + rewrite cats1 ; now apply Add_rcons.
    + apply IHk.
      rewrite cats1.
      now apply is_fun_rcons_notin_dom.
    + intros o' w Haddw.
      suff: List.incl (v ++ [:: (q, o')]) w.
      { intros Hincl.
        eapply ext_tree_indbarredP_monotone ; [ apply IHk | | eassumption].
        * rewrite cats1.
          now apply is_fun_rcons_notin_dom.
        * apply is_fun_list_incl with (v ++ [::(q, o')]).
          -- rewrite cats1 ; now apply is_fun_rcons_notin_dom.
          -- intros x Hinx ; apply (List.Add_in Haddw) in Hinx.
             destruct Hinx as [Hinx | Hinx] ; [subst | ] ; apply List.in_or_app ; auto.
             now right ; left.
      }
      intros x Hinx ; apply (List.Add_in Haddw).
      apply List.in_app_or in Hinx ; destruct Hinx as [Hinx | Hinx] ; [now right | ].
      destruct Hinx ; now left.
Qed.

Lemma test_noo (tau : ext_tree) (l : seq (I * O)) :
  indbarred_fun_list
    (fun u => exists n a, eval_ext_tree_aux_finapp tau u n nil = output a) l ->
  ext_tree_indbarredP tau l.
Proof.
  destruct l as [ | [i o] l] ; intros Hyp.
  - econstructor ; [intros i j K H ; inversion H | cbn ].
    remember (tau nil) as aux ; destruct aux as [q | r] ; [ | right ; left ; now exists r].
    left ; exists q ; split ; [auto | split ; [auto | ] ].
    intros o.
    eapply ext_tree_indbarredP_monotone with nil.
    + now eapply test.
    + intros i a a' Hina Hina'.
      destruct Hina as [H | H] ; inversion H ; subst ; clear H.
      destruct Hina' as [H | H] ; inversion H ; now subst.
    + now apply List.incl_nil_l.
  - eapply test ; eauto.
Qed.
  
  

  
Lemma eval_ext_tree_finapp_trace (tau : ext_tree) f n a l :
  eval_ext_tree_aux tau f n l = output a ->
  eval_ext_tree_aux_finapp tau [seq (i, f i) | i <- eval_ext_tree_trace_aux tau f n l]
    (size (eval_ext_tree_trace_aux tau f n l)) l = output a.
Proof.
  assert (aux := @is_fun_map (eval_ext_tree_trace_aux tau f n l) f) ; revert aux.
  change (eval_ext_tree_trace_aux tau f n l) with (nil ++ (eval_ext_tree_trace_aux tau f n l)) at 1 2.
  generalize (@nil I) as u ; revert l.
  induction n as [ | n IHn] ; cbn in * ; intros l u aux Heq.
  { destruct u ; cbn ; [assumption | now rewrite Heq ]. }
  remember (tau l) as r ; destruct r ; cbn in *.
  2:{ destruct u ; cbn ; now rewrite - Heqr. }
  erewrite <- cat_rcons, <- Heqr ; rewrite - cat_rcons in aux.
  suff: eval_list [seq (i, f i) | i <- rcons u s ++ eval_ext_tree_trace_aux tau f n (rcons l (f s))] s = Some (f s).
  { intros Hyp ; rewrite Hyp.
    specialize (IHn (rcons l (f s)) (rcons u s)) ; erewrite IHn ; [reflexivity | assumption | assumption].
  }
Admitted.
Print deval.

Fixpoint deval_list (d : @dialogue I O A) (l : list (I * O)) : option A :=
  match d with
  | eta a => Some a
  | beta q k => match eval_list l q with
                | None => None
                | Some o => deval_list (k o) l
                end
  end.

Lemma deval_list_deval d l alpha a:
  deval_list d [seq (i, alpha i) | i <- l] = Some a ->
  deval d alpha = a.
Admitted.

Fixpoint deval_trace (d : @dialogue I O A) f : list (I * O) :=
  match d with
  | eta a => nil
  | beta q k => (q, (f q)) :: (deval_trace (k (f q)) f)
  end.


  
Theorem GBI_GCI F :
  seq_cont_valid F ->
  dialogue_cont F.
Proof.
  intros [tau [HF Hval]].
  eapply Delta0_choice in HF as [HF].
  2:{
    intros α n. destruct eval_ext_tree eqn:E.
    - firstorder congruence.
    - left. destruct (HF α) as [m].
      f_equal. 
      eapply eval_ext_tree_output_unique; eauto. 
  }
  unfold GBI in HGBI.
  pose (T := fun (l : list (I * O)) =>
               exists d : dialogue,
                 forall (l' : list (I * O)) (a : A),
                   List.incl l l' ->
                    deval_list d l' = Some a <->
                      eval_ext_tree_aux_finapp tau l' (size l') nil = output a).
  have Help : ABbarred T.
  { intros alpha.
    destruct (HF alpha) as [n Hn].
    exists (eval_ext_tree_trace tau alpha n).
    unfold T.
    exists (eta (F alpha)).
    intros l' a Hincl.
    split ; intros Hyp.
    + cbn in *.
      inversion Hyp ; subst ; clear Hyp.
      admit.
    + cbn in *.
      admit.
  }
  apply HGBI, indbarred_indbarred_NoDup in Help.
  unfold dialogue_cont.
  unfold T in * ; clear T.
  suff: exists d : dialogue, forall (l : list (I * O)) (a : A),
      List.incl nil l ->
      deval_list d l = Some a <->
      eval_ext_tree_aux_finapp tau l (size l) nil = output a.

  { intros [d Hd].
    exists d ; intros alpha.
    specialize (HF alpha) as [n Hn].
    specialize (Hd [seq (i, alpha i) | i <- eval_ext_tree_trace tau alpha n] (F alpha))
      as [Hd1 Hd2] ; [now apply List.incl_nil_l | ].
    suff: deval_list d [seq (i, alpha i) | i <- eval_ext_tree_trace tau alpha n] = Some (F alpha).
    { intros Hyp.
      symmetry ; eapply deval_list_deval.
      eassumption.
    }
    apply Hd2 ; rewrite size_map.
    apply eval_ext_tree_finapp_trace ; exact Hn.
  }
  revert Help ; clear HF F.
  generalize (@nil (I * O)).
  intros l Help.
  pattern l.
  induction Help.
  - destruct H as [d Hd].
    exists d.
    intros l' a Hincl.
    assert (Hincl' := List.incl_tran H0 Hincl).
    specialize (Hd l' a Hincl') as [Hd1 Hd2] ; split ; intros Hyp.
    + now apply Hd1.
    + now apply Hd2.
  - clear H0.
    
    
    
    exists d.
    intros
  
  
  
  induction Help.
  
  
    
    2:{ cbn.

  
  pose (T := fun (l : list (I * O)) =>
               forall l', List.incl l l' ->
                          List.NoDup (map fst l') ->
                          exists a : A,
                            eval_ext_tree_aux_finapp tau l' (size l') (map snd l) = output a).
  have Help : ABbarred T.
  { intros alpha.
    destruct (HF alpha) as [n Hn].
    exists (eval_ext_tree_trace tau alpha n).
    unfold T.
    intros l' Hincl Hnodup ; exists (F alpha).
    admit.
  }
  apply HGBI, indbarred_indbarred_NoDup in Help.
  unfold dialogue_cont.
  
  induction Help.

  
  unfold T in * ; clear T.
  suff: exists d : dialogue, forall alpha : I -> O,
    exists l : seq (I * O),
      map alpha (map fst l) = map snd l /\
        forall l',
          List.incl l l' ->
          List.NoDup (map fst l') ->
          eval_ext_tree_aux_finapp tau l' (size l') (map snd l) = output (deval d alpha).
  {admit. }

  
  revert Help HF.
  unfold eval_ext_tree.

  
  change (@nil O) with (map snd (@nil (I * O))).
  generalize (@nil (I * O)) ; intros l Help.
  pattern l ; induction Help as [u v Hv Hincl Hnodup | ] ; intros HF.
  - specialize (Hv u Hincl Hnodup) as [a Ha].
    exists (eta a).
    intros alpha ; cbn.
    specialize (HF alpha) as [n Hn].
    exists v.
    
    suff: output (Q := I) (F alpha) = output a by (intros Heq ; inversion Heq).
    rewrite - Ha ; symmetry.
    

  
  suff: exists d : dialogue, forall (alpha : I -> O),
    exists l, (map alpha (map fst l)) = map snd l /\
                eval_ext_tree_aux_finapp tau l (size l) nil = output (deval d alpha).
  { intros [d Hd].
    exists d.
    intros alpha.
    specialize (Hd alpha) as [l [Hl1 Hl2]].
    admit. }
  clear HF.
  have aux: forall alpha, map alpha (map fst (@nil (I * O))) = map snd (@nil (I * O))
      by reflexivity.
  revert Help aux.
  generalize (@nil (I * O)).
  intros l Help ; pattern l ; induction Help as [u v Hv Hincl Hnodup | ] ; intros aux.
  - destruct Hv as [a Ha] ; exists (eta a).
    intros alpha ; cbn ; exists v.
    split.
    { admit. }
    assumption.
  -

  
  - revert Hv u Hincl Hnodup.
    generalize 0 as m.
    induction v as [ | v x] using last_ind ; intros.
    { cbn in *.
      destruct Hv as [a Heqa].
      exists (eta a) ; intros alpha.
      exists nil ; cbn.
      change (map snd u) with (map snd (nil ++ u)) ; rewrite map_cat.
      now erewrite valid_cat. 
    }
    cbn in *.
(*    remember (tau (map snd u)) as r.
    destruct r as [ i | ].
    2:{ exists (eta a) ; intros alpha ; exists 1.
        cbn ; now rewrite <- Heqr. }
    cbn in Hv.*)
    rewrite size_rcons in Hv; cbn in *.
    remember ( tau [seq i.2 | i <- take m (rcons v x)]) as s.
    destruct s as [j | a].

    2:{ exfalso.
        erewrite valid_cat in Heqr.
        
    











  
  suff: exists d : dialogue, forall alpha : I -> O,
      eval_ext_tree_aux_finapp tau (deval_trace d alpha) (size (deval_trace d alpha)) nil =
        output (deval d alpha).
  { admit. }
  clear HF ; unfold T in * ; clear T.
  revert Help.
  generalize (@nil (I * O)) ; generalize 0 ; intros n l Help.
  pattern l.
  induction Help as [u v [a Ha] Hincl Hnodup | i v Hnotin _ IHk].
  {
  2:{


    unfold T in *.
     

  
  unfold T in * ; clear T.
  suff: exists d : dialogue, forall (l : list (I * O)) (a : A),
      deval_list d l = Some a <->
      eval_ext_tree_aux_finapp tau l (size l) nil = output a.

  { intros [d Hd].
    exists d ; intros alpha.
    specialize (HF alpha) as [n Hn].
    specialize (Hd [seq (i, alpha i) | i <- eval_ext_tree_trace tau alpha n] (F alpha))
      as [Hd1 Hd2].
    suff: deval_list d [seq (i, alpha i) | i <- eval_ext_tree_trace tau alpha n] = Some (F alpha).
    { intros Hyp.
      symmetry ; eapply deval_list_deval.
      eassumption.
    }
    apply Hd2 ; rewrite size_map.
    apply eval_ext_tree_finapp_trace ; exact Hn.
  }
  clear HF.
  revert Help.
  replace (@nil O) with (map snd (take 0 (@nil (I * O)))) by reflexivity.
  generalize (@nil (I * O)) ; generalize 0 ; intros n l Help.
  pattern l.
  induction Help as [u v [a Ha] Hincl Hnodup | i v Hnotin _ IHk].  
  - admit.
  - 

    exists (eta a).
    intros w a'.
    split ; cbn.
    { intros Heq ; inversion Heq ; subst.
      
    exists (size v) ; cbn.
    rewrite - Ha.


  
    eapply eval_ext_tree_output_unique ; [eassumption | ].
    
    
      exists n, eval_ext_tree_aux tau alpha n (take 0 nil) = output (deval d alpha).
  { intros [d Hd].
    exists d ; intros alpha ; specialize (Hd alpha) as [n Hn] ; [ reflexivity | ].
    specialize (HF alpha) as [m Hm] ; unfold eval_ext_tree in *.
    eapply eval_ext_tree_output_unique ; eassumption.
  }
  clear HF.
  revert Help.
  replace (@nil O) with (map snd (@nil (I * O))) ; change (@nil I) with (map fst (@nil (I * O))).
  generalize (@nil (I * O)) ; generalize 0 ; intros n l Help.
  pattern l.
  induction Help as [u v [a Ha] Hincl Hnodup | i v Hnotin _ IHk].  
  - exists (eta a).
    intros alpha Heqalpha.
    exists (size v) ; cbn.
    rewrite - Ha.
    

    revert Hv u Hincl Hnodup.
    replace (@nil O) with (take 0 (map snd v)) by (now rewrite take0).
    clear T ; generalize 0 as m.
    induction v as [ | x] ; intros.
    { cbn in *.
      destruct Hv as [a Heqa].
      exists (eta a) ; intros alpha ; exists 1 ; cbn.
      unfold valid_ext_tree in Hval.
      change (map snd u) with (map snd (nil ++ u)) ; rewrite map_cat.
      now erewrite valid_cat. 
    }
    remember (tau (map snd u)) as r.
    destruct r as [ i | ].
    2:{ exists (eta a) ; intros alpha ; exists 1.
        cbn ; now rewrite <- Heqr. }
    cbn in Hv.
    remember (tau (take m (x.2 :: [seq i.2 | i <- v]))) as s.
    destruct s as [j | a].
    2:{ exfalso.
        erewrite valid_cat in Heqr.
        










  
  
  pose (T := fun (l : list (I * O)) =>
               (exists a : A, forall f, map f (map fst l) = map snd l ->
                                        eval_ext_tree_aux tau f (size l) nil = output a)).
  have Help : ABbarred T.
  { intros alpha.
    destruct (HF alpha) as [n Hn].
    exists (eval_ext_tree_trace tau alpha n).
    unfold T.
    exists (F alpha) ; intros f.
    erewrite <- (map_comp fst _).
    erewrite (@eq_map _ _ (fst \o (fun i : I => (i, alpha i))) id) ; [ | now intros k].
    erewrite map_id, <- (map_comp snd _).
    erewrite (@eq_map _ _ (snd \o (fun i : I => (i, alpha i))) alpha) ; [ | now intros k].
    intros Heqf.
    assert (aux:= eval_ext_tree_trace_size_eval_trace Hn).
    apply eval_ext_tree_trace_size_eval in Hn ; rewrite <- Hn, size_map ; symmetry.
    apply eval_ext_tree_continuous.
    now rewrite - aux.
  }
  apply HGBI, indbarred_indbarred_NoDup in Help.
  unfold dialogue_cont.
  eapply Delta0_choice in HF as [HF].
  2:{
    intros α n. destruct eval_ext_tree eqn:E.
    - firstorder congruence.
    - left. destruct (HF α) as [m].
      f_equal. 
      eapply eval_ext_tree_output_unique; eauto. 
  }
  unfold T in * ; clear T.
  suff: exists d : dialogue, forall (alpha : I -> O),
    exists n, eval_ext_tree_aux tau alpha n nil = output (deval d alpha).
  { intros [d Hd].
    exists d ; intros alpha ; specialize (Hd alpha) as [n Hn].
    specialize (HF alpha) as [m Hm] ; unfold eval_ext_tree in *.
    eapply eval_ext_tree_output_unique ; eassumption.
  }
  clear HF.
  revert Help ; unfold inductively_barred, eval_ext_tree.
  have aux : forall (f : I -> O), [seq f i | i <- [seq i.1 | i <- (@nil (I * O))]] =
                                    [seq i.2 | i <- (@nil (I * O))].
  intros f ; reflexivity.
  revert aux.
  generalize (@nil (I * O)) ; intros l Hyp Help ; revert Hyp.
  pattern l.
  induction Help as [u v Hv Hincl Hnodup | i v Hnotin _ IHk] ; intros Hyp.
  
  - destruct Hv as [a Ha].
    exists (eta a) ; intros alpha ; exists (size v).
    cbn.
    apply Ha.
    admit.
  -
    
  




  
  
  pose (gs := @eval_ext_tree_continuous _ _ _ tau) ; unfold modulus in gs.
    
               exists a : A, eval_ext_tree_aux_finapp tau l (size l) nil = output a).
  have Help : ABbarred T.
  { intros alpha.
    destruct (HF alpha) as [n Hn].
    exists (eval_ext_tree_trace tau alpha n).
    unfold T.
    exists (F alpha).
    rewrite - Hn size_map.

    

  
    
    admit.
  }
(*    exists (F alpha).
    rewrite - Hn eval_ext_tree_map.
    f_equal.
    erewrite <- map_comp ; apply eq_map.
    intros i ; reflexivity.
 *)
  apply HGBI, indbarred_indbarred_NoDup in Help.
  unfold dialogue_cont.
  eapply Delta0_choice in HF as [HF].
  2:{
    intros α n. destruct eval_ext_tree eqn:E.
    - firstorder congruence.
    - left. destruct (HF α) as [m].
      f_equal. 
      eapply eval_ext_tree_output_unique; eauto. 
  }
  unfold T in * ; clear T.
  suff: exists d : dialogue, forall (alpha : I -> O),
    exists l, eval_ext_tree_aux_finapp tau l (size l) nil = output (deval d alpha).
  { admit. }
  
  
  
  { intros [b Hb].
    exists b ; intros alpha; specialize (Hb alpha) as [n Heqn].
    specialize (HF alpha) as [m Heqm].
    unfold eval_ext_tree in *.
    eapply eval_ext_tree_output_unique ; eassumption.
  }
  revert Help HF ; unfold inductively_barred, eval_ext_tree.
  change (@nil O) with (map snd (@nil (I * O))).
  generalize (@nil (I * O)) ; intros l Help HF.

  clear HF.
  pattern l.
  induction Help as [u v Hv Hincl Hnodup | ].
  - unfold T in Hv.
    revert Hv u Hincl Hnodup.
    replace (@nil O) with (take 0 (map snd v)) by (now rewrite take0).
    clear T ; generalize 0 as m.
    induction v as [ | x] ; intros.
    { cbn in *.
      destruct Hv as [a Heqa].
      exists (eta a) ; intros alpha ; exists 1 ; cbn.
      unfold valid_ext_tree in Hval.
      change (map snd u) with (map snd (nil ++ u)) ; rewrite map_cat.
      now erewrite valid_cat. 
    }
    remember (tau (map snd u)) as r.
    destruct r as [ i | ].
    2:{ exists (eta a) ; intros alpha ; exists 1.
        cbn ; now rewrite <- Heqr. }
    cbn in Hv.
    remember (tau (take m (x.2 :: [seq i.2 | i <- v]))) as s.
    destruct s as [j | a].
    2:{ exfalso.
        erewrite valid_cat in Heqr.
        
    
    
    cbn in *.

      

    unfold T ; intros u ; destruct (tau u) ; [left ; now exists a | right].
    intros [a Hyp] ; now inversion Hyp.
  - clear l Help.
    intros u Hu ; cbn.
    remember (tau u) as r ; destruct r.
    + exists (spit a) ; intros alpha ; exists 0 ; now cbn.
    + exfalso ; destruct Hu as [a Ha] ; rewrite Ha in Heqr.
      now inversion Heqr.
  - intros u k IHk ; cbn in *.
    unshelve eexists.
    + apply bite ; intros o.
      exact (proj1_sig (IHk o)).
    + cbn.
      intros alpha.
      destruct (IHk (alpha 0)) as [b IHb].
      destruct (IHb (alpha \o succn)) as [n Hn] ; cbn in *.
      exists (S n) ; cbn ; rewrite <- Hn.
      clear -Hvalid.
      remember (tau u) as r ; destruct r.
      * destruct n ; cbn ; [symmetry ; now apply Hvalid |].
        suff: tau (rcons u (alpha 0)) = Some a by (intros Hyp ; now rewrite Hyp).
        now apply Hvalid.
      * generalize 0 ; clear Heqr ; revert alpha u.
        induction n ; [ reflexivity | cbn ; intros alpha u i].
        destruct (tau (rcons u (alpha i))) ; [reflexivity |].
        now eapply IHn.
Qed.
  
  
End GeneralisedBarInduction.
