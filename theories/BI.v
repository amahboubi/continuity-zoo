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
Require Import Lia.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".


Arguments ext_tree {_ _ _}, _ _ _.
Arguments Btree {_ _}, _ _.

Section Beval.
Variables O A : Type.
Notation I := nat.
Implicit Type (F : (I -> O) -> A).
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

End Beval.

Section ContinuousInduction.

Variable O : Type.
Notation I := nat.
Notation A := (seq O).
Implicit Type (F : (I -> O) -> A).
Implicit Type (b : @Btree O A).

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


  (*We define a specific oracle (pref_o l o alpha) that is equal to o for n <= (size l),
   and coincides with alpha everywhere else.*)

Definition pref_o (m : nat) (o : O) (alpha : I -> O) (n : I) :=
  if n <= m then o else alpha n.

Lemma pref_o_sizel m o : forall alpha, pref_o m o alpha m = o.
Proof.
  intros alpha ; unfold pref_o in *.
  now rewrite leqnn.
Qed.

Lemma pref_o_alpha m o : forall alpha n, m < n -> pref_o m o alpha n = alpha n.
Proof.
  intros alpha n H ; unfold pref_o.
  rewrite ltnNge in H ; rewrite (Bool.negb_involutive_reverse (n <= m)).
  now rewrite H.
Qed.

Lemma pref_o_eval P (l l' : seq O) o : forall alpha n,
    size l < size l' ->
    eval_ext_tree_aux (pred_to_ext_tree P) alpha n l' =
      eval_ext_tree_aux (pred_to_ext_tree P) (pref_o (size l) o alpha) n l'.
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

Lemma pref_o_beval_aux b m o n:
  m < n ->
  forall alpha, beval_aux b (pref_o m o alpha) n =
                  beval_aux b alpha n.
Proof.
  revert m n ; induction b as [ | ? IH] ; intros * Hinf alpha ; [reflexivity |].
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
    rewrite <- (Hyp (pref_o (size l) o alpha)), pref_o_sizel.
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
                      (projT1 (Hwf (pref_o (size l) o alpha))).-1 (rcons l o) =
                      output a}) as Hyp.
  { intros alpha.
    erewrite (pref_o_eval P (l := l) o) ; [ | erewrite size_rcons ; now eauto].
    clear Hb IHk ; destruct (Hwf (pref_o (size l) o alpha)) as [n Hn].
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
    exists (projT1 (Hwf (pref_o (size l) o alpha))).-1.
    now apply Hyp.
  }
  intros alpha ; specialize (Hb (pref_o (size l) o alpha)) ; cbn in *.
  rewrite pref_o_sizel in Hb.
  rewrite size_rcons.
  revert Hb ; generalize (Hyp alpha) ; generalize (Hwf (pref_o (size l) o alpha)).
  clear Hyp Hwf ; intros [n [x Hx]] [y Hy] Hb; cbn in *.
  rewrite - (pref_o_beval_aux _ o (m := (size l))) ; [ | now eauto].
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

Section ContinuousInductionCoind.

Variable O : Type.
Notation I := nat.
Notation A := (seq O).
Implicit Type (F : (I -> O) -> A).
Implicit Type (b : @Bitree O A).

Variable CI : forall F, Bseq_cont_interaction F -> dialogue_cont_Brouwer F.

CoFixpoint pred_to_Bitree_aux (P : seq O -> bool) (l : seq O) : @Bitree O A :=
  if (P l) then Bret _ l else Bvis (fun o => pred_to_Bitree_aux P (rcons l o)).

Lemma Bieval_pred_to_Bitree_spec (P : seq O -> bool) (l : seq O) alpha n u :
  Bieval (pred_to_Bitree_aux P l) alpha n = Some u ->
  P u.
Proof.
  revert alpha l u ; induction n ; intros * Heq ; cbn in *.
  - remember (P l) as b ; destruct b ; inversion Heq ; subst ; auto.
  - remember (P l) as b ; destruct b ; [inversion Heq ; subst ; auto | ].
    now apply IHn in Heq.
Qed.

Fixpoint Bieval_trace (b : @Bitree O A) alpha n : nat :=
  match n with
  | 0 => 0
  | S n => match b with
           | Bret _ => 0
           | Bvis k => S (Bieval_trace (k (alpha 0)) (alpha \o succn) n)
           end
  end.

Lemma Bieval_trace_spec (b : @Bitree O A) alpha n u :
  Bieval b alpha n = Some u ->
  Bieval b alpha (Bieval_trace b alpha n) = Some u.
Proof.
  revert b alpha u ; induction n as [ | n IHn] ; cbn ; intros b alpha u Heq.
  - destruct b ; auto.
  - destruct b ; auto.
    now apply IHn.
Qed.

Lemma Bieval_pred_trace (P : seq O -> bool) (alpha : I -> O) (n : nat) (l u : A) :
  Bieval (pred_to_Bitree_aux P l) (n_comp alpha (size l)) n = Some u ->
  u = l ++ (map alpha (iota (size l)
                         (Bieval_trace (pred_to_Bitree_aux P l) (n_comp alpha (size l)) n))).
Proof.
  revert P alpha l u ; induction n as [ | n IHn] ; cbn ; intros P alpha l u Heq.
  - rewrite cats0.
    destruct (P l) ; now inversion Heq.
  - destruct (P l) ; cbn ; [rewrite cats0 ; now inversion Heq | ].
    rewrite - cat1s catA cats1.
    rewrite n_comp_n_plus addn0 in Heq ; rewrite n_comp_n_plus addn0.
    specialize (IHn P alpha (rcons l (alpha (size l))) u).
    now rewrite size_rcons in IHn ; cbn in * ; specialize (IHn Heq).
Qed.    

Lemma barred_Bseq_cont_aux (P : seq O -> bool) (alpha : I -> O) (u : seq O) :
  (exists v, prefix (n_comp alpha (size u)) v /\ P (u ++ v)) ->
  exists v n, 
    Bieval (pred_to_Bitree_aux P u) (n_comp alpha (size u)) n = Some v.
Proof.
  intros [v [Hpref HP]].
  revert u alpha Hpref HP ; induction v as [ | a v IHv] ; intros.
  - exists u, 1 ; cbn in *.
    now rewrite cats0 in HP ; rewrite HP.
  - remember (P u) as b ; destruct b.
    + exists u, 1.
      now cbn ; rewrite - Heqb.
    + destruct (IHv (rcons u a) alpha) as [w [m Heqw]].
      * rewrite size_rcons ; cbn.
        unfold prefix in * ; cbn in *.
        apply (f_equal (drop 1)) in Hpref ; cbn in * ; do 2 (rewrite drop0 in Hpref).
        rewrite -> Hpref at 1.
        suff: forall n m (f : I -> O), [seq f i | i <- iota m.+1 n] =
                          [seq (f \o succn) i | i <- iota m n].
        { intros H ; now rewrite H. }
        clear ; induction n as [ | n IHn] ; intros alpha m ; [auto | ].
        cbn ; f_equal.
        now apply IHn.
      * now rewrite - cats1 - catA cat1s.
      * exists w, m.+1.
        cbn ; rewrite - Heqb ; rewrite size_rcons in Heqw ; cbn in *.
        suff: a = n_comp alpha (size u) 0 by (intros H ; rewrite - H).
        unfold prefix in Hpref ; cbn in *.
        now inversion Hpref.
Qed.

Lemma barred_Bseq_cont (P : seq O -> bool) :
  barred P ->
  inhabited (forall alpha,
        {n : nat &
               { u : seq O |
                 P u /\
                   Bieval (pred_to_Bitree_aux P nil) alpha n = Some u}}).
Proof.
  intros Hbar.
  suff: inhabited (forall alpha, {n : nat | exists u,
                                   P u /\
                                     Bieval (pred_to_Bitree_aux P nil) alpha n = Some u}).
  { intros Hi ; destruct Hi as [Hi]. econstructor.
    intros alpha. destruct (Hi alpha) as [n Hn].
    exists n. destruct Bieval; eauto ; [exists l | exfalso] ; now firstorder congruence.
  }  
  eapply Delta0_choice.
  {
    intros. remember (Bieval _ _ _) as ev ; destruct ev.
    + left ; exists l ; split ; auto.
      eapply Bieval_pred_to_Bitree_spec ; eauto.
    + right ; firstorder (eauto || congruence).
  }
  intros alpha ; specialize (Hbar alpha).
  apply (@barred_Bseq_cont_aux P alpha nil) in Hbar.
  destruct Hbar as [v [n Heval]].
  exists n, v ; split ; cbn in * ; auto.
  remember (P v) as b ; destruct b ; auto.
  revert alpha v Heqb Heval ; generalize (@nil O) as l.
  induction n as [ | n IHn] ; intros ; cbn in *.
  - remember (P l) as b' ; destruct b' ; inversion Heval ; cbn in *.
    subst ; rewrite - Heqb' in Heqb ; now inversion Heqb.
  - remember (P l) as b' ; destruct b' ; [ inversion Heval ; subst | ].
    + rewrite - Heqb' in Heqb ; now inversion Heqb. 
    + apply IHn in Heval ; auto.
Qed.

Definition pred_to_fun
  (P : seq O -> bool)
  (H : forall alpha,
      {n : nat &
             {u : seq O |
               P u /\
                 Bieval (pred_to_Bitree_aux P nil) alpha n = Some u}}) :
  (I -> O) -> A :=
  fun alpha => proj1_sig (projT2 (H alpha)).


Lemma pref_o_beval (b : @Btree O A) m o n:
  m < n ->
  forall alpha, beval b (n_comp (pref_o m o alpha) n) =
                  beval b (n_comp alpha n).
Proof.
  revert m n ; induction b as [ | ? IH] ; intros * Hinf alpha ; [reflexivity |].
  cbn.
  do 2 (rewrite n_comp_n_plus addn0) ; rewrite pref_o_alpha ; [ | assumption].
  specialize (IH (alpha n) m n.+1 (ltnW Hinf)) ; cbn in *;  eapply IH ; eauto.  
Qed.  


Lemma pref_o_Bieval b m o n j:
  m < n ->
  forall alpha, Bieval b (n_comp (pref_o m o alpha) n) j =
                  Bieval b (n_comp alpha n) j.
Proof.
  revert m n b ; induction j as [ | i IHi] ; intros * Hinf alpha ; [reflexivity |].
  cbn in * ; destruct b as [ | k] ; [reflexivity | ].
  do 2 (rewrite n_comp_n_plus addn0) ; rewrite pref_o_alpha ; [ | assumption].
  specialize (IHi m n.+1 (k (alpha n)) (ltnW Hinf)) ; cbn in *;  eapply IHi ; eauto.  
Qed.  

Proposition CoCI_BI (P : list O -> bool) :
  barred P -> inductively_barred P.
Proof.
  intros Hbar.
  have aux:= (barred_Bseq_cont Hbar).
  destruct aux as [aux].
  pose (F := pred_to_fun aux).
  have Fcon : Bseq_cont_interaction F.
  { exists (pred_to_Bitree_aux P nil).
    intros alpha ; exists (projT1 (aux alpha)).
    now apply (proj2_sig (projT2 (aux alpha))).
  }
  apply CI in Fcon ; destruct Fcon as [b Hb].
  unfold F, pred_to_fun in Hb.
  unfold inductively_barred ; revert aux F Hb.
  suff: forall (l : seq O)
               (aux : forall alpha : I -> O,
                   {n : I & {u : A | P u /\
                                       Bieval (pred_to_Bitree_aux P l)
                                         (n_comp alpha (size l)) n = Some u}}),
    (forall alpha : I -> O, ` (projT2 (aux alpha)) = beval b (n_comp alpha (size l))) ->
                           hereditary_closure (fun x : A => P x) l.
  { intros H ??? ; eapply H ; eauto.}
  clear Hbar ; induction b as [ | k IHk].
  - intros l aux Heq ; cbn in *.
    assert ({n : nat & forall alpha,
                   Bieval (pred_to_Bitree_aux P l) (n_comp alpha (size l)) n = Some r})
      as [n Hyp].
    { exists (size r) ; intros alpha.
      rewrite - (Heq alpha).
      destruct (aux alpha) as [n [u [HPu Hu]]] ; cbn in *.
      have Heq' := Bieval_pred_trace Hu ; subst.
      have Help := Bieval_trace_spec Hu.
      rewrite size_cat addnC size_map size_iota ; cbn ; now apply Bieval_monotone_plus.
    }
    clear Heq aux ; revert l Hyp.
    induction n as [ | n IHn] ; cbn ; intros l Hyp.
    all: case_eq (P l) ; intros Heq ; [now econstructor |].
    all: unfold pred_to_ext_tree in Hyp ; rewrite Heq in Hyp.
    all:  eapply hereditary_sons ; intros o.
    { specialize (Hyp (fun=> o)) ; now inversion Hyp. }
    change (fun l => if P l then output l else ask (size l))
      with (pred_to_ext_tree P) in Hyp.
    eapply IHn.
    intros alpha.
    rewrite <- (Hyp (pref_o (size l) o alpha)), n_comp_n_plus, addn0, pref_o_sizel.
    rewrite size_rcons ; erewrite <- (@pref_o_Bieval _ (size l) o (S (size l)) n) ; eauto.
  - cbn in * ; intros l aux Heq.
    case_eq (P l) ; intros eqP ; [ econstructor ; assumption | ].
    apply hereditary_sons ; intros o.
  (*We show that the evaluation of pred_to_ext_tree P using
    (pref_o alpha) leads to the same result as when using alpha. *)
  suff: forall alpha,
      {a : A &
             Bieval (pred_to_Bitree_aux P (rcons l o)) (n_comp alpha (size (rcons l o)))
               (projT1 (aux (pref_o (size l) o alpha))).-1 =
               Some a} ; [ intros Hyp | intros alpha].
    + unshelve eapply (IHk o).
      * intros alpha.
        exists (projT1 (aux (pref_o (size l) o alpha))).-1.
        exists (projT1 (Hyp alpha)) ; split ; [ | apply (projT2 (Hyp alpha))].
        eapply Bieval_pred_to_Bitree_spec ; exact (projT2 (Hyp alpha)).
      * intros alpha ; specialize (Heq (pref_o (size l) o alpha)) ; cbn in *.
        rewrite n_comp_n_plus addn0 pref_o_sizel in Heq.
        revert Heq ; generalize (Hyp alpha) ; rewrite size_rcons.
        generalize (aux (pref_o (size l) o alpha)) ; clear aux Hyp.
        intros [n [u [HPu Hu]]] [v Heqv] Hequ ; cbn in *.
        have H: u = beval (k o) (n_comp alpha (size l) \o succn).
        { rewrite Hequ ; now apply (@pref_o_beval _ _ _ (size l).+1). }
        rewrite - H ; clear H Hequ.
        destruct n ; cbn in * ; rewrite eqP in Hu ; [ inversion Hu | ].
        rewrite n_comp_n_plus addn0 pref_o_sizel in Hu.
        suff: Some u = Some v by (intros H ; inversion H).
        rewrite - Heqv - Hu.
        now eapply (@pref_o_Bieval _ (size l) o (S (size l)) n).
    + erewrite <- (@pref_o_Bieval _ (size l) o) ; [ | now rewrite size_rcons].
      destruct (aux (pref_o (size l) o alpha)) as [m [v [HPv Hv]]] ; cbn in *.
      destruct m ; cbn in * ; rewrite eqP in Hv ; [ now inversion Hv | ].
      rewrite n_comp_n_plus addn0 pref_o_sizel in Hv.
      exists v ; now rewrite size_rcons.
Qed.

Print pref_o_eval.
      suff: 
      
      rewrite - Hu.
      eauto.
        Print pref_o_beval.
        g
        
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
  }

    
  suff: forall alpha, P (beval b alpha).
  { clear Hbar aux F Hb ; induction b as [ r | k IHk] ; intros Hyp.
    - econstructor.
    
  

Fixpoint minimal_list_P (P : seq O -> bool) (u v : seq O) : seq O :=
  match v with
  | nil => u
  | a :: v => if P u then u else minimal_list_P P (rcons u a) v
  end.

Lemma minimal_list_P_spec (P : seq O -> bool) (u v : seq O) :
  P (u ++ v) = true ->
  (forall n, n < size u -> P (take n u) = false) ->
  P (minimal_list_P P u v) = true /\
    forall n, n < size (minimal_list_P P u v) -> P (take n (minimal_list_P P u v)) = false.
Proof.
  revert u ; induction v ; intros u Htrue Htake ; cbn in *.
  - rewrite cats0 in Htrue ; split ; auto.
  - remember (P u) as b ; destruct b.
    + split ; auto.
    + rewrite - cat1s catA cats1 in Htrue.
      specialize (IHv (rcons u a) Htrue).
      destruct (IHv) ; [ | split ; auto].
      rewrite size_rcons ; intros n Heq.
      case: (leqP n.+1 (size u)) ; intros Hinf.
      * rewrite - cats1 takel_cat ; [now apply Htake | now apply ltnW ].
      * pose (aux1:= minnE n (size u)) ; pose (aux2 := minnE (size u) n).
        erewrite subKn in aux1, aux2 ; [ | auto | auto].
        rewrite minnC in aux1 ; rewrite aux1 in aux2 ; subst.
        rewrite - cats1 takel_cat ; [now rewrite take_size | now apply leqnn].
Qed.
(*
Lemma barred_Bseq_cont_aux (P : seq O -> bool) :
  barred P ->
  forall (alpha : I -> O), exists u,
    (forall n, n < size u -> P (take n u) = false) /\
      forall n, n <= size u ->
                Bieval (pred_to_Bitree_aux P (take n u)) alpha (size u - n) = Some u.
Proof.
  intros Hbar alpha ; specialize (Hbar alpha) as [ u [Hpref HP]].
  exists (minimal_list_P P nil u) ; split.
  - apply minimal_list_P_spec ; now cbn.
  - have aux := @minimal_list_P_spec P nil u HP.
    destruct aux as [Htrue Hfalse] ; [ intros ? Hyp ; now inversion Hyp | ].
    revert Htrue Hfalse ; generalize (@nil O) as l ; clear HP Hpref.
    induction u as [ | u a IHu] using last_ind ; intros l Htrue Hfalse n Hinf.
    + cbn in *.
      induction l ; cbn in * ; [now rewrite Htrue | ].
      destruct n ; cbn.
      * rewrite (Hfalse 0) ; cbn.
    induction l as [ | l a IHl] using last_ind ; intros Htrue Hfalse n Hinf.
    + now cbn ; rewrite Htrue.
    + rewrite size_rcons.
      case: (leqP (size (rcons l a)) n) ; intros Hinf2.
      * suff: n = size (rcons l a).
        { intros Heq ; subst ; cbn.
          rewrite -> take_size, -> size_rcons, -> subnn ; cbn ; now rewrite Htrue.
        }
        rewrite - (subKn Hinf) - minnE ; rewrite <- (subKn Hinf2) at 2.
        now rewrite - minnE minnC.
      * specialize (Hfalse n Hinf2).
        rewrite - cats1 takel_cat ; [ | rewrite size_rcons in Hinf2 ; now apply ltnSE].

        2:{
        .
        .
        
      *
        rewrite take_size.

    apply minimal_list_P_spec ; now cbn.
Qed.

revert HP Hpref ; induction u as [ | u a IHu] using last_ind ; intros ; cbn in *.
  - exists nil ; split ; cbn ; [intros H ; now inversion H| now auto].
  -
       
Proof.
  intros Hbar alpha ; specialize (Hbar alpha) as [ u [Hpref HP]].
  revert HP Hpref ; induction u as [ | u a IHu] using last_ind ; intros ; cbn in *.
  - exists nil ; split ; cbn ; intros ? H ; [now inversion H | now rewrite HP].
  - have Hpref' : prefix alpha u.
    { unfold prefix in *.
      rewrite size_rcons - cats1 - addn1 iotaD map_cat in Hpref.
      apply (f_equal (take (size u))) in Hpref ; erewrite take_size_cat in Hpref ; [ | auto].
      now erewrite take_size_cat in Hpref ; [ | now rewrite size_map size_iota].
    }
    remember (P u) as b ; destruct b.
    + now apply IHu.
    + exists (rcons u a).
      
     
Qed.

Lemma barred_Bseq_cont (P : seq O -> bool) :
  barred P ->
  (forall m, P (take m nil) = false) ->
  forall alpha, exists u, 
    Bieval (pred_to_Bitree_aux P nil) alpha (size u) = Some u.
Proof.
  intros Hbar Hnot alpha ; specialize (Hbar alpha) as [u [Hpref HP]].
  exists (minimal_list_P P nil u).
  destruct (@minimal_list_P_spec P nil u HP) as [Hmint Hminf] ; [intros ? H ; inversion H | ].
  revert alpha Hpref HP Hmint Hminf Hnot.
  change u with (nil ++ u) at 1 2 ; generalize (@nil O) as l.
  induction u as [ | a u IHu] ; intros l.
  - cbn in *.
    rewrite cats0 ; induction l as [ | a l IHl].
    all:cbn in * ; intros alpha Hpref HP ; now rewrite HP.
  - intros alpha Hpref HP Hmint Hminf Hnot ; cbn in *.
    have aux:= Hnot (size l) ; rewrite take_size in aux ; rewrite aux.
    rewrite aux in Hmint, Hminf.
    remember (size (minimal_list_P P (rcons l a) u)) as m.
    destruct m.
    + symmetry in Heqm ; apply size0nil in Heqm.
      rewrite Heqm in Hmint ; specialize (Hnot 0).
      rewrite take0 in Hnot ; rewrite Hnot in Hmint ; now inversion Hmint.
    + cbn in * ; rewrite aux.
      erewrite <- IHu.
      rewrite - Heqm .
      cbn in * ; rewrite aux.
      eapply IHu.
    
    + now intros alpha Hpref HP ; cbn in * ; rewrite HP.
    revert alpha Hpref HP
  
  
  intros Hbar alpha ; apply barred_Bseq_cont_aux with P alpha in Hbar.
  destruct Hbar as [u [Htake Heval]].
  exists u.
  specialize (Heval 0
  forall alpha, exists u,
    (forall n, n < size u -> P (take n u) = false) /\
      forall n, n < size u ->
                Bieval (pred_to_Bitree_aux P (take n u)) alpha (size u - n) = Some u. 

  
}
    specialize (IHu Hpref') as [v [HP Heval]].
    remember (P u) as b ; destruct b.
    + exists v ; split ; auto.
    + exists v ; split ; auto.
    + exists (rcons u a) ; split.
  
  exists u.
  suff: forall l, prefix alpha (l ++ u) ->
                  P (l ++ u) ->
                  Bieval (pred_to_Bitree_aux P l) alpha (size u) = Some (l ++ u).
  { intros Hyp ; apply (Hyp nil) ; cbn ; auto. }
  clear ; induction u as [ | a u IHu] ; intros l Hpref HP ; cbn in *.
  - rewrite cats0 in Hpref, HP ; now rewrite HP cats0.
  - 
  *)
  
Proposition CoCI_BI (P : list O -> bool) :
  barred P -> inductively_barred P.
Proof.
  unfold inductively_barred ; intros HP.
  unfold barred in HP.
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


Lemma pred_to_Bitree_inv1 P l a :
  pred_to_Bitree_aux P l = Bret _ a -> l = a.
Proof.
  remember (pred_to_Bitree_aux P l) as aux.
  destruct aux.
  - unfold pred_to_Bitree_aux in *.
    inversion Heqaux.
  
  destruct (pred_to_Bitree_aux P l).
  destruct l ; cbn in *.
  case_eq (P l) ; intros Heq ; unfold pred_to_Bitree_aux in H.
  - rewrite Heq in H. ; now inversion H.
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

End ContinuousInductionCoind.



Section BarInduction.

  (*The aim of this Section is to prove that Sequential continuity + Bar Induction
   implies Dialogue continuity for I = nat.*)
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
  Bseq_cont F ->
  Bseq_cont_valid F.
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


Section BarInductionCoind.
  
Variable BI : forall A T, @BI_ind A T.
Variables O A : Type.
Notation I := nat.
Implicit Type (F : (I -> O) -> A).
Implicit Type (b : @Bitree O A).

Print hereditary_closure.

Lemma Bseq_cont_to_dialogue_cont_Brouwer F :
  Bseq_cont_interaction F -> dialogue_cont_Brouwer F.
Proof.
  intros [b Hb].
  pose (T:= fun l => exists r, Bitree_to_option b l = Some r).
   have Help : barred T.
  { intros alpha.
    specialize (Hb alpha) as [n HF].
    exists (map alpha (iota 0 n)) ; unfold T, prefix.
    split ; [ erewrite size_map ; now erewrite size_iota | ].
    exists (F alpha).
    now rewrite - Bitree_to_option_Bieval.
  }
  eapply BI in Help.
  eapply Delta0_choice in Hb as [HF].
  2:{
    intros α n. destruct Bieval eqn:E.
    - left. destruct (Hb α) as [m Hm].
      rewrite - E ; clear Hb Help T ; revert b E m Hm.
      generalize (F α) as a' ; clear F ; revert α.
      induction n ; intros ; [destruct b, m ; cbn in * ; inversion E ; inversion Hm ; now subst | ].
      destruct b ; cbn in * ; [destruct m ; inversion Hm ; now subst | ].
      destruct m ; [now inversion Hm | cbn in * ].
      eapply IHn ; eauto.
    - firstorder congruence.
  }
  suff: forall l, hereditary_closure T l ->
                  {d : Btree | forall f,
                    exists n, Bitree_to_option b (l ++ (map f (iota (size l) n))) = Some (beval d (n_comp f (size l)))}.
  { intros H ; specialize (H nil Help) as [d Hd] ; auto ; cbn.
    exists d ; intros f.
    specialize (HF f) as [n Hn] ; specialize (Hd f) as [m Hm].
    rewrite - Bitree_to_option_Bieval in Hm.
    eapply Bieval_output_unique ; eauto.
  }
  clear F HF Help ; intros l Help.
  pattern l.
  eapply hereditary_closure_rect in Help.
  - exact Help.
  - unfold T ; intros u ; destruct (Bitree_to_option b u) ; [now eauto | ].
    right ; intros [a Hyp] ; now inversion Hyp.
  - clear l Help ; intros u Hu ; cbn.
    remember (Bitree_to_option b u) as r ; destruct r.
    + exists (spit a) ; intros alpha ; exists 0 ; cbn ; now rewrite cats0.
    + exfalso ; destruct Hu as [a Ha] ; rewrite Ha in Heqr.
      now inversion Heqr.
  - intros u k IHk ; cbn in *.
    unshelve eexists.
    + apply bite ; intros o.
      exact (proj1_sig (IHk o)).
    + intros alpha ; cbn ; rewrite n_comp_n_plus addn0.
      destruct (IHk (alpha (size u))) as [x IHx].
      destruct (IHx alpha) as [n Hn] ; cbn in *.
      rewrite size_rcons in Hn ; cbn in *.
      exists (S n) ; cbn ; now rewrite - Hn - cats1 - catA cat1s.
Qed.

End BarInductionCoind.


Section GeneralisedBarInduction.
(*We generalize the previous result and aim to prove that 
  Sequential continuity + Generalized Bar Induction 
   implies Dialogue continuity for any type I with decidable equality.*)
Variable I : eqType.
Variables O A : Type.
Implicit Type (F : (I -> O) -> A).
Variable HGBI : forall T, @GBI I O T.

(*We start with two small lemmas about Add that will be useful later on.*)

Lemma Add_rcons {X : Type} (a : X) (l : seq X): List.Add a l (rcons l a).
Proof.
  induction l ; cbn.
  - now econstructor.
  - now econstructor.
Qed.

Lemma Add_cat {X : Type} (a : X) (u v w : seq X) :
  List.Add a u v ->
  List.Add a (u ++ w) (v ++ w).
Proof.
  induction 1 ; intros.
  - rewrite - cat1s - catA cat1s.
    now econstructor.
  - rewrite - cat1s - (cat1s x l') - catA - catA cat1s cat1s.
    now econstructor.
Qed.

(*We define is_fun_list, a predicate on lists u : seq (I * O)
 describing the fact that u is a finite approximation of some
 function f : I -> O.*)

Definition is_fun_list (u : seq (I * O)) :=
  forall i j j', List.In (i, j) u -> List.In (i, j') u -> j = j'.

(*Without much surprise, [seq (i, f i) | i <- u] for some list u : seq I
 is a finite approximation of some function.*)

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


(*is_fun_list is downwards closed.*)
Lemma is_fun_list_incl (u v : seq (I * O)) :
  is_fun_list v ->
  List.incl u v ->
  is_fun_list u.
Proof.
  intros Hfun Hincl i j j' Hin Hin'.
  apply Hincl in Hin, Hin' ; eapply Hfun ; eassumption.
Qed.

(*We can concatenate two finite approximations if their domains are disjoint.*)
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
  
(*Some lemmas about adding elements at the beginning or the end 
 of some finite approximation u.*)  
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
    
(*Since we have finite approximations of functions,
 we can consider them as partial functions, through eval_list.*)
Fixpoint eval_list (u : seq (I * O)) (i : I) : option O :=
  match u with
  | nil => None
  | (i', o') :: v => if i == i' then Some o' else eval_list v i
  end.

(*Some lemmas about eval_list.*)
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

Lemma eval_list_map_In (alpha : I -> O) :
  forall u i o, eval_list [seq (i, alpha i) | i <- u] i = Some o -> o = alpha i.
Proof.
  intros u i o H.
  revert H ; induction u ; cbn ; intros ; [now inversion H | ].
  destruct (@eqP I i a) ; subst ; [now inversion H | ].
  now apply IHu.
Qed.

(*We now define evaluation of an extensional tree
 using a finite approximation u : seq (I * O). *)

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

(*If we first evaluate an extensional tree tau with a function f : I -> O and
  reach an output, then we can evaluate tau with a finite approximation
  built from the trace of the previous evaluation.
 This will be useful to go from eval_ext_tree_aux to eval_ext_tree_aux_finapp
 in the final theorem.*)

Lemma eval_ext_tree_finapp_trace (tau : ext_tree) f n a l :
  eval_ext_tree_aux tau f n l = output a ->
  eval_ext_tree_aux_finapp tau [seq (i, f i) | i <- eval_ext_tree_trace_aux tau f n l] n l =
    output a.
Proof.
  assert (aux := @is_fun_map (eval_ext_tree_trace_aux tau f n l) f) ; revert aux.
  change (eval_ext_tree_trace_aux tau f n l) with (nil ++ (eval_ext_tree_trace_aux tau f n l)) at 1 2.
  generalize (@nil I) as u ; revert l.
  induction n as [ | n IHn] ; cbn in * ; intros l u aux Heq.
  { destruct u ; cbn ; [assumption | now rewrite Heq ]. }
  remember (tau l) as r ; destruct r ; cbn in *.
  2: assumption.
  erewrite <- cat_rcons ; erewrite <- cat_rcons in aux.
  suff: eval_list [seq (i, f i) |
                    i <- rcons u s ++ eval_ext_tree_trace_aux tau f n (rcons l (f s))] s =
          Some (f s).
  { intros Hyp ; rewrite Hyp.
    specialize (IHn (rcons l (f s)) (rcons u s)) ; erewrite IHn ; eauto.
  }
  apply In_eval_list ; [assumption | eapply (in_map (fun i => (i, f i)))].
  now rewrite - cats1 - catA cat1s ; eapply List.in_elt.
Qed.  

(*We now prove some technical lemmas proving that 
 eval_ext_tree_aux_finapp is monotone in different ways.*)
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

(*This lemma, a bit ad-hoc, proves that if the evaluation of some
 extensional tree tau using an approximation u is blocked because 
 of lack of fuel, although, the answer to the question is in u,
 then raising the fuel will lead to the same computation step,
 for any approximation v extending u.
 *)

Lemma eval_ext_tree_aux_finapp_one_step_fuel tau u v l n q a :
  is_fun_list v ->
  List.incl u v ->
  eval_list u q = Some a ->
  eval_ext_tree_aux_finapp tau u n l = ask q ->
  eval_ext_tree_aux_finapp tau u n.+1 l = eval_ext_tree_aux_finapp tau v n.+1 l.
Proof.
  revert u v l q.
  induction n as [ | n IHn] ; intros * Hfunv Hinclv Heval Hasku.
  - cbn in *.
    rewrite Hasku Heval.
    now erewrite eval_list_monotone ; eauto.
  - cbn in *.
    remember (tau l) as aux ; destruct aux as [i | r] ; subst ;
      [ | now inversion Hasku].
    remember (eval_list u i) as aux2 ; destruct aux2 as [ o | ].
    2:{ inversion Hasku ; subst.
        rewrite Heval in Heqaux2 ; now inversion Heqaux2.
    }
    now erewrite eval_list_monotone ; eauto.
Qed.


(*Let us now describe the structure of the proof.
  We want to go from seq_cont F to dialogue_cont F.
 Right now, we can do the following.*)
Lemma GBI_GCI_Fail F :
  seq_cont F ->
  dialogue_cont F.
Proof.
  intros HF.
  apply seq_cont_to_seq_cont_valid in HF.
  destruct HF as [tau [HF Hval]].
  eapply Delta0_choice in HF as [HF].
  2:{ intros α n.
      destruct eval_ext_tree eqn:E.
      - firstorder congruence.
      - left. destruct (HF α) as [m].
        f_equal. 
        eapply eval_ext_tree_output_unique; eauto. 
  }
  pose (T:= fun (l : seq (I * O)) =>
              exists n a, eval_ext_tree_aux_finapp tau l n nil = output a).
  have Help : ABbarred T.
  { intros alpha.
    destruct (HF alpha) as [n Hn].
    exists (eval_ext_tree_trace tau alpha n).
    unfold T.
    exists n, (F alpha).
    now eapply eval_ext_tree_finapp_trace.
  }
  apply HGBI in Help.
    (*What we lack is a way to go from indbarred T [::] to dialogue_cont F.*)
Abort.

(*
  Going from indbarred T [::] to the existence of a suitable dialogue tree is not easy.
  We will do so through several intermediate steps :

 - We will first define a predicate 
      ext_tree_indbarred : ext_tree -> seq (I * O)) -> Type 
   such that ext_tree_indbarred tau nil implies
   {d : dialogue & forall alpha, exists n,
        eval_ext_tree tau alpha n = output (deval d alpha)}.
   This will allow us to go from extensional trees to dialogue trees;

 - We will then define a predicate 
      ext_tree_indbarredP : ext_tree -> seq (I * O) -> Prop
   tailored to go through singleton elimination.
   We will then prove that 
      ext_tree_indbarredP tau l -> ext_tree_indbarred tau l,
   thus going from Prop to Type.

 - We will then prove that
      indbarred (fun l => exists n a,
                            eval_ext_tree_aux_finapp tau l n nil = output a) l ->
      is_fun_list l ->         
      ext_tree_indbarredP tau l
   This is the longest proof of the file.

- Finally, as 
     is_fun_list nil 
  is trivially true, we will retrieve
      indbarred (fun l => exists n a,
                            eval_ext_tree_aux_finapp tau l n nil = output a) nil ->
      ext_tree_indbarredP tau nil,
  which completes our proof.
*)


(*As explained, let us start by ext_tree_indbarred. 
  It is an inductive predicate that describes a tree of computations
  using tau and l, such that on the leaves of the tree
  eval_ext_tree_aux_finapp tau l n nil = output r
  for some r.
  There are three cases for this inductive :
  - ext_tree_eta is the leaf case, where the computation reaches an output r.
  - ext_tree_succ deals with the case when the computation is blocked
    because of the lack of fuel, and it allows us to change n with n.+1.
  - finally, ext_tree_beta deals with the case when the computation is blocked
    because l does not contain the answer to some query q. In that case, we
    branch over every possible answer a : A with l ++ [::(q, a)].
 *)

Inductive ext_tree_indbarred (tau : ext_tree) (l : seq (I * O)) (n : nat) : Type :=
| ext_tree_eta r : is_fun_list l ->
                   eval_ext_tree_aux_finapp tau l n nil = output r ->
                   ext_tree_indbarred tau l n
| ext_tree_succ q a : is_fun_list l ->
                      eval_ext_tree_aux_finapp tau l n nil = ask q ->
                      eval_list l q = Some a ->
                      ext_tree_indbarred tau l n.+1 ->
                      ext_tree_indbarred tau l n
| ext_tree_beta q : is_fun_list l ->
                    eval_ext_tree_aux_finapp tau l n nil = ask q ->
                    eval_list l q = None ->
                    (forall a, ext_tree_indbarred tau (l ++ [:: (q,a)]) n) ->
                      ext_tree_indbarred tau l n.


(*ext_tree_indbarred tau l n indeed allows us to retrieve a dialogue tree d.
 We first prove an auxiliary lemma for any l.*)

Lemma ext_tree_indbarred_dialogue_aux
  (tau : ext_tree) (Hvalid : valid_ext_tree tau)
  (l : list (I * O)) (n : nat)
  (Hyp : ext_tree_indbarred tau l n) :
  {d : dialogue & forall alpha,
        l = map (fun i => (i, alpha i)) (map fst l) ->
        exists n, eval_ext_tree tau alpha n = output (deval d alpha)}.
Proof.
  induction Hyp as [l n r Hfun Heval | l n i o Hfun Hask Hsome k [d IHd] |
                     l n i Hfun Hask Hnone k IHk].
  - exists (eta r).
    intros alpha Heqalpha ; exists n ; cbn in *.
    suff: forall u n l, eval_ext_tree_aux_finapp tau [seq (i, alpha i) | i <- u] n l = output r ->
                        eval_ext_tree_aux tau alpha n l = output r.
    { intros Hyp.
      eapply Hyp with (map fst l) ; cbn.
      now rewrite - Heqalpha.
    }
    clear ; intros.
    revert l H ; induction n ; cbn ; intros ; [assumption | ].
    remember (tau l) as aux ; destruct aux as [q | a] ; [ | assumption ].
    remember (eval_list [seq (i, alpha i) | i <- u] q) as aux2 ; destruct aux2 as [o | ].
    + eapply IHn.
      suff: o = alpha q by (intros Heq ; subst ; assumption).
      eapply eval_list_map_In ; eauto.
    + now inversion H.
  - exists d ; intros alpha Heqalpha.
    now apply (IHd alpha) ; clear IHd.
  - exists (beta i (fun o => projT1 (IHk o))).
    intros alpha Heqalpha ; cbn in *.
    eapply (projT2 (IHk (alpha i))).
    do 2 rewrite map_cat ; now rewrite - Heqalpha.
Qed.    
    
(*We can then prove our desired lemma when l = nil.*)    
    
Lemma ext_tree_indbarred_dialogue
  (tau : ext_tree) (Hvalid : valid_ext_tree tau) (n : nat)
  (Hyp : ext_tree_indbarred tau nil n) :
  {d : dialogue & forall alpha, exists n,
        eval_ext_tree tau alpha n = output (deval d alpha)}.
Proof.
  eapply ext_tree_indbarred_dialogue_aux in Hyp as [d Hd] ; auto.
  exists d.
  intros alpha ; eapply Hd ; reflexivity.
Qed.


(*We now define ext_tree_indbarredP, the same predicate as
 ext_tree_indbarred, albeit living in Prop.
 We tailor it to go through subsingleton elimination.*)

Unset Elimination Schemes.

Inductive ext_tree_indbarredP (tau : ext_tree) (l: seq (I * O)) (n : nat) : Prop :=
| etree_in : is_fun_list l ->
             ((exists q, eval_ext_tree_aux_finapp tau l n nil = ask q /\
                           eval_list l q = None /\
                           (forall a, ext_tree_indbarredP tau (l ++ [:: (q,a)]) n)) \/
                
                (exists r, eval_ext_tree_aux_finapp tau l n nil = output r) \/
                
                (exists q a, eval_ext_tree_aux_finapp tau l n nil = ask q /\
                             eval_list l q = Some a /\
                             ext_tree_indbarredP tau l n.+1)) ->
             ext_tree_indbarredP tau l n.

Set Elimination Schemes.

(*ext_tree_indbarredP can be eliminated into Type.*)

Fixpoint ext_tree_indbarredP_rect
  (tau : ext_tree)
  (P : seq (I * O) -> nat -> Type)
  (Hout : forall (l : seq (I * O)) (n : nat) (r : A) (Hfun : is_fun_list l)
                 (e : eval_ext_tree_aux_finapp tau l n [::] = output r), 
      P l n)
  (Hsucc : forall (l : seq (I * O)) (n : nat) (q : I) (a : O) (Hfun : is_fun_list l)
                 (Heq : eval_ext_tree_aux_finapp tau l n [::] = ask q)
                 (Hnone : eval_list l q = Some a)
                 (e : ext_tree_indbarredP tau l n.+1),
      P l n.+1 -> P l n)
  (Hask : forall (l : seq (I * O)) (n : nat) (q : I) (Hfun : is_fun_list l)
                 (Heq : eval_ext_tree_aux_finapp tau l n [::] = ask q)
                 (Hnone : eval_list l q = None)
                 (e : forall a : O, ext_tree_indbarredP tau (l ++ [:: (q,a)]) n),
      (forall a : O, P (l ++ [:: (q,a)]) n) -> P l n)
  (l : seq (I * O)) (n : nat) (e : ext_tree_indbarredP tau l n) : P l n.
Proof.
  destruct e as [Hnodup Hq].
  remember (eval_ext_tree_aux_finapp tau l n [::]) as aux.
  destruct aux as [q | r].
  - remember (eval_list l q) as aux2 ; destruct aux2 as [a | ].
    + suff: ext_tree_indbarredP tau l n.+1.
      { intros Hyp ; eapply Hsucc ; eauto. 
        now apply (ext_tree_indbarredP_rect tau P Hout Hsucc Hask).
      }
      destruct Hq as [[q' [Heq [Hnone Hq']]] | [[r Hr] | [q' [a' [Heq' [Hq' IH]]]]]] ;
        [ | now inversion Hr |  ].
      * injection Heq ; intros Heqq ; subst.
        rewrite Hnone in Heqaux2 ; now inversion Heqaux2.
      * inversion Heq' ; subst.
        rewrite Hq' in Heqaux2 ; inversion Heqaux2 ; now subst.
    + suff: forall a : O, ext_tree_indbarredP tau (l ++ [:: (q, a)]) n.
      { intros Hyp.
        eapply (Hask l n q Hnodup) ; [now auto | now symmetry | assumption | ] ; intros a.
        apply (ext_tree_indbarredP_rect tau P Hout Hsucc Hask) ; now apply Hyp.
      }
      destruct Hq as [[q' [Heq' Ho]]| [[r Hr] | [q' [a' [Heval [Hsome Hsuc]]]]]] ;
        [| now inversion Hr | ].
      * inversion Heq' ; subst ; now eapply Ho.
      * exfalso.
        injection Heval ; intros Heq ; subst.
        rewrite Hsome in Heqaux2 ; now inversion Heqaux2.
  - eapply (Hout l n r Hnodup).
    destruct Hq as [[q [Heq Ho]]| [[r' Hr] | [q' [a' [Heval _]]]]] ; [ now inversion Heq | | now inversion Heval ].
    inversion Hr ; now subst.
Defined.

(*We also provide an eliminator into Prop for the induction tactic later on.*)

Lemma ext_tree_indbarredP_ind
  (tau : ext_tree)
  (P : seq (I * O) -> nat -> Prop)
  (Hout : forall (l : seq (I * O)) (n : nat) (r : A) (Hfun : is_fun_list l)
                 (e : eval_ext_tree_aux_finapp tau l n [::] = output r), 
      P l n)
  (Hsucc : forall (l : seq (I * O)) (n : nat) (q : I) (a : O) (Hfun : is_fun_list l)
                 (Heq : eval_ext_tree_aux_finapp tau l n [::] = ask q)
                 (Hnone : eval_list l q = Some a)
                 (e : ext_tree_indbarredP tau l n.+1),
      P l n.+1 -> P l n)
  (Hask : forall (l : seq (I * O)) (n : nat) (q : I) (Hfun : is_fun_list l)
                 (Heq : eval_ext_tree_aux_finapp tau l n [::] = ask q)
                 (Hnone : eval_list l q = None)
                 (e : forall a : O, ext_tree_indbarredP tau (l ++ [:: (q,a)]) n),
      (forall a : O, P (l ++ [:: (q,a)]) n) -> P l n)
  (l : seq (I * O)) (n : nat) (e : ext_tree_indbarredP tau l n) : P l n.
Proof.
  eapply ext_tree_indbarredP_rect ; eauto.
Qed.  


(*ext_tree_indbarredP indeed implies ext_tree_indbarred.*)
Lemma ext_tree_indbarred_spec (tau : ext_tree) (l : seq (I * O)) (n : nat) :
  ext_tree_indbarredP tau l n ->
  ext_tree_indbarred tau l n.
Proof.
  induction 1 as [l a Hnodup Heqa | l q Hnodup Heq ? IHk  | Hsuc].
  - econstructor 1 ; eassumption.
  - econstructor 2 ; eauto. 
  - econstructor 3 ; now eauto.
Qed.


(*We will now try to go from indbarred to ext_tree_indbarred.
 We need some technical lemmas for this.*)


(*ext_tree_indbarredP is monotone with respect to list inclusion.*)

Lemma ext_tree_indbarredP_monotone tau u v n
  (Hu : ext_tree_indbarredP tau u n) :
  is_fun_list v ->
  List.incl u v ->
  ext_tree_indbarredP tau v n.
Proof.
  revert v ; induction Hu as [u n a Hnodup Heqa | u n q o' Hfunu Heq Hsome _ IHk |
                               u n q Hfunu Heq Hnoneu _ IHk] ; intros v Hfunv Hincl.
  - econstructor ; [eassumption | right ; left ; exists a].
    eapply eval_ext_tree_aux_finapp_monotone_output_list ; eassumption.
  - econstructor ; [assumption | right ; right].
    exists q, o' ; split ; [ | split].
    + now eapply eval_ext_tree_aux_finapp_monotone_ask_list_nomorefuel ; eauto.
    + now eapply eval_list_monotone ; eauto.
    + now apply IHk.
  - remember (eval_list v q) as aux ; destruct aux as [ a | ].
    + apply (IHk a _ Hfunv).
      apply List.incl_app ; [assumption | ].
      intros [q' o'] [Hyp | Hyp] ; inversion Hyp; subst.
      now apply eval_list_In.
    + econstructor ; [assumption | ].
      left ; exists q ; split ; [ | split ; [now auto | ] ].
      2: intros a ; apply (IHk a) ; [now apply eval_list_none_fun | auto].
      * eapply eval_ext_tree_aux_finapp_monotone_ask_list ; now eauto.
      *  apply List.incl_app ; [ now apply List.incl_appl | ].
         now apply List.incl_appr, List.incl_refl.
Qed.

(*The fuel n : nat is in fact irrelevant, and if 
 we have ext_tree_indbarred tau u n then we have
 ext_tree_indbarred tau u m for any other m.*)

Lemma ext_tree_indbarredP_change_fuel tau u n m
  (Hu : ext_tree_indbarredP tau u n) :
  ext_tree_indbarredP tau u m.
Proof.
  revert m ; induction Hu as [u n a Hnodup Heqa | u n q o Hfunu Heq Hsome _ IHu |
                               u n q Hfunu Heq Hnoneu _ IHu] ; intros m.
  - econstructor ; [ assumption | ].
    case: (leqP n m) ; intros Hinf ; [ | apply leqW in Hinf ; cbn in Hinf] ;
      apply subnKC in Hinf.
    + rewrite - Hinf; right ; left ; exists a.
      now eapply eval_ext_tree_aux_finapp_monotone_output_fuel.
    + revert Hinf ; generalize (n - m) as k.
      intros k; revert m n Heqa ; induction k ; intros m n Heqa Hinf.
      * rewrite addn0 in Hinf ; subst.
        eauto.
      * remember (eval_ext_tree_aux_finapp tau u m [::]) as aux.
        destruct aux as [q | r] ; [ | now eauto].
        right ; right.
        remember (eval_list u q) as aux2 ; destruct aux2 as [o | ].
        -- exists q, o ; split ; [auto | split ; [auto | ] ].
           econstructor ; [ assumption | ].
           specialize (IHk m.+1).
           eapply IHk ; [eauto | ].
           now rewrite addSn - addnS.
        -- symmetry in Heqaux ; rewrite - Hinf in Heqa.
           erewrite eval_ext_tree_aux_finapp_monotone_ask_fuel in Heqa ; eauto.
           now inversion Heqa.
  - now eapply IHu.
  - econstructor ; [ assumption | ].
    case: (leqP n m) ; intros Hinf ; [ | apply leqW in Hinf ; cbn in Hinf] ;
      apply subnKC in Hinf.
    + rewrite - Hinf; left ; exists q ; split ; [ | split ; eauto].
      now eapply eval_ext_tree_aux_finapp_monotone_ask_fuel ; eauto.
    + revert Hinf ; generalize (n - m) as k.
      intros k; revert m n Heq ; induction k ; intros m n Heq Hinf.
      * rewrite addn0 in Hinf ; subst ; now eauto.
      * remember (eval_ext_tree_aux_finapp tau u m [::]) as aux.
        destruct aux as [q' | r] ; [ | now eauto].
        remember (eval_list u q') as aux2 ; destruct aux2 as [o | ].
        -- right ; right ; exists q', o ; split ; [auto | split ; [auto | ] ].
           econstructor ; [ assumption | ].
           specialize (IHk m.+1).
           eapply IHk ; [eauto | ].
           now rewrite addSn - addnS.
        -- symmetry in Heqaux ; rewrite - Hinf in Heq.
           erewrite eval_ext_tree_aux_finapp_monotone_ask_fuel in Heq ; eauto.
Qed.


(*When going from some version of indbarred to ext_tree_indbarredP,
 the difficult part will be dealing with the split case.
 Indeed, in indbarred splitting can be done on any query q, while
 in ext_tree_indbarredP it has to be done on a precise query q such that
       eval_ext_tree_aux_finapp tau u (size u) = ask q.

 We thus need to reorganise splittings, or even get rid of them 
 in branches where they are not necessary.

 To do this, we use the predicate List.Add, which generalizez addition
 of an element to the list u anywhere in the list, and not only at the end.
 This is the longest and most technical proof of the file.*)

Lemma Add_induction_step (tau : ext_tree) (u v : seq (I * O)) (n : nat) (i : I) (o : O) :
  eval_list u i = None ->
  List.Add (i, o) u v ->
  (ext_tree_indbarredP tau v n) ->
  (forall a w, List.Add (i, a) u w ->
               ext_tree_indbarredP tau w n) ->
  ext_tree_indbarredP tau u n.
Proof.
  intros Hnone Hadd Hv Hyp.
  have Hincl : List.incl u v.
  { intros x Hin ; eapply List.Add_in ; [eassumption | now right]. }
  revert u Hincl Hnone Hadd Hyp.
  induction Hv as [l n a Hnodup Heqa | l n q o' Hfunl Heq Hsome k IHk |
                    l n q Hfunl Heq Hnonel k IHk] ; intros.
  all: have Hfunu : is_fun_list u by (eapply is_fun_list_incl ; eassumption). 
  - remember (eval_ext_tree_aux_finapp tau u n nil) as aux.
    destruct aux as [q' | r].
    2: econstructor ; [ assumption | right ; left ; now exists r].
    remember (eval_list u q') as aux2 ; destruct aux2 as [a' | ].
    + econstructor ; [assumption | right ; right ; exists q', a' ].
      split ; [now auto | split ; [now auto | ] ].
      symmetry in Heqaux.
      eapply (eval_ext_tree_aux_finapp_monotone_ask_list_nomorefuel (v := l)) in Heqaux ;
        eauto.
      rewrite Heqaux in Heqa ; now inversion Heqa.
    + destruct (@eqP I q' i) as [Heq' | Hnoteq] ; [subst | ].
      * econstructor ; [assumption | ].
        left ; exists i ; split ; [auto | split ; [assumption | ] ].
        intros a' ; apply (Hyp a').
        rewrite cats1 ; now apply Add_rcons.
      * exfalso.
        suff: eval_ext_tree_aux_finapp tau l n [::] = ask q'.
        { intros Heq' ; rewrite Heq' in Heqa ; now inversion Heqa. }
        eapply eval_ext_tree_aux_finapp_monotone_ask_list ; eauto.
        eapply eval_list_incl_none with (u ++ [:: (i, o)]) ; eauto.
        -- now apply eval_list_none_fun.
        -- intros x Hinx.
           eapply (List.Add_in Hadd) in Hinx.
           destruct Hinx as [Hl | Hr] ; apply List.in_or_app ; [right | ] ; now left.
        -- apply eval_list_notin_cat ; [now auto | cbn].
           intros [Heqi | Hfalse] ; auto.
  - remember (eval_ext_tree_aux_finapp tau u n nil) as aux.
    destruct aux as [q' | r].
    2: econstructor ; [ auto | right ; left ; now exists r ].
    remember (eval_list u q') as aux2 ; destruct aux2 as [a | ].
    + econstructor ; [ auto | ].
      right ; right ; exists q',a.
      split ; [now auto | split ; [now auto | ] ].
      eapply IHk ; eauto.
      intros a' w Haddw ; eapply ext_tree_indbarredP_change_fuel ; eauto.
    + destruct (@eqP I q' i) as [Heqi | Hnoteq] ; [subst | exfalso ].
      * econstructor ; [assumption | left].
        exists i ; split ; [auto | split ; [auto | ] ].
        intros a ; apply (Hyp a).
        rewrite cats1 ; now apply Add_rcons.
      * suff: eval_list l q' = None ; [ intros auxl | ].
        -- suff: ask (R := A) q = ask q' by
             (intros H ; inversion H ; subst ; rewrite auxl in Hsome ; inversion Hsome).
           rewrite - Heq.
           eapply eval_ext_tree_aux_finapp_monotone_ask_list ; eauto.
        -- eapply eval_list_incl_none with (u ++ [::(i, o)]).
           ++ now apply eval_list_none_fun.
           ++ intros x Hinx ; eapply (List.Add_in Hadd) in Hinx.
              destruct Hinx as [Hinx | Hinx] ; eapply List.in_or_app ; [| now left].
              right ; now left.
           ++ eapply eval_list_notin_cat ; auto ; cbn.
              intros [Hin | Hin] ; inversion Hin ; now auto.
  - remember (eval_ext_tree_aux_finapp tau u n nil) as aux.
    destruct aux as [q' | r].
    2: econstructor ; [ assumption | right ; left ; now exists r ].
    remember (eval_list u q') as aux2 ; destruct aux2 as [a | ].
    + econstructor ; [ assumption | ].
      right ; right ; exists q',a.
      split ; [now auto | split ; [now auto | ] ].
      remember (eval_ext_tree_aux_finapp tau u n.+1 nil) as aux3.
      destruct aux3 as [q'' | r].
      2: econstructor ; [ assumption | right ; left ; now exists r ].
      have Heqq: q'' = q ; [ | subst].
      { suff: ask (R := A) q'' = ask q by (intros H ; inversion H).
        eapply (eval_ext_tree_aux_finapp_monotone_ask_fuel 1) in Heq ; eauto.
        rewrite Heqaux3 - Heq addn1.
        eapply eval_ext_tree_aux_finapp_one_step_fuel ; eauto.
      }
      econstructor ; [assumption | left].
      exists q ; split ; [auto | split ; [now apply eval_list_incl_none with l | ] ].
      intros o'.
      have Hnoneu: eval_list (u ++ [:: (q, o')]) i = None.
      { apply eval_list_notin_cat ; [assumption | cbn].
        intros [Heqi | Hfalse] ; [ subst | now inversion Hfalse].
        suff: eval_list l i = Some o by (intros H ; rewrite Hnonel in H ; now inversion H).
        apply (In_eval_list Hfunl), (List.Add_in Hadd) ; now left.
      }
      eapply ext_tree_indbarredP_change_fuel with n.
      eapply (IHk o') ; eauto.
      -- apply List.incl_app ; [now apply List.incl_appl | ].
         apply List.incl_appr, List.incl_refl.
      -- now apply Add_cat.
      -- intros a' w Haddw.
         eapply ext_tree_indbarredP_monotone with ((i,a') :: u).
         ** now apply Hyp with a', List.Add_head.
         ** eapply is_fun_list_incl with ((u ++ [:: (q, o')]) ++ [::(i, a')]).
            { apply eval_list_none_fun ; auto ; apply eval_list_none_fun ; auto.
              apply eval_list_incl_none with l ; eauto.
            }
            intros y Hiny ; apply (List.Add_in Haddw) in Hiny.
            destruct Hiny as [Hiny | Hiny] ; [subst | ].
            --- apply List.in_or_app ; right ; now left.
            --- apply List.in_or_app ; now left.
         ** intros x Hinx.
            eapply (List.Add_in Haddw) ; rewrite - cat_cons.
            apply List.in_or_app ; now left.
    + suff: q' = i \/ (q' <> i /\ q' = q) ; [intros [Heqi | [Hnoteq Heqq] ] ; subst | ].
      * econstructor ; [assumption | ].
        left ; exists i ; split ; [auto | split ; [ auto | intros o'] ].
        apply (Hyp o') ; rewrite cats1 ; now apply Add_rcons.
      * econstructor ; [assumption | ].
        left ; exists q ; split ; [auto | split ; [ auto | ] ].
        intros o' ; eapply (IHk o').
        -- apply List.incl_app ; [now apply List.incl_appl | ].
           apply List.incl_appr, List.incl_refl.
        -- apply eval_list_notin_cat ; [assumption | ].
           cbn ; intros [Heqi | Hfalse] ; subst ; now auto.
        -- now apply Add_cat.
        -- intros a w Haddw.
           eapply ext_tree_indbarredP_monotone with ((i,a) :: u).
           ++ now apply Hyp with a, List.Add_head.
           ++ eapply is_fun_list_incl with ((u ++ [:: (q, o')]) ++ [::(i, a)]).
              { apply eval_list_none_fun ; auto ; [ now apply eval_list_none_fun | ].
                apply eval_list_notin_cat ; auto ; cbn.
                intros [Heqi | Hfalse] ; [now subst | now inversion Hfalse].
              }
              intros y Hiny ; apply (List.Add_in Haddw) in Hiny.
              destruct Hiny as [Hiny | Hiny] ; [subst | ].
              ** apply List.in_or_app ; right ; now left.
              ** apply List.in_or_app ; now left.
           ++ intros x Hinx.
              eapply (List.Add_in Haddw) ; rewrite - cat_cons.
              apply List.in_or_app ; now left.
      * destruct (@eqP I q' i) as [ | Hnoteq] ; [now left | right ; split ; auto].
        suff: ask (R := A) q = ask q' by (inversion 1).
        erewrite <- Heq ; eauto.
        eapply eval_ext_tree_aux_finapp_monotone_ask_list ; eauto.
        eapply eval_list_incl_none with ((i,o) :: u).
        -- eapply is_fun_cons_notin_dom ; eauto ; now apply eval_list_notin.
        -- intros x Hinx ; now apply (List.Add_in Hadd) in Hinx.
        -- cbn ; erewrite ifN_eq ; [now auto | ].
           now eapply contra_not_neq with (q' = i).
Qed.


(*Using the previous lemma, we can now go from indbarred to ext_tree_indbarredP. *)


(*We first prove an auxiliary lemma assuming that O is inhabited.*)

Lemma indbarred_fun_list_ext_tree_indbarredP_aux
  (tau : ext_tree) (l : seq (I * O)) (o : O) :
  indbarred
    (fun u => exists n a, eval_ext_tree_aux_finapp tau u n nil = output a) l ->
  is_fun_list l ->
  ext_tree_indbarredP tau l 0.
Proof.
  intros Hyp.
  induction Hyp as [u v [n [r Hr]] Hincl | q v Hnotin _ IHk]; intros Hfun.
  - eapply ext_tree_indbarredP_change_fuel with n ; eauto.
    econstructor ; [eassumption | right ; left ; exists r].
    now eapply eval_ext_tree_aux_finapp_monotone_output_list ; eauto.
  - unshelve eapply Add_induction_step with (v ++ [::(q,o)]) q o.
    + rewrite - (cat0s v) ; apply eval_list_notin_cat; auto.
    + rewrite cats1 ; now apply Add_rcons.
    + eapply ext_tree_indbarredP_change_fuel, IHk.
      rewrite cats1 ; now apply is_fun_rcons_notin_dom.
    + intros o' w Haddw.
      have Hincl: List.incl (v ++ [:: (q, o')]) w.
      { intros x Hx ; apply (List.Add_in Haddw).
        apply List.in_app_or in Hx ; now destruct Hx as [|[|]] ; [ right | left | left ].
      }
      eapply ext_tree_indbarredP_monotone ; [ | | eassumption].
      * eapply ext_tree_indbarredP_change_fuel, IHk.
        rewrite cats1 ; now apply is_fun_rcons_notin_dom.
      * apply is_fun_list_incl with (v ++ [::(q, o')]).
        -- rewrite cats1 ; now apply is_fun_rcons_notin_dom.
        -- intros x Hx ; apply (List.Add_in Haddw) in Hx.
           destruct Hx as [Hx | Hx] ; [subst | ] ; apply List.in_or_app ; eauto.
           now right ; left.
Qed.


(* We now prove the real lemma by destructing the list l to retrieve o : O.*)


Lemma indbarred_fun_list_ext_tree_indbarredP (tau : ext_tree) (l : seq (I * O)) :
  indbarred
    (fun u => exists n a, eval_ext_tree_aux_finapp tau u n nil = output a) l ->
  is_fun_list l ->
  ext_tree_indbarredP tau l 0.
Proof.
  destruct l as [ | [i o] l] ; intros Hyp Hfun.
  2: now eapply indbarred_fun_list_ext_tree_indbarredP_aux ; eauto.
  econstructor ; [intros i j K H ; inversion H | cbn ].
  remember (tau nil) as aux ; destruct aux as [q | r] ; [ | right ; left ; now exists r].
  left ; exists q ; split ; [auto | split ; [auto | ] ].
  intros o.
  eapply ext_tree_indbarredP_monotone with nil.
  - now eapply indbarred_fun_list_ext_tree_indbarredP_aux.
  - intros i a a' [Ha | Ha] [Ha' | Ha'] ; inversion Ha ; inversion Ha' ; now subst.
  - now apply List.incl_nil_l.
Qed.
  
  
(*We are now ready to prove our theorem.*)
  
Theorem GBI_GCI F :
  seq_cont F ->
  dialogue_cont F.
Proof.
  intros HF ; apply seq_cont_to_seq_cont_valid in HF.
  destruct HF as [tau [HF Hval]].
  pose (T:= fun (l : seq (I * O)) =>
              exists n a, eval_ext_tree_aux_finapp tau l n nil = output a).
  have Help : ABbarred T.
  { intros alpha.
    destruct (HF alpha) as [n Hn].
    exists (eval_ext_tree_trace tau alpha n), n, (F alpha).
    now eapply eval_ext_tree_finapp_trace.
  }
  have fun_nil : is_fun_list nil by (intros i j j' Hinj ; inversion Hinj).
  apply HGBI, indbarred_fun_list_ext_tree_indbarredP
    in Help ; auto.
  eapply ext_tree_indbarred_spec, (ext_tree_indbarred_dialogue Hval) in Help ; auto.
  destruct Help as [d Hd].
  exists d ; intros alpha.
  specialize (HF alpha) as [n Hn] ; specialize (Hd alpha) as [m Hm].
  eapply eval_ext_tree_output_unique ; now eauto.
Qed.  
  
  
End GeneralisedBarInduction.

Section GeneralisedBarInductionCoind.
(*We generalize the previous result and aim to prove that 
  Sequential continuity + Generalized Bar Induction 
   implies Dialogue continuity for any type I with decidable equality.*)
Variable I : eqType.
Variables O A : Type.
Implicit Type (F : (I -> O) -> A).
Variable HGBI : forall T, @GBI I O T.
Notation Itree := (@Itree I O A).


Fixpoint ieval_trace (i : Itree) (f : I -> O) (n : nat) : list I :=
  match n with
  | 0 => nil
  | S m => match i with
           | ret o => nil
           | vis q k => q :: (ieval_trace (k (f q)) f m)
           end
  end.

Fixpoint ieval_finapp (i : Itree) (l : seq (I * O)) (n : nat) : result :=
  match n with
  | 0 => match i with
         | ret o => output o
         | vis q k => ask q
         end
  | S n => match i with
           | ret o => output o
           | vis q k => match (eval_list l q) with
                        | Some o => ieval_finapp (k o) l n
                        | None => ask q
                        end
           end
  end.

Lemma ieval_finapp_trace tau f n a :
  ieval tau f n = output a ->
  ieval_finapp tau [seq (i, f i) | i <- ieval_trace tau f n] n =
    output a.
Proof.
  assert (aux := @is_fun_map _ _ (ieval_trace tau f n) f) ; revert aux.
  change (ieval_trace tau f n) with (nil ++ (ieval_trace tau f n)) at 1 2.
  generalize (@nil I) as u.
  revert f a tau ; induction n as [ | n IHn] ; intros * aux Heq.  
  - cbn in * ; destruct tau ; now inversion Heq.
  - cbn in * ; destruct tau as [ | q k] ; [now inversion Heq | ].
    suff : eval_list [seq (i, f i) | i <- u ++ q :: ieval_trace (k (f q)) f n] q = Some (f q).
    + intros Hyp ; rewrite Hyp - cat1s catA cats1.
      apply IHn ; auto.
      now rewrite -cats1 -catA cat1s.
    + apply In_eval_list ; auto ; eapply (in_map (fun i => (i, f i))).
      now eapply List.in_elt.
Qed.

(*We now prove some technical lemmas proving that 
 eval_itree_aux_finapp is monotone in different ways.*)
Lemma ieval_finapp_monotone_output_list
  (tau : Itree) (u v: seq (I * O)) (n : nat) (a : A) :
  is_fun_list v ->
  List.incl u v ->
  ieval_finapp tau u n = output a ->
  ieval_finapp tau v n = output a.
Proof.
  revert tau u v a; induction n as [| n IHn] ; intros * Hfun Hincl Heq ; [assumption| ].
  cbn in * ; destruct tau as [r | q k] ; [assumption | ].
  remember (eval_list u q) as ev ; destruct ev as [r' | ] ; [| now inversion Heq ].
  erewrite eval_list_monotone ; eauto.
Qed.

Lemma ieval_finapp_monotone_output_fuel
  (tau : Itree) (u: seq (I * O)) (n m : nat) (a : A) :
  ieval_finapp tau u n = output a ->
  ieval_finapp tau u (n + m) = output a.
Proof.
  revert tau ; induction n as [ | n IHn] ; cbn in * ; intros tau H.
  - destruct m ; cbn ; [assumption | destruct tau ; now rewrite H].
  - destruct tau as [ | q k] ; [assumption | ].
    destruct (eval_list u q) ; [ | now inversion H].
    now eapply IHn.
Qed.


Lemma ieval_finapp_monotone_ask_list
  (tau : Itree) (u v: seq (I * O)) (n : nat) (q : I) :
  is_fun_list v ->
  List.incl u v ->
  eval_list v q = None ->
  ieval_finapp tau u n = ask q ->
  ieval_finapp tau v n = ask q.
Proof.
  revert u v tau q.
  induction n as [| n IHn] ; intros * Hfun Hincl Hnotin Heq ; [assumption| ].
  cbn in *.
  destruct tau as [ r | q' k] ; [ assumption | ].
  remember (eval_list u q') as ev ; destruct ev as [r' | ].
  - erewrite eval_list_monotone ; now eauto.
  - injection Heq ; intros Heq' ; subst.
    remember (eval_list v q) as r' ; destruct r' as [q' | ] ; [ | reflexivity].
    symmetry in Heqr' ; apply eval_list_In, (in_map fst) in Heqr'.
    exfalso ; now inversion Hnotin.
Qed.


Lemma ieval_finapp_monotone_ask_fuel
  (tau : Itree) (u : seq (I * O)) (n m : nat) (q : I) :
  is_fun_list u ->
  eval_list u q = None ->
  ieval_finapp tau u n = ask q ->
  ieval_finapp tau u (n + m) = ask q.
Proof.
  revert u n tau q.
  induction n as [| n IHn] ; intros * Hfun Hnotin Heq ; cbn in *.
  - destruct m ; cbn ; [ assumption | destruct tau ; inversion Heq ; subst ; now rewrite Hnotin ].
  - destruct tau as [ r | q' k] ; cbn in * ; [ now inversion Heq | ].
    destruct (eval_list u q') ; cbn in * ; [ now apply IHn | assumption].
Qed.

Lemma ieval_finapp_monotone_ask_list_nomorefuel
  (tau : Itree) (u v: seq (I * O)) (n : nat) (q : I) (a : O) :
  is_fun_list v ->
  List.incl u v ->
  eval_list u q = Some a ->
  ieval_finapp tau u n = ask q ->
  ieval_finapp tau v n = ask q.
Proof.
  revert u v tau q.
  induction n as [| n IHn] ; intros * Hfun Hincl Hnotin Heq ; [assumption| ].
  cbn in * ; destruct tau as [r | q' k] ; auto.
  remember (eval_list u q') as ev ; destruct ev as [r' | ].
  - erewrite eval_list_monotone ; now eauto.
  - injection Heq ; intros Heq' ; subst.
    rewrite Hnotin in Heqev ; now inversion Heqev.
Qed.


Inductive itree_indbarred (d : Itree) (l : seq (I * O)) (n : nat) : Type :=
| itree_eta r : is_fun_list l ->
                ieval_finapp d l n = output r ->
                itree_indbarred d l n
| itree_succ q a : is_fun_list l ->
                      ieval_finapp d l n = ask q ->
                      eval_list l q = Some a ->
                      itree_indbarred d l n.+1 ->
                      itree_indbarred d l n
| itree_beta q : is_fun_list l ->
                    ieval_finapp d l n  = ask q ->
                    eval_list l q = None ->
                    (forall a, itree_indbarred d (l ++ [:: (q,a)]) n) ->
                      itree_indbarred d l n.


(*itree_indbarred tau l n indeed allows us to retrieve a dialogue tree d.
 We first prove an auxiliary lemma for any l.*)

Lemma itree_indbarred_dialogue_aux
  (tau : Itree)
  (l : list (I * O)) (n : nat)
  (Hyp : itree_indbarred tau l n) :
  {d : dialogue & forall alpha,
        l = map (fun i => (i, alpha i)) (map fst l) ->
        exists n, ieval tau alpha n = output (deval d alpha)}.
Proof.
  induction Hyp as [l n r Hfun Heval | l n i o Hfun Hask Hsome k [d IHd] |
                     l n i Hfun Hask Hnone k IHk].
  - exists (eta r).
    intros alpha Heqalpha ; exists n ; cbn in *.
    suff: forall u n, ieval_finapp tau [seq (i, alpha i) | i <- u] n = output r ->
                        ieval tau alpha n = output r.
    { intros Hyp.
      eapply Hyp with (map fst l) ; cbn.
      now rewrite - Heqalpha.
    }
    clear ; intros.
    revert u tau H ; induction n ; cbn ; intros ; [assumption | ].
    destruct tau as [ | q k] ; [ assumption | ].
    remember (eval_list [seq (i, alpha i) | i <- u] q) as aux2.
    destruct aux2 as [o | ] ; [ | now inversion H].
    eapply IHn.
    suff: o = alpha q by (intros Heq ; subst ; eassumption).
    eapply eval_list_map_In ; eauto.
  - exists d ; intros alpha Heqalpha.
    now apply (IHd alpha) ; clear IHd.
  - exists (beta i (fun o => projT1 (IHk o))).
    intros alpha Heqalpha ; cbn in *.
    eapply (projT2 (IHk (alpha i))).
    do 2 rewrite map_cat ; now rewrite - Heqalpha.
Qed.    
    
(*We can then prove our desired lemma when l = nil.*)    
    
Lemma itree_indbarred_dialogue
  (tau : Itree) (n : nat)
  (Hyp : itree_indbarred tau nil n) :
  {d : dialogue & forall alpha, exists n,
        ieval tau alpha n = output (deval d alpha)}.
Proof.
  eapply itree_indbarred_dialogue_aux in Hyp as [d Hd] ; auto.
  exists d.
  intros alpha ; eapply Hd ; reflexivity.
Qed.


(*We now define ext_tree_indbarredP, the same predicate as
 ext_tree_indbarred, albeit living in Prop.
 We tailor it to go through subsingleton elimination.*)

Unset Elimination Schemes.

Inductive itree_indbarredP (tau : Itree) (l: seq (I * O)) (n : nat) : Prop :=
| itree_in : is_fun_list l ->
             ((exists q, ieval_finapp tau l n = ask q /\
                           eval_list l q = None /\
                           (forall a, itree_indbarredP tau (l ++ [:: (q,a)]) n)) \/
                
                (exists r, ieval_finapp tau l n = output r) \/
                
                (exists q a, ieval_finapp tau l n = ask q /\
                             eval_list l q = Some a /\
                             itree_indbarredP tau l n.+1)) ->
             itree_indbarredP tau l n.

Set Elimination Schemes.

(*itree_indbarredP can be eliminated into Type.*)

Fixpoint itree_indbarredP_rect
  (tau : Itree)
  (P : seq (I * O) -> nat -> Type)
  (Hout : forall (l : seq (I * O)) (n : nat) (r : A) (Hfun : is_fun_list l)
                 (e : ieval_finapp tau l n = output r), 
      P l n)
  (Hsucc : forall (l : seq (I * O)) (n : nat) (q : I) (a : O) (Hfun : is_fun_list l)
                 (Heq : ieval_finapp tau l n = ask q)
                 (Hnone : eval_list l q = Some a)
                 (e : itree_indbarredP tau l n.+1),
      P l n.+1 -> P l n)
  (Hask : forall (l : seq (I * O)) (n : nat) (q : I) (Hfun : is_fun_list l)
                 (Heq : ieval_finapp tau l n = ask q)
                 (Hnone : eval_list l q = None)
                 (e : forall a : O, itree_indbarredP tau (l ++ [:: (q,a)]) n),
      (forall a : O, P (l ++ [:: (q,a)]) n) -> P l n)
  (l : seq (I * O)) (n : nat) (e : itree_indbarredP tau l n) : P l n.
Proof.
  destruct e as [Hnodup Hq].
  remember (ieval_finapp tau l n) as aux.
  destruct aux as [q | r].
  - remember (eval_list l q) as aux2 ; destruct aux2 as [a | ].
    + suff: itree_indbarredP tau l n.+1.
      { intros Hyp ; eapply Hsucc ; eauto. 
        now apply (itree_indbarredP_rect tau P Hout Hsucc Hask).
      }
      destruct Hq as [[q' [Heq [Hnone Hq']]] | [[r Hr] | [q' [a' [Heq' [Hq' IH]]]]]] ;
        [ | now inversion Hr |  ].
      * injection Heq ; intros Heqq ; subst.
        rewrite Hnone in Heqaux2 ; now inversion Heqaux2.
      * inversion Heq' ; subst.
        rewrite Hq' in Heqaux2 ; inversion Heqaux2 ; now subst.
    + suff: forall a : O, itree_indbarredP tau (l ++ [:: (q, a)]) n.
      { intros Hyp.
        eapply (Hask l n q Hnodup) ; [now auto | now symmetry | assumption | ] ; intros a.
        apply (itree_indbarredP_rect tau P Hout Hsucc Hask) ; now apply Hyp.
      }
      destruct Hq as [[q' [Heq' Ho]]| [[r Hr] | [q' [a' [Heval [Hsome Hsuc]]]]]] ;
        [| now inversion Hr | ].
      * inversion Heq' ; subst ; now eapply Ho.
      * exfalso.
        injection Heval ; intros Heq ; subst.
        rewrite Hsome in Heqaux2 ; now inversion Heqaux2.
  - eapply (Hout l n r Hnodup).
    destruct Hq as [[q [Heq Ho]]| [[r' Hr] | [q' [a' [Heval _]]]]] ; [ now inversion Heq | | now inversion Heval ].
    inversion Hr ; now subst.
Defined.

(*We also provide an eliminator into Prop for the induction tactic later on.*)

Lemma itree_indbarredP_ind
  (tau : Itree)
  (P : seq (I * O) -> nat -> Prop)
  (Hout : forall (l : seq (I * O)) (n : nat) (r : A) (Hfun : is_fun_list l)
                 (e : ieval_finapp tau l n = output r), 
      P l n)
  (Hsucc : forall (l : seq (I * O)) (n : nat) (q : I) (a : O) (Hfun : is_fun_list l)
                 (Heq : ieval_finapp tau l n = ask q)
                 (Hnone : eval_list l q = Some a)
                 (e : itree_indbarredP tau l n.+1),
      P l n.+1 -> P l n)
  (Hask : forall (l : seq (I * O)) (n : nat) (q : I) (Hfun : is_fun_list l)
                 (Heq : ieval_finapp tau l n = ask q)
                 (Hnone : eval_list l q = None)
                 (e : forall a : O, itree_indbarredP tau (l ++ [:: (q,a)]) n),
      (forall a : O, P (l ++ [:: (q,a)]) n) -> P l n)
  (l : seq (I * O)) (n : nat) (e : itree_indbarredP tau l n) : P l n.
Proof.
  eapply itree_indbarredP_rect ; eauto.
Qed.  


(*itree_indbarredP indeed implies itree_indbarred.*)
Lemma itree_indbarred_spec (tau : Itree) (l : seq (I * O)) (n : nat) :
  itree_indbarredP tau l n ->
  itree_indbarred tau l n.
Proof.
  induction 1 as [l a Hnodup Heqa | l q Hnodup Heq ? IHk  | Hsuc].
  - econstructor 1 ; eassumption.
  - econstructor 2 ; eauto. 
  - econstructor 3 ; now eauto.
Qed.


(*We will now try to go from indbarred to itree_indbarred.
 We need some technical lemmas for this.*)


(*itree_indbarredP is monotone with respect to list inclusion.*)

Lemma itree_indbarredP_monotone tau u v n
  (Hu : itree_indbarredP tau u n) :
  is_fun_list v ->
  List.incl u v ->
  itree_indbarredP tau v n.
Proof.
  revert v ; induction Hu as [u n a Hnodup Heqa | u n q o' Hfunu Heq Hsome _ IHk |
                               u n q Hfunu Heq Hnoneu _ IHk] ; intros v Hfunv Hincl.
  - econstructor ; [eassumption | right ; left ; exists a].
    eapply ieval_finapp_monotone_output_list ; eassumption.
  - econstructor ; [assumption | right ; right].
    exists q, o' ; split ; [ | split].
    + now eapply ieval_finapp_monotone_ask_list_nomorefuel ; eauto.
    + now eapply eval_list_monotone ; eauto.
    + now apply IHk.
  - remember (eval_list v q) as aux ; destruct aux as [ a | ].
    + apply (IHk a _ Hfunv).
      apply List.incl_app ; [assumption | ].
      intros [q' o'] [Hyp | Hyp] ; inversion Hyp; subst.
      now apply eval_list_In.
    + econstructor ; [assumption | ].
      left ; exists q ; split ; [ | split ; [now auto | ] ].
      2: intros a ; apply (IHk a) ; [now apply eval_list_none_fun | auto].
      * eapply ieval_finapp_monotone_ask_list ; now eauto.
      *  apply List.incl_app ; [ now apply List.incl_appl | ].
         now apply List.incl_appr, List.incl_refl.
Qed.

(*The fuel n : nat is in fact irrelevant, and if 
 we have itree_indbarred tau u n then we have
 itree_indbarred tau u m for any other m.*)

Lemma itree_indbarredP_change_fuel tau u n m
  (Hu : itree_indbarredP tau u n) :
  itree_indbarredP tau u m.
Proof.
  revert m ; induction Hu as [u n a Hnodup Heqa | u n q o Hfunu Heq Hsome _ IHu |
                               u n q Hfunu Heq Hnoneu _ IHu] ; intros m.
  - econstructor ; [ assumption | ].
    case: (leqP n m) ; intros Hinf ; [ | apply leqW in Hinf ; cbn in Hinf] ;
      apply subnKC in Hinf.
    + rewrite - Hinf; right ; left ; exists a.
      now eapply ieval_finapp_monotone_output_fuel.
    + revert Hinf ; generalize (n - m) as k.
      intros k; revert m n Heqa ; induction k ; intros m n Heqa Hinf.
      * rewrite addn0 in Hinf ; subst ; now eauto.
      * remember (ieval_finapp tau u m) as aux.
        destruct aux as [q | r] ; [ | now eauto].
        right ; right.
        remember (eval_list u q) as aux2 ; destruct aux2 as [o | ].
        -- exists q, o ; split ; [auto | split ; [auto | ] ].
           econstructor ; [ assumption | ].
           eapply (IHk m.+1) ; [eauto | now rewrite addSn - addnS].
        -- symmetry in Heqaux ; rewrite - Hinf in Heqa.
           erewrite ieval_finapp_monotone_ask_fuel in Heqa ; eauto.
           now inversion Heqa.
  - now eapply IHu.
  - econstructor ; [ assumption | ].
    case: (leqP n m) ; intros Hinf ; [ | apply leqW in Hinf ; cbn in Hinf] ;
      apply subnKC in Hinf.
    + rewrite - Hinf; left ; exists q ; split ; [ | split ; eauto].
      now eapply ieval_finapp_monotone_ask_fuel ; eauto.
    + revert Hinf ; generalize (n - m) as k.
      intros k; revert m n Heq ; induction k ; intros m n Heq Hinf.
      * rewrite addn0 in Hinf ; subst ; now eauto.
      * remember (ieval_finapp tau u m) as aux.
        destruct aux as [q' | r] ; [ | now eauto].
        remember (eval_list u q') as aux2 ; destruct aux2 as [o | ].
        -- right ; right ; exists q', o ; split ; [auto | split ; [auto | ] ].
           econstructor ; [ assumption | ].
           eapply (IHk m.+1) ; [eauto | now rewrite addSn - addnS].
        -- symmetry in Heqaux ; rewrite - Hinf in Heq.
           erewrite ieval_finapp_monotone_ask_fuel in Heq ; eauto.
Qed.


Lemma ieval_finapp_one_step_fuel tau u v n q a :
  is_fun_list v ->
  List.incl u v ->
  eval_list u q = Some a ->
  ieval_finapp tau u n = ask q ->
  ieval_finapp tau u n.+1 = ieval_finapp tau v n.+1.
Proof.
  revert tau u v q.
  induction n as [ | n IHn] ; intros * Hfunv Hinclv Heval Hasku.
  - cbn in *.
    destruct tau ; eauto ; inversion Hasku ; subst.
    now erewrite Heval, eval_list_monotone ; eauto.
  - cbn in *.
    destruct tau as [ | i k ]; eauto.
    remember (eval_list u i) as aux2 ; destruct aux2 as [ o | ].
    2:{ inversion Hasku ; subst.
        rewrite Heval in Heqaux2 ; now inversion Heqaux2.
    }
    now erewrite eval_list_monotone ; eauto.
Qed.

(*When going from some version of indbarred to itree_indbarredP,
 the difficult part will be dealing with the split case.
 Indeed, in indbarred splitting can be done on any query q, while
 in itree_indbarredP it has to be done on a precise query q such that
       ieval_finapp tau u (size u) = ask q.

 We thus need to reorganise splittings, or even get rid of them 
 in branches where they are not necessary.

 To do this, we use the predicate List.Add, which generalizez addition
 of an element to the list u anywhere in the list, and not only at the end.
 This is the longest and most technical proof of the file.*)

Lemma iAdd_induction_step tau (u v : seq (I * O)) (n : nat) (i : I) (o : O) :
  eval_list u i = None ->
  List.Add (i, o) u v ->
  (itree_indbarredP tau v n) ->
  (forall a w, List.Add (i, a) u w ->
               itree_indbarredP tau w n) ->
  itree_indbarredP tau u n.
Proof.
  intros Hnone Hadd Hv Hyp.
  have Hincl : List.incl u v.
  { intros x Hin ; eapply List.Add_in ; [eassumption | now right]. }
  revert u Hincl Hnone Hadd Hyp.
  induction Hv as [l n a Hnodup Heqa | l n q o' Hfunl Heq Hsome k IHk |
                    l n q Hfunl Heq Hnonel k IHk] ; intros.
  all: have Hfunu : is_fun_list u by (eapply is_fun_list_incl ; eassumption). 
  - remember (ieval_finapp tau u n) as aux.
    destruct aux as [q' | r] ; [ | econstructor ; now eauto].
    remember (eval_list u q') as aux2 ; destruct aux2 as [a' | ].
    + econstructor ; [assumption | right ; right ; exists q', a' ].
      split ; [now auto | split ; [now auto | ] ].
      symmetry in Heqaux.
      eapply (ieval_finapp_monotone_ask_list_nomorefuel (v := l)) in Heqaux ;
        eauto.
      rewrite Heqaux in Heqa ; now inversion Heqa.
    + destruct (@eqP I q' i) as [Heq' | Hnoteq] ; [subst | ].
      * econstructor ; [assumption | ].
        left ; exists i ; split ; [auto | split ; [assumption | ] ].
        intros a' ; apply (Hyp a').
        rewrite cats1 ; now apply Add_rcons.
      * exfalso.
        suff: ieval_finapp tau l n = ask q'.
        { intros Heq' ; rewrite Heq' in Heqa ; now inversion Heqa. }
        eapply ieval_finapp_monotone_ask_list ; eauto.
        eapply eval_list_incl_none with (u ++ [:: (i, o)]) ; eauto.
        -- now apply eval_list_none_fun.
        -- intros x Hinx.
           eapply (List.Add_in Hadd) in Hinx.
           destruct Hinx as [Hl | Hr] ; apply List.in_or_app ; [right | ] ; now left.
        -- apply eval_list_notin_cat ; [now auto | cbn].
           intros [Heqi | Hfalse] ; auto.
  - remember (ieval_finapp tau u n) as aux.
    destruct aux as [q' | r] ; [ | econstructor ; now eauto].
    remember (eval_list u q') as aux2 ; destruct aux2 as [a | ].
    + econstructor ; [ auto | ].
      right ; right ; exists q',a.
      split ; [now auto | split ; [now auto | ] ].
      eapply IHk ; eauto.
      intros a' w Haddw ; eapply itree_indbarredP_change_fuel ; eauto.
    + destruct (@eqP I q' i) as [Heqi | Hnoteq] ; [subst | exfalso ].
      * econstructor ; [assumption | left].
        exists i ; split ; [auto | split ; [auto | ] ].
        intros a ; apply (Hyp a).
        rewrite cats1 ; now apply Add_rcons.
      * suff: eval_list l q' = None ; [ intros auxl | ].
        -- suff: ask (R := A) q = ask q' by
             (intros H ; inversion H ; subst ; rewrite auxl in Hsome ; inversion Hsome).
           rewrite - Heq ; now eapply ieval_finapp_monotone_ask_list ; eauto.
        -- eapply eval_list_incl_none with (u ++ [::(i, o)]).
           ++ now apply eval_list_none_fun.
           ++ intros x Hinx ; eapply (List.Add_in Hadd) in Hinx.
              destruct Hinx as [Hinx | Hinx] ; eapply List.in_or_app ; [| now left].
              right ; now left.
           ++ eapply eval_list_notin_cat ; auto ; cbn.
              intros [Hin | Hin] ; inversion Hin ; now auto.
  - remember (ieval_finapp tau u n) as aux.
    destruct aux as [q' | r].
    2: econstructor ; [ assumption | right ; left ; now exists r ].
    remember (eval_list u q') as aux2 ; destruct aux2 as [a | ].
    + econstructor ; [ assumption | ].
      right ; right ; exists q',a.
      split ; [now auto | split ; [now auto | ] ].
      remember (ieval_finapp tau u n.+1) as aux3.
      destruct aux3 as [q'' | r] ; [ | econstructor ; now eauto].
      have Heqq: q'' = q ; [ | subst].
      { suff: ask (R := A) q'' = ask q by (intros H ; inversion H).
        eapply (ieval_finapp_monotone_ask_fuel 1) in Heq ; eauto.
        rewrite Heqaux3 - Heq addn1.
        eapply ieval_finapp_one_step_fuel ; eauto.
      }
      econstructor ; [assumption | left].
      exists q ; split ; [auto | split ; [now apply eval_list_incl_none with l | ] ].
      intros o'.
      have Hnoneu: eval_list (u ++ [:: (q, o')]) i = None.
      { apply eval_list_notin_cat ; [assumption | cbn].
        intros [Heqi | Hfalse] ; [ subst | now inversion Hfalse].
        suff: eval_list l i = Some o by (intros H ; rewrite Hnonel in H ; now inversion H).
        apply (In_eval_list Hfunl), (List.Add_in Hadd) ; now left.
      }
      eapply itree_indbarredP_change_fuel with n.
      eapply (IHk o') ; eauto.
      -- apply List.incl_app ; [now apply List.incl_appl | ].
         apply List.incl_appr, List.incl_refl.
      -- now apply Add_cat.
      -- intros a' w Haddw.
         eapply itree_indbarredP_monotone with ((i,a') :: u).
         ** now apply Hyp with a', List.Add_head.
         ** eapply is_fun_list_incl with ((u ++ [:: (q, o')]) ++ [::(i, a')]).
            { apply eval_list_none_fun ; auto ; apply eval_list_none_fun ; auto.
              apply eval_list_incl_none with l ; eauto.
            }
            intros y Hiny ; apply (List.Add_in Haddw) in Hiny.
            destruct Hiny as [Hiny | Hiny] ; [subst | ].
            --- apply List.in_or_app ; right ; now left.
            --- apply List.in_or_app ; now left.
         ** intros x Hinx.
            eapply (List.Add_in Haddw) ; rewrite - cat_cons.
            apply List.in_or_app ; now left.
    + suff: q' = i \/ (q' <> i /\ q' = q) ; [intros [Heqi | [Hnoteq Heqq] ] ; subst | ].
      * econstructor ; [assumption | ].
        left ; exists i ; split ; [auto | split ; [ auto | intros o'] ].
        apply (Hyp o') ; rewrite cats1 ; now apply Add_rcons.
      * econstructor ; [assumption | ].
        left ; exists q ; split ; [auto | split ; [ auto | ] ].
        intros o' ; eapply (IHk o').
        -- apply List.incl_app ; [now apply List.incl_appl | ].
           apply List.incl_appr, List.incl_refl.
        -- apply eval_list_notin_cat ; [assumption | ].
           cbn ; intros [Heqi | Hfalse] ; subst ; now auto.
        -- now apply Add_cat.
        -- intros a w Haddw.
           eapply itree_indbarredP_monotone with ((i,a) :: u).
           ++ now apply Hyp with a, List.Add_head.
           ++ eapply is_fun_list_incl with ((u ++ [:: (q, o')]) ++ [::(i, a)]).
              { apply eval_list_none_fun ; auto ; [ now apply eval_list_none_fun | ].
                apply eval_list_notin_cat ; auto ; cbn.
                intros [Heqi | Hfalse] ; [now subst | now inversion Hfalse].
              }
              intros y Hiny ; apply (List.Add_in Haddw) in Hiny.
              destruct Hiny as [Hiny | Hiny] ; [subst | ].
              ** apply List.in_or_app ; right ; now left.
              ** apply List.in_or_app ; now left.
           ++ intros x Hinx.
              eapply (List.Add_in Haddw) ; rewrite - cat_cons.
              apply List.in_or_app ; now left.
      * destruct (@eqP I q' i) as [ | Hnoteq] ; [now left | right ; split ; auto].
        suff: ask (R := A) q = ask q' by (inversion 1).
        erewrite <- Heq ; eauto.
        eapply ieval_finapp_monotone_ask_list ; eauto.
        eapply eval_list_incl_none with ((i,o) :: u).
        -- eapply is_fun_cons_notin_dom ; eauto ; now apply eval_list_notin.
        -- intros x Hinx ; now apply (List.Add_in Hadd) in Hinx.
        -- cbn ; erewrite ifN_eq ; [now auto | ].
           now eapply contra_not_neq with (q' = i).
Qed.

(*We first prove an auxiliary lemma assuming that O is inhabited.*)

Lemma indbarred_fun_list_itree_indbarredP_aux
  tau (l : seq (I * O)) (o : O) :
  indbarred
    (fun u => exists n a, ieval_finapp tau u n = output a) l ->
  is_fun_list l ->
  itree_indbarredP tau l 0.
Proof.
  intros Hyp.
  induction Hyp as [u v [n [r Hr]] Hincl | q v Hnotin _ IHk]; intros Hfun.
  - eapply itree_indbarredP_change_fuel with n ; eauto.
    econstructor ; [eassumption | right ; left ; exists r].
    now eapply ieval_finapp_monotone_output_list ; eauto.
  - unshelve eapply iAdd_induction_step with (v ++ [::(q,o)]) q o.
    + rewrite - (cat0s v) ; apply eval_list_notin_cat; auto.
    + rewrite cats1 ; now apply Add_rcons.
    + eapply itree_indbarredP_change_fuel, IHk.
      rewrite cats1 ; now apply is_fun_rcons_notin_dom.
    + intros o' w Haddw.
      have Hincl: List.incl (v ++ [:: (q, o')]) w.
      { intros x Hx ; apply (List.Add_in Haddw).
        apply List.in_app_or in Hx ; now destruct Hx as [|[|]] ; [ right | left | left ].
      }
      eapply itree_indbarredP_monotone ; [ | | eassumption].
      * eapply itree_indbarredP_change_fuel, IHk.
        rewrite cats1 ; now apply is_fun_rcons_notin_dom.
      * apply is_fun_list_incl with (v ++ [::(q, o')]).
        -- rewrite cats1 ; now apply is_fun_rcons_notin_dom.
        -- intros x Hx ; apply (List.Add_in Haddw) in Hx.
           destruct Hx as [Hx | Hx] ; [subst | ] ; apply List.in_or_app ; eauto.
           now right ; left.
Qed.


(* We now prove the real lemma by destructing the list l to retrieve o : O.*)


Lemma indbarred_fun_list_itree_indbarredP tau (l : seq (I * O)) :
  indbarred
    (fun u => exists n a, ieval_finapp tau u n = output a) l ->
  is_fun_list l ->
  itree_indbarredP tau l 0.
Proof.
  destruct l as [ | [i o] l] ; intros Hyp Hfun.
  2: now eapply indbarred_fun_list_itree_indbarredP_aux ; eauto.
  econstructor ; [intros i j K H ; inversion H | cbn ].
  destruct tau as [r | q k] ; [eauto | ].
  left ; exists q ; split ; [auto | split ; [auto | ] ].
  intros o.
  eapply itree_indbarredP_monotone with nil.
  - now eapply indbarred_fun_list_itree_indbarredP_aux.
  - intros i a a' [Ha | Ha] [Ha' | Ha'] ; inversion Ha ; inversion Ha' ; now subst.
  - now apply List.incl_nil_l.
Qed.
  
  
(*We are now ready to prove our theorem.*)
  
Theorem iGBI_GCI F :
  seq_cont_interaction F ->
  dialogue_cont F.
Proof.
  intros [tau HF].
  pose (T:= fun (l : seq (I * O)) =>
              exists n a, ieval_finapp tau l n = output a).
  have Help : ABbarred T.
  { intros alpha.
    destruct (HF alpha) as [n Hn].
    exists (ieval_trace tau alpha n), n, (F alpha).
    now eapply ieval_finapp_trace.
  }
  have fun_nil : is_fun_list (@nil (I * O)) by (intros i j j' Hinj ; inversion Hinj).
  apply HGBI, indbarred_fun_list_itree_indbarredP
    in Help ; auto.
  eapply itree_indbarred_spec, (itree_indbarred_dialogue) in Help ; auto.
  destruct Help as [d Hd].
  exists d ; intros alpha.
  specialize (HF alpha) as [n Hn] ; specialize (Hd alpha) as [m Hm].
  eapply ieval_output_unique ; now eauto.
Qed.  


End GeneralisedBarInductionCoind.
