From mathcomp Require Import all_ssreflect.
From mathcomp Require Import zify.
Require Import Program.
From Equations Require Import Equations.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Require Import Lia.
Require Import extra_principles.
Require Import continuity_zoo_Prop.
Require Import Brouwer_ext.
Require Import brede_herbelin.

(* Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!". *)


Arguments ext_tree {_ _ _}, _ _ _.
Arguments Btree {_ _}, _ _.


(*
In this file, we study different variants of Bar Induction and try to relate them to
continuity principles.

Variant 1 : Decidable Bar Induction. We prove in the first two Sections
          that decidable Bar Induction is equivalent to an axiom stating that
          (Bseq_cont_interaction <-> dialogue_cont_Brouwer). We call that axiom 
          Continuity Induction.

Variant 2 : following Brede and Herbelin in "On the logical structure of choice and 
            bar induction principles", we define Generalized decidable Bar Induction.
            This generalizes decidable Bar Induction at any query and answer types Q and A.
            We prove that GdBI implies that
            (seq_cont_interaction <-> dialogue_cont),
            i.e. the generalization of Continuity Induction to arbitrary Q and A.
            However, this time the generalization of Continuity Induction does not imply
            GdBI ; we need an enumeration of Q.

Variant 3 : in "Principles of bar induction and continuity on Baire space",
            Kawai defines a variant of Bar Induction which he dubs c_BI for 
            "Bar induction for continuous functions".
            This variant is redefined in Fujiwara-Kawai's paper "Equivalence of
            bar induction
            and bar recursion for continuous functions with continuous moduli".
            We follow this last definition and get the following :
            - assuming equivalence between existential modulus continuity and 
            Brouwer continuity, we can derive Kawai's c_BI.
            - assuming Kawai's c_BI, we cannot prove the converse, we would need
            stronger choice axioms. Kawai manages to prove it, using AC^{0,1} and
            AC^{1,0}_{!}.
            If we replaced existence in Prop by existence in Type,
            we would be able to prove their equivalence.
*)

Section BarInduction.

(*The aim of this Section is to prove that decidable Bar Induction implies the equivalence
 between Bcoind_dial_cont and dialogue_cont_Brouwer.*)
  
Variable dBI : forall R T, (forall a, {T a} + {~ (T a)}) -> @BI_ind R T.
Variables A R : Type.
Notation Q := nat.
Implicit Type (F : (Q -> A) -> R).
Implicit Type (b : @Bitree A R).

Proposition Bseq_cont_to_dialogue_cont_Brouwer F :
  Bcoind_dial_cont F -> dialogue_cont_Brouwer F.
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
  eapply dBI in Help.
  2:{ intros u ; remember (Bitree_to_option b u) as x ; destruct x as [r | ].
      + left ; exists r ; eauto.
      + right ; intros [x Hx] ; rewrite - Heqx in Hx ; inversion Hx.
  }
  eapply Delta0_choice in Hb as [HF].
  2:{
    intros α n. destruct Bieval eqn:E.
    - left. destruct (Hb α) as [m Hm].
      rewrite - E ; clear Hb Help T ; revert b E m Hm.
      generalize (F α) as a' ; clear F ; revert α.
      induction n ; intros ; [destruct b, m ; cbn in * ; inversion E ; inversion Hm ;
                              now subst | ].
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
    + exists (spit r) ; intros alpha ; exists 0 ; cbn ; now rewrite cats0.
    + exfalso ; destruct Hu as [a Ha] ; rewrite Ha in Heqr.
      now inversion Heqr.
  - intros u k IHk ; cbn in *.
    unshelve eexists.
    + apply bite ; intros a.
      exact (proj1_sig (IHk a)).
    + intros alpha ; cbn ; rewrite n_comp_n_plus addn0.
      destruct (IHk (alpha (size u))) as [x IHx].
      destruct (IHx alpha) as [n Hn] ; cbn in *.
      rewrite size_rcons in Hn ; cbn in *.
      exists (S n) ; cbn ; now rewrite - Hn - cats1 - catA cat1s.
Qed.

End BarInduction.


Section ContinuousInduction.

(*The aim of this Section is to prove that assuming as an axiom the 
  equivalence between Bcoind_dial_cont and dialogue_cont_Brouwer
  allows to derive decidable Bar Induction. 
 Thus, together with the previous Section, the two axioms are equivalent.*)  

Variable A : Type.
Notation Q := nat.
Notation R := (seq A).
Implicit Type (F : (Q -> A) -> R).
Implicit Type (b : @Bitree A R).

Variable CI : forall F, Bcoind_dial_cont F -> dialogue_cont_Brouwer F.

CoFixpoint pred_to_Bitree_aux (P : seq A -> bool) (l : seq A) : @Bitree A R :=
  if (P l) then Bret _ l else Bvis (fun a => pred_to_Bitree_aux P (rcons l a)).

Fixpoint beval_trace {X Y} (b : @Btree X Y) (f : nat -> X) : list X :=
  match b with
  | spit _ => nil
  | bite k => f 0 :: (beval_trace (k (f 0)) (f \o succn))
  end.

  

Lemma Bieval_pred_to_Bitree_spec (P : seq A -> bool) (l : seq A) alpha n u :
  Bieval (pred_to_Bitree_aux P l) alpha n = Some u ->
  P u.
Proof.
  revert alpha l u ; induction n ; intros * Heq ; cbn in *.
  - remember (P l) as b ; destruct b ; inversion Heq ; subst ; auto.
  - remember (P l) as b ; destruct b ; [inversion Heq ; subst ; auto | ].
    now apply IHn in Heq.
Qed.

Fixpoint Bieval_trace (b : @Bitree A R) alpha n : nat :=
  match n with
  | 0 => 0
  | S n => match b with
           | Bret _ => 0
           | Bvis k => S (Bieval_trace (k (alpha 0)) (alpha \o succn) n)
           end
  end.

Lemma Bieval_trace_spec (b : @Bitree A R) alpha n u :
  Bieval b alpha n = Some u ->
  Bieval b alpha (Bieval_trace b alpha n) = Some u.
Proof.
  revert b alpha u ; induction n as [ | n IHn] ; cbn ; intros b alpha u Heq.
  - destruct b ; auto.
  - destruct b ; auto.
    now apply IHn.
Qed.

Lemma Bieval_pred_trace (P : seq A -> bool) (alpha : Q -> A) (n : nat) (l u : R) :
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

Lemma barred_Bseq_cont_aux (P : seq A -> bool) (alpha : Q -> A) (u : seq A) :
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
        suff: forall n m (f : Q -> A), [seq f i | i <- iota m.+1 n] =
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

Lemma barred_Bseq_cont (P : seq A -> bool) :
  barred P ->
  inhabited (forall alpha,
        {n : nat &
               { u : seq A |
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
  revert alpha v Heqb Heval ; generalize (@nil A) as l.
  induction n as [ | n IHn] ; intros ; cbn in *.
  - remember (P l) as b' ; destruct b' ; inversion Heval ; cbn in *.
    subst ; rewrite - Heqb' in Heqb ; now inversion Heqb.
  - remember (P l) as b' ; destruct b' ; [ inversion Heval ; subst | ].
    + rewrite - Heqb' in Heqb ; now inversion Heqb. 
    + apply IHn in Heval ; auto.
Qed.

Definition pred_to_fun
  (P : seq A -> bool)
  (H : forall alpha,
      {n : nat &
             {u : seq A |
               P u /\
                 Bieval (pred_to_Bitree_aux P nil) alpha n = Some u}}) :
  (Q -> A) -> R :=
  fun alpha => proj1_sig (projT2 (H alpha)).



Definition pref_a (m : nat) (a : A) (alpha : Q -> A) (n : Q) :=
  if n <= m then a else alpha n.

Lemma pref_a_eq m a : forall alpha, pref_a m a alpha m = a.
Proof.
  intros alpha ; unfold pref_a in *.
  now rewrite leqnn.
Qed.

Lemma pref_a_alpha m a : forall alpha n, m < n -> pref_a m a alpha n = alpha n.
Proof.
  intros alpha n H ; unfold pref_a.
  rewrite ltnNge in H ; rewrite (Bool.negb_involutive_reverse (n <= m)).
  now rewrite H.
Qed.

Lemma pref_a_beval (b : @Btree A R) m a n:
  m < n ->
  forall alpha, beval b (n_comp (pref_a m a alpha) n) =
                  beval b (n_comp alpha n).
Proof.
  revert m n ; induction b as [ | ? IH] ; intros * Hinf alpha ; [reflexivity |].
  cbn.
  do 2 (rewrite n_comp_n_plus addn0) ; rewrite pref_a_alpha ; [ | assumption].
  specialize (IH (alpha n) m n.+1 (ltnW Hinf)) ; cbn in * ; erewrite IH ; eauto.  
Qed.  


Lemma pref_a_Bieval b m a n j:
  m < n ->
  forall alpha, Bieval b (n_comp (pref_a m a alpha) n) j =
                  Bieval b (n_comp alpha n) j.
Proof.
  revert m n b ; induction j as [ | i IHi] ; intros * Hinf alpha ; [reflexivity |].
  cbn in * ; destruct b as [ | k] ; [reflexivity | ].
  do 2 (rewrite n_comp_n_plus addn0) ; rewrite pref_a_alpha ; [ | assumption].
  specialize (IHi m n.+1 (k (alpha n)) (ltnW Hinf)) ; cbn in *;  eapply IHi ; eauto.  
Qed.  


Proposition CoCI_BI (P : list A -> bool) :
  barred P -> inductively_barred P.
Proof.
  intros Hbar.
  have aux:= (barred_Bseq_cont Hbar).
  destruct aux as [aux].
  pose (F := pred_to_fun aux).
  have Fcon : Bcoind_dial_cont F.
  { exists (pred_to_Bitree_aux P nil).
    intros alpha ; exists (projT1 (aux alpha)).
    now apply (proj2_sig (projT2 (aux alpha))).
  }
  apply CI in Fcon ; destruct Fcon as [b Hb].
  unfold F, pred_to_fun in Hb.
  unfold inductively_barred ; revert aux F Hb.
  suff: forall (l : seq A)
               (aux : forall alpha : Q -> A,
                   {n : Q & {u : R | P u /\
                                       Bieval (pred_to_Bitree_aux P l)
                                         (n_comp alpha (size l)) n = Some u}}),
      (forall alpha : Q -> A, ` (projT2 (aux alpha)) = beval b (n_comp alpha (size l))) ->
      hereditary_closure (fun x : R => P x) l.
  { intros H ??? ; eapply H ; eauto. }
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
    elim: n l Hyp {Heq aux} => [| n ihn] l /=. 
    1, 2: case: ifP => hPl Hyp; first exact: hereditary_self. 
    1, 2: apply: hereditary_sons=> aa.
    + by move/(_ (fun _ => aa)): Hyp => Hyp //.
    apply: ihn => alpha.
    rewrite -(Hyp (pref_a (size l) aa alpha)) n_comp_n_plus addn0 pref_a_eq.
    rewrite size_rcons -(@pref_a_Bieval _ (size l) aa (S (size l)) n) //.
  - cbn in * ; intros l aux Heq.
    case_eq (P l) ; intros eqP ; [ econstructor ; assumption | ].
    apply hereditary_sons ; intros a.
    (*We show that the evaluation of pred_to_ext_tree P using
      (pref_a alpha) leads to the same result as when using alpha. *)
    suff: forall alpha,
        {r : R &
               Bieval (pred_to_Bitree_aux P (rcons l a)) (n_comp alpha (size (rcons l a)))
                 (projT1 (aux (pref_a (size l) a alpha))).-1 =
                 Some r} ; [ intros Hyp | intros alpha].
    + unshelve eapply (IHk a).
      * intros alpha.
        exists (projT1 (aux (pref_a (size l) a alpha))).-1.
        exists (projT1 (Hyp alpha)) ; split ; [ | apply (projT2 (Hyp alpha))].
        eapply Bieval_pred_to_Bitree_spec ; exact (projT2 (Hyp alpha)).
      * intros alpha ; specialize (Heq (pref_a (size l) a alpha)) ; cbn in *.
        rewrite n_comp_n_plus addn0 pref_a_eq in Heq.
        revert Heq ; generalize (Hyp alpha) ; rewrite size_rcons.
        generalize (aux (pref_a (size l) a alpha)) ; clear aux Hyp.
        intros [n [u [HPu Hu]]] [v Heqv] Hequ ; cbn in *.
        have H: u = beval (k a) (n_comp alpha (size l) \o succn).
        { rewrite Hequ ; now apply (@pref_a_beval _ _ _ (size l).+1). }
        rewrite - H ; clear H Hequ.
        destruct n ; cbn in * ; rewrite eqP in Hu ; [ inversion Hu | ].
        rewrite n_comp_n_plus addn0 pref_a_eq in Hu.
        suff: Some u = Some v by (intros H ; inversion H).
        rewrite - Heqv - Hu.
        now eapply (@pref_a_Bieval _ (size l) a (S (size l)) n).
    + erewrite <- (@pref_a_Bieval _ (size l) a) ; [ | now rewrite size_rcons].
      destruct (aux (pref_a (size l) a alpha)) as [m [v [HPv Hv]]] ; cbn in *.
      destruct m ; cbn in * ; rewrite eqP in Hv ; [ now inversion Hv | ].
      rewrite n_comp_n_plus addn0 pref_a_eq in Hv.
      exists v ; now rewrite size_rcons.
Qed.


End ContinuousInduction.




Section GeneralisedBarInduction.
(*We generalize the previous result and aim to prove that 
  Sequential continuity + Generalized Bar Induction 
   implies Dialogue continuity for any type Q with decidable equality.*)
Variable Q : eqType.
Variables A R : Type.
Implicit Type (F : (Q -> A) -> R).
Variable HGBI : forall (T : list (Q * A) -> Prop), (forall u, decidable (T u)) -> GBI T.
Notation Itree := (@Itree Q A R).

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

(*We define is_fun_list, a predicate on lists u : seq (Q * A)
 describing the fact that u is a finite approximation of some
 function f : Q -> O.*)

Definition is_fun_list (u : seq (Q * A)) :=
  forall i j j', List.In (i, j) u -> List.In (i, j') u -> j = j'.

(*Without much surprise, [seq (i, f i) | q <- u] for some list u : seq I
 is a finite approximation of some function.*)

Lemma is_fun_map (u : seq Q) (f : Q -> A) :
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
Lemma is_fun_list_incl (u v : seq (Q * A)) :
  is_fun_list v ->
  List.incl u v ->
  is_fun_list u.
Proof.
  intros Hfun Hincl i j j' Hin Hin'.
  apply Hincl in Hin, Hin' ; eapply Hfun ; eassumption.
Qed.

(*We can concatenate two finite approximations if their domains are disjoint.*)
Lemma is_fun_cat_notin_dom (u v : seq (Q * A))
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
Lemma is_fun_cons_notin_dom (u : seq (Q * A)) (q : Q) (a : A)
  (Hu : is_fun_list u)
  (H : ~ (List.In q (map fst u))) :
  is_fun_list ((q,a) :: u).
Proof.
  rewrite - cat1s ; apply is_fun_cat_notin_dom ; [ | assumption | ].
  { intros i' j j' Hinj Hinj' ; cbn in *.
    destruct Hinj as [Heq | ] ; [ inversion Heq ; subst | now exfalso].
    destruct Hinj' as [Heq' | ] ; [ inversion Heq' ; now subst | now exfalso].
  }
  intros i'.
  case: (@eqP Q q i') ; [intros Heq ; subst ; now right | intros Hnoteq ; left].
  cbn ; intros [Heq | Hfalse] ; [ now apply Hnoteq | assumption].
Qed.

Lemma is_fun_rcons_notin_dom (u : seq (Q * A)) (q : Q) (a : A)
  (Hu : is_fun_list u)
  (H : ~ (List.In q (map fst u))) :
  is_fun_list (rcons u (q,a)).
Proof.
  rewrite - cats1 ; apply is_fun_cat_notin_dom ; [ assumption | | ].
  { intros i' j j' Hinj Hinj' ; cbn in *.
    destruct Hinj as [Heq | ] ; [ inversion Heq ; subst | now exfalso].
    destruct Hinj' as [Heq' | ] ; [ inversion Heq' ; now subst | now exfalso].
  }
  intros i'.
  case: (@eqP Q q i') ; [intros Heq ; subst ; now left | intros Hnoteq ; right].
  cbn ; intros [Heq | Hfalse] ; [ now apply Hnoteq | assumption].
Qed.  
    
(*Since we have finite approximations of functions,
 we can consider them as partial functions, through eval_list.*)
Fixpoint eval_list (u : seq (Q * A)) (q : Q) : option A :=
  match u with
  | nil => None
  | (q', o') :: v => if q == q' then Some o' else eval_list v q
  end.

(*Some lemmas about eval_list.*)
Lemma eval_list_In u q a :
  eval_list u q = Some a ->
  List.In (q, a) u.
Proof.
  revert q a ; induction u as [ | [i' o'] v IHv] ; intros q a Heq ; cbn in *.
  { now inversion Heq. }
  case (@eqP Q q i') ; [intros Heqi ; subst ; left | intros Hnoteqi].
  { erewrite eq_refl in Heq ; inversion Heq  ; now subst. }
  eapply (introF (b:= q == i') eqP) in Hnoteqi.
  rewrite Hnoteqi in Heq.
  apply IHv in Heq ; now right.
Qed.

  
Lemma In_eval_list u q a :
  is_fun_list u ->
  List.In (q, a) u ->
  eval_list u q = Some a.
Proof.
  revert q a ; induction u as [ | [i' o'] v IHv] ; intros q a Hfun Hin ; cbn in *.
  { now inversion Hin. }
  destruct Hin as [Heq | Hin] ; [inversion Heq ; subst ; now rewrite eq_refl | ].
  case (@eqP Q q i') ; [intros Heq ; subst | intros Hnoteq].
  { f_equal.
    eapply Hfun ; [left ; reflexivity | now right ].
  }
  apply IHv ; [ | assumption].
  eapply is_fun_list_incl ; [eassumption | ].
  apply List.incl_tl ; now apply List.incl_refl.
Qed.


Lemma eval_list_In_is_fun u q a :
  is_fun_list u ->
  eval_list u q = Some a ->
  is_fun_list (u ++ [:: (q, a)]).
Proof.
  intros Hfun Heq q' a' a'' Hina' Hina''. 
  apply List.in_app_or in Hina', Hina''.
  destruct Hina' as [Hina' | Heqa'].
  2:{ destruct Heqa' as [Heqa' | Hfalse] ; [ inversion Heqa' ; clear Heqa' ; subst | now inversion Hfalse].
      destruct Hina'' as [Hina'' | Heqa'']; [ apply In_eval_list in Hina'' ; [ | assumption] | ].
      2:{ destruct Heqa'' as [Heqa'' | Hfalse] ; [ inversion Heqa'' ; now subst | now inversion Hfalse]. }
      rewrite Heq in Hina'' ; now inversion Hina''.
  }
  destruct Hina'' as [Hina'' | Heqa''] ; [eapply Hfun ; now eauto | ].
  destruct Heqa'' as [Heqa'' | Hfalse] ; [ inversion Heqa'' ; subst | now inversion Hfalse].
  apply In_eval_list in Hina' ; [ | assumption].
  rewrite Heq in Hina' ; now inversion Hina'.
Qed.  
    
            

Lemma eval_list_notin u q :
  eval_list u q = None ->
  ~ List.In q [seq i.1 | i <- u].
Proof.
  revert q ; induction u as [ | [q' o'] v IHv] ; intros q Heq Hin ; [assumption | ].
  cbn in * ; destruct Hin as [Heq' | Hin] ; [subst | ].
  { rewrite eq_refl in Heq ; now inversion Heq. }
  eapply IHv ; [ | eassumption].
  destruct (q == q') ; [now inversion Heq | assumption].
Qed.

Lemma eval_list_none_fun u q a :
  is_fun_list u ->
  eval_list u q = None ->
  is_fun_list (u ++ [:: (q,a)]).
Proof.
  intros Hfun Hnone ; eapply is_fun_cat_notin_dom ; [assumption | | ].
  -  intros x y y' [Hyp1 | Hyp1] [Hyp2 | Hyp2] ; inversion Hyp1 ; inversion Hyp2 ; now subst.
  - intros i.
    destruct (@eqP Q q i) as [Heq | Hnoteq] ; [ subst ; left | ].
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

Lemma eval_list_monotone (u v : seq (Q * A)) (q : Q) (a : A) :
  is_fun_list v ->
  List.incl u v ->
  eval_list u q = Some a ->
  eval_list v q = Some a.
Proof.
  intros Hfun Hincl Heq.
  apply In_eval_list ; [assumption | ].
  apply Hincl ; now apply eval_list_In in Heq.
Qed.

Lemma eval_list_incl_none (u v : seq (Q * A)) (q : Q):
  is_fun_list v ->
  List.incl u v ->
  eval_list v q = None ->
  eval_list u q = None.
Proof.
  intros Hfun Hincl Heq.
  remember (eval_list u q) as aux ; destruct aux as [o | ] ; [ | reflexivity].
  erewrite (eval_list_monotone Hfun Hincl) in Heq ; [eassumption | eauto].
Qed.

Lemma eval_list_map_In (alpha : Q -> A) :
  forall u q a, eval_list [seq (i, alpha i) | i <- u] q = Some a -> a = alpha q.
Proof.
  intros u q a H.
  revert H ; induction u as [ | x u IHu] ; cbn ; intros ; [now inversion H | ].
  destruct (@eqP Q q x) ; subst ; [now inversion H | ].
  now apply IHu.
Qed.




(* We now define ieval_finapp, a way of evaluating an interaction tree 
 with a finite approximation of a function, represented via eval_list.*)


Fixpoint ieval_finapp (i : Itree) (l : seq (Q * A)) (n : nat) : result :=
  match n with
  | 0 => match i with
         | ret r => output r
         | vis q k => ask q
         end
  | S n => match i with
           | ret r => output r
           | vis q k => match (eval_list l q) with
                        | Some a => ieval_finapp (k a) l n
                        | None => ask q
                        end
           end
  end.


(*We now prove some technical lemmas, showing that 
 ieval_finapp is monotone in different ways.*)
Lemma ieval_finapp_monotone_output_list
  (tau : Itree) (u v: seq (Q * A)) (n : nat) (r : R) :
  is_fun_list v ->
  List.incl u v ->
  ieval_finapp tau u n = output r ->
  ieval_finapp tau v n = output r.
Proof.
  revert tau u v r; induction n as [| n IHn] ; intros * Hfun Hincl Heq ; [assumption| ].
  cbn in * ; destruct tau as [r' | q k] ; [assumption | ].
  remember (eval_list u q) as ev ; destruct ev as [r'' | ] ; [| now inversion Heq ].
  erewrite eval_list_monotone ; eauto.
Qed.

Lemma ieval_finapp_monotone_output_fuel
  (tau : Itree) (u: seq (Q * A)) (n m : nat) (r : R) :
  ieval_finapp tau u n = output r ->
  ieval_finapp tau u (n + m) = output r.
Proof.
  elim: n tau => [ | n ihn] [aa <- | q k] //=; first by case: m.
  by case: (eval_list u q) => // a /ihn.
Qed.
  
Lemma ieval_finapp_monotone_ask_list
  (tau : Itree) (u v: seq (Q * A)) (n : nat) (q : Q) :
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
  (tau : Itree) (u : seq (Q * A)) (n m : nat) (q : Q) :
  is_fun_list u ->
  eval_list u q = None ->
  ieval_finapp tau u n = ask q ->
  ieval_finapp tau u (n + m) = ask q.
Proof.
  elim: n u tau q => [ | n ihn] u [r | qq k] q Hfun Hnotin //=.
  - by case=> ->; case: m => //= m; rewrite Hnotin.
  - case (eval_list u qq) => // o; exact: ihn.
Qed.

Lemma ieval_finapp_monotone_ask_list_nomorefuel
  (tau : Itree) (u v: seq (Q * A)) (n : nat) (q : Q) (a : A) :
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


(*We define the trace of evaluation of an interaction tree.*)
Fixpoint ieval_trace (i : Itree) (f : Q -> A) (n : nat) : list Q :=
  match n with
  | 0 => nil
  | S m => match i with
           | ret a => nil
           | vis q k => q :: (ieval_trace (k (f q)) f m)
           end
  end.

(*If we first evaluate an interaction tree i with a function f : Q -> A and
  reach an output, then we can evaluate i with a finite approximation
  built from the trace of the previous evaluation.
 This will be useful to go from ieval to ieval_finapp
 in the final theorem.*)

Lemma ieval_finapp_trace tau f n r :
  ieval tau f n = output r ->
  ieval_finapp tau [seq (i, f i) | i <- ieval_trace tau f n] (size (ieval_trace tau f n)) =
    output r.
Proof.
  assert (aux := @is_fun_map (ieval_trace tau f n) f) ; revert aux.
  change (ieval_trace tau f n) with (nil ++ (ieval_trace tau f n)) at 1 2.
  generalize (@nil Q) as u.
  revert f r tau ; induction n as [ | n IHn] ; intros * aux Heq.  
  - cbn in * ; destruct tau ; now inversion Heq.
  - cbn in * ; destruct tau as [ | q k] ; [now inversion Heq | ].
    suff : eval_list [seq (i, f i) | i <- u ++ q :: ieval_trace (k (f q)) f n] q = Some (f q).
    + intros Hyp ; cbn ; rewrite Hyp - cat1s catA cats1.
      apply IHn ; auto.
      now rewrite -cats1 -catA cat1s.
    + apply In_eval_list ; auto ; eapply (in_map (fun i => (i, f i))).
      now eapply List.in_elt.
Qed.

(*Let us now describe the structure of the proof.
  We want to go from seq_cont F to dialogue_cont F.
 Right now, we can do the following. *)
Lemma GBI_GCI_Fail F :
  coind_dial_cont F ->
  dialogue_cont F.
Proof.
  intros HF.
  destruct HF as [tau HF].
  eapply Delta0_choice in HF as [HF].
  2:{ intros α n.
      destruct ieval eqn:E.
      - right ; intros Heq ; inversion Heq.
      - left. destruct (HF α) as [m].
        f_equal. 
        eapply ieval_output_unique; eauto. 
  }
  pose (T:= fun (l : seq (Q * A)) =>
              exists a, ieval_finapp tau l (size l) = output a).
  have Help : ABbarred T.
  { intros alpha.
    destruct (HF alpha) as [n Hn].
    exists (ieval_trace tau alpha n).
    unfold T.
    exists (F alpha).
    rewrite size_map.
    now eapply ieval_finapp_trace.
  }
  apply HGBI in Help.
    (*What we lack is a way to go from indbarred T [::] to dialogue_cont F.*)
Abort.

(*
  Going from indbarred T [::] to the existence of a suitable dialogue tree is not easy.
  We will do so through several intermediate steps :

 - We will first define a predicate 
      itree_indbarred : Itree -> seq (Q * A)) -> Type 
   such that itree_indbarred tau nil implies
   {d : dialogue & forall alpha, exists n,
        ieval tau alpha n = output (deval d alpha)}.
   This will allow us to go from interaction trees to dialogue trees;

 - We will then define a predicate 
      itree_indbarredP : Itree -> seq (Q * A) -> Prop
   tailored to go through singleton elimination.
   We will then prove that 
      itree_indbarredP tau l -> itree_indbarred tau l,
   thus going from Prop to Type.

 - We will then prove that
      indbarred (fun l => exists n a,
                            ieval_finapp tau l n nil = output a) l ->
      is_fun_list l ->         
      itree_indbarredP tau l
   This is the longest proof of the file.

- Finally, as 
     is_fun_list nil 
  is trivially true, we will retrieve
      indbarred (fun l => exists n a,
                            ieval_finapp tau l n nil = output a) nil ->
      itree_indbarredP tau nil,
  which completes our proof.
*)

(*As explained, let us start by itree_indbarred. 
  It is an inductive predicate that describes a tree of computations
  using tau and l, such that on the leaves of the tree
  ieval_finapp tau l n nil = output r
  for some r.
  There are three cases for this inductive :
  - itree_eta is the leaf case, where the computation reaches an output r.
  - itree_succ deals with the case when the computation is blocked
    because of the lack of fuel, and it allows us to change n with n.+1.
  - finally, itree_beta deals with the case when the computation is blocked
    because l does not contain the answer to some query q. In that case, we
    branch over every possible answer r : R with l ++ [::(q, a)].
 *)

Inductive itree_indbarred (d : Itree) (l : seq (Q * A)) (n : nat) : Type :=
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
  (l : list (Q * A)) (n : nat)
  (Hyp : itree_indbarred tau l n) :
  {d : dialogue & forall alpha,
        l = map (fun i => (i, alpha i)) (map fst l) ->
        exists n, ieval tau alpha n = output (deval d alpha)}.
Proof.
  induction Hyp as [l n r Hfun Heval | l n i a Hfun Hask Hsome k [d IHd] |
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
    destruct aux2 as [a | ] ; [ | now inversion H].
    eapply IHn.
    suff: a = alpha q by (intros Heq ; subst ; eassumption).
    eapply eval_list_map_In ; eauto.
  - exists d ; intros alpha Heqalpha.
    now apply (IHd alpha) ; clear IHd.
  - exists (beta i (fun a => projT1 (IHk a))).
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


(*We now define itree_indbarredP, the same predicate as
 itree_indbarred, albeit living in Prop.
 We tailor it to go through subsingleton elimination.*)

Unset Elimination Schemes.

Inductive itree_indbarredP (tau : Itree) (l: seq (Q * A)) (n : nat) : Prop :=
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
  (P : seq (Q * A) -> nat -> Type)
  (Hout : forall (l : seq (Q * A)) (n : nat) (r : R) (Hfun : is_fun_list l)
                 (e : ieval_finapp tau l n = output r), 
      P l n)
  (Hsucc : forall (l : seq (Q * A)) (n : nat) (q : Q) (a : A) (Hfun : is_fun_list l)
                 (Heq : ieval_finapp tau l n = ask q)
                 (Hnone : eval_list l q = Some a)
                 (e : itree_indbarredP tau l n.+1),
      P l n.+1 -> P l n)
  (Hask : forall (l : seq (Q * A)) (n : nat) (q : Q) (Hfun : is_fun_list l)
                 (Heq : ieval_finapp tau l n = ask q)
                 (Hnone : eval_list l q = None)
                 (e : forall a : A, itree_indbarredP tau (l ++ [:: (q,a)]) n),
      (forall a : A, P (l ++ [:: (q,a)]) n) -> P l n)
  (l : seq (Q * A)) (n : nat) (e : itree_indbarredP tau l n) : P l n.
Proof.
  destruct e as [Hnodup Hq].
  remember (ieval_finapp tau l n) as aux.
  destruct aux as [q | r].
  - remember (eval_list l q) as aux2 ; destruct aux2 as [a | ].
    + assert (Hyp : itree_indbarredP tau l n.+1); last first.
      { eapply Hsucc ; eauto. 
        now apply (itree_indbarredP_rect tau P Hout Hsucc Hask).
      }
      destruct Hq as [[q' [Heq [Hnone Hq']]] | [[r Hr] | [q' [a' [Heq' [Hq' IH]]]]]] ;
        [ | now inversion Hr |  ].
      * injection Heq ; intros Heqq ; subst.
        rewrite Hnone in Heqaux2 ; now inversion Heqaux2.
      * inversion Heq' ; subst.
        rewrite Hq' in Heqaux2 ; inversion Heqaux2 ; now subst.
    + assert (Hyp : forall a : A, itree_indbarredP tau (l ++ [:: (q, a)]) n); last first.
      { eapply (Hask l n q Hnodup) ; [now auto | now symmetry | assumption | ] ; intros a.
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
  (P : seq (Q * A) -> nat -> Prop)
  (Hout : forall (l : seq (Q * A)) (n : nat) (r : R) (Hfun : is_fun_list l)
                 (e : ieval_finapp tau l n = output r), 
      P l n)
  (Hsucc : forall (l : seq (Q * A)) (n : nat) (q : Q) (a : A) (Hfun : is_fun_list l)
                 (Heq : ieval_finapp tau l n = ask q)
                 (Hnone : eval_list l q = Some a)
                 (e : itree_indbarredP tau l n.+1),
      P l n.+1 -> P l n)
  (Hask : forall (l : seq (Q * A)) (n : nat) (q : Q) (Hfun : is_fun_list l)
                 (Heq : ieval_finapp tau l n = ask q)
                 (Hnone : eval_list l q = None)
                 (e : forall a : A, itree_indbarredP tau (l ++ [:: (q,a)]) n),
      (forall a : A, P (l ++ [:: (q,a)]) n) -> P l n)
  (l : seq (Q * A)) (n : nat) (e : itree_indbarredP tau l n) : P l n.
Proof.
  eapply itree_indbarredP_rect ; eauto.
Qed.  


(*itree_indbarredP indeed implies itree_indbarred.*)
Lemma itree_indbarred_spec (tau : Itree) (l : seq (Q * A)) (n : nat) :
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
  revert m ; induction Hu as [u n r Hnodup Heqr | u n q r Hfunu Heq Hsome _ IHu |
                               u n q Hfunu Heq Hnoneu _ IHu] ; intros m.
  - econstructor ; [ assumption | ].
    case: (leqP n m) ; intros Hinf ; [ | apply leqW in Hinf ; cbn in Hinf];
      apply subnKC in Hinf.
    + rewrite - Hinf; right ; left ; exists r.
      now eapply ieval_finapp_monotone_output_fuel.
    + revert Hinf; rewrite subSS; generalize (n - m) as k.
      intros k; revert m n Heqr ; induction k ; intros m n Heqa Hinf.
      * suff -> : m = n by eauto.
        lia.
      * remember (ieval_finapp tau u m) as aux eqn: Heqaux.
        destruct aux as [q | ] ; [ | now eauto].
        right ; right.
        remember (eval_list u q) as aux2 eqn: Heqaux2; destruct aux2 as [a | ].
        -- exists q, a ; split ; [auto | split ; [auto | ] ].
           econstructor ; [ assumption | ].
           eapply (IHk m.+1) ; [eauto | now rewrite addSn - addnS].
        -- symmetry in Heqaux2. 
           have {} Hinf : n = m + k.+1 by lia.
           by move: Heqa; rewrite Hinf (ieval_finapp_monotone_ask_fuel _ _ Heqaux2).
  - now eapply IHu.
  - econstructor ; [ assumption | ].
    case: (leqP n m) ; intros Hinf ; [ | apply leqW in Hinf ; cbn in Hinf] ;
      apply subnKC in Hinf.
    + rewrite - Hinf; left ; exists q ; split ; [ | split ; eauto].
      now eapply ieval_finapp_monotone_ask_fuel ; eauto.
    + revert Hinf ; rewrite subSS; generalize (n - m) as k.
      intros k; revert m n Heq ; induction k ; intros m n Heq Hinf.
      * suff -> : m = n by eauto.
        lia. 
      * remember (ieval_finapp tau u m) as aux eqn: Heqaux.
        destruct aux as [q' | r] ; [ | now eauto].
        remember (eval_list u q') as aux2 eqn: Heqaux2; destruct aux2 as [a | ].
        -- right ; right ; exists q', a ; split ; [auto | split ; [auto | ] ].
           econstructor ; [ assumption | ].
           eapply (IHk m.+1) ; [eauto | now rewrite addSn - addnS].
        -- symmetry in Heqaux2.
           have {} Hinf : n = m + k.+1 by lia.
           move: Heq; rewrite Hinf (ieval_finapp_monotone_ask_fuel _ _ Heqaux2) //.
           by eauto.
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
    destruct tau as [ | q' k ]; eauto.
    remember (eval_list u q') as aux2 ; destruct aux2 as [ a' | ].
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

 To do this, we use the predicate List.Add, which generalizes addition
 of an element to the list u anywhere in the list, and not only at the end.
 This is the longest and most technical proof of the file.*)

Lemma Add_induction_step tau (u v : seq (Q * A)) (n : nat) (q : Q) (a : A) :
  eval_list u q = None ->
  List.Add (q, a) u v ->
  (itree_indbarredP tau v n) ->
  (forall a w, List.Add (q, a) u w ->
               itree_indbarredP tau w n) ->
  itree_indbarredP tau u n.
Proof.
  intros Hnone Hadd Hv Hyp.
  have Hincl : List.incl u v.
  { intros x Hin ; eapply List.Add_in ; [eassumption | now right]. }
  revert u Hincl Hnone Hadd Hyp.
  induction Hv as [l n r Hnodup Heqa | l n q' a' Hfunl Heq Hsome k IHk |
                    l n q' Hfunl Heq Hnonel k IHk] ; intros.
  all: have Hfunu : is_fun_list u by (eapply is_fun_list_incl ; eassumption). 
  - remember (ieval_finapp tau u n) as aux.
    destruct aux as [q' | r'] ; [ | econstructor ; now eauto].
    remember (eval_list u q') as aux2 ; destruct aux2 as [a' | ].
    + econstructor ; [assumption | right ; right ; exists q', a' ].
      split ; [now auto | split ; [now auto | ] ].
      symmetry in Heqaux.
      eapply (ieval_finapp_monotone_ask_list_nomorefuel (v := l)) in Heqaux ;
        eauto.
      rewrite Heqaux in Heqa ; now inversion Heqa.
    + destruct (@eqP Q q' q) as [Heq' | Hnoteq] ; [subst | ].
      * econstructor ; [assumption | ].
        left ; exists q ; split ; [auto | split ; [assumption | ] ].
        intros a' ; apply (Hyp a').
        rewrite cats1 ; now apply Add_rcons.
      * exfalso.
        suff: ieval_finapp tau l n = ask q'.
        { intros Heq' ; rewrite Heq' in Heqa ; now inversion Heqa. }
        eapply ieval_finapp_monotone_ask_list ; eauto.
        eapply eval_list_incl_none with (u ++ [:: (q, a)]) ; eauto.
        -- now apply eval_list_none_fun.
        -- intros x Hinx.
           eapply (List.Add_in Hadd) in Hinx.
           destruct Hinx as [Hl | Hr] ; apply List.in_or_app ; [right | ] ; now left.
        -- apply eval_list_notin_cat ; [now auto | cbn].
           intros [Heqi | Hfalse] ; auto.
  - remember (ieval_finapp tau u n) as aux.
    destruct aux as [q'' | r] ; [ | econstructor ; now eauto].
    remember (eval_list u q'') as aux2 ; destruct aux2 as [a'' | ].
    + econstructor ; [ auto | ].
      right ; right ; exists q'',a''.
      split ; [now auto | split ; [now auto | ] ].
      eapply IHk ; eauto.
      intros a''' w Haddw ; eapply itree_indbarredP_change_fuel ; eauto.
    + destruct (@eqP Q q'' q) as [Heqi | Hnoteq] ; [subst | exfalso ].
      * econstructor ; [assumption | left].
        exists q ; split ; [auto | split ; [auto | ] ].
        intros a'' ; apply (Hyp a'').
        rewrite cats1 ; now apply Add_rcons.
      * suff: eval_list l q'' = None ; [ intros auxl | ].
        -- suff: ask (R := R) q' = ask q'' by
             (intros H ; inversion H ; subst ; rewrite auxl in Hsome ; inversion Hsome).
           rewrite - Heq ; now eapply ieval_finapp_monotone_ask_list ; eauto.
        -- eapply eval_list_incl_none with (u ++ [::(q, a)]).
           ++ now apply eval_list_none_fun.
           ++ intros x Hinx ; eapply (List.Add_in Hadd) in Hinx.
              destruct Hinx as [Hinx | Hinx] ; eapply List.in_or_app ; [| now left].
              right ; now left.
           ++ eapply eval_list_notin_cat ; auto ; cbn.
              intros [Hin | Hin] ; inversion Hin ; now auto.
  - remember (ieval_finapp tau u n) as aux.
    destruct aux as [q'' | r].
    2: econstructor ; [ assumption | right ; left ; now exists r ].
    remember (eval_list u q'') as aux2 ; destruct aux2 as [a' | ].
    + econstructor ; [ assumption | ].
      right ; right ; exists q'',a'.
      split ; [now auto | split ; [now auto | ] ].
      remember (ieval_finapp tau u n.+1) as aux3.
      destruct aux3 as [q''' | r] ; [ | econstructor ; now eauto].
      have Heqq: q''' = q' ; [ | subst].
      { suff: ask (R := R) q''' = ask q' by (intros H ; inversion H).
        eapply (ieval_finapp_monotone_ask_fuel 1) in Heq ; eauto.
        rewrite Heqaux3 - Heq addn1.
        eapply ieval_finapp_one_step_fuel ; eauto.
      }
      econstructor ; [assumption | left].
      exists q' ; split ; [auto | split ; [now apply eval_list_incl_none with l | ] ].
      intros a''.
      have Hnoneu: eval_list (u ++ [:: (q', a'')]) q = None.
      { apply eval_list_notin_cat ; [assumption | cbn].
        intros [Heqi | Hfalse] ; [ subst | now inversion Hfalse].
        suff: eval_list l q = Some a by (intros H ; rewrite Hnonel in H ; now inversion H).
        apply (In_eval_list Hfunl), (List.Add_in Hadd) ; now left.
      }
      eapply itree_indbarredP_change_fuel with n.
      eapply (IHk a'') ; eauto.
      -- apply List.incl_app ; [now apply List.incl_appl | ].
         apply List.incl_appr, List.incl_refl.
      -- now apply Add_cat.
      -- intros a''' w Haddw.
         eapply itree_indbarredP_monotone with ((q,a''') :: u).
         ** now apply Hyp with a''', List.Add_head.
         ** eapply is_fun_list_incl with ((u ++ [:: (q', a'')]) ++ [::(q, a''')]).
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
    + suff: q'' = q \/ (q'' <> q /\ q'' = q') ; [intros [Heqi | [Hnoteq Heqq] ] ; subst | ].
      * econstructor ; [assumption | ].
        left ; exists q ; split ; [auto | split ; [ auto | intros o'] ].
        apply (Hyp o') ; rewrite cats1 ; now apply Add_rcons.
      * econstructor ; [assumption | ].
        left ; exists q' ; split ; [auto | split ; [ auto | ] ].
        intros a' ; eapply (IHk a').
        -- apply List.incl_app ; [now apply List.incl_appl | ].
           apply List.incl_appr, List.incl_refl.
        -- apply eval_list_notin_cat ; [assumption | ].
           cbn ; intros [Heqi | Hfalse] ; subst ; now auto.
        -- now apply Add_cat.
        -- intros a'' w Haddw.
           eapply itree_indbarredP_monotone with ((q,a'') :: u).
           ++ now apply Hyp with a'', List.Add_head.
           ++ eapply is_fun_list_incl with ((u ++ [:: (q', a')]) ++ [::(q, a'')]).
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
      * destruct (@eqP Q q'' q) as [ | Hnoteq] ; [now left | right ; split ; auto].
        suff: ask (R := R) q' = ask q'' by (inversion 1).
        erewrite <- Heq ; eauto.
        eapply ieval_finapp_monotone_ask_list ; eauto.
        eapply eval_list_incl_none with ((q,a) :: u).
        -- eapply is_fun_cons_notin_dom ; eauto ; now apply eval_list_notin.
        -- intros x Hinx ; now apply (List.Add_in Hadd) in Hinx.
        -- cbn ; erewrite ifN_eq ; [now auto | ].
           now eapply contra_not_neq with (q'' = q).
Qed.

(*The bulk of the proof is done, we now need to show that indbarred implies itree_indbarredP.
*We first prove an auxiliary lemma assuming that A is inhabited.*)

Lemma indbarred_fun_list_itree_indbarredP_aux
  tau (l : seq (Q * A)) (a : A) :
  indbarred
    (fun u => exists a, ieval_finapp tau u (size u) = output a) l ->
  is_fun_list l ->
  itree_indbarredP tau l 0.
Proof.
  intros Hyp.
  induction Hyp as [u v [r Hr] Hincl | q v Hnotin _ IHk]; intros Hfun.
  - eapply itree_indbarredP_change_fuel with (size v) ; eauto.
    econstructor ; [eassumption | right ; left ; exists r].
    now eapply ieval_finapp_monotone_output_list ; eauto.
  - unshelve eapply Add_induction_step with (v ++ [::(q,a)]) q a.
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


(* We now prove the real lemma by destructing the list l to retrieve a : O.*)


Lemma indbarred_fun_list_itree_indbarredP tau (l : seq (Q * A)) :
  indbarred
    (fun u => exists a, ieval_finapp tau u (size u) = output a) l ->
  is_fun_list l ->
  itree_indbarredP tau l 0.
Proof.
  destruct l as [ | [i o] l] ; intros Hyp Hfun.
  2: now eapply indbarred_fun_list_itree_indbarredP_aux ; eauto.
  econstructor ; [intros q j K H ; inversion H | cbn ].
  destruct tau as [r | q k] ; [eauto | ].
  left ; exists q ; split ; [auto | split ; [auto | ] ].
  intros o.
  eapply itree_indbarredP_monotone with nil.
  - now eapply indbarred_fun_list_itree_indbarredP_aux.
  - intros q' a a' [Ha | Ha] [Ha' | Ha'] ; inversion Ha ; inversion Ha' ; now subst.
  - now apply List.incl_nil_l.
Qed.
  
  
(*We are now ready to prove our theorem.*)
  
Theorem GBI_GCI F :
  coind_dial_cont F ->
  dialogue_cont F.
Proof.
  intros [tau HF].
  pose (T:= fun (l : seq (Q * A)) =>
              exists a, ieval_finapp tau l (size l) = output a).
  have Help : ABbarred T.
  { intros alpha.
    destruct (HF alpha) as [n Hn].
    exists (ieval_trace tau alpha n), (F alpha).
    rewrite size_map.
    now eapply ieval_finapp_trace.
  }
  have fun_nil : is_fun_list (@nil (Q * A)) by (intros q j j' Hinj ; inversion Hinj).
  apply HGBI in Help. 
  2:{ unfold T ; clear.
      intros u ; destruct (ieval_finapp tau u (size u)) ; [right | left] ; eauto.
      intros [a Ha] ; now inversion Ha.
  }
  eapply indbarred_fun_list_itree_indbarredP
    in Help ; auto.
  eapply itree_indbarred_spec, (itree_indbarred_dialogue) in Help ; auto.
  destruct Help as [d Hd].
  exists d ; intros alpha.
  specialize (HF alpha) as [n Hn] ; specialize (Hd alpha) as [m Hm].
  eapply ieval_output_unique ; now eauto.
Qed.  


End GeneralisedBarInduction.

Section ContinuousBarInduction.
  
  Variables A R : Type.

  Variable CI : forall F : (nat -> A) -> R,
      ex_modulus_cont_nat F -> dialogue_cont_Brouwer F.

  Definition c_bar (P : seq A -> Prop) :=
    exists F : (nat -> A) -> R,
      ex_modulus_cont_nat F /\
        (forall (alpha : nat -> A) (n : nat), P (map alpha (iota 0 n)) <->
                                                modulus_at F alpha (iota 0 n)).

  Definition c_BI := forall P, c_bar P -> inductively_barred P.

  Lemma beval_ext (b : @Btree A R) f g :
    f =1 g ->
    beval b f = beval b g.
  Proof.
    revert f g ; induction b as [ | k IHk] ; [reflexivity | intros f g Heq ; cbn ].
    rewrite Heq ; apply IHk.
    intros n ; cbn ; now rewrite Heq.
  Qed.         

  Fixpoint beval_list (b : @Btree A R) (l : seq A) : option R :=
    match b with
    | spit r => Some r
    | bite k => match l with
                | nil => None
                | x :: q => beval_list (k x) q
                end
    end.

  Lemma beval_list_mon (b : @Btree A R) (l l' : seq A) (r : R) :
    beval_list b l = Some r -> beval_list b (l ++ l') = Some r.
  Proof.
    revert l l' ; induction b ; cbn in * ; intros l l' Heq ; [auto | ].
    destruct l ; [now inversion Heq | cbn ; now apply H].
  Qed.
  
  Lemma beval_list_barred_aux (b : @Btree A R) (P : seq A -> Prop)
    (u : seq A) (Hyp : forall v, (exists y, beval_list b v = Some y) -> P (u ++ v)) :
    hereditary_closure P u.
  Proof.
    revert u Hyp ; induction b as [ r | k IHk] ; intros u Hyp.
    - econstructor ; erewrite <- cats0 ; apply Hyp ; exists r ; now trivial.
    - econstructor 2 ; intros x.
      apply (IHk x).
      intros v ; rewrite - cats1 - catA cat1s ; now apply (Hyp (x::v)).
  Qed.

  Lemma beval_list_barred (b : @Btree A R) :
    hereditary_closure (fun l => exists y, beval_list b l = Some y) nil.
  Proof.
    eapply beval_list_barred_aux ; cbn ; intros v ; now eauto.
  Qed.

  Lemma beval_list_modulus_at (b: @Btree A R) (a : A) (u : seq A) (r : R) :
    beval_list b u = Some r -> modulus_at (beval b) (from_pref a u) (iota 0 (size u)).
  Proof.
    revert a u r ; induction b as [ r | k IHk] ; intros x u y Heq beta Hbeta ; [reflexivity | ].
    destruct u as [ | x' u] ; cbn in * ; [now inversion Heq | ].
    have aux: (nth x (x':: u) \o succn) =1 nth x u by (intros [] ; reflexivity).
    etransitivity ; [eapply (@beval_ext _ _ (nth x u)) ; auto | ].
    have Heq':= f_equal (fun l => nth x l 0) Hbeta ; cbn in * ; subst.
    eapply IHk ; [now eauto | ].
    have Heq' := f_equal (drop 1) Hbeta ; cbn in * ; do 2 rewrite drop0 in Heq'.
    suff: forall m n (x1 x2 : A) u beta,
        [seq from_pref x1 (x2 :: u) i | i <- iota n.+1 m] = [seq beta i | i <- iota n.+1 m] ->
        [seq from_pref x1 u i | i <- iota n m] = [seq (beta \o succn) i | i <- iota n m].
    { clear - Heq' ; intros Hyp ; eapply Hyp ; eauto. }
    clear ; induction m as [ | m IHm] ; intros * H ; cbn in * ; [reflexivity | ].
    f_equal ; [exact (f_equal (fun l => nth x1 l 0) H) | ].
    eapply IHm.
    apply (f_equal (drop 1)) in H ; cbn in * ; do 2 rewrite drop0 in H ; eassumption.
Qed.    
    

Theorem CI_imp_c_BI : c_BI.
Proof.
  intros P [F [contF HF]] ; apply CI in contF as [b Hb].
  unfold inductively_barred.
  have aux := beval_list_barred b.
  econstructor 2.
  induction aux as [ u [y Hy] | ] ; intros a ; [ | now econstructor 2].
  econstructor. 
  erewrite <- take_size.
  erewrite <- (map_nth_iota0 a) ; [ | eauto].
  unfold pref in HF.
  rewrite size_rcons.
  apply HF ; intros beta Heq ; do 2 (rewrite Hb).
  eapply beval_list_modulus_at with y ; [ | rewrite size_rcons] ; eauto.
  now rewrite - cats1 ; apply beval_list_mon.
Qed.    
  
End ContinuousBarInduction.


Section cBI_implies_CI_fail.
  (*Below is an attempt at proving that cBI implies CI, failing because of a lack of 
    choice principles.*)
          
  Variables A R : Type.

  Variable cBI : c_BI A R.

  (*We need to redefine the nth function, such that it immediately reduces when
   applied to nil. *)
  
  Fixpoint nth' {T} (t : T) (s : seq T) (n : nat) {struct s} : T :=
    match s, n with
    | [::], _ => t
    | x :: s', 0 => x
    | x :: s', k.+1 => nth' t s' k
    end.

  Lemma nth_nth' {T} (t : T) s n : nth t s n = nth' t s n.
  Proof.
    revert n ; induction s ; cbn ; [now destruct n | induction n ; now cbn ; auto].
  Qed.
    
  (*This is the failing Lemma.*)
  Lemma c_BI_imp_CI (a : A) : forall F : (nat -> A) -> R,
      ex_modulus_cont_nat F -> dialogue_cont_Brouwer F.
  Proof.
    intros F HF.
    (*We need a suitable predicate to become a c_bar.
     The following is quite natural, we need to assume a : A to define it.*)
    pose (P := fun l => modulus_at F (from_pref a l) (iota 0 (size l))).
    have aux: c_bar R P.
    { exists F ; split ; [assumption | ].
      intros alpha n ; split ; [intros HP beta Heq | unfold P].
      + etransitivity ; [symmetry |] ; apply HP ; rewrite size_map size_iota.
        * erewrite map_nth_iota0 ; [ | rewrite size_map size_iota ; lia]. 
          now erewrite <- take_size, size_map, size_iota.
        * erewrite map_nth_iota0 ; [ | rewrite size_map size_iota ; lia]. 
          now erewrite <- take_size, size_map, size_iota, Heq.
      + rewrite size_map size_iota ; intros Hmod beta Heq. 
        etransitivity ; [symmetry ; eapply Hmod | eapply Hmod].
        * erewrite map_nth_iota0 ; [ | rewrite size_map size_iota ; lia]. 
          now erewrite <- take_size, size_map, size_iota at 1.
        * erewrite <- Heq, map_nth_iota0 ; [ | rewrite size_map size_iota ; lia]. 
          now erewrite <- take_size, size_map, size_iota at 1.
    }
    apply cBI in aux ; unfold inductively_barred, P in aux.
    (*P is now inductively barred, we can try and build a Brouwer tree out of it.*)
    unfold dialogue_cont_Brouwer.
    (*We generalize the goal to any list l : A and not only nil. This is where we use
     nth'. *)
    suff: forall (l : seq A),
        hereditary_closure (fun u => modulus_at F (from_pref a u) (iota 0 (size u))) l ->
        exists b : Btree, forall alpha,
          F (fun n => nth' (alpha n) l n) = beval b (fun n => nth' (alpha n) l n)
          by (intros Hyp ; apply (Hyp nil aux)).
    clear ; intros l aux.
    (*We proceed by induction on aux.*)
    induction aux as [u HP | u k IHk].
    - (* The function
         (fun n : nat => nth' (alpha n) u n)
         validates the condition of HP, no matter what alpha is.*)
      exists (spit (F (from_pref a u))).
      intros alpha ; etransitivity ; [ symmetry |] ; eapply HP ; auto.
      erewrite map_nth_iota0, take_size ; [ | lia].
      suff: forall (alpha : nat -> A) u v,
          u ++ v = u ++ [seq nth' (alpha i) (u ++ v) i | i <- iota (size u) (size v)]
          by (intros Hyp ; apply (Hyp alpha nil)).
      clear ; intros alpha u v ; revert u ; induction v as [ | x v IHv] ; [reflexivity | ].
      cbn ; intros u ; do 2 (rewrite - cat1s catA cats1).
      suff: x = nth' (alpha (size u)) (rcons u x ++ v) (size u).
      { intros Heq ; rewrite - Heq - (size_rcons u x) ; now eapply IHv. }
      clear ; generalize (alpha (size u)) as n ; revert v.
      induction u ; cbn ; [reflexivity | assumption].
    - (* Intuitively, the dialogue tree we want to build is
       bite (fun (a : A) => (IHk a).1) 
       Unfortunately, this does not work since (IHk a) provides a mere existence.
       We thus cannot conclude.
       *)
  Abort. 


End cBI_implies_CI_fail.
