
From mathcomp Require Import all_ssreflect.
Require Import Program.
From Equations Require Import Equations.
Require Import extra_principles.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import continuity_zoo_Prop.

Arguments ext_tree {_ _ _}, _ _ _.
Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".

(* This file presents Brouwer-like equivalents of extensional trees and interaction,
   trees, i.e. trees that ask their questions "in order", much like Brouwer trees 
   vs dialogue trees.
 *)

(*TODO : in the other files we never use Brouwer extensional trees, only Brouwer
 interaction trees, maybe remove the former altogether? *)

Section Brouwer_ext_tree.

  (*The goal of this Section is to provide an extensional tree equivalent to Brouwer
    trees, and to prove that it is equivalent to seq_contW. *)

Variable O A : Type.
Notation I := nat.
Implicit Type (F : (I -> O) -> A).

(* TODO : move this elsewhere or streamline it *)
Lemma nth_map_iota  (f : nat -> O) m n k o : (n <= m) ->
                               nth o (map f (iota k (S m))) n = f (k + n).
Proof.
move=> lenm.
have -> : k + n = nth k (iota k m.+1) n by rewrite nth_iota.
rewrite (nth_map k) // size_iota //.
Qed.

(* TODO : move this elsewhere or streamline it *)
Lemma iota_rcons (i j : nat) : rcons (iota i j) (i + j) = iota i j.+1.
Proof.
have -> : iota i j.+1 = iota i (j + 1) by rewrite addn1.
by rewrite -cats1 iotaD.
Qed.


(* TODO : move this elsewhere or streamline it *)
Lemma from_pref_finite_equal l (alpha : I -> O) o :
  forall n, le (List.list_max l) n ->
  map (from_pref o (map alpha (iota 0 (S n)))) l = map alpha l.
Proof.
  induction l ; cbn in * ; [reflexivity |] ; intros n Hle.
  unfold from_pref in *.
  f_equal.
  2:{ eapply IHl.
      unfold List.list_max.
      etransitivity ; [ | eassumption].
      now eapply PeanoNat.Nat.max_lub_r.
  }
  change (nth o ([seq alpha i | i <- iota 0 (S n)]) a = alpha a).
  erewrite nth_map_iota ; [reflexivity |].
  destruct (@leP a n)  as [ | notle] ; auto.
  exfalso ; apply notle.
  etransitivity ; [ | eassumption ].
  now eapply PeanoNat.Nat.max_lub_l.
Qed.


(* TODO : move this elsewhere or streamline it *)
Lemma leq_le i j : i <= j -> le i j.
Proof. by move/leP. Qed.


(*Brouwer extensional trees: they go to option A, and None is considered to be "next query".*)
Definition Bext_tree := list O -> option A.

Fixpoint Beval_ext_tree_aux (tau : Bext_tree) (f : I -> O) (n : nat) (l : seq O) (i : I) :
  option A :=
  match n, tau l with
  |S k, None => Beval_ext_tree_aux tau f k (rcons l (f i)) (S i)
  |_, _ =>  tau l
  end.


Definition Beval_ext_tree tau f n := Beval_ext_tree_aux tau f n nil 0.

(*Continuity via Brouwer extensional trees*)
Definition Bseq_cont F :=
  exists tau : Bext_tree, forall alpha, exists n : nat, Beval_ext_tree tau alpha n = Some (F alpha).

(*The following is a bunch of lemmas that mimick lemmas about extensional trees,
 albeit for Brouwer extensional trees this time. *)

Definition wf_Bext_tree (tau : Bext_tree) :=
  forall f : I -> O,  exists n o, tau (map f (iota 0 n)) = Some o.

Definition Bvalid_ext_tree (tau : Bext_tree) :=
  forall (f : I -> O) (k : I) (a : A), tau (map f (iota 0 k)) = Some a ->
                          tau (map f (iota 0 k.+1)) = Some a.

Definition Bseq_cont_valid F :=
  exists tau : Bext_tree,
    (forall alpha, exists n : nat, Beval_ext_tree tau alpha n = Some (F alpha)) /\
      (Bvalid_ext_tree tau).

Lemma Bvalid_plus (tau : Bext_tree) :
  Bvalid_ext_tree tau -> forall f k j a,
      tau (map f (iota 0 k)) = Some a ->
      tau (map f (iota 0 (k + j))) = Some a.
Proof.
move=> H f k j; elim: j k => [| j ihj] k a e; first by rewrite addn0.
rewrite addnS; apply: (ihj k.+1).
exact: H.
Qed.

Fixpoint Beval_ext_tree_trace_aux
  (tau : Bext_tree) (f : I -> O) (n : nat) (l : seq O) (i : I) : I :=
  match n, tau l with
  | S k, None => S (Beval_ext_tree_trace_aux tau f k (rcons l (f i)) (S i))
  | _ , _ => 0
  end.

Definition Beval_ext_tree_trace tau f n := Beval_ext_tree_trace_aux tau f n nil 0.

Lemma Beval_ext_tree_map_aux tau f n l i :
  Beval_ext_tree_aux tau f n l i =
    tau (l ++ map f (iota i ((Beval_ext_tree_trace_aux tau f n l i)))).
Proof.
elim: n l i =>[| n ihn] l i /=; first by rewrite cats0.
case e: (tau l) => [a |] /=; first by rewrite cats0.
by rewrite -cat_rcons.
Qed.

Lemma Beval_ext_tree_constant (tau : Bext_tree) (f : I -> O) n a l i :
    tau l = Some a ->
    Beval_ext_tree_aux tau f n l i = Some a.
Proof. by elim: n l i => [| n ihn] l i //= ->. Qed.

Lemma Beval_ext_tree_output_unique tau f l n1 n2 o1 o2 i :
  Beval_ext_tree_aux tau f n1 l i = Some o1 ->
  Beval_ext_tree_aux tau f n2 l i = Some o2 ->
  o1 = o2.
Proof.
elim: n1 n2 l i => [| n1 ihn1] [ | n2] l i /=.
1, 2: by move=> -> [].
1, 2: case: (tau l) => [ o -> [] // | q //].
intros H. eapply ihn1 ; eassumption.
Qed.

Lemma Beval_ext_tree_monotone (tau : Bext_tree ) f n k a l i :
  Beval_ext_tree_aux tau f n l i = Some a ->
  Beval_ext_tree_aux tau f (n + k) l i = Some a.
Proof.
  revert l i ; induction n as [ | n IHn] ; cbn in * ; intros l i H.
  1: now eapply Beval_ext_tree_constant.
  destruct (tau l) ; [ assumption |].
  now eapply IHn.
Qed.

Lemma eval_ext_tree_from_pref (tau : @ext_tree I O A) f n l o :
  eval_ext_tree_aux tau f n (map f l) =
    eval_ext_tree_aux tau (from_pref o (map f (iota 0 (S (List.list_max (l ++ (eval_ext_tree_trace_aux tau f n (map f l)))))))) n (map f l).
Proof.
  revert l.
  induction n ; intros ; [reflexivity |].
  - cbn.
    destruct (tau (map f l)) as [i |] ; [ | reflexivity].
    unfold from_pref.
    pose (help := @nth_map_iota f ((List.list_max
                                      (l ++  (i :: eval_ext_tree_trace_aux tau f n (rcons (map f l) (f i)))))) i 0 o).
    cbn in help.
    erewrite help ; clear help.
    2:{ erewrite List.list_max_app ; erewrite  PeanoNat.Nat.max_comm.
        erewrite <- List.list_max_app ; cbn.
        suff: forall n, eqn (i - (Nat.max i n)) 0 by auto.
        clear.
        induction i ; [reflexivity |] ; intros [ | n] ; [ | cbn ; auto].
        now eapply leqnn.
    }
    erewrite <- map_rcons.
    erewrite IHn ; unfold from_pref.
    do 2 f_equal.
    now erewrite cat_rcons.
Qed.

(*Same for the trace of eval_ext_tree*)
Lemma eval_ext_tree_trace_from_pref (tau : ext_tree I O A) f n k l o :
  le (List.list_max (l ++ (eval_ext_tree_trace_aux tau f n (map f l)))) k ->
  eval_ext_tree_trace_aux tau f n (map f l) =
    eval_ext_tree_trace_aux tau (from_pref o (map f (iota 0 (S k)))) n (map f l).
Proof.
  revert l.
  induction n ; intros ; [reflexivity |].
  - cbn in *.
    destruct (tau (map f l)) as [i |] ; [ | reflexivity].
    unfold from_pref.
    f_equal.
    pose (help := @nth_map_iota f k i 0 o).
    cbn in help.
    erewrite help ; clear help.
    2:{ clear IHn. revert H.
        set (p := List.list_max _).
        suff: le i p.
        2:{ unfold p ; clear p.
            erewrite List.list_max_app ; erewrite  PeanoNat.Nat.max_comm.
            erewrite <- List.list_max_app ; cbn.
            now eapply PeanoNat.Nat.max_lub_l.
        }
        clear.
        generalize p ; clear p ; intros p Hip Hpk.
        have aux := PeanoNat.Nat.le_trans _ _ _ Hip Hpk ; clear Hip ; clear Hpk.
        induction aux ; [now eapply leqnn |now eapply leqW].
    }
    erewrite <- map_rcons ; erewrite <- map_rcons in H.
    eapply IHn.
    now erewrite cat_rcons.
Qed.

(*A technical lemma to prove that eval_ext_tree using lists as partial oracles
 is monotone*)
Lemma eval_ext_tree_pref_monotone_aux (tau : ext_tree I O A) f n a o l :
  eval_ext_tree_aux tau f n (map f l) = output a ->
  eval_ext_tree_aux tau (from_pref o (map f (iota 0 (n + (S (List.list_max (l ++ (eval_ext_tree_trace_aux tau f n (map f l)))))))))
    (n + (S (List.list_max (l ++ (eval_ext_tree_trace_aux tau f n (map f l))))))
    (map f l) = output a.
Proof.
  intros H.
  eapply eval_ext_tree_monotone.
  unshelve erewrite eval_ext_tree_from_pref in H ; [assumption |].
  rewrite <- H ; clear H.
  eapply eval_ext_tree_continuous.
  erewrite from_pref_finite_equal ; erewrite <- plus_n_Sm .
  1: erewrite from_pref_finite_equal ; [ reflexivity |].
  all: set t:= eval_ext_tree_trace_aux _ _ _ _ ;
    suff: t = eval_ext_tree_trace_aux tau f n [seq f i | i <- l] ;
      [ | symmetry ;  eapply eval_ext_tree_trace_from_pref].
  2,4: now eapply PeanoNat.Nat.le_add_l.
  all: unfold t ; clear t ; intros Haux ; erewrite Haux.
  1: etransitivity ; [ | now eapply PeanoNat.Nat.le_add_l].
  all: erewrite List.list_max_app ; now eapply PeanoNat.Nat.max_lub_r.
Qed.

Lemma eval_ext_tree_pref_monotone (tau : ext_tree I O A) f n a o :
  eval_ext_tree tau f n = output a ->
  eval_ext_tree tau (from_pref o (map f (iota 0 (n + (S (List.list_max (eval_ext_tree_trace tau f n)))))))
    (n + (S (List.list_max (eval_ext_tree_trace tau f n)))) = output a.
Proof.
  now apply: eval_ext_tree_pref_monotone_aux _ _ _ _ _ nil.
Qed.

(*Turning ext_tree to Brouwer ext_tree*)
Definition extree_to_extree (tau : ext_tree I O A) (o : O) : ext_tree I O A :=
  fun l => eval_ext_tree tau (from_pref o l) (size l).

Definition extree_to_Bextree (tau : ext_tree I O A) (o : O) : Bext_tree :=
  fun l =>
    let m := (List.list_max (eval_ext_tree_trace tau (from_pref o l) (size l))).+1 in
    if m <= size l then
      (match extree_to_extree tau o l with
            | output a => Some a
            | ask i => None
       end)
    else None.

Lemma extree_to_Bextree_spec tau alpha n a o :
  eval_ext_tree tau alpha n = output a ->
  extree_to_Bextree tau o (map alpha (iota 0 (n + (S (List.list_max (eval_ext_tree_trace tau alpha n)))))) = Some a.
Proof.
  intros Heq.
  unfold extree_to_Bextree.
  unfold extree_to_extree.
  erewrite size_map ; erewrite size_iota.
  erewrite (eval_ext_tree_pref_monotone o Heq).
  unfold eval_ext_tree_trace.
  set m1 := List.list_max _.
  set m2 := List.list_max _.
  case: (ltnP m1 (n +m2.+1)) => hm //.
  suff {hm}: m1 < n + m2.+1 by rewrite ltnNge hm.
  rewrite {}/m1 {}/m2.
  set m:= (X in (n + X)).
  set x := eval_ext_tree_trace_aux _ _ _ _.
  suff -> : x = eval_ext_tree_trace_aux tau alpha n [::]
    by rewrite {}/x {}/m addnS ltnS leq_addl.
  rewrite {}/x.
  erewrite (eval_ext_tree_trace_monotone (n := n) m) ; [ | eassumption].
  erewrite (eval_ext_tree_trace_from_pref (f := alpha) (l := nil)) ;
    rewrite {}/m ; first by rewrite addnS.
  set m1 := List.list_max _.
  set m2 := List.list_max _.
  suff: m1 = m2.
  { rewrite {}/m1 {}/m2. intros H ; rewrite H ; apply PeanoNat.Nat.le_add_l. }
  rewrite {}/m1 {}/m2.
  f_equal.
  cbn ; symmetry.
  eapply eval_ext_tree_trace_monotone.
  exact Heq.
Qed.


Lemma ext_tree_to_Bext_tree_valid tau o:
  Bvalid_ext_tree (extree_to_Bextree tau o).
Proof.
  intros f k a.
  unfold extree_to_Bextree in *.
  unfold extree_to_extree in *.
  repeat erewrite size_map.
  repeat erewrite size_iota.
  set fk := from_pref _ _.
  set m := List.list_max _.
  intros Heq.
  have lem : m < k.
  { destruct (m < k) ; [trivial |].
    now inversion Heq.
  }
  rewrite lem in Heq.
  have eval_aux : eval_ext_tree tau fk k = output a.
  1: destruct (eval_ext_tree tau fk k) ;
  now inversion Heq.
  set fk1 := from_pref _ _.
  set m' := List.list_max _.
  suff: eval_ext_tree tau fk k = eval_ext_tree tau fk1 k.
  2:{ eapply eval_ext_tree_continuous.
      unfold fk1.
      erewrite from_pref_finite_equal.
      2: eapply leq_le ; now eapply ltnW.
      unfold fk.
      destruct k ; [reflexivity |].
      erewrite from_pref_finite_equal ; [reflexivity |].
      eapply leq_le.
      now eapply ltnSE.
  }
  intros Heqfk.
  suff: m' < k.+1.
  { intros lem' ; rewrite lem' ; clear m' lem'.
    suff: eval_ext_tree tau fk1 k.+1 = output a ;
      first by intros h ; now rewrite h.
    suff: eval_ext_tree tau fk1 k.+1 = eval_ext_tree tau fk1 k.
    1: intros Haux ; now rewrite Haux -eval_aux.
    rewrite Heqfk in eval_aux ; rewrite eval_aux.
    erewrite <- PeanoNat.Nat.add_1_r ; unfold eval_ext_tree in *.
    now eapply eval_ext_tree_monotone.
  }
  suff: m = m'.
  1: intros H ; rewrite - H - (PeanoNat.Nat.add_1_r k) ;
  now eapply ltn_addr.
  unfold m ; unfold m'.
  f_equal.
  unfold eval_ext_tree_trace in *.
  rewrite - (PeanoNat.Nat.add_1_r k).
  erewrite <- eval_ext_tree_trace_monotone.
  2: rewrite Heqfk in eval_aux ; eassumption.
  eapply eval_ext_tree_trace_continuous.
  unfold fk1.
  erewrite from_pref_finite_equal.
  2: eapply leq_le ; now eapply ltnW.
  unfold fk.
  destruct k ; [reflexivity |].
  erewrite from_pref_finite_equal ; [reflexivity |].
  eapply leq_le.
  now eapply ltnSE.
Qed.

(*Continuity via ext_trees implies continuity via Brouwer ext_trees*)
Lemma seq_cont_to_Brouwer_aux F (o : O) tau alpha :
  (exists n : I, eval_ext_tree tau alpha n = output (F alpha) ) ->
  exists n : I, Beval_ext_tree (extree_to_Bextree tau o) alpha n = Some (F alpha).
Proof.
  intros [n Htau].
  exists (n + (S (List.list_max (eval_ext_tree_trace tau alpha n)))).
  unfold Beval_ext_tree.
  change nil with (map alpha (iota 0 0)).
  generalize 0 at 2 3 as k.
  eapply (extree_to_Bextree_spec o) in Htau ; revert Htau.
  set m:= n + _.
  suff aux: forall tau m k f a,
      tau (map f (iota 0 (m + k))) = Some a ->
      (forall i j a', tau (map f (iota 0 j)) = Some a' ->
                    tau (map f (iota 0 (i + j))) = Some a') ->
      Beval_ext_tree_aux tau f m (map f (iota 0 k)) k = Some a.
  1:{ intros ; eapply aux.
      2:{ intros.
          erewrite PeanoNat.Nat.add_comm.
          eapply Bvalid_plus ; [ | assumption].
          now eapply ext_tree_to_Bext_tree_valid.
      }
      eapply Bvalid_plus ; [ | assumption].
      now eapply ext_tree_to_Bext_tree_valid.
  }
  clear ; intros * ; revert k.
  induction m ; intros * Htau Hvalid ; [eassumption |].
  cbn.
  remember (tau [seq f i | i <- iota 0 k]) as r ; destruct r.
  1: rewrite - Htau ; symmetry ; now eapply Hvalid.
  rewrite - map_rcons iota_rcons.
  apply IHm ; [now erewrite <- plus_n_Sm | assumption].
Qed.


(*Getting rid of the o:O assumption*)
Definition extree_to_Bextree_noo (tau : ext_tree I O A) : Bext_tree :=
  fun l => match l with
           | nil => match (tau l) with
                    | output a => Some a
                    | ask _ => None
                    end
           | o :: q => extree_to_Bextree tau o (o::q)
           end.

Lemma extree_to_Bextree_noo_eq tau f n k :
  Beval_ext_tree_aux (extree_to_Bextree_noo tau) f n (map f (iota 0 (S k))) (S k) =
              Beval_ext_tree_aux (extree_to_Bextree tau (f 0)) f n (map f (iota 0 (S k))) (S k).
Proof.
  revert k ; induction n ; intros ; [reflexivity |].
  cbn.
  set t := extree_to_Bextree _ _ _.
  destruct t ; [reflexivity |].
  rewrite - map_rcons iota_rcons.
  exact (IHn (k.+1)).
Qed.

Proposition seq_cont_to_Brouwer F : seq_cont F -> Bseq_cont F.
Proof.
  intros [tau Htau].
  exists (extree_to_Bextree_noo tau).
  intros alpha.
  specialize (Htau alpha).
  destruct (seq_cont_to_Brouwer_aux (alpha 0) Htau) as [n Haux].
  destruct Htau as [m Htau].
  exists n.
  destruct n; [now inversion Haux |].
  cbn in *.
  remember (tau nil) as r ; destruct r.
  1: change [:: alpha 0] with (map alpha (iota 0 1)) ; now erewrite extree_to_Bextree_noo_eq.
  suff: @output I _ a = output (F alpha) ; [intros H ; now inversion H |].
  rewrite - Htau ; symmetry.
  now eapply (@eval_ext_tree_monotone _ _ _ _ _ 0).
Qed.

End Brouwer_ext_tree.




Section Brouwer_interaction_trees.
  
Variable A R : Type.
Notation Q := nat.
Implicit Type (F : (Q -> A) -> R).

CoInductive Bitree : Type :=
  | Bret : R -> Bitree
| Bvis : (A -> Bitree) -> Bitree.

Local Notation itree := (@Itree nat A R).

Fixpoint Bieval (b : Bitree) (f : Q -> A) (n : nat) : option R :=
  match n with
  | 0 => match b with
         | Bret o => Some o
         | Bvis k => None
         end
  | S n => match b with
           | Bret o => Some o
           | Bvis k => Bieval (k (f 0)) (f \o S) n
           end
  end.

Lemma Bieval_monotone b f n r:
  Bieval b f n = Some r ->
  Bieval b f n.+1 = Some r.
Proof.
  revert b f ; induction n ; intros b f Heq ; cbn in * ; [destruct b ; now inversion Heq | ].
  destruct b ; [now inversion Heq | ].
  now eapply (IHn (b (f 0)) (f \o succn)).
Qed.

Lemma Bieval_monotone_plus b f n m r:
  Bieval b f n = Some r ->
  Bieval b f (n + m) = Some r.
Proof.
  revert n ; induction m ; intros n Heq ; [ now rewrite addn0 | ].
  rewrite addnS - addSn ; now apply IHm, Bieval_monotone.
Qed.

Lemma Bieval_output_unique b f n m r r' :
  Bieval b f n = Some r ->
  Bieval b f m = Some r' ->
  r = r'.
Proof.
  destruct (@leqP n m) as [Hinf | Hinf].
  - rewrite - (subnKC Hinf) ; intros Heqr Heqr'.
    erewrite Bieval_monotone_plus in Heqr' ; eauto ; now inversion Heqr'.
  - rewrite - (subnKC Hinf) ; intros Heqr Heqr'.
    erewrite Bieval_monotone_plus in Heqr ; [ | eapply Bieval_monotone ; eauto].
    now inversion Heqr.
Qed.


Definition Bseq_cont_interaction F :=
  exists τ : Bitree, forall f : Q -> A, exists n : nat, Bieval τ f n = Some (F f).


Fixpoint Bitree_to_option (i : Bitree)  (l : list A) : option R :=
  match l with
  | nil => match i with
           | Bvis k => None
           | Bret o => Some o
           end
  | cons a l' => match i with
                 | Bvis k => Bitree_to_option (k a) l'
                 | Bret o => Some o
                 end
  end.

Lemma Bitree_to_option_Bieval (i : Bitree) (n : nat) (alpha : Q -> A) :
  Bieval i alpha n = Bitree_to_option i (map alpha (iota 0 n)).
Proof.
  revert alpha i ; induction n as [ | n IHn] ; intros ; [auto | ].
  cbn ; destruct i as [ | k] ; [reflexivity | ].
  suff: forall m, [seq alpha i | i <- iota m.+1 n] = [seq (alpha \o succn) i | i <- iota m n].
  { intros H ; rewrite H ; now apply IHn. }
  clear ; revert alpha ; induction n as [ | n IHn] ; intros alpha m ; [auto | ].
  cbn ; f_equal.
  now apply IHn.
Qed.  

(*Going from Brouwer interaction trees to interaction trees*)

CoFixpoint Bitree_to_itree_aux  (b : Bitree) (n : nat) : itree :=
  match b with
  | Bret a => ret a
  | Bvis k => vis n (fun o => Bitree_to_itree_aux (k o) (S n))
  end.

Definition Bitree_to_itree b := Bitree_to_itree_aux b 0.

Lemma Bitree_to_itreeP_aux b alpha n m r:
  Bieval b (n_comp alpha n) m = Some r <->
    ieval (Bitree_to_itree_aux b n) alpha m = output r.
Proof.
  split.
  - revert n b ; induction m ; cbn ; intros n b Heq.
    + destruct b ; inversion Heq ; now subst.
    + destruct b ; [inversion Heq ; now subst | ].
      apply IHm.
      rewrite n_comp_n_plus in Heq ; now rewrite addn0 in Heq.
  - revert n b ; induction m ; cbn ; intros n b Heq.
    + destruct b ; now inversion Heq.
    + destruct b ; [now inversion Heq | ].
      change (n_comp alpha n \o succn) with (n_comp alpha n.+1).
      apply IHm.
      now rewrite n_comp_n_plus addn0.
Qed.


Lemma Bitree_to_itreeP b alpha m r :
  Bieval b alpha m = Some r <->
    ieval (Bitree_to_itree b) alpha m = output r.
Proof.
  exact (Bitree_to_itreeP_aux b alpha 0 m r).
Qed.


Lemma Bitree_cont_to_itree_cont (F : (nat -> A) -> R) :
  Bseq_cont_interaction F -> seq_cont_interaction F.
Proof.
  intros [b Hb].
  exists (Bitree_to_itree b) ; intros alpha.
  specialize (Hb alpha) as [n Hn] ; exists n.
  now apply Bitree_to_itreeP.
Qed.

CoFixpoint itree_to_Bitree (l : seq A) (d : itree) : Bitree.
Proof.
  refine (match d with
          | ret o => Bret o
          | vis n k => Bvis (fun a => _)
          end).
  refine (if n < size l
          then itree_to_Bitree (rcons l a) (k (nth a l n))
          else itree_to_Bitree (rcons l a) (vis n k)).
Defined.  

Lemma itree_to_Bitree_seq (n m : nat) (d : itree) (alpha : Q -> A) (r : R) :
  Bieval (itree_to_Bitree (map alpha (iota 0 m)) d) (n_comp alpha m) n = Some r ->
  Bieval (itree_to_Bitree (map alpha (iota 0 m.+1)) d) (n_comp alpha m.+1) n = Some r.
Proof.
  revert d alpha m ; induction n ; intros * Hyp.
  - cbn in * ; destruct d ; now inversion Hyp.
  - cbn in * ; destruct d as [ | q k] ; [now inversion Hyp | ].
    destruct (leqP q.+1 m) as [H | H].
    + have aux := ltn_addr 1 H ; rewrite addn1 in aux ; cbn in aux, H.
      rewrite size_map size_iota H in Hyp.
      rewrite size_map size_iota aux.
      rewrite - cats1 n_comp_n_plus addn1 ; rewrite n_comp_n_plus addn0 in Hyp.
      change [:: alpha m.+1] with (map alpha (iota m.+1 1)).
      rewrite - map_cat - iotaD addn1.
      change (n_comp alpha m \o succn) with (n_comp alpha m.+1).
      apply IHn ; unfold itree_to_Bitree.
      rewrite - cat1s ; change [:: alpha 0] with (map alpha (iota 0 1)).
      rewrite - map_cat - iotaD add1n.
      erewrite nth_map, (nth_iota q) ; [ | | rewrite size_iota] ; eauto ; cbn.
      erewrite nth_map, (nth_iota q) in Hyp ; [ | | rewrite size_iota] ; eauto ; cbn in *.
      rewrite - Hyp - cats1 ; change [:: alpha m] with (map alpha (iota m 1)).
      now rewrite - map_cat - iotaD addn1.
    + rewrite ltnNge - subn_eq0  in H ; rewrite size_map size_iota - if_neg in Hyp.
      cbn in * ; rewrite H in Hyp.
      rewrite size_map size_iota.
      rewrite n_comp_n_plus addn0 - cats1 in Hyp.
      rewrite - (map_cat alpha _ (iota m 1)) - iotaD in Hyp.
      remember (eqn (q - m)%Nrec 0) as b ; destruct b.
      * rewrite n_comp_n_plus addn1 - cats1 ; rewrite addn1 in Hyp.
        apply Bieval_monotone in Hyp; cbn in Hyp.
        rewrite size_map size_iota - Heqb - cats1 n_comp_n_plus addn1 in Hyp.
        assumption.
      * rewrite n_comp_n_plus addn1 - cats1 - (map_cat alpha _ (iota m.+1 1)) - iotaD addn1.
        apply IHn.
        rewrite addn1 in Hyp.
        assumption.
Qed.
    
Lemma itree_to_BitreeP (n m : nat) (d : itree) (alpha : Q -> A) (r : R) :
  ieval d alpha n = output r ->
  exists k, Bieval (itree_to_Bitree (map alpha (iota 0 m)) d) (n_comp alpha m) k = Some r.
Proof.
  revert d m ; induction n ; intros d m Hyp.
  - cbn in *.
    exists 0 ; cbn.
    destruct d ; now inversion Hyp.
  - cbn in *.
    destruct d as [ | q k ] ; [exists 0 ; now inversion Hyp | ] ; cbn.
    specialize (IHn (k (alpha q)) m.+1 Hyp) as [i Hj].
    exists (i.+1 + (q.+1 - m)).
    remember (q.+1 - m) as x.
    clear Hyp.
    revert q m Heqx Hj.
    induction x ; intros.
    + rewrite addn0.
      cbn in * ; rewrite size_map size_iota.
      rewrite - Heqx ; cbn.
      rewrite (nth_map 0) ; [ rewrite nth_iota | rewrite size_iota] ; cbn ; eauto.
      rewrite n_comp_n_plus addn0 - cats1.
      now change ([:: alpha m]) with (map alpha (iota m 1)) ; rewrite - map_cat - iotaD addn1.
    + rewrite addnS ; cbn in *.
      rewrite size_map size_iota.
      rewrite - if_neg - Heqx ; cbn.
      specialize (IHx q m.+1).
      rewrite size_rcons size_map size_iota; rewrite size_map size_iota in IHx.
      cbn in *.
      have aux : x = q - m. 
      { eapply (f_equal Nat.pred) in Heqx ; cbn in * ; now rewrite Heqx subSKn. }
      cbn in aux ; rewrite - aux; rewrite - aux in IHx ; specialize (IHx erefl).
      destruct x.
      * cbn in * ; rewrite -> addn0 ; rewrite -> addn0 in IHx.
        do 2 (rewrite n_comp_n_plus - cats1) ; rewrite addn0 addn1.
        rewrite - (map_cat alpha _ (iota m 1)) - iotaD addn1.
        rewrite n_comp_n_plus - cats1 in IHx ; rewrite addn1 in IHx.
        now apply IHx, (itree_to_Bitree_seq (m := m.+1)).
      * cbn in *.
        rewrite - IHx ; [ | now apply  (itree_to_Bitree_seq (m := m.+1))].
        repeat (rewrite n_comp_n_plus) ; rewrite addn0 addn1.
        repeat (rewrite - cats1).
        now change ([:: alpha m]) with (map alpha (iota m 1)) ; rewrite - map_cat - iotaD addn1.
Qed.
    
Lemma itree_to_Bitree_cont (F : (nat -> A) -> R) :
  seq_cont_interaction F -> Bseq_cont_interaction F.
Proof.
  intros [d Hd].
  exists (itree_to_Bitree nil d).
  intros alpha ; specialize (Hd alpha) as [n Hn].
  now apply (itree_to_BitreeP (n := n) 0).
Qed.


  
End Brouwer_interaction_trees.
