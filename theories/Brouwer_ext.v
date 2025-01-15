
Require Import Program.
From Equations Require Import Equations.
Require Import extra_principles Util.
From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import continuity_zoo_Prop.
Require Import Lia.

Arguments ext_tree {_ _ _}, _ _ _.
(* Set Default Goal Selector "!".*)

(* This file presents Brouwer-like equivalents of extensional trees and interaction,
   trees, i.e. trees that ask their questions "in order", much like Brouwer trees 
   vs dialogue trees.
 *)

Section Brouwer_ext_tree.

  (*The goal of this Section is to provide an extensional tree equivalent to Brouwer
    trees, and to prove that it is equivalent to seq_contW. *)

Variable A R : Type.
Notation Q := nat.
Implicit Type (F : (Q -> A) -> R).

Lemma from_pref_map_iota  (f : nat -> A) m n k a : (n <= m) ->
    from_pref a (map f (iota k (S m))) n = f (k + n).
Proof.
move=> lenm.
have -> : k + n = nth k (iota k m.+1) n by rewrite nth_iota.
rewrite /from_pref (nth_map k) // size_iota //.
Qed.

Lemma from_pref_finite_equal l (alpha : Q -> A) a n :
  \max_(i <- l) i <= n ->
  map (from_pref a (map alpha (iota 0 n.+1))) l = map alpha l.
Proof.
  elim: l => [| k l ihl] //.
  rewrite big_cons geq_max; case /andP=> lekn /ihl h /=.
  by rewrite -h /= from_pref_map_iota.
Qed.

(*
Lemma leq_le i j : i <= j -> le i j.
Proof. by move/leP. Qed.
*)

(*Brouwer extensional trees: they go to option R, and None is considered to be "next query".*)
Definition Bext_tree := list A -> option R.

Fixpoint Beval_ext_tree_aux (tau : Bext_tree) (f : Q -> A) (n : nat) (l : seq A) (q : Q) :
  option R :=
  match n, tau l with
  |S k, None => Beval_ext_tree_aux tau f k (rcons l (f q)) (S q)
  |_, _ =>  tau l
  end.


Definition Beval_ext_tree tau f n := Beval_ext_tree_aux tau f n nil 0.

(*Continuity via Brouwer extensional trees*)
Definition Bseq_cont F :=
  exists tau : Bext_tree, forall alpha, exists n : nat, Beval_ext_tree tau alpha n = Some (F alpha).

(*The following is a bunch of lemmas that mimick lemmas about extensional trees,
 albeit for Brouwer extensional trees this time. *)

Definition wf_Bext_tree (tau : Bext_tree) :=
  forall f : Q -> A,  exists n o, tau (map f (iota 0 n)) = Some o.

Definition Bvalid_ext_tree (tau : Bext_tree) :=
  forall (f : Q -> A) (k : Q) (r : R), tau (map f (iota 0 k)) = Some r ->
                          tau (map f (iota 0 k.+1)) = Some r.

Definition Bseq_cont_valid F :=
  exists tau : Bext_tree,
    (forall alpha, exists n : nat, Beval_ext_tree tau alpha n = Some (F alpha)) /\
      (Bvalid_ext_tree tau).

Lemma Bvalid_plus (tau : Bext_tree) :
  Bvalid_ext_tree tau -> forall f k j r,
      tau (map f (iota 0 k)) = Some r ->
      tau (map f (iota 0 (k + j))) = Some r.
Proof.
move=> H f k j; elim: j k => [| j ihj] k r e; first by rewrite addn0.
rewrite addnS; apply: (ihj k.+1).
exact: H.
Qed.

Lemma Bvalid_every_list (tau : Bext_tree) :
  Bvalid_ext_tree tau ->
  forall l l' r, tau l = Some r -> tau (l ++ l') = Some r.
Proof.
  unfold Bvalid_ext_tree ; intros Hvalid l l' r Heqr.
  destruct l' as [ | a l'] ; [now rewrite cats0 | ].
  rewrite - (take_size (l ++ a :: l')) - (map_nth_iota0 a) size_cat ; [ | lia].
  apply Bvalid_plus ; auto.
  rewrite map_nth_iota0  ; [ | rewrite size_cat ; lia].
  now rewrite (take_size_cat (a :: l') erefl).
Qed.

Fixpoint Beval_ext_tree_trace_aux
  (tau : Bext_tree) (f : Q -> A) (n : nat) (l : seq A) (q : Q) : Q :=
  match n, tau l with
  | S k, None => S (Beval_ext_tree_trace_aux tau f k (rcons l (f q)) (S q))
  | _ , _ => 0
  end.

Definition Beval_ext_tree_trace tau f n := Beval_ext_tree_trace_aux tau f n nil 0.

Lemma Beval_ext_tree_map_aux tau f n l q :
  Beval_ext_tree_aux tau f n l q =
    tau (l ++ map f (iota q ((Beval_ext_tree_trace_aux tau f n l q)))).
Proof.
elim: n l q =>[| n ihn] l q /=; first by rewrite cats0.
case e: (tau l) => [a |] /=; first by rewrite cats0.
by rewrite -cat_rcons.
Qed.

Lemma Beval_ext_tree_constant (tau : Bext_tree) (f : Q -> A) n r l q :
    tau l = Some r ->
    Beval_ext_tree_aux tau f n l q = Some r.
Proof. by elim: n l q => [| n ihn] l q //= ->. Qed.

Lemma Beval_ext_tree_output_unique tau f l n1 n2 o1 o2 q :
  Beval_ext_tree_aux tau f n1 l q = Some o1 ->
  Beval_ext_tree_aux tau f n2 l q = Some o2 ->
  o1 = o2.
Proof.
elim: n1 n2 l q => [| n1 ihn1] [ | n2] l q /=.
1, 2: by move=> -> [].
1, 2: case: (tau l) => [ a -> [] // | q' //].
intros H. eapply ihn1 ; eassumption.
Qed.

Lemma Beval_ext_tree_monotone (tau : Bext_tree ) f n k r l q :
  Beval_ext_tree_aux tau f n l q = Some r ->
  Beval_ext_tree_aux tau f (n + k) l q = Some r.
Proof.
  revert l q ; induction n as [ | n IHn] ; simpl in * ; intros l q H.
  1: now eapply Beval_ext_tree_constant.
  destruct (tau l) ; [ assumption |].
  now eapply IHn.
Qed.

Lemma eval_ext_tree_from_pref a (tau : @ext_tree Q A R) f n l :
  eval_ext_tree_aux tau f n (map f l) =
    eval_ext_tree_aux tau (from_pref a (map f (iota 0 (\max_(q <- l ++ (eval_ext_tree_trace_aux tau f n (map f l))) q).+1))) n (map f l).
Proof.
  elim: n l => [| n ihn l] //=.
  case: (tau _) => [q |] //.
  rewrite from_pref_map_iota; last first.
    by rewrite big_cat /= maxnC leq_max leq_bigmax_seq ?mem_head.
  - by rewrite -map_rcons ihn cat_rcons. 
Qed.

(*Same for the trace of eval_ext_tree*)
Lemma eval_ext_tree_trace_from_pref a (tau : ext_tree Q A R) f n k l :
  \max_(q <- l ++ (eval_ext_tree_trace_aux tau f n (map f l))) q <= k ->
  eval_ext_tree_trace_aux tau f n (map f l) =
    eval_ext_tree_trace_aux tau (from_pref a (map f (iota 0 (S k)))) n (map f l).
Proof.
  elim: n l => [| n ihn] l //=.
  case: (tau _) => [q |] // h.
  rewrite from_pref_map_iota; last first.
  - by move/bigmax_leqP_seq: h; apply; rewrite // mem_cat mem_head orbT.
  - by rewrite -map_rcons in h *; rewrite ihn // cat_rcons.
Qed. 


(*A technical lemma to prove that eval_ext_tree using lists as partial oracles
 is monotone*)
 Lemma eval_ext_tree_pref_monotone_aux a (tau : ext_tree Q A R) f n r l (ll := eval_ext_tree_trace_aux tau f n [seq f i | i <- l] : seq Q
 ):
 eval_ext_tree_aux tau f n (map f l) = output r ->
 eval_ext_tree_aux tau (from_pref a (map f (iota 0 (n + (\max_(i <- l ++ ll) i).+1))))
   (n + (\max_(i <- l ++ ll) i).+1) (map f l) = 
   output r.
Proof.
  move=> h.
  apply: eval_ext_tree_monotone.
  rewrite -h (eval_ext_tree_from_pref a).
  apply: eval_ext_tree_continuous.
  rewrite addnS -eval_ext_tree_trace_from_pref -/ll ?leq_addl // from_pref_finite_equal.
  - by rewrite from_pref_finite_equal // big_cat /= leq_maxr.
  - by apply: (leq_trans _ (leq_addl _ _)); rewrite big_cat leq_maxr.
Qed.  

Lemma eval_ext_tree_pref_monotone (tau : ext_tree Q A R) f n r a :
  eval_ext_tree tau f n = output r ->
  eval_ext_tree tau (from_pref a (map f (iota 0 (n + (\max_(i <- eval_ext_tree_trace tau f n) i).+1))))
    (n + (\max_(i <- eval_ext_tree_trace tau f n) i).+1) = output r.
Proof.
  exact: eval_ext_tree_pref_monotone_aux _ _ _ _ _ nil.
Qed.

(*Turning ext_tree to Brouwer ext_tree*)
Definition extree_to_extree (tau : ext_tree Q A R) (a : A) : ext_tree Q A R :=
  fun l => eval_ext_tree tau (from_pref a l) (size l).

Definition extree_to_Bextree (tau : ext_tree Q A R) (a : A) : Bext_tree :=
  fun l =>
    let m := (\max_(i <- (eval_ext_tree_trace tau (from_pref a l) (size l))) i).+1 in
    if m <= size l then
      (match extree_to_extree tau a l with
            | output r => Some r
            | ask q => None
       end)
    else None.

Lemma extree_to_Bextree_spec tau alpha n r a :
  eval_ext_tree tau alpha n = output r ->
  extree_to_Bextree tau a (map alpha (iota 0 (n + (\max_(i <- eval_ext_tree_trace tau alpha n) i).+1))) = Some r.
Proof.
  intros he.
  rewrite /extree_to_Bextree /extree_to_extree size_map size_iota.
  rewrite (eval_ext_tree_pref_monotone _ he) /eval_ext_tree_trace.
  case: ifP => //.
  set x := eval_ext_tree_trace_aux _ _ _ _.
  suff -> : x = eval_ext_tree_trace_aux tau alpha n [::].
  - by rewrite {}/x addnS ltnS leq_addl.
  - rewrite {}/x.
  set m1 := (X in n + X).
  rewrite (eval_ext_tree_trace_monotone m1 he) /m1 addnS.
  rewrite -[LHS](eval_ext_tree_trace_from_pref a (l := [::])) //.
  by rewrite -addnS -(eval_ext_tree_trace_monotone _ he) leq_addl.
Qed.


Lemma ext_tree_to_Bext_tree_valid tau a:
  Bvalid_ext_tree (extree_to_Bextree tau a).
Proof.
  move=> f k r.
  rewrite /extree_to_Bextree /extree_to_extree !size_map !size_iota.
  case: k => [| k] //.
  set m1 := (X in X < _); set m2 := (X in X < k.+2).
  case: ifP => // lem.
  set fk := from_pref _ _; set fk1 := from_pref _ _.
  case e : (eval_ext_tree tau fk k.+1) => [// | aa] [] ea.
  rewrite ea in e => {ea aa}.
  have e1 : eval_ext_tree tau fk k.+1 = eval_ext_tree tau fk1 k.+1.
    apply: eval_ext_tree_continuous.
    by rewrite from_pref_finite_equal ?from_pref_finite_equal // ltnW.
  have e2 : eval_ext_tree tau fk1 k.+2 = eval_ext_tree tau fk1 k.+1.
    by rewrite -e1 e -addn1; apply: eval_ext_tree_monotone; rewrite -[LHS]e1.
  suff -> : m2 < k.+2 by rewrite e2 -e1 e. 
  suff <- : m1 = m2 by rewrite ltnS; exact: ltnW.
  rewrite /m1 /m2 -/fk -/fk1.
  suff -> : eval_ext_tree_trace tau fk k.+1 = eval_ext_tree_trace tau fk1 k.+2 by [].
  rewrite -[_.+2]addn1 /eval_ext_tree_trace. 
  rewrite -[RHS](@eval_ext_tree_trace_monotone _ _ _ _ _ _ _ r); last by rewrite -[LHS]e1.
  by apply: eval_ext_tree_trace_continuous; rewrite !from_pref_finite_equal // ltnW.
  Qed.
 
Hint Resolve ext_tree_to_Bext_tree_valid.

(*Continuity via ext_trees implies continuity via Brouwer ext_trees*)
Lemma seq_cont_to_Brouwer_aux F (a : A) tau alpha :
  (exists n : Q, eval_ext_tree tau alpha n = output (F alpha)) ->
  exists n : Q, Beval_ext_tree (extree_to_Bextree tau a) alpha n = Some (F alpha).
Proof.
  case=> n Htau.
  exists (n + (\max_(i <- eval_ext_tree_trace tau alpha n) i).+1).
  rewrite /Beval_ext_tree -[[::]]/(map alpha (iota 0 0)).
  move: {3 4}0 => k.
  move/(extree_to_Bextree_spec a): Htau.
  set m := n + _.
  suff aux ttau mm kk f r :
    ttau (map f (iota 0 (mm + kk))) = Some r ->
    (forall i j a', ttau (map f (iota 0 j)) = Some a' ->
                    ttau (map f (iota 0 (j + i))) = Some a') ->
                    Beval_ext_tree_aux ttau f mm (map f (iota 0 kk)) kk = Some r.
    move=> h; apply: aux; last by move=> i j aa; apply: Bvalid_plus.
    exact: Bvalid_plus.
    clear => e h.
    elim: mm kk e => [| m ihm] k e //=.
    case er: (ttau [seq f i | i <- iota 0 k]) => [aa |].
    symmetry; rewrite -e addnC; exact: h.
  by rewrite -map_rcons iota_rcons; apply: ihm; rewrite addnS.
  Qed.

(*Getting rid of the o:O assumption*)
Definition extree_to_Bextree_noo (tau : ext_tree Q A R) : Bext_tree :=
  fun l => match l with
           | nil => match (tau l) with
                    | output r => Some r
                    | ask _ => None
                    end
           | a :: q => extree_to_Bextree tau a (a::q)
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
  suff: @output Q _ r = output (F alpha) ; [intros H ; now inversion H |].
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
         | Bret a => Some a
         | Bvis k => None
         end
  | S n => match b with
           | Bret a => Some a
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
           | Bret a => Some a
           end
  | cons a l' => match i with
                 | Bvis k => Bitree_to_option (k a) l'
                 | Bret a => Some a
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
  | Bvis k => vis n (fun a => Bitree_to_itree_aux (k a) (S n))
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
          | ret a => Bret a
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
  elim: n d alpha m => [| n ihn] [| q k] alpha m //=.
  rewrite !size_map !size_iota !n_comp_n_plus addn0 addn1.
  rewrite -!map_rcons !iota_rcons -!map_cons.
  have aux s : 0 :: iota 1 s = iota 0 s.+1 by rewrite -cat1s -(iotaD 0 1 s) add1n.
  rewrite !aux.
  case: (ltngtP q m) => H.
  - have -> : q < m.+1 by rewrite ltnS ltnW.
    move/ihn; set u1 := nth _ _ _. set u2 := nth _ _ _.
    suff -> : u1 = u2 by [].
   rewrite {}/u1 {}/u2 !(nth_map 0) ?size_iota //; last by rewrite ltnS ltnW.
   rewrite !nth_iota //; last by rewrite ltnS ltnW.
  - rewrite ltnS leqNgt H; exact: ihn.
  - rewrite ltnS leq_eqVlt H eqxx /=. 
     move/Bieval_monotone=> /=.
     rewrite size_map size_iota ltnS leqnn n_comp_n_plus addn1 -map_rcons -map_cons.
     by rewrite iota_rcons aux.
Qed.

Lemma itree_to_BitreeP (n m : nat) (d : itree) (alpha : Q -> A) (r : R) :
  ieval d alpha n = output r ->
  exists k, Bieval (itree_to_Bitree (map alpha (iota 0 m)) d) (n_comp alpha m) k = Some r.
Proof.
  elim: n d m => [| n ihn] [rr | q k] m //=  Hyp ; inversion Hyp ; subst.
  - by exists 0.
  - by exists 0. 
  - have {Hyp ihn} [i Hj] := ihn (k (alpha q)) m.+1 Hyp.
    exists (i.+1 + (q.+1 - m)).
    case: (posnP (q.+1 - m)) => Heqx.
    + rewrite Heqx addn0 /= size_map size_iota.
      have ltqn : q < m by rewrite /leq -Heqx eqxx.
      rewrite ltqn (nth_map 0) ?size_iota //.
      by rewrite n_comp_n_plus -map_rcons addn0 iota_rcons nth_iota.
    + have {Heqx} leqmq : m <= q by move: Heqx; rewrite subn_gt0 ltnS.
      have e : q = m + (q - m) by rewrite (subnKC).
      move: Hj. rewrite subSn // addSn -addnS. 
      rewrite [in vis _ _]e [in alpha _]e {leqmq e}. move: (q - m) => x.
      elim: x m => [| x ihx] m.
      * rewrite addn0 addn2 /=.
        rewrite size_map size_iota /= ltnn /= size_rcons size_map size_iota ltnSn.
        rewrite !n_comp_n_plus -!map_rcons addn0 addn1 !iota_rcons.
        rewrite (nth_map 0) ?size_iota // nth_iota // add0n => h.
        exact: itree_to_Bitree_seq.
      * rewrite [m + x.+1]addnS => h.
        rewrite [i + _]addnS /= size_map size_iota -if_neg -leqNgt -addnS leq_addr.
        rewrite n_comp_n_plus addn0 -map_rcons iota_rcons [m + _]addnS.
        apply: ihx; exact: itree_to_Bitree_seq.
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
