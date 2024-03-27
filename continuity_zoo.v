From mathcomp Require Import all_ssreflect.
Require Import Program.
From Equations Require Import Equations.
Require Import extra_principles.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section continuity_principles.

(* I is for oracle's input, O is for oracle's output, A is for return type *)
(* TODO : change for Q, A, (questions/answers from oracle) and T *)  
Variable I O A : Type.

Implicit Type (F : (I -> O) -> A).

(* Dialogue trees are from von Oosten, but the inductive type presentation is 
   probably from Escardó, TODO let's ask him.
   Inductive dialogue trees. See, e.g., Escardó
   https://www.cs.bham.ac.uk//~mhe/dialogue/dialogue-to-brouwer.agda *)
Inductive dialogue :=
  | eta : A -> dialogue
  | beta : I -> (O -> dialogue) -> dialogue.

Implicit Type (d : dialogue).

Fixpoint deval d (f : I -> O) : A :=
  match d with
  | eta o => o
  | beta q k => deval (k (f q)) f
  end.

(* Escardó's eloquence *)
Definition dialogue_cont F := {d : dialogue & F =1 deval d}.

(* Intensional dialogue continuity.*)
Inductive is_dialogue : ((I -> O) -> A) -> Type :=
  | teta o : is_dialogue (fun _ => o)
  | tbeta (q : I) (k : O -> (I -> O) -> A) (H : forall a, is_dialogue (k a))
      : is_dialogue (fun f => k (f q) f).

(* TODO : trace the literature for Brouwer trees
TODO: have a look at CPP24 paper by Eremondi. See also may be Coq files by F. Pottier
Jon Sterling's Brouwer trees, i.e. Escardó's dialogue normalized by giving 
queries in order. *)
Inductive Btree : Type :=
  | spit : A -> Btree
  | bite : (O -> Btree) -> Btree.

Implicit Type (b : Btree).

Fixpoint beval b (f : nat -> O) : A :=
  match b with
  |spit o => o
  |bite k => beval (k (f 0)) (f \o S)
  end.

Definition btree_contP G := {b : Btree & G =1 beval b}.

(* For fun, the nat-dependent version. *)
Inductive Btree_dep (P : nat -> Type) : nat -> Type :=
| Beta_dep : forall n, A -> Btree_dep P n
| Bbeta_dep : forall n,
    (P n -> Btree_dep P (S n)) -> Btree_dep P n.

(* Escardó and Oliva : conversion Btree <-> dialogue : see below
https://www.cs.bham.ac.uk//~mhe/dialogue/dialogue-to-brouwer.agda *)

(* Sterling in Agda:  Btree-continous <-> dialogue-continuous
 Currently the exact transposition in Coq does not work
 TODO : see whether we can patch this *)


(* Xia et al.'s interaction trees. Connected to
of Forster et al.' sequential continuity, see below
It is dialogue + delay monad *)
CoInductive itree (E: Type -> Type) (R: Type) : Type :=
| Ret (r : R) (* computation terminating with value r *)
| Tau (t : itree E R) (* "silent" tau transition with child t *)
| Vis {O : Type} (e : E O) (k : O -> itree E R).


(* Forster et al.'s sequential continuity, for which they credit van Oosten. We skip the 
   reject constructor *)
(* Forster et al.: https://arxiv.org/pdf/2307.15543.pdf *)
(* Van Oosten: https://projecteuclid.org/journals/notre-dame-journal-of-formal-logic/volume-52/issue-4/Partial-Combinatory-Algebras-of-Functions/10.1215/00294527-1499381.full *)

Inductive result (TI TA : Type) : Type :=
|ask : TI -> result TI TA
|output : TA -> result TI TA.

Arguments ask {TI TA}.
Arguments output {TI TA}.

(* Forster et al's extensional trees. *)
Definition ext_tree := list O -> result I A.

(* Step-indexed evaluation of an ext_tree against oracle f. 
eval_ext_tree tau f n will ask *exactly* n times the oracle. *)

Fixpoint eval_ext_tree_aux (tau : ext_tree) (f : I -> O) (n : nat) (l : list O) : result I A := 
  match n, tau l with
  |S k, ask q => eval_ext_tree_aux tau f k (rcons l (f q))
  |_, _ => tau l
  end.
               
Definition eval_ext_tree tau f n := eval_ext_tree_aux tau f n [::].

Lemma eval_ext_tree_ext tau1 tau2 f n :
   tau1 =1 tau2 -> eval_ext_tree tau1 f n = eval_ext_tree tau2 f n.
Proof.
rewrite /eval_ext_tree; elim: n [::] => [|n ihn] l tauE; rewrite /= tauE //.
case: (tau2 l) => // q; exact: ihn. 
Qed.

Lemma eval_ext_tree_constant (tau : ext_tree) (f : I -> O) :
  forall n a l, tau l = output a -> eval_ext_tree_aux tau f n l = output a.
Proof.
  intros n a.
  induction n ; intros l H.
  - assumption.
  - cbn.
    now rewrite H.
Qed.    

Lemma eval_ext_tree_output_unique tau f l n1 n2 o1 o2 :
  eval_ext_tree_aux tau f n1 l = output o1 ->
  eval_ext_tree_aux tau f n2 l = output o2 ->
  o1 = o2.
Proof.
elim: n1 n2 l => [| n1 ihn1] [ | n2] l /=.
1, 2: by move=> -> [].
1, 2: case: (tau l) => [q // | o -> [] //]; exact: ihn1.  
Qed.

(* Sequence of questions asked while step-index evaluating tau via f at depth n *)

Fixpoint eval_ext_tree_trace_aux (tau : ext_tree) (f : I -> O) (n : nat) (l : list O) : list I :=
  match n, (tau l) with
  | S k, ask q => q :: (eval_ext_tree_trace_aux tau f k (rcons l (f q)))
  | _ , _ => [::]
  end.

(* Related: Andrej Bauer pointed to them 1.7.5 van Oosten's "Relaizability: an introduction to its categorical side" book introducing the trace associated to a run from a query a to a result b using oracle f, called an f-dialogue.
   He later called this "interrogations" *)
Definition eval_ext_tree_trace tau f n := eval_ext_tree_trace_aux tau f n [::].

Lemma eval_ext_tree_map_aux tau f n l :
  eval_ext_tree_aux tau f n l =
     tau (l ++ (map f (eval_ext_tree_trace_aux tau f n l))).
Proof.
elim: n l => [|n ihn] l //=; first by rewrite cats0.
case e: (tau l) => [q | o'] /=; last by rewrite cats0 e.
by rewrite ihn cat_rcons.
Qed.

Lemma eval_ext_tree_map tau f n : 
  eval_ext_tree tau f n = tau (map f (eval_ext_tree_trace tau f n)).
Proof.
rewrite /eval_ext_tree_trace /eval_ext_tree; exact:eval_ext_tree_map_aux.
Qed.


(*TODO : move this to some Section with lemmas about eval_ext_tree*)
Lemma eval_ext_tree_monotone (tau : ext_tree ) f n k a l :
  eval_ext_tree_aux tau f n l = output a ->
  eval_ext_tree_aux tau f (n + k) l = output a.
Proof.
  revert l ; induction n as [ | n IHn] ; cbn in * ; intros l H.
  1: now eapply eval_ext_tree_constant.
  destruct (tau l) ; [ | assumption].
  now eapply IHn.
Qed.

(*TODO : move this to some Section with lemmas about eval_ext_tree*)
Lemma eval_ext_tree_trace_monotone (tau : ext_tree) f n k a l :
  eval_ext_tree_aux tau f n l = output a ->
  eval_ext_tree_trace_aux tau f n l = eval_ext_tree_trace_aux tau f (n + k) l.
Proof.
  revert l ; induction n as [ | n IHn] ; cbn in * ; intros l H.
  destruct k ; cbn ; [reflexivity | now rewrite H].
  destruct (tau l) ; [ | reflexivity].
  f_equal.
  now eapply IHn.
Qed.

Lemma eval_ext_tree_trace_size_eval (tau : ext_tree) f n a l :
  eval_ext_tree_aux tau f n l = output a ->
  eval_ext_tree_aux tau f (size (eval_ext_tree_trace_aux tau f n l)) l = output a.
Proof.
  revert l ; induction n as [ | n IHn] ; cbn in * ; intros l H ; [assumption |].
  case_eq (tau l) ; intros i Heq ; rewrite Heq in H ; cbn ; rewrite Heq.
  2: now trivial.
  now eapply IHn.
Qed.  


(* this one had more hypotheses about "total" and "well-founded" *)
Definition ext_tree_for F (τ : ext_tree) : Type :=
  forall f : I -> O, {n : nat & eval_ext_tree τ f n = output (F f)}.

(* TODO: as this is the one seq_cont we care about, may be change its name *)
Definition seq_contW F :=
  {τ : ext_tree & ext_tree_for F τ}.

Definition wf_ext_tree (tau : ext_tree) :=
  forall f : nat -> O,  {n & {o & tau (map f (iota 0 n)) = output o} }.

(* Conjectures:
- seq_contW F tau -> well_founded tau when I = nat ? have a section about Baire spaces 
TODO (longer term) : think about PCA results we could obtain from these definitions. In this context,
the latter conjecture might play a role, otherwise, probably not.
 *)


(* May be require more than wf, but also possibly non_empty and/or valid *)
Definition seq_cont F :=
  { tau : ext_tree &  prod (wf_ext_tree tau)  (ext_tree_for F tau)}.

Definition valid_ext_tree (tau : ext_tree) := 
  forall l o,  tau l = output o -> forall a, tau (rcons l a) = output o.

Lemma valid_cat (tau : ext_tree) l l' o :
  valid_ext_tree tau -> tau l = output o -> tau (l ++ l') = output o.
Proof.
  destruct l' using last_ind ; intros.
  - now rewrite cats0.
  - rewrite - rcons_cat.
    eapply H.
    now eapply IHl'.
Qed.

(* Interrogations (van Oosten) *)
Inductive interrogation (f : I -> O) : seq (I * O) -> (seq O -> result I A) -> Type :=
  NoQuestions τ : interrogation f [::] τ
| Ask l τ q a : f q = a ->
                interrogation f l τ ->
                τ (map snd l) = ask q -> interrogation f (rcons l (q, a)) τ.

Definition continuous_via_interrogations_ex F τ :=
  forall f, { ans & prod (interrogation f ans τ) (τ (map snd ans) = output (F f)) }.

Definition continuous_via_interrogations F :=
  { τ & continuous_via_interrogations_ex F τ }.

Definition modulus_on A' (F : (I -> O) -> A') (f : I -> O) (l : seq I) :=
  forall g : I -> O, map f l = map g l -> F f = F g.

 (* TODO (maybe) Modulus is not exposed here... Misnomer? *)
Definition modulus_continuous A' (F : (I -> O) -> A') :=
  forall f, { L & modulus_on F f L }.

Definition modulus A' (F : (I -> O) -> A') (M : (I -> O) -> list I) :=
   forall f g,  map f (M f) = map g (M f) ->  F f = F g.

(* This one is the one: *)
Definition continuous_via_modulus A' (F : (I -> O) -> A') :=
  { M & modulus F M }.

Definition auto_modulus (F : (I -> O) -> A) M :=
  prod (modulus F M) (modulus M M).

Definition uniform_continuous (F : (I -> O) -> A) :=
  { l : list I & forall f : I -> O, modulus_on F f l}.

End continuity_principles.

Arguments eta {I O A} o.
Arguments beta {I O A} q k.
Arguments spit {O A} o.
Arguments bite {O A} k.


Arguments ask {TI TA}.
Arguments output {TI TA}.

Section Brouwer.

Variable O A : Type.
Local Notation Brouwer := (Btree O A).
Local Notation dialogue := (dialogue nat O A).

(*Going from Brouwer trees to dialogue trees*)

Fixpoint Btree_to_dialogue_aux  (b : Brouwer) (n : nat) : dialogue :=
  match b with
  | spit a => eta a
  | bite k => beta n (fun o => Btree_to_dialogue_aux (k o) (S n))
  end.

Definition Btree_to_dialogue b := Btree_to_dialogue_aux b 0.

Fixpoint n_comp (f : nat -> O) (n : nat) : nat -> O :=
  match n with
  | 0 => f
  | S k => (n_comp f k) \o S
  end.

Lemma n_comp_n_plus f n k : n_comp f n k = f (n + k).
Proof.
  revert k ; induction n as [ | n IHn] ; [reflexivity |].
  intros k ; cbn.
  erewrite IHn.
  now erewrite plus_n_Sm.
Qed.

Lemma Btree_to_dialogueP_aux b alpha n :
  beval b (n_comp alpha n) = deval (Btree_to_dialogue_aux b n) alpha.
Proof.
  revert n ; induction b ; [reflexivity |].
  intros. cbn.
  erewrite (H _ (S n)).
  erewrite n_comp_n_plus.
  now erewrite <- plus_n_O.
Qed.

Lemma Btree_to_dialogueP b alpha :
  beval b alpha = deval (Btree_to_dialogue b) alpha.
Proof.
  exact (Btree_to_dialogueP_aux b alpha 0).
Qed.

Lemma bcont_to_dialogue_cont (F : (nat -> O) -> A) :
  btree_contP F -> dialogue_cont F.
Proof.
  intros [b Hb].
  exists (Btree_to_dialogue b) ; intros alpha.
  rewrite (Hb alpha).
  exact (Btree_to_dialogueP b alpha).
Qed.

(*Going from dialogue trees to Brouwer trees, in two different ways.*)
  
(*Here is the proof by Sterling:
http://jonsterling.github.io/agda-effectful-forcing/Dialogue.Normalize.html*)


(*norm1 and norm2 specify when a dialogue tree is normalizable into a Brouwerian one*)
Inductive norm1 : list O -> dialogue -> Type :=
| normret : forall l a, norm1 l (eta a)
| normask : forall l i k, norm2 l i k l -> norm1 l (beta i k)
with
  norm2 : list O -> nat -> (O -> dialogue) -> list O -> Type :=
| normzerocons : forall l k l' j,  norm1 l (k j) -> norm2 l 0 k (cons j l')
| normsucccons : forall l i k l' j, norm2 l i k l' -> norm2 l (S i) k (cons j l')
| normzeronil : forall l k,
    (forall o, norm1 (cons o l) (k o)) ->
    norm2 l 0 k nil
| normsuccnil : forall l i k,
    (forall o, norm2 (cons o l) i k nil) ->
    norm2 l (S i) k nil.


(*If a dialogue tree is normalizable, we can indeed retrieve a Brouwer tree*)
Lemma reify : forall l d, norm1 l d -> Brouwer
with reify2 : forall l i k l', norm2 l i k l' -> Brouwer.
Proof.
  - intros * H.
    induction H as [ l a | l i k IH].
    + exact (spit a).
    + exact (reify2 l i k l IH).
  - intros * H.
    induction H as [ | l i k l' j Hnorm IH | l k ke | l i k ke].
    + eapply (reify _ _).
      eassumption.
    + exact IH.
    + eapply bite.
      exact (fun o => reify _ _ (ke o)).
    + eapply bite.
      exact (fun o => reify2 _ _ _ _ (ke o)).
Defined.

(*Then Sterling shows that any dialogue tree is normalizable.
Unfortunately the following code is not accepted by Coq.*)
(* TODO see whether we can patch this *)
Fail Equations reflect (l : list O) (d : dialogue) : norm1 l d:=
  reflect l (eta a) := @normret l a ;
  reflect l (beta n q) := normask (@reflect2 l n q l)
where reflect2 l1 i k l2 : norm2 l1 i k l2 :=
  reflect2 l1 0 k nil := normzeronil (fun o => reflect (cons o l1) (k o)) ;
  reflect2 l1 (S j) k nil := normsuccnil (fun o => reflect2 (cons o l1) j k nil) ;
  reflect2 l1 0 k (cons o l2) := normzerocons l2 (reflect l1 (k o)) ;
  reflect2 l1 (S j) k (cons o l2) := normsucccons o (reflect2 l1 j k l2) .

    
(* This is the proof by Escardó and Oliva:
  https://www.cs.bham.ac.uk//~mhe/dialogue/dialogue-to-brouwer.agda *)


(* (follow n b) is the immediate subtree of b selected when alpha 0 = n,
   for any alpha *)
Definition follow (o : O) (b : Brouwer) : Brouwer :=
  match b with
  |spit a => b (* reached answer *)
  |bite k => k o (* select the nth child tree *)
  end.

(* Resulting spec wrt to beval. Note the composition with successor, so
as to query alpha on n at depth n. *)
Lemma followP (alpha : nat -> O) (b : Brouwer) :
  beval b alpha = beval (follow (alpha 0) b) (alpha \o S).
Proof. by case: b. Qed.

(* (Bbeta k n) is an equivalent subtree to (k (alpha n)), constructed
   as a bite branching according to the value of (alpha n), for any alpha *)
Fixpoint Bbeta (k : O -> Brouwer) (n : nat) : Brouwer :=
  match n with
  |0 => bite (fun m => ((follow m) \o k) m)
  |n.+1 => bite (fun m => Bbeta ((follow m) \o k) n)
end.

Lemma BbetaP (alpha : nat -> O) n k : 
  beval (k (alpha n)) alpha = beval (Bbeta k n) alpha.
Proof.
elim: n k alpha => [| n ihn] k alpha /=.
- by rewrite -followP.
- by rewrite -ihn -followP.  
Qed.

(* Conversion from dialogue to Brouwer trees *)
Fixpoint dialogue_to_Btree (d : dialogue) : Brouwer :=
  match d with
  |eta o => spit o
  |beta n k => Bbeta (dialogue_to_Btree \o k) n 
end.

Lemma dialogue_to_BtreeP d alpha :
  deval d alpha = beval (dialogue_to_Btree d) alpha.
Proof.
elim: d alpha => [o | n k ihd] alpha //=.
rewrite -BbetaP; exact: ihd.
Qed.

Lemma dialogue_to_btree_cont (F : (nat -> O) -> A) :
  dialogue_cont F -> btree_contP F.
Proof.
  intros [d Hd].
  exists (dialogue_to_Btree d).
  intros alpha ; rewrite (Hd alpha) ; now apply dialogue_to_BtreeP.
Qed.

End Brouwer.

Section SelfModulation.

(* In this section, we assume queries are nat, and prove that self-modulating moduli 
of standard continuity imply sequential continuity.*)
Variable O A : Type.

Implicit Type (F : (nat -> O) -> A).
Implicit Types (tau : ext_tree nat O A).

  
(* Apparently F continuous for M and M continuous implies there 
   (exist M', auto_modulus F M') (ref?) *)

Definition from_pref (a_dflt : O) (l : seq O) : nat -> O := nth a_dflt l.

(*The function that goes from a modulus to an extensional tree.*)

Definition modulus_to_ext_tree (a_dflt : O) F (M : (nat -> O) -> seq nat) (l : seq O) : result nat A :=
  let g := from_pref a_dflt l in
    if \max_(i <- M g) i < size l
    then output (F g)
    else ask (size l).

Lemma eval_modulus_to_ext a F M f m :  modulus M M ->
  eval_ext_tree_trace (modulus_to_ext_tree a F M) f m = iota 0 (minn m (\max_(i <- M f) i).+1).
Proof.
  move=> MmodM; rewrite /eval_ext_tree_trace.
  suff aux : forall i,
      i <= (\max_(j <- M f) j).+1 ->
      iota 0 i ++ eval_ext_tree_trace_aux (modulus_to_ext_tree a F M) f m (map f (iota 0 i)) =
        iota 0 (minn (i + m) (\max_(j <- M f) j).+1).
  by apply:  (aux 0).
  elim: m=> [|m ihm] i /= hi1.
  by rewrite cats0 addn0; move/minn_idPl: hi1 => ->.
  rewrite /modulus_to_ext_tree size_map size_iota.
  case: ifP=> hi2.
  - have eM : M (from_pref a [seq f i | i <- iota 0 i]) = M f.
    { apply: MmodM.
      apply/eq_in_map=> x hx.
      have hi : x < i by apply: leq_ltn_trans hi2; exact: leq_bigmax_seq.
      by rewrite /from_pref (nth_map 0)  ?size_iota // nth_iota // add0n.
    }
    suff -> : i = (\max_(j <- M f) j).+1.
    have /minn_idPr-> : (\max_(j <- M f) j).+1 <= (\max_(j <- M f) j).+1 + m.+1 by rewrite leq_addr.
    by rewrite cats0.  
    by move: hi1; rewrite -eM leq_eqVlt ltnNge hi2 orbF; move/eqP. 
  - rewrite -/(modulus_to_ext_tree a F M) -cat_rcons.
    have -> : rcons (iota 0 i) i = iota 0 i.+1 by rewrite -cats1 -addn1 iotaD.
    have -> : rcons [seq f i | i <- iota 0 i] (f i) = [seq f i | i <- iota 0 i.+1].
    by rewrite -cats1 -addn1 iotaD map_cat.
    rewrite addnS -addSn; apply: ihm.
    move: hi1; rewrite leq_eqVlt; case/orP=> // /eqP ei.
    suff : \max_(i <- M (from_pref a [seq f i | i <- iota 0 i])) i < i by rewrite hi2.
    suff <- : M f = M (from_pref a [seq f i0 | i0 <- iota 0 i]) by rewrite ei.
    apply: MmodM; apply/eq_in_map=> x hx.
    have hi : x < i by rewrite ei ltnS; apply: leq_bigmax_seq.
    rewrite /from_pref (nth_map 0)  ?size_iota // nth_iota // add0n.
Qed.

Lemma self_modulus_seq_cont F M (a : O) : modulus M M -> modulus F M -> seq_contW F.
Proof.
move=> MmodM MmodF. exists (modulus_to_ext_tree a F M) => f. 
pose m := \max_(i <- M f) i.
exists m.+1.
rewrite eval_ext_tree_map.
have -> := eval_modulus_to_ext a F f m.+1 MmodM.
rewrite /modulus_to_ext_tree size_map size_iota.
have eqM : M f = M (from_pref a [seq f i | i <- iota 0 m.+1]).
  apply: MmodM.
  set l := M _. 
  apply/eq_in_map=> x hx.
  have {hx} hx : x < m.+1 by rewrite ltnS /m; apply: leq_bigmax_seq.
  by rewrite /from_pref (nth_map 0) ?size_iota // nth_iota.
rewrite minnn -eqM leqnn; congr output; apply: MmodF.
apply/eq_in_map=> x hx.
have {hx} hx : x < m.+1 by rewrite ltnS /m eqM; apply: leq_bigmax_seq.
by rewrite /from_pref; rewrite (nth_map 0) ?size_iota // nth_iota // size_iota. 
Qed.

(* TODO : weaken the self modulating hypothesis in the lemma above, using Fujiwara-Kawai's proof 
   from "equivalence of bar induction and bar recursion (...)" that, in part in Coq, we can prove 
   that modulus F M -> modulus M M' -> exists M'', modulus M'' M'' /\ modulus F M'' *)
End SelfModulation.

Section AxiomFreeImplications.

Variable I O A : Type.

Implicit Type (F : (I -> O) -> A).
Implicit Type (tau : ext_tree I O A).

Lemma dialogue_is_dialogue (d : dialogue I O A) : is_dialogue (deval d).
Proof.
  induction d as [ | i k ke] ; cbn.
  - now econstructor.
  - now eapply (tbeta i ke).
Qed.

(* is seems impossible to get rid of the comm cut, hence =1 *)
Lemma is_dialogue_to_dialogue_ext F :
  is_dialogue F -> {d : dialogue I O A & F =1 deval d}.
Proof.
elim=> [o |q k ih1 ih2].
- by exists (eta o).
- exists (beta q (fun a => projT1 (ih2 a))) => f /=.  
  by case: (ih2 (f q)) => /=. 
Qed.


(** From dialogue to extensional trees **)
Fixpoint dialogue_to_ext_tree (d : dialogue I O A) (l : seq O) : result I A :=
 match l, d with
  | _ , eta o => output o
  | [::], beta q _ => ask q
  | a :: l, beta _ k => dialogue_to_ext_tree (k a) l
  end.

(* Dialogue continuity implies any form of sequential continuity *)

Lemma dialogue_to_ext_tree_wf d : wf_ext_tree (dialogue_to_ext_tree d).
Proof.
elim: d => [ o| n k ihd] f.
- by exists 0; exists o.
- have [m [o mP]] := ihd (f 0) (f \o S).
  exists m.+1; exists o. 
  suff -> : [seq f i | i <- iota 0 m.+1] =
                              f 0 :: [seq (f \o succn) i | i <- iota 0 m] by [].
  by rewrite /=; congr (_ :: _); rewrite -[1]/(1 + 0) iotaDl -map_comp.
Qed.

Lemma dialogue_to_ext_tree_valid d : valid_ext_tree (dialogue_to_ext_tree d).
Proof.
elim: d => [ o| n k ihd]; first by case.
case=> [| hd tl] //=; exact: ihd.
Qed.

Lemma dialogue_to_seq_cont  (F : (I -> O) -> A) : dialogue_cont F -> seq_contW F.
Proof.
  case=> d dP; exists (dialogue_to_ext_tree d); rewrite /ext_tree_for.
  elim: d F dP=> [o | q k ihd] F dP f.
  - by rewrite dP; exists 0.
  - have {}/ihd ihd : deval (k (f q)) =1 deval (k (f q)) by move=> ?.
    rewrite dP.
    specialize (ihd f) as [n Hn].
    exists n.+1.
    cbn.
    revert Hn.
    unfold eval_ext_tree.
    generalize (@nil O) as l.
    induction n as [ | n IHn] ; intros * Heq.
    + cbn in *.
      assumption.
    + cbn in *.
      destruct (dialogue_to_ext_tree (k (f q)) l).
      2: assumption.
      eapply IHn.
      assumption.
Qed.


(*Weak sequential continuity is equivalent to Coinductive dialogue continuity*)


(* TODO : move to the definitions section *)
(*We first define a Coinductive without Tau transitions*)
  CoInductive Itree :=
  | ret : A -> Itree
  | vis : I -> (O -> Itree) -> Itree.

  
  (*Then we define the step-indexed evaluation of such a tree.*)
  Fixpoint ieval (i : Itree) (f : I -> O) (n : nat) : result I A :=
    match n with
    | 0 => match i with
           | ret o => output o
           | vis q k => ask q
           end
    | S n => match i with
             | ret o => output o
             | vis q k => ieval (k (f q)) f n
             end
    end.

  (*Continuity with Coinductive dialogue trees*)
  Definition int_tree_for F (τ : Itree) : Type :=
    forall f : I -> O, { n : nat & ieval τ f n = output (F f) }.

(* TODO: rm the final W ? *)
  Definition int_tree_contW F :=
    {τ : Itree & int_tree_for F τ }.

  
  (*From extensional trees to Coinductive dialogue trees.*)
  
  CoFixpoint ext_tree_to_int_tree (e : ext_tree I O A) (l : list O) : Itree :=
    match e l with
    | ask q => vis q (fun a => ext_tree_to_int_tree e (rcons l a))
    | output o => ret o
    end.
  
  
  Lemma seq_contW_int_tree_contW F :
    seq_contW F -> int_tree_contW F.
  Proof.
    intros [e He].
    exists (ext_tree_to_int_tree e nil).
    intros f ; specialize (He f).
    destruct He as [n Heq] ; exists n.
    rewrite <- Heq ; clear Heq.
    revert e.
    unfold eval_ext_tree.
    generalize (@nil O).
    induction n as [ | n IHn] ; intros l e.
    - cbn in *.
      destruct (e l) ; reflexivity.
    - cbn in *.
      destruct  (e l).
      + eapply IHn.
        reflexivity.
  Qed.      

  (*From coinductive dialogue trees to sequential continuity*)
  
  Fixpoint int_tree_to_ext_tree (i : Itree) (l : list O) : result I A :=
    match l with
    | nil => match i with
             | vis q k => ask q
             | ret o => output o
             end
    | cons a l' => match i with
                   | vis q k => int_tree_to_ext_tree (k a) l'
                   | ret o => output o
                   end
    end.
  
  Lemma int_tree_to_ext_tree_one_step : forall n q k f l,
      eval_ext_tree_aux (int_tree_to_ext_tree (vis q k)) f n ((f q) :: l) =
        eval_ext_tree_aux (int_tree_to_ext_tree (k (f q))) f n l.
  Proof.
    intro n.
    induction n as [ | n IHn] ; intros.
    - reflexivity.
    - cbn.
      destruct (int_tree_to_ext_tree (k (f q)) l).
      apply IHn.
      reflexivity.
  Qed.
  
  
  Lemma int_tree_contW_seq_contW F :
    int_tree_contW F -> seq_contW F.
  Proof.
    intros [i Hi].
    exists (int_tree_to_ext_tree i).
    intros f ; specialize (Hi f) as [n Heq].
    exists n.
    rewrite <- Heq ; clear Heq ; revert i.
    induction n as [ | n IHn] ; intro i.
    - cbn in *.
      now destruct i.
    - cbn in *.
      destruct i ; [reflexivity |].
      erewrite int_tree_to_ext_tree_one_step.
      now apply IHn.
  Qed.


(*The trace of evaluation of an extensional tree is a modulus of continuity
 for the evaluation of that extensional tree.*)
Lemma eval_ext_tree_continuous (tau : ext_tree I O A) n l :
  modulus (fun alpha => eval_ext_tree_aux tau alpha n l)
    (fun alpha => eval_ext_tree_trace_aux tau alpha n l).
Proof.
elim: n l => [| n ihn] l alpha beta /= eqab //=.
case: (tau l) eqab => // i /= [<- e].
exact: ihn.
Qed.

Lemma eval_ext_tree_trace_continuous (tau : ext_tree I O A) n l :
  modulus (fun alpha => eval_ext_tree_trace_aux tau alpha n l)
    (fun alpha => eval_ext_tree_trace_aux tau alpha n l).
Proof.
elim: n l => [| n ihn] l alpha beta //= eqab.
case: (tau l) eqab => // i [<- e]; congr (_ :: _).
exact: ihn.
Qed.

(*Continuity via extensional trees implies continuity via moduli*)
Lemma continuous_ext_tree_to_modulus F : seq_contW F -> continuous_via_modulus F.
Proof.
  move=> [] tau F_eq_eval.
  exists (fun alpha => eval_ext_tree_trace_aux tau alpha (projT1 (F_eq_eval alpha)) nil).
  intros alpha beta H.
  eapply (eval_ext_tree_output_unique (I := I)).
  + rewrite - (projT2 (F_eq_eval alpha)) ; unfold eval_ext_tree.
    now rewrite (@eval_ext_tree_continuous tau (projT1 (F_eq_eval alpha)) nil alpha beta H).
  + now eapply (projT2 (F_eq_eval beta)).
Qed.  


(* Weak seq continuity implies modulus continuity (old version) :
Lemma continuous_ext_tree_to_modulus F : seq_contW F -> modulus_continuous F.
Proof.
  move=> [] tau F_eq_eval f.
  case: (F_eq_eval f) => n F_eq_eval_f.
    exists (eval_ext_tree_trace tau f n) => g g_coin.
    have eval_f_g_eq : eval_ext_tree tau g n = eval_ext_tree tau f n.
    { revert tau g_coin F_eq_eval_f F_eq_eval.
      unfold eval_ext_tree_trace ; unfold eval_ext_tree.
      generalize (@nil O).
      induction n as [ | n IHn] ; intros.
      - reflexivity.
      - cbn in *.
        destruct (tau l) ; cbn in *.
        injection g_coin ; clear g_coin ; intros H Heqfg.
        rewrite <- Heqfg.
        eapply IHn ; try assumption.
        reflexivity.
    }
    case: (F_eq_eval g) => m mP.
    rewrite F_eq_eval_f in eval_f_g_eq.
    now destruct (eval_ext_tree_output_unique mP eval_f_g_eq).
Qed.

*)



Fixpoint ext_tree_valid_aux
  (tau : ext_tree I O A) (l l' : list O) : result I A := 
  match l, tau l' with
  |cons a u, ask q => ext_tree_valid_aux tau u (rcons l' a)
  |_, _ => tau l'
  end.

Definition ext_tree_valid
  (tau : ext_tree I O A) (l : list O) : result I A :=
  ext_tree_valid_aux tau l nil.

Lemma ext_tree_valid_valid tau l l' l'' a:
  ext_tree_valid_aux tau l l' = output a ->
  ext_tree_valid_aux tau (l ++ l'') l' = output a.
Proof.
  revert l' l'' ; induction l as [ | u q IHq] ; cbn ; intros * Heq.
  { destruct l'' ; cbn ; [ assumption | now rewrite Heq]. }
  case_eq (tau l') ; intros i Heqi ; rewrite Heqi in Heq ; [ | assumption].
  now apply IHq.
Qed.  

Lemma ext_tree_valid_eqtau_ask
  (tau : ext_tree I O A) (l l' : list O) i o :
  ext_tree_valid_aux tau l l' = ask i ->
  ext_tree_valid_aux tau (rcons l o) l' = tau (rcons (l' ++ l) o).
Proof.
  revert l'.
  induction l as [ | u q IHq].
  { cbn ; intros l' Heq.
    rewrite Heq.
    now rewrite cats0. }
  cbn ; intros l' Heq.
  case_eq (tau l').
  all: intros a eqtau ; rewrite eqtau in Heq.
  2: now inversion Heq.
  rewrite <- cat_rcons.
  now apply IHq.  
Qed.
  
Lemma eval_ext_tree_valid_eqtau
  (tau : ext_tree I O A) (n : nat) (f : I -> O) a :
  eval_ext_tree_aux tau f n nil = output a ->
  eval_ext_tree_aux (ext_tree_valid tau) f n nil = output a.
Proof.
  assert (forall j,
             ext_tree_valid tau (take j nil) = tau (take j nil)) as Hyp.
  { induction j ; cbn ; now reflexivity. }
  revert Hyp.
  generalize (@nil O).
  induction n ; cbn ; intros ; erewrite <- (take_size l) ; erewrite Hyp.
  { now rewrite take_size. }
  rewrite (take_size l).
  case_eq (tau l) ; intros j eqj ; rewrite eqj in H ; [ | assumption]. 
  apply IHn ; [ | assumption ].
  intros k.
  case: (leqP (S (size l)) k).
  { intros inf ; rewrite <- (size_rcons l (f j)) in inf.
    erewrite take_oversize ; [ | assumption].
    unfold ext_tree_valid.
    erewrite ext_tree_valid_eqtau_ask ; [reflexivity |].
    erewrite <- eqj ; erewrite <- take_size at 1 2.
    now apply Hyp. }
  intros sup ; erewrite <- cats1.
  erewrite takel_cat ; [ | now eapply ltnSE].
  now apply Hyp.
Qed.

Lemma seq_cont_valid F :
  seq_contW F ->
  {tau & prod (ext_tree_for F tau) (valid_ext_tree tau)} .
Proof.
  intros [tau Htau].
  exists (ext_tree_valid tau).
  split.
  { intros alpha.
    specialize (Htau alpha) as [n Hn].
    exists n.
    now apply eval_ext_tree_valid_eqtau.
  }
  intros l a Heq o.
  unfold ext_tree_valid in * ; rewrite - cats1.
  now apply ext_tree_valid_valid.
Qed.  
  
    
  

End AxiomFreeImplications.




Section WithFunExt.

Variable funext : forall A B (f g : A -> B), f =1 g -> f = g.

Variable I O A : Type.
(* Variables (cQ cA : countType) (fA : finType). *)
Implicit Type (F : (I -> O) -> A).

Lemma is_dialogue_to_dialogue F : is_dialogue F ->
                                  {d : dialogue I O A & F = deval d}.
Proof.
elim=> [o |q k ih1 ih2].
- by exists (eta o).
- exists (beta q (fun a => projT1 (ih2 a)))=> /=.  
  by apply: funext=> f; case: (ih2 (f q)) => /= d ->.
Defined.

Lemma dialogue_cont_to_is_dialogue F :  dialogue_cont F ->
                                        is_dialogue F.
Proof.
  intros [d Hd].
  apply funext in Hd ; subst.
  now apply dialogue_is_dialogue.
Defined.

End WithFunExt.
 

Section Cantor.

Variable A : Type.
Implicit Type (F : (nat -> bool) -> A).
Implicit Type (d : dialogue nat bool A).
(*From a proof of uniform continuity, we build a dialogue tree*)

(*A way to interpret lists of pairs as functions*)
Fixpoint list_to_cantor (l : list (prod nat bool)) (n : nat) : bool :=
  match l with
  | nil => true
  | (m, b) :: q => match (PeanoNat.Nat.eq_dec) n m with
                   | left e => b
                   | right e => list_to_cantor q n
                   end
  end.
  
(*A dialogue tree built from a list. Crucially, we apply l to the function
 derived using acc and list_to_cantor*)
Fixpoint list_to_dialogue F (l : list nat) (acc : list (prod nat bool)) :=
  match l with
  | nil => eta (F (list_to_cantor acc))
  | cons i q => beta i (fun o => list_to_dialogue F q ((i,o) :: acc))
  end.

(*The trace of an evaluation of a dialogue tree*)
Fixpoint deval_list_to_dialogue_trace  (l : list nat) (f : nat -> bool) (acc: list (prod nat bool)) :
  list (prod nat bool) :=
  match l with
  | nil => acc
  | cons i q =>  deval_list_to_dialogue_trace q f ((i, f i) :: acc)
  end.

Lemma list_to_cantor_swap l acc1 acc2 f a1 a2 n :
  list_to_cantor (deval_list_to_dialogue_trace l f (acc1 ++ ((a1, f a1) :: ((a2, f a2) :: acc2)))) n =
    list_to_cantor (deval_list_to_dialogue_trace l f (acc1 ++ ((a2, f a2) :: ((a1, f a1) :: acc2)))) n.
Proof.
  revert acc1 acc2 a1 a2 n f ; induction l ; intros ; cbn.
  { induction acc1 ; cbn.
    { destruct (PeanoNat.Nat.eq_dec n a1) as [e |] ; [ | reflexivity].
      rewrite e.
      destruct (PeanoNat.Nat.eq_dec a1 a2) as [e' | ne'] ; [now rewrite e' | reflexivity].
    }
    now rewrite IHacc1.
  }
  erewrite <- cat_cons.
  exact (IHl ((a, f a) :: acc1) acc2 a1 a2 n f).
Qed.  

(*f is equal on l to the function derived from the trace of execution of the dialogue tree built
 using l.*)
Lemma list_to_dialogue_deval_eq (l : list nat) (f : nat -> bool) (acc: list (prod nat bool)) :
  map f l = map (list_to_cantor (deval_list_to_dialogue_trace l f acc)) l.
Proof.
  revert acc.
  induction l ; intros ; [reflexivity |].
  cbn.
  f_equal.
  { clear IHl ; revert acc ; induction l ; cbn ; intros.
    { destruct (PeanoNat.Nat.eq_dec a a) ; [reflexivity |].
      exfalso ; exact (n Logic.eq_refl).
    }
    rewrite (list_to_cantor_swap l nil acc f a0 a a) ; cbn in *.
    now eapply IHl.
  }
  eapply IHl.
Qed.    

(*dialogue trees are continuous*)
Lemma list_to_dialogue_eq : forall F l acc f g,
      map f l = map g l ->
      deval (list_to_dialogue F l acc) f = deval (list_to_dialogue F l acc) g.
Proof.
  intros F l ; induction l ; intros * Heqfg ; [reflexivity |].
  cbn in *.
  injection Heqfg ; intros Heqfgl Heqfga ; clear Heqfg ; rewrite Heqfga.
  now eapply IHl.
Qed.  
        

(*The desired result.*)
Lemma uniform_is_dialogue F : uniform_continuous F -> dialogue_cont F.
Proof.
  intros [l H].
  exists (list_to_dialogue F l nil).
  intros f.
  unshelve erewrite list_to_dialogue_eq.
  3: unshelve eapply list_to_dialogue_deval_eq.
  2: exact nil.
  specialize (H f (list_to_cantor (deval_list_to_dialogue_trace l f nil)) (list_to_dialogue_deval_eq _ _ _)).
  rewrite H ; clear H.
  generalize (@nil (prod nat bool)).
  induction l ; intros acc ; [reflexivity |].
  cbn.
  erewrite IHl. 
  do 4 f_equal.
  clear.
  revert acc; induction l ; intros ; cbn.
  { destruct (PeanoNat.Nat.eq_dec a a) as [e | ne] ; [reflexivity |].
    exfalso ; exact (ne Logic.eq_refl).
  }
  rewrite (list_to_cantor_swap l nil acc f a0 a a).
  eapply IHl.
Qed.

(*We now go the other way around.*)

Fixpoint dialogue_to_list d : list nat :=
  match d with
  | eta a => nil
  | beta i k => i :: (dialogue_to_list (k true)) ++ (dialogue_to_list (k false))
  end.

Lemma dialogue_is_uniform F : dialogue_cont F -> uniform_continuous F.
Proof.
  intros [d H].
  exists (dialogue_to_list d) ; intros f g Hfg.
  do 2 erewrite H.
  clear H F.
  induction d as [ | i k ke] ; [reflexivity |] ; cbn in *.
  injection Hfg ; intros Hfgl Hfgi ; clear Hfg ; rewrite Hfgi.
  specialize (ke (g i)).
  destruct (g i).
  { apply ke.
    do 2 erewrite map_cat in Hfgl.
    apply (f_equal (take (size [seq f i | i <- dialogue_to_list (k true)]))) in Hfgl.
    do 2 erewrite take_size_cat in Hfgl ; try reflexivity.
    exact Hfgl.
    now do 2 erewrite size_map.
  }
  { apply ke.
    do 2 erewrite map_cat in Hfgl.
    apply (f_equal (drop (size [seq f i | i <- dialogue_to_list (k true)]))) in Hfgl.
    do 2 erewrite drop_size_cat in Hfgl ; try reflexivity.
    exact Hfgl.
    now do 2 erewrite size_map.
  }
Qed.

(* TODO : following Andrej's comments, say something about compactness, this could be generalized to 
   more compacts*)

End Cantor.

Module generalised.

Require Import List.
Import ListNotations.

Inductive Forall (A : Type) (P : A -> Type) : seq.seq A -> Type :=
    Forall_nil : Forall P [] | Forall_cons : forall (x : A) (l : seq.seq A), P x -> Forall P l -> Forall P (x :: l).

Definition barred {A B} T :=
  forall α : A -> B, { u : list (A * B) & (Forall (fun '(a,b) => α a = b) u * T u)%type }.

Inductive indbarred {A B} T : list (A * B) -> Type :=
| ieta u' u : T u' -> indbarred T (u' ++ u)
| ibeta a v : ~ In a (map fst v) ->
              (forall b, indbarred T (v ++ [(a,b)])) ->
              indbarred T v.

Lemma indbarred_lem {A B} {b0 : B} T l :
  @indbarred A B T l ->
  ({ u' & { u & { a & {b & ((l = u' ++ u ++ [(a,b)])%SEQ * T u')%type}}}} + { u & T (l ++ u)%SEQ }).
Proof.
  induction 1.
  - destruct u using last_ind.
    + right. exists []. now rewrite !cats0.
    + clear IHu. left. destruct x. exists u'. exists u. exists a, b. split; eauto.
      rewrite <- cat_rcons. now rewrite cats0.
  - destruct v.
    + cbn in *.
      destruct (X b0) as [(? & ? & ? & ? & ? & ?) | (? & ?) ].
      eauto. eauto. 
    + destruct p as [a' b].
      cbn in *. 
      destruct (X b) as [(? & ? & ? & ? & ? & ?) | (? & ?) ].
      * rewrite <- !cat_rcons in e. rewrite !cats0 in e.
        rewrite <- !rcons_cat in e.
        rewrite <- !rcons_cons in e.
        eapply rcons_inj in e. inversion e. subst.
        destruct x0 using last_ind.
        { right.
          exists nil.
          now rewrite cats0 H0 cats0.
        }
        left.

        inversion e.
        exists x.
        exists x0.
        destruct x3 as [a b].
        exists a ; exists b.
        rewrite - cats1 in H1.
        now split.
      * right. eexists ((a, b) :: x). rewrite <- app_assoc in t.
        cbn in *. eassumption.
Qed.

Definition GBI {A B} T :=
  inhabited (forall l, (T l) + (T l -> False)) ->
  @barred A B T -> indbarred T [].

Require Import Lia.

Lemma rev_list_rect {A} : forall P:list A-> Type,
    P [] ->
    (forall (a:A) (l:list A), P (rev l) -> P (rev (a :: l))) ->
    forall l:list A, P (rev l).
Proof.
  intros P ? ? l; induction l; auto.
Qed.

Theorem rev_rect {A} : forall P:list A -> Type,
    P [] ->
    (forall (x:A) (l:list A), P l -> P (l ++ [x])) -> forall l:list A, P l.
Proof.
  intros P ? ? l. rewrite <- (rev_involutive l).
  apply (@rev_list_rect A P); cbn; auto.
Qed.

Theorem GBI_to {I O A} F {i0 : I} :
  (forall T, @GBI I O T) ->
  seq_contW F ->
  @dialogue_cont I O A F.
Proof.
  intros gbi [τ Hτ]. red in Hτ.
  pose (T := fun v => let qs := [seq i.1 | i <- v] in
                   let ans := [seq i.2 | i <- v] in
                   forall n, PeanoNat.Nat.lt n (length v) ->
                             τ (take n ans) = ask (seq.nth i0 qs n) \/
                              exists o : A, τ (take n ans) = output o
        ).
  unshelve epose proof (gbi (fun v => {o | τ [seq i.2 | i <- v] = output o
                                        /\ T v
                          }) _ _) as Barred.
  - constructor. intros l. clear. induction l using rev_rect.
    + destruct τ.
      * right. firstorder congruence.
      * left. exists a. split; try red; intros; cbn in *. eauto. lia.
    + destruct IHl as [(? & ? & ?) | ?].
      * left. exists x0. split. admit.
        red; intros. rewrite app_length in H1; cbn in H1.
        assert (PeanoNat.Nat.lt n (length l) \/ n = (length l)) as [Hn | Hn] by lia.
        -- left. 
           rewrite <- map_take. rewrite take_size_cat.
           admit.
        -- admit.
      * admit.
      * admit.
  - intros α. destruct (Hτ α) as (n & Hn). exists (seq.map (fun i => (i, α i)) (eval_ext_tree_trace τ α n)).
    split.
    + clear. induction (eval_ext_tree_trace τ α n); cbn; econstructor; eauto.
    + exists (F α). 
      rewrite <- map_comp. 
      cbn. 
      rewrite <- Hn. split. symmetry.
      rewrite eval_ext_tree_map. reflexivity. admit.
  - red.
    revert Hτ.
    revert Barred. unfold eval_ext_tree.
    assert (T []).
    { red. cbn. intros. lia. }
    revert H.
    change (@nil O) with (seq.map snd (@nil (I * O))).
    generalize (@nil (I * O)).
    intros. unshelve eexists.
    clear Hτ H.
    { induction Barred.
      + destruct t as [o _]. apply (eta o).
      + apply beta. exact a. exact X. }
    intros f. specialize (Hτ f).
    have Hvalid: valid_ext_tree τ by admit.
    induction Barred; cbn; intros.
    + destruct t. cbn in *. admit.
    + pose proof (i (f a)) as i'.
      unshelve eapply indbarred_lem in i'.
      exact (f i0).
      eapply H0.
      * cbn.
        destruct i' as [[l [l' [x [y [Heqvl [o [Heqtau Hyp]]]]]]] | [l [o [Heqtau Hyp]]]].
        { assert (x = a /\ y = f a /\ v = l ++ l') as [H1 [H2 H3]] by admit.
          subst.
          unfold T ; unfold T in Hyp ; cbn.
          intros m Hm.
          assert (PeanoNat.Nat.lt m (size l) \/ PeanoNat.Nat.le (size l) m) as Hl by lia.
          repeat erewrite map_app.
          destruct Hl as [Hl | Hl].
          { assert (m < size l) as mlt by admit.
            specialize (Hyp _ Hl).
            erewrite takel_cat.
            2:{ erewrite size_cat.
                erewrite size_map.
                admit.
            }
            erewrite takel_cat.
            2:{ erewrite size_map.
                admit.
            }
            cbn.
            erewrite <- catA.
            erewrite cats1.
            erewrite (@nth_cat _ i0 (map [eta fst] l) (rcons (map [eta fst] l') a) m).
            rewrite size_map.
            rewrite mlt.
            assumption.
          }
          clear Hyp.
          right.
          exists o.
          erewrite <- catA.
          erewrite take_cat.
          assert (m < size (map [eta snd] l) = false) as H1 by admit.
          rewrite H1 ; clear H1.
          now eapply valid_cat.
        }
        unfold T ; unfold T in Hyp ; intros m Hltm.
        assert (PeanoNat.Nat.lt m (length ((v ++ [(a, f a)]) ++ l))) as Hltm'.
        { erewrite size_cat.
          now eapply PeanoNat.Nat.lt_lt_add_r.
        }
        specialize (Hyp m Hltm') ; clear Hltm'.
        assert (m <= (length (v ++ [(a, f a)]))) as Hlem by admit.
        repeat erewrite map_cat in Hyp.
        erewrite takel_cat in Hyp.
        2:{ erewrite size_cat, size_map, size_map.
            now erewrite size_cat in Hlem.
        }
        erewrite nth_cat in Hyp.
        assert (m < size ([seq i.1 | i <- v] ++ [seq i.1 | i <- [(a, f a)]])) as H' by admit.
        rewrite H' in Hyp ; clear H'.
        repeat erewrite map_cat.
        assumption.
      * destruct Hτ as [m Hm]. rewrite <- Hm. exists m.
        destruct i' as [[l [l' [x [y [Heqvl [o [Heqtau Hyp]]]]]]] | [l [o [Heqtau Hyp]]]].
        -- assert (x = a /\ y = f a /\ v = l ++ l') as [H1 [H2 H3]] by admit.
           subst.
           repeat erewrite map_app.
           set (t1 := eval_ext_tree_aux _ _ _ _).
           set (t2 := eval_ext_tree_aux _ _ _ _).
           have eq1: t1 = output o.
           { rewrite {}/t1.
             eapply eval_ext_tree_constant.
             erewrite valid_cat ; try eassumption.
             reflexivity.
             erewrite valid_cat ; try eassumption ; reflexivity.
           }
           have eq2: t2 = output o.
           { rewrite {}/t2.
             eapply eval_ext_tree_constant.
             erewrite valid_cat ; try eassumption.
             reflexivity.
           }
           now rewrite eq1 eq2.
        -- unfold T in Hyp ; cbn in Hyp.
           have Hlt: PeanoNat.Nat.lt (size (map snd v)) (length ((v ++ [(a, f a)]) ++ l))
             by admit.
           specialize (Hyp (size (map snd v)) Hlt) ; clear Hlt.
           assert (Haux := take_size_cat (n := size (map [eta snd] v)) (s1:= (map [eta snd] v))).
           repeat erewrite map_app in Hyp.
           erewrite <- catA in Hyp.
           erewrite Haux in Hyp by reflexivity ; clear Haux.
           destruct Hyp as [Hyp | [o' Hyp]].
           { assert ((seq.nth i0 ((map [eta fst] v ++ [a]) ++ map [eta fst] l) 
                        (size (map snd v))) = a)
               as eqa by admit.
             cbn in Hyp.
             rewrite eqa in Hyp ; clear eqa.
             destruct m.
             { cbn in *.
               rewrite Hyp in Hm.
               now inversion Hm.
             }
             rewrite Hm.
             erewrite <- PeanoNat.Nat.add_1_r.
             eapply eval_ext_tree_monotone.
             cbn in Hm.
             rewrite Hyp in Hm.
             erewrite map_app.
             change (map snd [(a, f a)]) with ([f a]).
             erewrite cats1.
             exact Hm.
           }
           erewrite eval_ext_tree_constant.
           { erewrite eval_ext_tree_constant ; [reflexivity | eassumption]. }
           erewrite map_app.
           now eapply valid_cat.
Admitted.

Set Bullet Behavior "Strict Subproofs".

Theorem to_BI {O A} :
  forall inj : list O -> A,
  (forall F, seq_contW F ->
        @btree_contP O A F) -> forall T, (forall l, (T l) + (T l -> False)) -> @BI_ind O T.
Proof.
  intros inj ci T T_dec Hbar.
  epose (τ l := match T_dec l with
                | inl _ => output (inj l)
                | inr _ => ask (length l)
                end).
Admitted.

End generalised.


Section ContinuousInduction.

  Variable O : Type.
  Notation I := nat.
  Notation A := (seq O).
  Implicit Type (F : (I -> O) -> A).

Variable CI : forall F, seq_contW F -> dialogue_cont F.

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
  seq_contW (@ext_tree_to_fun tau H).
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

Section GBI_BI.
  Variables A B : Type.
Implicit Type (T : seq (nat * B) -> Type).


Fixpoint ord_aux {C} (u : list C) (n : nat) : list (nat * C) :=
  match u with
  | nil => nil
  | a :: q => (n, a) :: (ord_aux q (S n))
  end.

Definition ord {C} u := ord_aux (C := C) u 0.

Lemma ord_map_snd {C} n (u : list C) : map snd (ord_aux u n) = u.
Proof.
  revert n ; induction u as [ | c q IHq] ; intros n ; [reflexivity |].
  cbn ; f_equal.
  now apply IHq.
Qed.


Lemma ord_inj {C} n (u u' : list C) : ord_aux u n = ord_aux u' n -> u = u'.
Proof.
  revert n u'.
  induction u ; intros n u' Heq.
  { induction u' ; [reflexivity | cbn in * ; now inversion Heq]. }
  destruct u' ; [now inversion Heq |].
  cbn in * ; inversion Heq ; subst.
  f_equal.
  eapply IHu ; eassumption.
Qed.

Lemma ord_cat {C} n (u u' : list C) : ord_aux (u ++ u') n = ord_aux u n ++ (ord_aux u' (size u + n)).
Proof.
  revert n ; induction u ; intros ; cbn ;  [reflexivity |].
  f_equal.
  erewrite plus_n_Sm.
  exact (IHu n.+1).
Qed.

Lemma ord_take {C} n m (u : list C) : ord_aux (take n u) m = take n (ord_aux u m).
Proof.
  revert n m ; induction u ; intros ; cbn ; [reflexivity |].
  destruct n ; [reflexivity |] ; cbn.
  f_equal.
  now apply IHu.
Qed.


Lemma ord_drop {C} n m (u : list C) : ord_aux (drop n u) (n + m) = drop n (ord_aux u m).
Proof.
  revert n m ; induction u ; intros ; cbn ; [reflexivity |].
  destruct n ; [reflexivity |] ; cbn.
  erewrite plus_n_Sm.
  now apply IHu.
Qed.


Lemma ord_size {C} n (u : list C) : size (ord_aux u n) = size u.
Proof.
  revert n ; induction u ; intro n ; [reflexivity |].
  cbn.
  f_equal ; now apply IHu.
Qed.

Lemma ord_rcons {C} n (u : list C) a : ord_aux (rcons u a) n = rcons (ord_aux u n) (size u + n, a).
Proof.
  revert n ; induction u ; intros ; cbn ; [reflexivity |].
  f_equal.
  now erewrite IHu, plus_n_Sm.
Qed.

Lemma ord_nth {C} b (u : list C) n m : (n + m, nth b u m) = nth (n + m, b) (ord_aux u n) m.
Proof.
  revert n m ; induction u ; intros.
  { now do 2 rewrite nth_nil. }
  cbn.
  destruct m.
  { cbn ; now rewrite <- plus_n_O. }
  cbn.
  rewrite <- plus_n_Sm, <- plus_Sn_m.
  now apply (IHu n.+1 m).
Qed.  


Lemma ord_in {C} n m (u : list C) a : List.In (m, a) (ord_aux u n) -> List.In a u.
Proof.
  revert a n m ; induction u ; intros * Hyp ; cbn in * ; [assumption |].
  destruct Hyp as [Heq | Hin].
  { left.
    now inversion Heq.
  }
  right.
  eapply IHu.
  eassumption.
Qed.

Lemma ord_nth_in {C} n m b (u : list C) :
  n < size u ->
  List.In (nth (n + m, b) (ord_aux u m) n) (ord_aux u m).
Proof.
  revert n m b ; induction u ; intros n m b Hyp ; [now inversion Hyp |].
  cbn.
  destruct n.
  { cbn in * ; now left. }
  right ; cbn in *.
  rewrite plus_n_Sm.
  now apply IHu.
Qed.

Lemma ord_incl {C} n m (u u' : list C) : List.incl (ord_aux u n) (ord_aux u' m) -> List.incl u u'.
Proof.
  revert n m u' ; induction u ; intros ; cbn.
  { now eapply List.incl_nil_l. }
  cbn in *.
  apply List.incl_cons_inv in H as [H1 H2].
  apply IHu in H2.
  apply List.incl_cons ; [ | eassumption].
  eapply ord_in.
  eassumption.
Qed.

Lemma ord_notin {C} i j c (u : list C) :
  i < j -> List.In (i, c) (ord_aux u j) -> False.
Proof.
  revert i j ; induction u ; intros * Hinf Hyp ; [now auto |].
  destruct Hyp as [Heq | Hin].
  2: { eapply IHu ; [ | eassumption] ; now apply leqW. }
  inversion Heq ; subst.
  rewrite ltnn in Hinf ; now inversion Hinf.
Qed.    

Lemma ord_sizeu_notin :
  forall (l : seq B) n,  ~ List.In (n + size l) [seq i.1 | i <- ord_aux l n].
Proof.
  induction l ; intros ; cbn ; [easy |].
  intros H.
  destruct H.
  { clear -H ; induction n ; cbn in * ; [now inversion H | now injection H]. }
  specialize (IHl (n.+1)) ; cbn in *.
  erewrite <- plus_n_Sm in H ; now apply IHl.
Qed.


Lemma ord_in_2 {C} n m (u : list C) a :
  List.In (m + n, a) (ord_aux u n) ->
  a = nth a u m.
Proof.
  revert n m ; induction u ; cbn ; [now auto |].
  intros n m [Heq | Hin].
  { inversion Heq ; subst.
    suff: m = 0 by (intros H ; subst ;  reflexivity).
    apply (f_equal (subn^~ n)) in H0.
    now rewrite -> addnK, subnn in H0.
  }
  case: (leqP m 0) ; intros Hm.
  { exfalso.
    eapply (@ord_notin _ n n.+1 a u) ; [now apply ltnSn |].
    suff: m = 0 by (intros Heq ; rewrite Heq in Hin; cbn in * ; assumption).
    rewrite leqn0 in Hm ; eapply elimT ; [ now apply eqP | exact Hm].
  }
  eapply prednK in Hm.
  rewrite <- Hm, plus_Sn_m, plus_n_Sm in Hin.
  apply IHu in Hin.
  now change (a = nth a (a0 :: u) (m.-1.+1)) in Hin ; rewrite Hm in Hin.
Qed.
  

Lemma ord_NoDup {C} n (u : list C) : List.NoDup (ord_aux u n).
Proof.
  revert n ; induction u ; intros ; [econstructor |].
  cbn ; econstructor 2 ; [ | now eapply IHu].
  intros Hyp ; eapply (ord_notin (i := n) (j := n.+1)) ; [ | eassumption].
  now apply ltnSn.
Qed.


Lemma ord_incl' {C} n (u u' : list C) :
  List.incl (ord_aux u n) (ord_aux u' n) -> ord_aux u n = take (size u) (ord_aux u' n).
Proof.
  revert n u' ; induction u ; intros ; cbn.
  { now rewrite take0. }
  assert (Hainu := (H (n,a) (or_introl (erefl)))).
  assert (Heqa := @ord_in_2 _ n 0 u' a Hainu).
  destruct u' ; [now inversion Hainu | cbn in * ; subst].
  f_equal.
  apply IHu ; clear Hainu IHu.
  intros [m c'] Hin.
  destruct (H (m, c') (or_intror Hin)) as [Heq | HIn] ; [ | assumption].
  exfalso.
  destruct ((List.NoDup_cons_iff (n, c) (ord_aux u n.+1)).1 (ord_NoDup n (c::u))) as [Hnotin Hdup].
  inversion Heq ; subst ; now apply Hnotin.
Qed.


Lemma ord_inf_size_aux u n m :
  n <= m ->
  m < (size u + n) ->
  {b : B & List.In (m, b) (ord_aux u n)}.
Proof.
  revert n m ; induction u ; intros n m Hn Hm.
  have aux : n < n by (eapply leq_ltn_trans ; [eassumption | exact Hm]).
  rewrite ltnn in aux ; now inversion aux.
  cbn.
  case: (leqP m n).
  { intros Hmn.
    exists a ; left.
    suff: m = n by (intros Heq ; subst).
    have Hyp: (m == n) by (erewrite eqn_leq, Hn, Hmn).
    clear - Hyp.
    revert m Hyp ; induction n ; intros.
    { induction m ; cbn in * ; [reflexivity | now inversion Hyp]. }
    destruct m ; [now inversion Hyp |] ; cbn in *.
    now rewrite (IHn m Hyp).
  }
  clear Hn ; intros Hn.
  edestruct (IHu n.+1 m Hn) as [b Hb].
  2:{ exists b ; now right. }
  change (m < (size u + n).+1 = true) in Hm.
  now erewrite <- plus_n_Sm.
Qed.

Lemma ord_inf_size u n :
  n < size u ->
  {b : B & List.In (n, b) (ord u) }.
Proof.
  unfold ord ; intros Hn.
  eapply ord_inf_size_aux ; [easy |].
  now erewrite <- plus_n_O.
Qed.

Lemma ord_map_aux u n (alpha : nat -> B) : ord_aux [seq alpha i | i <- u] n =
                                [seq (i.1, alpha i.2) | i <- ord_aux u n ].
Proof.
  revert n alpha ; induction u ; [ reflexivity |] ; intros.
  cbn.
  f_equal.
  now eapply IHu.
Qed.

Lemma ord_iota_aux i j : ord_aux (iota i j) i =
                             [seq (i, i) | i <- iota i j].
Proof.
  revert i ; induction j ; [reflexivity |] ; intros.
  cbn ; f_equal.
  now eapply IHj.
Qed.

(*Some technical lemmas*)

Lemma in_map {X Y} (u : seq X) (f : X -> Y) a :
  List.In a u -> List.In (f a) (map f u).
Proof.
  revert a ; induction u ; cbn ; [auto |].
  intros x Hax.
  destruct Hax as [Heq | Hin].
  { left ; now subst. }
  right.
  now eapply IHu.
Qed.


Lemma map_incl {X Y} (u u' : seq X) (f : X -> Y) :
  List.incl u u' -> List.incl (map f u) (map f u').
Proof.
  revert u' ; induction u ; intros u' H.
  { now eapply List.incl_nil_l. }
  intros y Hy.
  cbn in * ; destruct Hy as [Heq | Hin].
  { rewrite - Heq ; eapply in_map.
    eapply H ; cbn.
    now left.
  }
  eapply IHu ; [ | assumption].
  now destruct (List.incl_cons_inv H).
Qed.

Lemma in_iota i j k : i <= j  -> j < (i + k) -> List.In j (iota i k).
Proof.
  revert i j ; induction k ; intros i j Hij Hjik.
  { exfalso.
    erewrite <- plus_n_O, leq_gtF in Hjik ; [now inversion Hjik | assumption].
  }
  case: (leqP i.+1 j) ; intros Hyp ; [right | left].
  { eapply IHk ; [ assumption | now rewrite -> plus_Sn_m, plus_n_Sm]. }
  eapply elimT ; [now eapply eqP |].
  eapply ltnSE in Hyp ; now rewrite -> eqn_leq, Hij, Hyp.
Qed.

Lemma incl_iota_max u : List.incl u (iota 0 (List.list_max u).+1).
Proof.
  intros n Hin.
  apply in_iota ; [now apply leq0n|].
  change (0 + (List.list_max u).+1) with (List.list_max u).+1.
  rewrite ltnS.
  eapply introT ; [ now eapply leP | ].
  eapply ((List.Forall_forall) (fun x => le x (List.list_max u))) ; [ | eassumption].
  now apply (List.list_max_le u (List.list_max u)).1.
Qed.

Definition is_tree (P : list B -> Type) :=
  forall u n, P u -> P (take n u).

Definition Downarborification (P : list B -> Type) (u : list B) : Type :=
  forall n, P (take n u).

CoInductive pruning (P : list B -> Type) : list B -> Type :=
  prune a u : P u -> pruning P (rcons u a) -> pruning P u.

Definition choicefun (P : list B -> Type) :=
  {alpha : nat -> B & forall n : nat, P [seq (alpha i) | i <- iota 0 n] }.

Definition DC := forall (P : list B -> Type), pruning P nil -> choicefun P.

Definition ABis_tree T :=
  forall u v, List.incl v u -> T u -> T v.

Inductive ABUparborification T : list (nat * B) -> Type :=
| Tarbor l l' : T l -> List.incl l' l -> ABUparborification T l'.

Definition DownABarborification T u : Type :=
  forall v, List.incl v u -> T v.


Definition ABchoicefun T :=
  {alpha : nat -> B & forall u : list nat, T [seq (i, alpha i) | i <- u]}.

CoInductive ABapprox T : list (prod nat B) -> Type :=
  approx u : DownABarborification T u ->
             (forall n : nat, ~ List.In n (map fst u) ->
                              {b : B & ABapprox T (rcons u (n, b))}) ->
             ABapprox T u.

Definition GDC := forall T,  ABapprox T nil -> ABchoicefun T.

Definition monotone {C} (P : list C -> Type) :=
  forall l l', P l -> P (l ++ l').

Inductive Upmonotonisation {C} (T : list C -> Type) : list C -> Type :=
| mon l l' : T l -> Upmonotonisation T (l ++ l').

Definition Downmonotonisation {C} (T : list C -> Type) : list C -> Type :=
  fun u => forall v, T (u ++ v).

(* A more handy version for concrete formal proofs *)
Definition ABbarred T :=
  forall α : nat -> B, {u : list nat & T [seq (i, α i) | i <- u]}.

Inductive indbarred T : list (nat * B) -> Type :=
  | ieta u' u : T u -> List.incl u u' -> indbarred T u'
  | ibeta a v : ~ List.In a (map fst v) ->
              (forall b, indbarred T (v ++ [:: (a,b)])) -> indbarred T v.

Inductive indbarred_spec T :  list (nat * B) -> Type := 
 |Eta : forall u l, T (l ++ u) -> indbarred_spec T l
 |Beta : forall u' u a b, T u' -> indbarred_spec T (rcons (u' ++ u) (a, b)).

Arguments Eta {T} u l.

Definition ABmonotone {C} (P : list C -> Type) :=
  forall l l', List.incl l l' -> P l -> P l'.

Inductive ABUpmonotonisation {C} (T : list C -> Type) : list C -> Type :=
| Tmon l l' : T l -> List.incl l l' -> ABUpmonotonisation T l'.

Definition ABDownmonotonisation {C} (T : list C -> Type) : list C -> Type :=
  fun u => forall v, List.incl u v -> T v.

Lemma Upmonot_monotone {C} P : @monotone C (Upmonotonisation P).
Proof.
  intros _ w [u v Hu].
  destruct (Monoid_isLaw__to__SemiGroup_isLaw C) as [opA].
  erewrite <- opA.
  now econstructor.
Qed.


Lemma monot_barred {C} (P : list C -> Type) : barred P -> barred (Upmonotonisation P).
Proof.
  intros H alpha ; specialize (H alpha).
  destruct H as [l [Hpref HP]].
  exists l ; split ; [assumption |].
  now erewrite <- cats0 ; econstructor.
Qed.  

  
Lemma ABUpmonot_monotone {C} P : @ABmonotone C (ABUpmonotonisation P).
Proof.
  intros l l' Hll' Hyp.
  inversion Hyp ; subst.
  econstructor.
  2: eapply List.incl_tran ; eassumption.
  assumption.
Qed.

Lemma ABDownmonot_monotone {C} P : @ABmonotone C (ABDownmonotonisation P).
Proof.
  unfold ABDownmonotonisation ; intros u v Huv Hyp w Hvw.
  eapply Hyp, List.incl_tran ; now eassumption.
Qed.

(* Generalized Bar Induction, phrased using the Herbelin-Brede way *)
Definition GBI T := ABbarred T -> indbarred T [::].

Lemma ABmonot_barred T : ABbarred T -> ABbarred (ABUpmonotonisation T).
Proof.
  intros H alpha. specialize (H alpha).
  destruct H as [l Hpref].
  exists l.
  econstructor ; [ eassumption |].
  now apply List.incl_refl.
Qed.  



Definition TtoP (T : list (nat * B) -> Type) (l : list B) : Type :=
  T (ord l).

Inductive PtoT (P : list B -> Type) : list (nat * B) -> Type :=
| ptot : forall l, P l -> PtoT P (ord l).

Definition PtoT_dual (P : list B -> Type) : list (nat * B) -> Type :=
  fun u => forall v, u = ord v -> P v.


Definition TtoP_PtoT_ret P : forall l, P l -> TtoP (PtoT P) l :=
  fun l Hl => ptot Hl.

Lemma TtoP_PtoT_inv P : forall l, TtoP (PtoT P) l -> P l.
Proof.
  intros u H.
  inversion H.
  now eapply ord_inj in H1 ; subst.
Qed.  


Lemma PtoT_TtoP_inv (T : list (nat * B) -> Type) l :
  PtoT (TtoP T) l -> T l. 
Proof.
  unfold TtoP ; intros H.
  inversion H ; now subst.
Qed.

Lemma PtoT_TtoP_ret (T : list (nat * B) -> Type) u :
  T (ord u) -> PtoT (TtoP T) (ord u). 
Proof.
  intro H ; econstructor.
  unfold TtoP ; assumption.
Qed.

Definition DCProp11 :=
  forall P u, P u -> TtoP (ABUparborification (PtoT P)) u.

Definition BIProp11Down :=
  forall P u, monotone P -> P u -> TtoP (ABDownmonotonisation (PtoT_dual P)) u.

Definition DCProp11_rev :=
  forall P u, is_tree P -> TtoP (ABUparborification (PtoT P)) u -> P u.

Definition BIProp11Down_rev :=
  forall P u, TtoP (ABDownmonotonisation (PtoT_dual P)) u -> P u.

Definition DCProp12 :=
  forall T u, ABis_tree T -> ABapprox T (ord u) -> pruning (TtoP T) u.

Definition BIProp12 :=
  forall T u, ABmonotone T -> indbarred T (ord u) -> hereditary_closure (TtoP T) u.

Definition DCProp12_rev :=
  forall T u, ABis_tree T -> pruning (TtoP T) u -> ABapprox T (ord u).

Definition BIProp12_rev :=
  forall T u, hereditary_closure (TtoP T) u -> indbarred T (ord u).

Definition DCProp12_sym :=
  forall P u, pruning P u -> ABapprox (ABUparborification (PtoT P)) (ord u).

Definition BIProp12Down :=
  forall P u, indbarred (ABDownmonotonisation (PtoT_dual P)) (ord u) ->
  hereditary_closure P u.

Definition BIProp12Down_rev :=
  forall P u, monotone P -> hereditary_closure P u ->
              indbarred (ABDownmonotonisation (PtoT_dual P)) (ord u).

Definition DCProp13 :=
  forall T, ABchoicefun T -> choicefun (TtoP T).

Definition BIProp13 :=
  forall T, ABmonotone T -> ABbarred T -> barred (TtoP T).

Definition DCProp13_rev :=
  forall T, ABis_tree T -> choicefun (TtoP T) -> ABchoicefun T.

Definition BIProp13_rev :=
  forall T, barred (TtoP T) -> ABbarred T.

Definition DCProp13_Up :=
  forall P, is_tree P -> ABchoicefun (ABUparborification (PtoT P)) -> choicefun P.

Definition BIProp13Down :=
  forall P, ABbarred (ABDownmonotonisation (PtoT_dual P)) -> barred P.

Definition BIProp13Down_rev :=
  forall P, monotone P -> barred P -> ABbarred (ABDownmonotonisation (PtoT_dual P)).

(*These lemmas with Upmonotonisation are true, even though they are not the duals of
 propositions about DC and GDC.*)
Definition BIProp11Up :=
  forall P l, P l -> TtoP (ABUpmonotonisation (PtoT P)) l.

Definition BIProp11Up_rev :=
  forall P l, monotone P -> TtoP (ABUpmonotonisation (PtoT P)) l -> P l.

Definition BIProp12Up :=
  forall P u, monotone P -> indbarred (ABUpmonotonisation (PtoT P)) (ord u) ->
              hereditary_closure P u.

Definition BIProp12Up_rev :=
  forall P u, hereditary_closure P u ->
              indbarred (ABUpmonotonisation (PtoT P)) (ord u).

(*The next two Lemmas are Proposition 11 in Brede-Herbelin's Paper*)

Lemma P_ABUp_PtoTB : BIProp11Up.
Proof.
  intros P l Hl.
  unfold TtoP.
  econstructor ; [econstructor ; eassumption |].
  now apply List.incl_refl.
Qed.

Lemma P_ABDown_PtoT : BIProp11Down.
Proof.
  intros P l HP Hl v Hincl ; unfold TtoP ; intros w Heq.
  subst.
  apply ord_incl' in Hincl ; erewrite <- ord_take in Hincl.
  eapply ord_inj in Hincl ; rewrite Hincl in Hl.
  erewrite <- cat_take_drop ; eapply HP.
  eassumption.
Qed.

Lemma monotone_ABUp_PtoT_P : BIProp11Up_rev. 
Proof.
  intros P l HP Hl.
  unfold TtoP in *.
  inversion Hl as [u v Hu Hincl Heq] ; subst.
  inversion Hu as [w Hw] ; unfold ord in * ; subst.
  apply ord_incl' in Hincl ; rewrite - ord_take in Hincl ; apply ord_inj in Hincl.
  erewrite <- (cat_take_drop (size w)) ; apply HP.
  now rewrite - Hincl.
Qed.

Lemma monotone_ABDown_PtoT_P : BIProp11Down_rev.
Proof.
  intros P l Hl ; unfold TtoP, ABDownmonotonisation, PtoT_dual in *.
  now specialize (Hl (ord l) (List.incl_refl _) l erefl).
Qed.


  
(*The next two Lemmas are Proposition 12 in Brede-Herbelin's paper.*)

Lemma indbarred_inductively_barred : BIProp12.
Proof.
  suff: forall T u v,
      ABmonotone T ->
      List.incl v (ord u) ->
      indbarred T v ->
      hereditary_closure (TtoP T) u.
  { intros Hyp T u Hmon Hu.
    eapply Hyp ; [assumption | now apply List.incl_refl | eassumption].
  }
  intros T u v Hmon Hincl Hv.
  revert u Hincl.
  induction Hv as [ | n v notin k IHk]; intros.
  { econstructor.
    unfold TtoP.
    eapply Hmon ; [ | eassumption].
    now eapply List.incl_tran  ; eassumption.
  }
  clear notin k.
  suff : forall m, n.+1 - (size u) = m -> hereditary_closure (TtoP T) u.
  { intros Hyp. eapply Hyp ; reflexivity. }
  intros m ; revert u IHk Hincl.
  induction m ; intros * IHk Hincl Heq.
  {  case: (leqP n.+1 (size u)).
     { intros Hninf.
       eapply ord_inf_size in Hninf as [b Hb].
       eapply (IHk b).
       eapply List.incl_app ; [assumption |].
       eapply List.incl_cons ; [ assumption | now eapply List.incl_nil_l].
     }
     intros Hinf.
     exfalso.
     unshelve eapply (PeanoNat.Nat.sub_gt _ _ _ Heq).
     eapply (proj1 (PeanoNat.Nat.le_succ_l (size u) n.+1)).
     exact (@leP (size u).+1 n.+1 Hinf).
  }
  econstructor 2 ; intros b.
  eapply IHm ; [assumption | |].
  { unfold ord ; erewrite ord_rcons, <- plus_n_O.
    erewrite <- cats1.
    now eapply List.incl_appl.
  }
  now erewrite size_rcons, subnS, Heq.
Qed.

Lemma inductively_barred_indbarred : BIProp12_rev.
Proof.
  intros T l Hl ; induction Hl as [l Hl | l k IHl].
  { unfold TtoP in *.
    econstructor ; [eassumption |].
    now apply List.incl_refl.
  }
  unshelve econstructor 2.
  exact (size l).
  { unfold ord ; exact (@ord_sizeu_notin l 0). }
  unfold ord in * ; intros a ; specialize (IHl a).
  erewrite ord_rcons, <- plus_n_O in IHl.
  now rewrite cats1.
Qed.  


Lemma indbarred_inductively_barred_dual : BIProp12Up.
Proof.
  intros P u Hmon Hbar.
  suff: hereditary_closure (TtoP (ABUpmonotonisation (PtoT P))) u.
  { clear Hbar.
    intros Hbar.
    induction Hbar as [u Hyp | u k IHk] ;
      [econstructor ; now eapply monotone_ABUp_PtoT_P |].
    econstructor 2 ; assumption.
  }
  eapply indbarred_inductively_barred ; [ | assumption].
  now apply ABUpmonot_monotone.
Qed.

Lemma inductively_barred_indbarred_dual :  BIProp12Up_rev.
Proof.
  intros P u Hered.
  eapply inductively_barred_indbarred ; unfold TtoP.
  induction Hered as [u Hu | u k IHk ] ; [ | now econstructor 2].
  do 2 econstructor ; [now econstructor ; eassumption |].
  now apply List.incl_refl.
Qed.

Lemma indbarred_inductively_barred_Down_dual : BIProp12Down.
Proof.
  intros P u Hbar.
  suff: hereditary_closure (TtoP (ABDownmonotonisation (PtoT_dual P))) u.
  { clear Hbar.
    intros Hbar ; unfold TtoP, ABDownmonotonisation, PtoT_dual in *.
    induction Hbar as [u Hyp | u k IHk] ; [econstructor | ].
    { eapply Hyp ; [ eapply List.incl_refl | reflexivity]. }
    econstructor 2 ; eassumption.
  }
  eapply indbarred_inductively_barred ; [ | assumption].
  now apply ABDownmonot_monotone.
Qed.

Lemma inductively_barred_indbarred_Down_dual : BIProp12Down_rev.
Proof.
  intros P u Hmon Hered.
  apply inductively_barred_indbarred ; unfold TtoP, PtoT_dual, ABDownmonotonisation, ord.
  induction Hered as [ u Hu | u k IHk] ; [ | now econstructor 2 ].
  econstructor ; intros v Hincl w Heq ; subst.
  apply ord_incl' in Hincl ; rewrite - ord_take in Hincl ; apply ord_inj in Hincl.
  now erewrite <- (cat_take_drop (size u)), <- Hincl ; apply Hmon.
Qed.


(*The next two Lemmas are Proposition 13 in Brede-Herbelin's paper.*)
Lemma NBbarred_barred : BIProp13. 
Proof.
  intros T Hmon HTbar alpha.
  specialize (HTbar alpha) as [u Hu].
  exists [seq (alpha i) | i <- iota 0 (List.list_max u).+1].
  split ; [ unfold prefix ; now rewrite -> size_map, size_iota |].
  unfold TtoP, ord.
  erewrite ord_map_aux, ord_iota_aux, <- map_comp.
  unshelve erewrite (eq_map (g:= fun i => (i, alpha i))) ; [ | intros ? ; reflexivity].
  eapply Hmon ; [ | eassumption].
  intros [n b] Hin.
  eapply map_incl ; [ | eassumption ].
  now eapply incl_iota_max.
Qed.


Lemma barred_NBbarred : BIProp13_rev.
Proof.
  intros T Hbar alpha.
  specialize (Hbar alpha) as [u [Hpref Hu]].
  unfold TtoP in Hu.
  exists (map fst (ord u)).
  suff: ord u = [seq (i, alpha i) | i <- [seq i.1 | i <- ord u]]
    by (intro Heq; rewrite - Heq ; exact Hu).
  clear Hu.
  erewrite <- map_comp.
  unfold prefix, ord in * ; revert Hpref ; generalize 0.
  induction u ; cbn ;  intros ; [reflexivity |].
  inversion Hpref as [H0] ; subst ; f_equal.
  now erewrite <- H, <- IHu ; [ | assumption].
Qed.


Lemma Proposition13_dual : BIProp13Down.
Proof.
  intros P HTbar alpha.
  specialize (HTbar alpha) as [u Hu].
  exists [seq (alpha i) | i <- iota 0 (List.list_max u).+1].
  split ; [ unfold prefix ; now rewrite -> size_map, size_iota |].
  unfold TtoP, ord.
  unfold ABDownmonotonisation, PtoT_dual in *.
  eapply Hu.
  2:{ reflexivity. }
  unfold ord.
  erewrite ord_map_aux, ord_iota_aux, <- map_comp.
  unshelve erewrite (eq_map (f:= fun i => (i, alpha i))).
  exact ((fun i : nat * nat => (i.1, alpha i.2)) \o (fun i : nat => (i, i))).
  2:{ intros ? ; reflexivity. }
  eapply map_incl. 
  now eapply incl_iota_max.
Qed.

Lemma Proposition13_dual_rev : BIProp13Down_rev.
Proof.
  intros P Hmon Hbar alpha ; unfold ABDownmonotonisation, PtoT_dual.
  specialize (Hbar alpha) as [u [Hpref Hu]].
  exists (map fst (ord u)).
  suff: ord u = [seq (i, alpha i) | i <- [seq i.1 | i <- ord u]].
  { intro Heq; rewrite - Heq ; intros v Hincl w Heqvw ; subst.
    apply ord_incl' in Hincl.
    rewrite - ord_take in Hincl ; apply ord_inj in Hincl.
    erewrite <- (cat_take_drop (size u)) ; apply Hmon.
    now rewrite - Hincl.
  }
  unfold prefix, ord in * ; rewrite Hpref ord_map_aux ord_iota_aux.
  repeat erewrite <- map_comp.
  now eapply eq_map.
Qed.  
  

Lemma arbor_is_tree P : is_tree (Downarborification P).
Proof.
  intros u n Hu.
  unfold Downarborification in * ; intros m.
  case: (leqP n m) ; intros Hinf.
  { erewrite take_taker ; [ | assumption].
    now apply Hu.
  }
  erewrite take_takel ; [now apply Hu |].
  now apply ltnW.
Qed.

Lemma DownABarbor_is_tree T : ABis_tree (DownABarborification T).
Proof.
  intros u n Hu.
  unfold DownABarborification in * ; intros Hyp v Hincl.
  apply Hyp.
  eapply List.incl_tran ; eassumption.
Qed.

Lemma UpABarbor_is_tree T : ABis_tree (ABUparborification T).
Proof.
  intros u n Hu HT.
  induction HT.
  econstructor ; [eassumption | ].
  now eapply List.incl_tran ; eassumption.
Qed.

Lemma Prop11 : DCProp11.
Proof.
  intros P HP ; unfold TtoP.
  econstructor ; [econstructor ; eassumption |].
  now apply List.incl_refl.
Qed.

Lemma Prop11_rev : DCProp11_rev.
Proof.
  intros P u Htree HP ; unfold TtoP in *.
  inversion HP ; subst.
  inversion X ; subst.
  apply ord_incl' in H.
  rewrite - ord_take in H ; apply ord_inj in H ; rewrite H.
  unfold is_tree in * ; now apply Htree.
Qed.

Lemma Prop11_rev_Down P u :
  TtoP (DownABarborification (PtoT P)) u ->
  P u.
Proof.
  intros HP ; unfold TtoP, DownABarborification in *.
  specialize (HP (ord u) (List.incl_refl _)).
  inversion HP ; subst.
  apply ord_inj in H0 ; subst.
  assumption.
Qed.


Lemma Prop12 : DCProp12.
Proof.
  intros T u Htree.
  generalize (@erefl _ (ord u)).
  generalize (ord u) at 2 3 ; intros l Heq Happ. revert l Happ u Heq.
  refine (cofix aux l Happ := match Happ as H in ABapprox _ u0 return
                            forall u : seq B, ord u = u0 -> pruning (TtoP T) u with
                            | approx l Harb Hyp => _
                            end).
  intros u Heq ; subst.
  unshelve edestruct (Hyp (size u)) ; [exact (@ord_sizeu_notin u 0) |].
  unshelve econstructor ; [assumption | |].
  { unfold TtoP.
    now specialize (Harb (ord u) (List.incl_refl _)).
  }
  eapply (aux (rcons (ord u) (size u, x))) ; [assumption |].
  unfold ord ; now rewrite -> ord_rcons, <- plus_n_O.
Qed.


Lemma Prop12_rev : DCProp12_rev.
Proof.
  suff: forall T u v,
      ABis_tree T ->
      pruning (TtoP T) u ->
      List.incl v (ord u) ->
      ABapprox T v.
  { intros Hyp T u Htree Hprun.
    eapply Hyp ; [eassumption | eassumption | now apply List.incl_refl].
  }
  intros T u v Htree Hprun Hincl.
  unfold TtoP in Hprun ; revert Hprun v Hincl.
  revert u.
  refine (cofix aux u Hprun := match Hprun as H0 in pruning _ v0
                                     return forall w, List.incl w (ord v0) -> ABapprox T w
                             with
                             | prune c u Hu Hprun' => _
                               end).
  clear u0 Hprun ; intros w Hincl ; subst.
  econstructor.
  { intros x Hincl'.
    eapply Htree ; [ | eassumption].
    eapply List.incl_tran ; eassumption.
  }
  intros n _.
  unshelve refine ((fix aux2 m :=
            match m as m0 return
                  forall (n : nat) (u : seq B) (c : B) (w : seq (nat * B)),
                    T (ord u) ->
                    pruning (fun l : seq B => T (ord l)) (rcons u c) ->
                    List.incl w (ord u) -> n.+1 - size u = m0 ->
                    {b : B & ABapprox T (rcons w (n, b))}
            with
              | 0 => _
            | S m => _
            end) (n.+1 - size u) _ u c _ _ _ _ _). 
  { clear - aux ; intros n u c v Hu Hprun Hincl Heq.
    destruct u as [ | u b IHu] using last_ind ; [now inversion Heq |] ; clear IHu.
    exists (nth b (rcons u b) n).
    eapply aux ; [ exact Hprun |].
    rewrite - cats1.
    apply List.incl_app.
    { unfold ord ; rewrite ord_rcons - cats1 ; now apply List.incl_appl. }
    clear v Hincl.
    unfold ord ; rewrite -> ord_rcons, nth_rcons, <- plus_n_O.
    rewrite size_rcons in Heq ; change (n - size u = 0) in Heq.
    case: (leqP (size u) n) ; intros Hinf.
    { suff: n = size u.
      { intros Heq' ; subst.
        rewrite -> eq_refl, <- cats1 ; cbn.
        rewrite -> ord_rcons, <- plus_n_O, <- cats1.
        now apply List.incl_appl, List.incl_appr, List.incl_refl.
      }
      suff: (n == size u) by now move/eqP.
      now rewrite -> eqn_leq, -> Hinf, <- subn_eq0, Heq.
    }
    rewrite (@ord_nth _ b u 0 n) ; cbn.
    eapply List.incl_tran.
    2:{ rewrite <- cats1 ; apply List.incl_appl ; now apply List.incl_refl. }
    rewrite -> ord_rcons, <- plus_n_O, <- cats1 ; apply List.incl_appl.
    apply List.incl_cons ; [ | now apply List.incl_nil_l].
    erewrite (plus_n_O n) at 1.
    now eapply ord_nth_in.
  }
  clear - aux aux2 ; intros n u c v Hu Hprun Hincl Heq.
  inversion Hprun ; subst.
  eapply (aux2 _ _ (rcons u c)).
  assumption.
  eassumption.
  { eapply List.incl_tran ; [eassumption | clear Hincl].
    unfold ord ; rewrite <- cats1, ord_cat, <- plus_n_O.
    apply List.incl_appl ; now apply List.incl_refl.
  }
  rewrite -> size_rcons, subnS, Heq.
  reflexivity.
  all: try assumption.
  reflexivity.
Admitted.

Lemma Prop12_sym : DCProp12_sym.
Proof.
  intros P u Hprun.
  apply Prop12_rev ; [now apply UpABarbor_is_tree |].
  revert u Hprun.
  cofix aux.
  intros _ [b u Hu Hprun].
  econstructor ; [now eapply Prop11 |].
  apply aux.
  eassumption.
Qed.

Lemma pruning_ext P Q l :
  (forall u, P u = Q u) ->
            pruning P l ->
            pruning Q l.
Proof.
  intros Hex ; revert l.
  refine (cofix aux l Hprun := match Hprun as H in pruning _ l0 return pruning Q l0 with
                            | prune b u Hu Hyp => _
                             end).
  econstructor ; [now erewrite <- Hex |].
  apply aux ; eassumption.
Qed.  

Lemma choicefun_arbor P :
  choicefun (Downarborification P) ->
  choicefun P.
Proof.
  intros [alpha Halpha] ; exists alpha.
  unfold Downarborification in Halpha.
  intros n ; specialize (Halpha n n).
  now rewrite <- map_take, take_iota, minnn in Halpha.
Qed.

Lemma choicefun_arbor_rev P :
  choicefun P ->
  choicefun (Downarborification P).
Proof.
  intros [alpha Halpha] ; exists alpha ; unfold Downarborification in *.
  intros n m ; rewrite <- map_take, take_iota.
  now apply Halpha.
Qed.

Lemma barred_Upmon_barred (P : list B -> Type) :
  barred (Upmonotonisation P) ->
  barred P.
Proof.
  unfold barred.
  intros Hyp alpha.
  specialize (Hyp alpha) as [u [Hpref Halpha]].
  destruct Halpha as [u v Hu].
  exists u ; split ; [ | assumption].
  unfold prefix in *.
  eapply (f_equal (take (size u))) in Hpref.
  rewrite take_size_cat in Hpref ; [ | reflexivity].
  rewrite -> Hpref at 1.
  rewrite <- map_take, take_iota, size_cat.
  suff: forall n m, minn n (n + m) = n.
  { intros Hmin ; now erewrite Hmin. }
  clear ; intros n ; induction n ; intros m ; cbn ; [now rewrite min0n |].
  now erewrite minnSS, IHn.
Qed.  
  
  

Lemma pruning_arbor P l :
  (P l -> forall n, P (take n l)) ->
  pruning P l ->
  pruning (Downarborification P) l.
Proof.
  intros HP Hprun ; revert l Hprun HP.
  refine (cofix aux l Hprun :=
            match Hprun as H in pruning _ l0
                  return (P l0 -> forall n, P (take n l0)) -> pruning _ l0 with
            | prune b u Hu Hyp => _
            end).
  intros Htake.
  econstructor.
  { intros n.
    now apply Htake.
  }
  apply aux ; [eassumption |].
  intros Hu' n.
  case: (leqP n (size u)) ; intros Hinf.
  { erewrite <- cats1, takel_cat ; [now apply Htake | assumption]. }
  erewrite <- cats1, take_cat.
  erewrite <- (subnSK Hinf).
  apply ltnW, leq_gtF in Hinf ; rewrite Hinf ; cbn ; rewrite cats1.
  now destruct Hyp.
Qed.

Lemma test (P : list B -> Type) l :
  (forall n, P (take n l) -> P l) ->
  hereditary_closure (Upmonotonisation P) l ->
  hereditary_closure P l.
Proof.
  intros HP Hered.
  induction Hered as [u Hu | u k IHk].
  { destruct Hu.
    econstructor ; apply (HP (size l)).
    now rewrite take_size_cat.
  }
  econstructor 2 ; intros a ; apply IHk.
  intros n.
  case: (leqP n (size u)) ; intros Hinf.
  2:{ erewrite <- cats1, take_cat.
      erewrite <- (subnSK Hinf).
      now apply ltnW, leq_gtF in Hinf ; rewrite Hinf ; cbn ; rewrite cats1.
  }
  clear k
  erewrite <- cats1 , takel_cat ; [ | assumption].
    apply HP in Hn.
Abort.
  
Lemma prop13 : DCProp13.
Proof.
  intros T [alpha Halpha] ; exists alpha ; intros n.
  unfold TtoP.
  specialize (Halpha (iota 0 n)).
  unfold ord ; rewrite ord_map_aux ord_iota_aux - map_comp.
  erewrite eq_map ; [eassumption |].
  now intros k.
Qed.

Lemma prop13_rev : DCProp13_rev.
Proof.
  intros T Htree [alpha Halpha] ; exists alpha ; intros u.
  specialize (Halpha (List.list_max u).+1) ; unfold TtoP in Halpha.
  eapply Htree ; [ | eassumption].
  unfold ord ; rewrite ord_map_aux ord_iota_aux - map_comp.
  unshelve erewrite (eq_map (g:= fun i => (i, alpha i)) _ (iota 0 _)) ; [now intros k |].
  now eapply map_incl, incl_iota_max.
Qed.

Lemma prop13dual : DCProp13_Up. 
Proof.
  intros p Htree [alpha Halpha] ; exists alpha ; intros n.
  specialize (Halpha (iota 0 n)). 
  inversion Halpha as [l1 l2 Hl Hincl Heq].
  subst.
  inversion Hl ; subst.
  unfold is_tree in Htree.
  erewrite (eq_map (g := (fun i => (i.1, alpha i.2)) \o (fun n => (n, n)))),
    map_comp, <- ord_iota_aux, <- ord_map_aux in Hincl ; [ | now intro k].
  eapply ord_incl' in Hincl ; rewrite <- ord_take, size_map, size_iota in Hincl.
  apply ord_inj in Hincl ; rewrite Hincl.
  now apply Htree.
Qed.

  
(*GBI_monot is used in the proof of Theorem 5 in Brede-Herbelin's paper.*)
Lemma GBI_monot :
  (forall T : list (nat * B) -> Type, ABmonotone T -> GBI T) ->
  forall (T : list (nat * B) -> Type), GBI T.
Proof.
  intros HBI T Hbar.
  suff: forall l,
      indbarred (ABUpmonotonisation T) l ->
      indbarred T l. 
  { intros Hyp.
    apply Hyp.
    apply HBI ; [now apply ABUpmonot_monotone |].
    apply ABmonot_barred, Hbar.
  }
  clear HBI ; intros l Hl.
  induction Hl.
  { inversion t as [l l' Hl Heq].
    subst.
    econstructor ; [eassumption |].
    now eapply List.incl_tran ; eassumption.
  }
  econstructor 2. eassumption.
  eassumption.
Qed.

Lemma BI_GBI : 
  (forall P : list B -> Type, BI_ind P) ->
  forall (T : list (nat * B) -> Type), GBI T.
Proof.
  intros HBI.
  apply GBI_monot ; intros T Hmon HTbar.
  change (@nil (nat * B)) with (ord (@nil B)).
  apply inductively_barred_indbarred.
  apply HBI.
  apply NBbarred_barred ; assumption.
Qed.

Lemma hered_dec (P : list B -> Type) (l : list B) :
  (forall u, (P u) + (P u -> False)) ->
  hereditary_closure (Upmonotonisation P) l ->
  (forall n, P (take n l) -> False) ->
  hereditary_closure P l.
Proof.
  intros Hdec Hyp ; induction Hyp as [_ [u u' Hu] | u k IHk] ; intros Hnot.
  { exfalso.
    apply (Hnot (size u)).
    now erewrite take_size_cat.
  }
  econstructor 2 ; intros b.
  destruct (Hdec (rcons u b)) ; [now econstructor |].
  apply IHk.
  intros n.
  erewrite <- cats1, take_cat.
  case: (leqP (size u) n) ; intros Hinf ; [ | now apply Hnot].
  case : (n - (size u)) ; cbn ; [rewrite cats0 - (take_size u) ; now apply Hnot |].
  intros _ ; now rewrite cats1.
Qed.
  
  
    
Lemma BI_monot_dec (P : list B -> Type) :
  (forall u, (P u) + (P u -> False)) ->
  (forall P : list B -> Type, monotone P -> BI_ind P) ->
  BI_ind P.
Proof.
  intros Hdec HBI Hbar ; unfold BI_ind, inductively_barred in *.
  destruct (Hdec nil) ; [now econstructor |].
  apply hered_dec ; [assumption | | trivial].
  apply HBI ; [now apply Upmonot_monotone |].
  now apply monot_barred.
Qed.
  
  
  
Lemma GBI_BI_mon :
  (forall (T : list (nat * B) -> Type), GBI T) ->
  forall T' : list B -> Type, monotone T' -> BI_ind T'.
Proof.
  intros HGBI T' Hmon BarT'.
  unfold GBI, inductively_barred in *.
  apply indbarred_inductively_barred_dual ; [assumption |].
  apply HGBI.
  suff: ABbarred (PtoT T').
  { intros HTbar alpha ; specialize (HTbar alpha) as [u Hu].
    exists u.
    econstructor ; [eassumption | now apply List.incl_refl].
  }
  eapply barred_NBbarred.
  intros alpha ; specialize (BarT' alpha) as [u [prefu Hu]].
  exists u ; split ; [assumption |].
  now eapply TtoP_PtoT_ret.
Qed.

Lemma GDC_tree T :
  (forall T, ABis_tree T -> ABapprox T nil -> ABchoicefun T) ->
  ABapprox T nil ->
  ABchoicefun T.
Proof.
  intros HGDC Happ.
  suff: ABchoicefun (DownABarborification T).
  { intros [alpha Hyp].
    exists alpha.
    intros u ; specialize (Hyp u).
    unfold DownABarborification in *.
    now specialize (Hyp _ (List.incl_refl _)).
  }
  apply HGDC ; [now apply DownABarbor_is_tree |].
  clear HGDC.
  revert Happ ; generalize (@nil (nat * B)).
  cofix H ; intros u Happ.
  destruct Happ.
  econstructor.
  { intros v Hincl w Hincl'.
    apply d ; eapply List.incl_tran ; eassumption.
  }
  intros n Hnotin.
  specialize (s n Hnotin) as [b Happ].
  exists b.
  now apply H.
Qed.  
  

Lemma Theorem5: DC -> forall T, ABis_tree T -> ABapprox T nil -> ABchoicefun T.
Proof.
  intros Hyp T Htree Happ.
  apply prop13_rev ; [assumption |].
  apply Hyp.
  now apply Prop12 ; [assumption |].
Qed.  

Lemma Theorem5rev : GDC -> DC.
Proof.
  intros Hyp P Hprun.
  apply choicefun_arbor.
  apply prop13dual; [apply arbor_is_tree |].
  unfold GDC in Hyp ; apply Hyp.
  change (@nil (nat * B)) with (ord (@nil B)).
  apply Prop12_sym.
  eapply pruning_arbor ; [assumption |]. 
  intros n ; cbn ; now destruct Hprun.
Qed.


Lemma GBI_BI :
  (forall (T : list (nat * B) -> Type), GBI T) ->
  forall T' : list B -> Type,  BI_ind T'.
Proof.
  intros HGBI P BarP.
  pose (Hyp1 := choicefun_arbor).
  pose (Hyp1dual := monot_barred (C := B)).
  pose (Hyp2 := prop13dual) ; unfold DCProp13_Up in *.
  pose (Hyp2dual := Proposition13_dual_rev) ; unfold BIProp13Down_rev in *. 
  pose (Hyp3 := arbor_is_tree).
  pose (Hyp3dual := @Upmonot_monotone B).
  pose (Hyp4:= Prop12_sym) ; unfold DCProp12_sym, DCProp13_Up in *.
  pose (Hyp4dual := indbarred_inductively_barred_Down_dual) ; unfold BIProp12Down in *.
  pose (Hyp5:= pruning_arbor).
  
  pose 
  unfold GBI in HGBI.
  unfold inductively_barred.
  suff: BIProp12Down ; unfold BIProp12Down.
  Print Theorem5rev.
  Print choicefun_arbor.
  { intros H12.
    apply H12.
    apply HGBI.
    suff: BIProp13Down_rev ; unfold BIProp13Down_rev.
    { intros H13rev.
      apply H13rev ; [ | assumption].
    suff: forall l : seq B,
        hereditary_closure (TtoP (ABDownmonotonisation (PtoT_dual (Upmonotonisation P)))) l ->
        hereditary_closure (Upmonotonisation P) l.
    { intros Hyp.
      unfold BIProp12Down in *.
      suff: hereditary_closure (Upmonotonisation P) nil ->
            hereditary_closure P nil.
      { intros Hypnaze.
        apply Hypnaze.
        apply Hyp.
        apply grz.
        apply HGBI.
        apply H13rev.
        { unfold TtoP. admit. }
        intros alpha.
        specialize (BarP alpha) as [u [Hpref Hu]].
        exists u ; split ; [assumption |].
        unfold TtoP, ABDownmonotonisation, PtoT_dual.
        intros v Hincl w Heq ; subst.
        apply ord_incl' in Hincl ; erewrite <- ord_take in Hincl.
        eapply ord_inj in Hincl.
        erewrite <- (cat_take_drop (size u)) ; econstructor.
        now rewrite - Hincl.
      }
        rewrite Hincl in Hl.
        Print Upmonotonisation.
      
    specialize (H13rev (Upmonotonisation P) (@Upmonot_monotone _ _) (monot_barred BarP)).

    
  forall l : seq B,
  pruning (Downarborification P) l ->
  pruning (TtoP (ABUparborification (PtoT (Downarborification P)))) l    apply HGBI in H13rev.
    apply grz.
    clear grz HGBI.
    cbn.
    induction H13rev as [u v Hv Hincl | u k IHk].
    2:{ econstructor 2 ; eassumption. }
    unfold ABDownmonotonisation, PtoT_dual in *.
    specialize (Hv u Hincl).
    econstructor.
    Print Upmonotonisation.
    intros w Hincl' x Heq ; subst.
    specialize (Hv x

    
    [ | econstructor 2].
    
  suff: BIProp13.
  apply HGBI.
  unfold ABDownmonotonisation, PtoT_dual, ABbarred.
  cbn.
  intros alpha.
  specialize (BarT' alpha) as [u [Hpref Hu]].
  exists (iota 0 (size u)).
  intros v Hincl w Heq.
  subst.
  unfold prefix in *.
  
  apply barred_NBbarred.
  apply NBbarred_barred ; [now apply ABDownmonot_monotone |].
  
  apply prop13_rev.
      2:{

        apply Hyp.
      unshelve eapply Prop12_rev ; [exact nil | now apply ABarbor_is_tree | | ].
  2:{ now apply List.incl_refl. }
  destruct Hprun as [b l HP Hprun].
  unshelve econstructor ; [assumption | | ].
  unfold TtoP.
  intros v Hincl.
  
  
  
  eq_refl, ltnn, <- plus_n_O, <- cats1.
      apply List.incl_appr, List.incl_cons ; [ now left | now apply List.incl_nil_l].
    }
    
      cbn.
      case: (ltnP n (size u)).
      { intros Hinf ; apply ltn_eqF in Hinf ; rewrite Hinf in Heqn ; now inversion Heqn. }
    apply List.incl_cons ; [ | now apply List.incl_nil_l].
    
    Print has.
    .
    
subn_eq0

    case: (leqP n.+1 (size u)).
     { intros Hninf.
       eapply ord_inf_size in Hninf as [b Hb].
       exists b ; econstructor.
       unfold TtoP in Hprun ; destruct Hprun as [b' u Hu].
       eapply (IHk b).
       eapply List.incl_app ; [assumption |].
       eapply List.incl_cons ; [ assumption | now eapply List.incl_nil_l].
     }
     intros Hinf.
     exfalso.
     unshelve eapply (PeanoNat.Nat.sub_gt _ _ _ Heq).
     eapply (proj1 (PeanoNat.Nat.le_succ_l (size u) n.+1)).
     exact (@leP (size u).+1 n.+1 Hinf).
  }
  econstructor 2 ; intros b.
  eapply IHm ; [assumption | |].
  { unfold ord ; erewrite ord_rcons, <- plus_n_O.
    erewrite <- cats1.
    now eapply List.incl_appl.
  }
  now erewrite size_rcons, subnS, Heq.
    

Lemma GBI_BI' :
  (forall (T : list (nat * B) -> Type), GBI T) ->
  forall T' : list B -> Type, BI_ind T'.
Proof.
  intros HGBI T' BarT'.
  pose (T:= (PtoT T')).
  have aux: Tbarred (PtoT T').
  { eapply barred_NBbarred.
    intros alpha ; specialize (BarT' alpha) as [u [prefu Hu]].
    exists u ; split ; [assumption |].
    now eapply TtoP_inj.
  }
  apply HGBI in aux ; clear HGBI.
  suff: forall u l,
      l = ord u ->
      indbarred T l -> hereditary_closure T' u by
      (intros H ; apply (H nil (ord nil))).
  clear aux ; intros u l Heq Hl.
  revert u Heq.
  induction Hl ; intros.
  { subst.
    econstructor.
    unfold T in t.
    inversion t ; subst.
    apply ord_incl' in i ; rewrite - ord_take in i ; apply ord_inj in i.
    erewrite <- (cat_take_drop (size l)) ; apply Hmon.
    now rewrite - i.
  }

  
  induction aux.
  inversion t.
  subst.
  
  eapply indbarred_inductively_barred in aux.
  
  
  suff: forall l, indbarred T l -> hereditary_closure T' (map snd l) by
      (intros H ; change (hereditary_closure T' (map (snd (A:= nat)) nil)) ; now apply H).
  clear aux ; intros l aux ; induction aux.
  econstructor ; unfold T in * ; clear T.
    
    generalize 0 ; induction u ; intros n ; [ assumption |].
    cbn in *.


Lemma inductively_barred_indbarred T l :
  indbarred T l -> {u & prod (List.incl (ord u) l) (hereditary_closure (TtoP T) u)}.
Proof.
  intros Hl.
  induction Hl as [l l' Hl | l k IHl].
  admit.
  assert (b : B) by admit.
  destruct (X b) as [u [Hincl Hered]].
  assert (Hyp : forall q (x : nat * B), {List.In x q} + {~ List.In x q}) by admit.
  destruct (Hyp (ord u) (l, b)).
  2:{ assert (List.incl (ord u) k) by admit.
      exists u.
      split ; assumption.
  }
  
      
  
  


(* TODO : secure the names generated by inversions and destruct using*)
Lemma indbarredP T (b : B) (l : list (nat * B)) : indbarred T l -> indbarred_spec T l.
Proof.
elim=> [u u' Tu |a v _ hvbar ih].
- destruct u using last_ind.
  + destruct u' using last_ind.
    * exact: (Eta [::]). 
      have -> : [::] ++ rcons u' x = rcons ([::] ++ u') x by [].
      case: x => a bb; exact: Beta.
    * destruct u' using last_ind.
      - by rewrite cats0; apply: (Eta [::]); rewrite cats0.
      - have -> : rcons u x ++ rcons u' x0 = rcons ((rcons u x) ++ u') x0 by rewrite rcons_cat.
        by case: x0 {IHu} => aa bbb; apply: Beta.
- destruct v using last_ind.
  + pose x := ih b. inversion x.
    * exact: (Eta ((a, b) :: u)).
    * exact: (Eta u').
  +  pose y := ih b. inversion y. 
     * by apply: (Eta ((a, b) :: u)); rewrite -cat1s catA.
     * have -> : rcons v x = u' ++ u.
       erewrite cats1 in H0 ; eapply rcons_inj in H0 ; now inversion H0.
       destruct u using last_ind.
       - by rewrite cats0; apply: (Eta [::]); rewrite cats0.
       - rewrite -rcons_cat; case: x0 H0 => [aa  bb] H0; exact: Beta.
Qed.

(* Generalized Bar Induction, phrased using the Herbelin-Brede way *)
Definition GBI T := Tbarred T -> indbarred T [::].
  
Lemma GBI_to_BI : (forall T, GBI T) -> forall (T' : seq B -> Type), BI_ind T'.
Proof.
  intros HGBI T' BarT'.
  unfold GBI in HGBI.
  pose (T := fun (u : seq (nat * B)) => T' (map snd u)).
  have aux: Tbarred T.
  { intros alpha ; unfold T.
    specialize (BarT' alpha) as [u [prefu Hu]].
    exists (List.seq 0 (size u)).
    suff: u = [seq i.2 | i <- [seq (i, alpha i) | i <- List.seq 0 (size u)]] by
      intros Heq ; now rewrite - Heq.
    unfold prefix in prefu ; rewrite prefu ; clear prefu Hu.
    generalize (size u) as n, 0 as m ; clear u.
    induction n ; cbn ; intros ; [reflexivity |].
    f_equal ; now eapply IHn. }
  apply HGBI in aux ; clear HGBI.
  unfold inductively_barred.
  suff: forall l, indbarred T l -> hereditary_closure T' (map snd l) by
      (intros H ; change (hereditary_closure T' (map (snd (A:= nat)) nil)) ; now apply H).
  clear aux ; intros l aux ; induction aux.
  unfold T in t.
  econstructor.
    
    generalize 0 ; induction u ; intros n ; [ assumption |].
    cbn in *.
  
  
  
End GBI_BI.

(* Now let's prove seq_contW + bar induction -> dialogue or Brouwer 
   May be find a better principle for reasoning on trees, equivalent to bar induction
   TODO: find a better way to separate the concern of orders in queries and 
   the "bar-induction-like" principle
   TODO : tame the le vs <= mess.
*)

Section Brouwer_ext_tree.

  (*The goal of this Section is to provide an extensional tree equivalent to Brouwer trees,
   and to prove that it is equivalent to seq_contW. *)

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
  {tau : Bext_tree & forall alpha, {n : nat & Beval_ext_tree tau alpha n = Some (F alpha)} }.


(*The following is a bunch of lemmas that mimick lemmas about extensional trees,
 albeit for Brouwer extensional trees this time. *)
Definition Bvalid_ext_tree (tau : Bext_tree) (f : I -> O) :=
  forall (k : I) (a : A), tau (map f (iota 0 k)) = Some a ->
                          tau (map f (iota 0 k.+1)) = Some a.

Lemma Bvalid_plus (tau : Bext_tree) f :
  Bvalid_ext_tree tau f -> forall k j a,
      tau (map f (iota 0 k)) = Some a ->
      tau (map f (iota 0 (k + j))) = Some a.
Proof.
move=> H k j; elim: j k => [| j ihj] k a e; first by rewrite addn0.
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

(* Moved to Axiom Free Implications.

Lemma eval_ext_tree_continuous (tau : ext_tree I O A) n l :
  modulus (fun alpha => eval_ext_tree_aux tau alpha n l)
    (fun alpha => eval_ext_tree_trace_aux tau alpha n l).
Proof.
elim: n l => [| n ihn] l alpha beta /= eqab //=.
case: (tau l) eqab => // i /= [<- e].
exact: ihn.
Qed.

Lemma eval_ext_tree_trace_continuous (tau : ext_tree I O A) n l :
  modulus (fun alpha => eval_ext_tree_trace_aux tau alpha n l)
    (fun alpha => eval_ext_tree_trace_aux tau alpha n l).
Proof.
elim: n l => [| n ihn] l alpha beta //= eqab.
case: (tau l) eqab => // i [<- e]; congr (_ :: _).
exact: ihn.
Qed.
 *)

(*Now we try to turn extensional trees into Brouwer extensional trees.
 We start by proving that eval_ext_tree on an oracle can be seen as eval_ext_tree
 on a partial oracle computed via a list*)


Lemma eval_ext_tree_from_pref (tau : ext_tree I O A) f n l o :
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
  suff -> : x = eval_ext_tree_trace_aux tau alpha n [::].
  by rewrite {}/x {}/m addnS ltnS leq_addl.
  rewrite {}/x.
  erewrite (eval_ext_tree_trace_monotone (n := n) m) ; [ | eassumption].
  erewrite (eval_ext_tree_trace_from_pref (f := alpha) (l := nil)) ;
    rewrite {}/m ; first by rewrite addnS.
  set m1 := List.list_max _.
  set m2 := List.list_max _.
  suff: m1 = m2 ; rewrite {}/m1 {}/m2.
  by intros H ; rewrite H ; apply PeanoNat.Nat.le_add_l.
  f_equal.
  cbn ; symmetry.
  eapply eval_ext_tree_trace_monotone.
  exact Heq.
Qed.

  
Lemma ext_tree_to_Bext_tree_valid tau o f:
  Bvalid_ext_tree (extree_to_Bextree tau o) f.
Proof.
  intros k a.
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
  {n : I & eval_ext_tree tau alpha n = output (F alpha) } ->
  {n : I & Beval_ext_tree (extree_to_Bextree tau o) alpha n = Some (F alpha)}.
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


Proposition seq_cont_to_Brouwer F : seq_contW F -> Bseq_cont F.
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

Section BarInduction.


  (*The aim of this Section is to prove that Sequential continuity + Bar Induction
   implies Dialogue continuity.*)
Variable BI : forall A T, @BI_ind A T.
Variable O A : Type.
Notation I := nat.
Implicit Type (F : (I -> O) -> A).
Local Notation Bext_tree := (Bext_tree O A).


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
  {tau : Bext_tree &
           forall alpha, {n : nat & Beval_ext_tree tau alpha n = Some (F alpha)}
  } ->
  {tau : Bext_tree &
           prod (forall alpha, {n : nat & Beval_ext_tree tau alpha n = Some (F alpha)})
             (forall alpha, Bvalid_ext_tree tau alpha) }.
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
  {tau : Bext_tree &
           prod (forall alpha, {n : nat & Beval_ext_tree tau alpha n = Some (F alpha)})
             (Bvalid_ext_tree2 tau) } ->
  btree_contP F.
Proof.
  intros [tau [HF Hvalid]].
  pose (T := fun l => {a : A & tau l = Some a}).
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
  unfold inductively_barred in Help ; unfold Beval_ext_tree in HF.
  have auxil: forall alpha : I -> O,
      {k : I & Some (F alpha) = tau [seq alpha i | i <- iota 0 k]}.
  { intros alpha.
    specialize (HF alpha) as [n HFn].
    erewrite Beval_ext_tree_map_aux in HFn ; cbn in HFn.
    econstructor ; symmetry ; eassumption.
  }
  revert Help HF.
  generalize (@nil O) ; intros l Help HF.
  unshelve eexists.
  { clear HF Hvalid.
    induction Help as [l [a Heqa] | l _ IH] ; intros.
    1: exact (spit a).
    unshelve refine (bite (fun o => IH o)).
  }
  intros alpha.
  set (t:= beval _).
  suff: Some (F alpha) = Some (t alpha) by 
    intro H ; injection H.
  rewrite {}/t.
  specialize (HF alpha) as [n HFn].
  rewrite <- HFn ; revert HFn ; generalize (F alpha) ; intros x HFn ; clear auxil F.
  revert alpha HFn; induction Help as [l [a Heqa] | l ? IH] ; intros.
  { destruct n ; [assumption |].
    cbn ; now rewrite Heqa.
  }
  cbn in *.
  erewrite <- IH.
  { clear IH h.
    revert alpha l HFn ; generalize 0 as i.
    induction n ; intros.
    - cbn in * ; rewrite HFn.
      symmetry.
      now eapply Hvalid.
    - cbn in *.
      remember (tau l) as r.
      destruct r.
      + erewrite Hvalid ; try eassumption.
        now rewrite <- Heqr.
      + clear Heqr.
        revert HFn ; remember (tau (rcons l (alpha i))) as r.
        destruct r ; intros.
        * eapply Beval_ext_tree_constant.
          now symmetry.
        * cbn.
          now eapply IHn.
  }
  clear IH h ; revert alpha l HFn ; generalize 0 as i.
  induction n ; intros.
  - cbn in *.
    now eapply Hvalid.
  - cbn in *.
    remember (tau l) as r.
    destruct r.
    + erewrite Hvalid ; try eassumption.
      now rewrite <- Heqr.
    + clear Heqr.
      revert HFn ; remember (tau (rcons l (alpha i))) as r.
      destruct r ; intros.
      * cbn.
        rewrite <- HFn ; symmetry.
        now eapply Beval_ext_tree_constant.
      * cbn.
        now eapply IHn.
Qed.

  
Lemma Bseq_cont_valid_to_dialogue F :
  {tau : Bext_tree &
           prod (forall alpha, {n : nat & Beval_ext_tree tau alpha n = Some (F alpha)})
             (forall alpha, Bvalid_ext_tree tau alpha) } ->
  btree_contP F.
Proof.
  intros [tau [HF Hvalid]].
  eapply Bseq_cont_valid2_to_dialogue.
  exists tau.
  split ; [assumption |].
  now apply Bvalid_Bvalid2.
Qed.  


Proposition Bseq_cont_to_Bcont F :
  seq_contW F ->
  dialogue_cont F.
Proof.
  intros H.
  eapply  bcont_to_dialogue_cont.
  eapply Bseq_cont_valid_to_dialogue.
  eapply Bseq_cont_to_Bseq_cont_valid.
  now eapply seq_cont_to_Brouwer.
Qed.
  
  
End BarInduction.
