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

Inductive indbarredP {A B} (T : _ -> Prop) : list (A * B) -> Prop :=
| ietaP u' u : T u' -> indbarredP T (u' ++ u)
| ibetaP a v : ~ In a (map fst v) ->
              (forall b, indbarredP T (v ++ [(a,b)])) ->
              indbarredP T v.

Inductive indbarred {A B} T : list (A * B) -> Type :=
| ieta u' u : T u' -> indbarred T (u' ++ u)
| ibeta a v : ~ In a (map fst v) ->
              (forall b, indbarred T (v ++ [(a,b)])) ->
              indbarred T v.

Definition monotone {X} T := forall a b : list X, incl a b -> T a -> T b.

Lemma indbarred_barred {A B} T : @indbarred A B T nil -> monotone T -> barred T.
Proof.
  unfold barred. intros H Hmon.
  change (forall α : A -> B, {u : seq.seq (A * B) & (Forall (fun '(a, b) => α a = b) u * T ([] ++ u))%type}).
  revert H. generalize (@nil (A * B)).
  induction 1; intros α.
  - exists []. split. econstructor. eapply Hmon. 2: eassumption.
    eapply incl_appl, incl_appl, incl_refl.
  - destruct (X (α a) α) as (u & H1 & H2).
    exists (u ++ [(a,α a)]). split.
    clear - H1. induction H1; cbn; econstructor; eauto using Forall.
    eapply Hmon. 2: eassumption.
    repeat eapply incl_app.
    + eapply incl_appl, incl_refl.
    + eapply incl_appr, incl_appr, incl_refl.
    + eapply incl_appr, incl_appl, incl_refl.
Qed.

(* Lemma indbarred_Acc {A B} T : @indbarredP A B T nil -> monotone T -> forall u, Acc (fun v1 v2 => exists a b, v1 = v2 ++ [(a,b)] /\ ~ T v1) u.
Proof.
  intros H Hmon u.
  change u with (nil ++ u). revert u.
  revert H. generalize (@nil (A * B)).
  induction 1; intros w.
  - econstructor. intros ? (? & ? & -> & ?).
    destruct H0. eapply Hmon. 2: eassumption.
    eapply incl_appl, incl_appl, incl_appl, incl_refl.
  - econstructor. intros ? (? & ? & -> & ?).
    

    destruct H0. eapply Hmon. 2: eassumption.
    eapply incl_appl, incl_appl, incl_appl, incl_refl.
  - econstructor. 

Qed. *)


(* Goal forall A B T, (forall l, {T l} + {~ T l}) -> forall l, @indbarredP A B T l -> inhabited (indbarred T l). *)
(* Proof. *)
(*   intros A B T D l H. *)
(*   induction H. *)
(*   - econstructor. econstructor. assumption. *)
(*   -  *)

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
    intros. induction Barred.
    + destruct t as [o Ho]. exists (eta o).
      cbn in *. 
      

    intros f. specialize (Hτ f).
    have Hvalid: valid_ext_tree τ by admit.
Admitted.

Set Bullet Behavior "Strict Subproofs".

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
  Admitted.



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
