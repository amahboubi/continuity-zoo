From mathcomp Require Import all_ssreflect.
Require Import Program.
From Equations Require Import Equations.
Require Import extra_principles.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma Sigma1_choice {X} (R : X -> nat -> Prop) :
  (forall x n, {R x n} + {~ R x n}) -> 
  (forall x, exists n, R x n) ->
  inhabited (forall x, {n | R x n}).
Admitted.

(** * Definitions  *)

Section continuity_principles.

(* I is for oracle's input, O is for oracle's output, A is for return type *)
(* TODO : change for Q, A, (questions/answers from oracle) and T *)
Context {I O A : Type}.

(** ** Dialogue continuity  *)

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
Definition dialogue_cont F := exists d : dialogue, F =1 deval d.

(** ** Intensional dialogue continuity  *)

(* Intensional dialogue continuity.*)
Inductive is_dialogue : ((I -> O) -> A) -> Type :=
  | teta o : is_dialogue (fun _ => o)
  | tbeta (q : I) (k : O -> (I -> O) -> A) (H : forall a, is_dialogue (k a))
      : is_dialogue (fun f => k (f q) f).

Definition int_dialogue_cont F := inhabited (is_dialogue F).

(** *** Brouwer continuity, Baire space variant of dialogue continuity  *)

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

Definition dialogue_cont_Brouwer G := exists b : Btree, G =1 beval b.

(* For fun, the nat-dependent version. *)
Inductive Btree_dep (P : nat -> Type) : nat -> Type :=
| Beta_dep : forall n, A -> Btree_dep P n
| Bbeta_dep : forall n,
    (P n -> Btree_dep P (S n)) -> Btree_dep P n.

(* TODO: move *)
(* Escardó and Oliva : conversion Btree <-> dialogue : see below
https://www.cs.bham.ac.uk//~mhe/dialogue/dialogue-to-brouwer.agda *)

(* Sterling in Agda:  Btree-continous <-> dialogue-continuous
 Currently the exact transposition in Coq does not work
 TODO : see whether we can patch this *)

(** ** Sequential continuity  *)

(* Forster et al.'s sequential continuity, for which they credit van Oosten. We skip the
   reject constructor *)
(* Forster et al.: https://arxiv.org/pdf/2307.15543.pdf *)
(* Van Oosten: https://projecteuclid.org/journals/notre-dame-journal-of-formal-logic/volume-52/issue-4/Partial-Combinatory-Algebras-of-Functions/10.1215/00294527-1499381.full *)

Inductive result : Type :=
|ask : I -> result
|output : A -> result.

(* Forster et al's extensional trees. *)
Definition ext_tree := list O -> result.

Fixpoint eval_ext_tree_aux (tau : ext_tree) (f : I -> O) (n : nat) (l : list O) : result :=
  match n, tau l with
  |S k, ask q => eval_ext_tree_aux tau f k (rcons l (f q))
  |_, _ => tau l
  end.

Definition eval_ext_tree tau f n := eval_ext_tree_aux tau f n [::].

(* TODO: as this is the one seq_cont we care about, may be change its name *)
Definition seq_cont F :=
  exists τ : ext_tree, forall f : I -> O, exists n : nat, eval_ext_tree τ f n = output (F f).

Definition wf_ext_tree (tau : ext_tree) :=
  forall f : nat -> O,  exists n o, tau (map f (iota 0 n)) = output o.

(* Conjectures: TODO: move
- seq_contW F tau -> well_founded tau when I = nat ? have a section about Baire spaces
TODO (longer term) : think about PCA results we could obtain from these definitions. In this context,
the latter conjecture might play a role, otherwise, probably not.
 *)

(** *** Sequential continuity via interrogations  *)

(* Interrogations (van Oosten) *)
Inductive interrogation (f : I -> O) : seq (I * O) -> (seq O -> result) -> Prop :=
  NoQuestions τ : interrogation f [::] τ
| Ask l τ q a : f q = a ->
                interrogation f l τ ->
                τ (map snd l) = ask q -> interrogation f (rcons l (q, a)) τ.

Definition seq_cont_interrogations F :=
  exists τ, forall f, exists qs_and_ans, interrogation f qs_and_ans τ /\ τ (map snd qs_and_ans) = output (F f).

(** *** Sequential continuity via interaction trees  *)

(* Xia et al.'s interaction trees. Connected to
of Forster et al.' sequential continuity, see below
It is dialogue + delay monad *)
CoInductive itree (E: Type -> Type) (R: Type) : Type :=
| Ret (r : R) (* computation terminating with value r *)
| Tau (t : itree E R) (* "silent" tau transition with child t *)
| Vis {O : Type} (e : E O) (k : O -> itree E R).

(*We first define a Coinductive without Tau transitions*)
CoInductive Itree :=
| ret : A -> Itree
| vis : I -> (O -> Itree) -> Itree.

(*Then we define the step-indexed evaluation of such a tree.*)
Fixpoint ieval (i : Itree) (f : I -> O) (n : nat) : result :=
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

Definition seq_cont_interaction F :=
  exists τ : Itree, forall f : I -> O, exists n : nat, ieval τ f n = output (F f).

(** ** Modulus continuity  *)

Definition modulus_at A' (F : (I -> O) -> A') (f : I -> O) (l : seq I) :=
  forall g : I -> O, map f l = map g l -> F f = F g.

Definition ex_modulus_cont A' (F : (I -> O) -> A') :=
  forall f, exists L, modulus_at F f L.

Definition modulus A' (F : (I -> O) -> A') (M : (I -> O) -> list I) :=
   forall f g,  map f (M f) = map g (M f) ->  F f = F g.

Definition comp_modulus_cont A' (F : (I -> O) -> A') :=
  exists M, modulus F M.

Definition self_modulus_cont A' (F : (I -> O) -> A') :=
  exists M,   modulus F M /\ modulus M M.

Definition uni_cont (F : (I -> O) -> A) :=
  exists l : list I, forall f : I -> O, modulus_at F f l.

End continuity_principles.

Section Intensional_Dialogue.

Variable I O A : Type.

Implicit Type (F : (I -> O) -> A).

Lemma dialogue_is_dialogue (d : @dialogue I O A) : is_dialogue (deval d).
Proof.
  induction d as [ | i k ke] ; cbn.
  - now econstructor.
  - now eapply (tbeta i ke).
Qed.

Lemma is_dialogue_to_dialogue_ext F :
  is_dialogue F -> {d : @dialogue I O A & F =1 deval d}.
Proof.
elim=> [o |q k ih1 ih2].
- by exists (eta o).
- exists (beta q (fun a => projT1 (ih2 a))) => f /=.
  by case: (ih2 (f q)) => /=.
Qed.

Theorem int_dialogue_cont_to_dialogue_cont F :
  int_dialogue_cont F -> dialogue_cont F.
Proof.
  intros [[d H] % is_dialogue_to_dialogue_ext].
  exists d. assumption.
Qed.

Variable funext : forall A B (f g : A -> B), f =1 g -> f = g.

Lemma is_dialogue_to_dialogue F : int_dialogue_cont F ->
                                  exists d : @dialogue I O A, F = deval d.
Proof.
  intros [[d H] % is_dialogue_to_dialogue_ext].
  exists d. apply funext, H.
Qed.

Lemma dialogue_cont_to_is_dialogue F :  dialogue_cont F ->
                                        int_dialogue_cont F.
Proof.
  intros [d Hd].
  apply funext in Hd ; subst. econstructor.
  now apply dialogue_is_dialogue.
Qed.

End Intensional_Dialogue.

(** * Brouwer trees  *)

Section Brouwer.

Variable O A : Type.
Local Notation Brouwer := (@Btree O A).
Local Notation dialogue := (@dialogue nat O A).

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

Lemma dialogue_cont_Brouwer_to_dialogue_cont (F : (nat -> O) -> A) :
  dialogue_cont_Brouwer F -> dialogue_cont F.
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

Section reflect.

  Variable (reflect2 : forall l1 i k l2, norm2 l1 i k l2).

  Equations reflect  (l : list O) (d : dialogue) : norm1 l d:=
    reflect l (eta a) := @normret l a ;
    reflect l (beta n q) := normask (@reflect2 l n q l).

End reflect.

Derive Subterm for list.

Fail Equations reflect2 (l1 : list O) (i : nat) (k : O -> dialogue) (l2 : list O) : norm2 l1 i k l2 by wf (length l2, k) (lexprod (lt, lt)) :=
  reflect2 l1 0 k nil := normzeronil (fun o => reflect reflect2 (cons o l1) (k o)) ;
  reflect2 l1 (S j) k nil := normsuccnil (fun o => reflect2 (cons o l1) j k nil) ;
  reflect2 l1 0 k (cons o l2) := normzerocons l2 (reflect reflect2 l1 (k o)) ;
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
  | eta o => spit o
  | beta n k => Bbeta (dialogue_to_Btree \o k) n
  end.

Lemma dialogue_to_BtreeP d alpha :
  deval d alpha = beval (dialogue_to_Btree d) alpha.
Proof.
  elim: d alpha => [o | n k ihd] alpha //=.
  rewrite -BbetaP; exact: ihd.
Qed.

Lemma dialogue_to_btree_cont (F : (nat -> O) -> A) :
  dialogue_cont F -> dialogue_cont_Brouwer F.
Proof.
  intros [d Hd].
  exists (dialogue_to_Btree d).
  intros alpha ; rewrite (Hd alpha) ; now apply dialogue_to_BtreeP.
Qed.

End Brouwer.

Section Sequential.

Context {I O A : Type}.

Implicit Type tau : @ext_tree I O A.

Lemma eval_ext_tree_ext tau1 tau2 f n :
   tau1 =1 tau2 -> eval_ext_tree tau1 f n = eval_ext_tree tau2 f n.
Proof.
  rewrite /eval_ext_tree; elim: n [::] => [|n ihn] l tauE; rewrite /= tauE //.
  case: (tau2 l) => // q; exact: ihn.
Qed.

Lemma eval_ext_tree_constant tau (f : I -> O) :
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

Fixpoint eval_ext_tree_trace_aux tau (f : I -> O) (n : nat) (l : list O) : list I :=
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
Lemma eval_ext_tree_monotone tau f n k a l :
  eval_ext_tree_aux tau f n l = output a ->
  eval_ext_tree_aux tau f (n + k) l = output a.
Proof.
  revert l ; induction n as [ | n IHn] ; cbn in * ; intros l H.
  1: now eapply eval_ext_tree_constant.
  destruct (tau l) ; [ | assumption].
  now eapply IHn.
Qed.

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

Definition ext_tree_for F tau :=
 forall f : I -> O, exists n : nat, eval_ext_tree tau f n = output (F f).

(* May be require more than wf, but also possibly non_empty and/or valid *)
Definition seq_cont_wf F :=
  exists tau, wf_ext_tree tau /\ ext_tree_for F tau.

Definition valid_ext_tree tau :=
  forall l o,  tau l = output o -> forall a, tau (rcons l a) = output o.
  
Definition seq_cont_valid (F : (I -> O) -> A) :=
  exists tau, ext_tree_for F tau /\ valid_ext_tree tau.

Lemma seq_cont_wf_to_seq_cont F :
  seq_cont_wf F -> seq_cont F.
Proof.
  firstorder.
Qed.

Lemma valid_cat (tau : ext_tree) l l' o :
  valid_ext_tree tau -> tau l = output o -> tau (l ++ l') = output o.
Proof.
  destruct l' using last_ind ; intros.
  - now rewrite cats0.
  - rewrite - rcons_cat.
    eapply H.
    now eapply IHl'.
Qed.

(** *** Dialogue continuity implies sequential continuity  *)

(** From dialogue to extensional trees **)
Fixpoint dialogue_to_ext_tree (d : @dialogue I O A) (l : seq O) : @result I A :=
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

Lemma dialogue_to_ext_tree_for d :
  ext_tree_for (deval d) (dialogue_to_ext_tree d).
Proof.
  rewrite /ext_tree_for.
  elim: d => [o | q k ihd] f.
  - by exists 0.
  - specialize (ihd (f q) f) as [n Hn].
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

Theorem dialogue_to_seq_cont  (F : (I -> O) -> A) :
  dialogue_cont F -> seq_cont F.
Proof.
  intros [d Hd]. exists (dialogue_to_ext_tree d).
  red in Hd. setoid_rewrite Hd.
  apply dialogue_to_ext_tree_for.
Qed.

(** *** Sequential continuity is equivalent to sequential continuity with interrogations *)

(* TODO *)

(** *** Sequential continuity is equivalent to interaction tree continuity  *)

CoFixpoint ext_tree_to_int_tree (e : @ext_tree I O A) (l : list O) : Itree :=
  match e l with
  | ask q => vis q (fun a => ext_tree_to_int_tree e (rcons l a))
  | output o => ret o
  end.

Lemma seq_cont_to_seq_cont_interaction (F : (I -> O) -> A) :
  seq_cont F -> seq_cont_interaction F.
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

Fixpoint int_tree_to_ext_tree (i : Itree) (l : list O) : @result I A :=
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

Lemma seq_cont_interaction_to_seq_cont (F : (I -> O) -> A) :
  seq_cont_interaction F -> seq_cont F.
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

Theorem seq_cont_iff_seq_cont_interaction (F : (I -> O) -> A) :
  seq_cont F <-> seq_cont_interaction F.
Proof.
  split.
  - apply seq_cont_to_seq_cont_interaction.
  - apply seq_cont_interaction_to_seq_cont.
Qed.

(** Results about wf and valid trees  *)

Fixpoint ext_tree_valid_aux
  (tau : @ext_tree I O A) (l l' : list O) : @result I A := 
  match l, tau l' with
  |cons a u, ask q => ext_tree_valid_aux tau u (rcons l' a)
  |_, _ => tau l'
  end.

Definition ext_tree_valid
  (tau : @ext_tree I O A) (l : list O) : @result I A :=
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
  (tau : @ext_tree I O A) (l l' : list O) i o :
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
  (tau : @ext_tree I O A) (n : nat) (f : I -> O) a :
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

Proposition seq_cont_to_seq_cont_valid F :
  seq_cont F ->
  seq_cont_valid F.
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

End Sequential.

(** ** Modulus continuity  *)

Section Modulus.

Variable I O A : Type.

(** *** Sequential continuity implies self-modulating continuity  *)

(*The trace of evaluation of an extensional tree is a modulus of continuity
 for the evaluation of that extensional tree.*)
Lemma eval_ext_tree_continuous (tau : @ext_tree I O A) n l :
  modulus (fun alpha => eval_ext_tree_aux tau alpha n l)
    (fun alpha => eval_ext_tree_trace_aux tau alpha n l).
Proof.
  elim: n l => [| n ihn] l alpha beta /= eqab //=.
  case: (tau l) eqab => // i /= [<- e].
  exact: ihn.
Qed.

Lemma eval_ext_tree_trace_continuous (tau : @ext_tree I O A) n l :
  modulus (fun alpha => eval_ext_tree_trace_aux tau alpha n l)
    (fun alpha => eval_ext_tree_trace_aux tau alpha n l).
Proof.
  elim: n l => [| n ihn] l alpha beta //= eqab.
  case: (tau l) eqab => // i [<- e]; congr (_ :: _).
  exact: ihn.
Qed.

Variable A_eq_dec : forall a1 a2 : A, {a1 = a2} + {a1 <> a2}.

(*Continuity via extensional trees implies continuity via moduli*)
Lemma continuous_ext_tree_to_modulus (F : (I -> O) -> A) : seq_cont F -> comp_modulus_cont F.
Proof.
  move=> [] tau. intros [F_eq_eval] % Sigma1_choice.
  2:{ intros x n. destruct eval_ext_tree. right. 1: congruence.
      edestruct A_eq_dec. left. f_equal. apply e. right. congruence. }
  exists (fun alpha => eval_ext_tree_trace_aux tau alpha (projT1 (F_eq_eval alpha)) nil).
intros alpha beta H.
  eapply (eval_ext_tree_output_unique (I := I)).
  + rewrite - (projT2 (F_eq_eval alpha)) ; unfold eval_ext_tree.
    now rewrite (@eval_ext_tree_continuous tau (projT1 (F_eq_eval alpha)) nil alpha beta H).
  + now eapply (projT2 (F_eq_eval beta)).
Qed.

(* In this section, we assume queries are nat, and prove that self-modulating moduli
of standard continuity imply sequential continuity.*)

Implicit Type (F : (nat -> O) -> A).
Implicit Types (tau : @ext_tree nat O A).

Definition from_pref (a_dflt : O) (l : seq O) : nat -> O := nth a_dflt l.

(*The function that goes from a modulus to an extensional tree.*)

Definition modulus_to_ext_tree (a_dflt : O) F (M : (nat -> O) -> seq nat) (l : seq O) : @result nat A :=
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

Lemma self_modulus_seq_cont F (a : O) : 
  self_modulus_cont F -> seq_cont F.
Proof.
  intros (M & MmodF & MmodM).
  exists (modulus_to_ext_tree a F M) => f.
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

(* TODO: cleanup and integrate fujiwara kawaii results *)
(* TODO: first, we need equivalent presentation of modulus for nat *)
End Modulus.

(** ** Continuity for Cantor space  *)

Section Cantor.

Variable A : Type.
Implicit Type (F : (nat -> bool) -> A).
Implicit Type (d : @dialogue nat bool A).
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
Lemma uniform_is_dialogue F : uni_cont F -> dialogue_cont F.
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

Lemma dialogue_is_uniform F : dialogue_cont F -> uni_cont F.
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
