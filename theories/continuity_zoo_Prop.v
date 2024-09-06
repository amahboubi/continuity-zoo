From mathcomp Require Import all_ssreflect.
Require Import Program Lia ConstructiveEpsilon.
From mathcomp Require Import zify.
From Equations Require Import Equations.
Require Import extra_principles.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".

Lemma Delta0_choice {X} (R : X -> nat -> Prop) :
  (forall x n, {R x n} + {~ R x n}) -> 
  (forall x, exists n, R x n) ->
  inhabited (forall x, {n | R x n}).
Proof.
  constructor => x.
  exact: constructive_indefinite_ground_description_nat.
Qed.

(** * Definitions  *)

Section continuity_principles.

(* Q is for oracle questions, A is for oracle answers, R is for return type *)
Context {Q A R : Type}.

(** ** Dialogue continuity  *)

Implicit Type (F : (Q -> A) -> R).

(* Dialogue trees are from von Oosten, but the inductive type presentation is
   probably from Escardó, TODO let's ask him.
   Inductive dialogue trees. See, e.g., Escardó
   https://www.cs.bham.ac.uk//~mhe/dialogue/dialogue-to-brouwer.agda *)
Inductive dialogue :=
  | eta : R -> dialogue
  | beta : Q -> (A -> dialogue) -> dialogue.

Implicit Type (d : dialogue).

Fixpoint deval d (f : Q -> A) : R :=
  match d with
  | eta r => r
  | beta q k => deval (k (f q)) f
  end. 

(* Escardó's eloquence *)
Definition dialogue_cont F := exists d : dialogue, F =1 deval d.

(** ** Intensional dialogue continuity  *)

Inductive is_dialogue : ((Q -> A) -> R) -> Type :=
  | teta r : is_dialogue (fun _ => r)
  | tbeta (q : Q) (k : A -> (Q -> A) -> R) (H : forall a, is_dialogue (k a))
      : is_dialogue (fun f => k (f q) f).

(* Boxing is_dialogue in Prop *)
Definition int_dialogue_cont F := inhabited (is_dialogue F).

(** *** Brouwer continuity, Baire space variant of dialogue continuity  *)

(* TODO : trace the literature for Brouwer trees
TODO: have a look at CPP24 paper by Eremondi. See also may be Coq files by F. Pottier


Jon Sterling's Brouwer trees, i.e. Escardó's dialogue normalized by giving
queries in order. *)
Inductive Btree : Type :=
  | spit : R -> Btree
  | bite : (A -> Btree) -> Btree.

Implicit Type (b : Btree).

Fixpoint beval b (f : nat -> A) : R :=
  match b with
  |spit r => r
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
|ask : Q -> result
|output : R -> result.

(* Forster et al's extensional trees. *)
Definition ext_tree := list A -> result.

Fixpoint eval_ext_tree_aux (tau : ext_tree) (f : Q -> A) (n : nat) (l : list A) : result :=
  match n, tau l with
  |S k, ask q => eval_ext_tree_aux tau f k (rcons l (f q))
  |_, _ => tau l
  end.

Definition eval_ext_tree tau f n := eval_ext_tree_aux tau f n [::].

(* TODO: as this is the one seq_cont we care about, may be change its name *)
Definition seq_cont F :=
  exists τ : ext_tree, forall f : Q -> A, exists n : nat, eval_ext_tree τ f n = output (F f).

Definition wf_ext_tree (tau : ext_tree) :=
  forall f : nat -> A,  exists n o, tau (map f (iota 0 n)) = output o.

(* Conjectures: TODO: move
- seq_contW F tau -> well_founded tau when I = nat ? have a section about Baire spaces
TODO (longer term) : think about PCA results we could obtain from these definitions. In this context,
the latter conjecture might play a role, otherwise, probably not.
 *)

(** *** Sequential continuity via interrogations  *)

(* Interrogations (van Oosten) *)
Inductive interrogation (f : Q -> A) : seq A -> (seq A -> result) -> Prop :=
  NoQuestions τ : interrogation f [::] τ
| Ask l τ q a : f q = a ->
                interrogation f l τ ->
                τ l = ask q -> interrogation f (rcons l a) τ.

Definition seq_cont_via_interrogations F :=
  exists τ, forall f, exists ans, interrogation f ans τ /\ τ ans = output (F f).

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
| ret : R -> Itree
| vis : Q -> (A -> Itree) -> Itree.

(*Then we define the step-indexed evaluation of such a tree.*)
Fixpoint ieval (i : Itree) (f : Q -> A) (n : nat) : result :=
  match n with
  | 0 => match i with
         | ret r => output r
         | vis q k => ask q
         end
  | S n => match i with
           | ret r => output r
           | vis q k => ieval (k (f q)) f n
           end
  end.

Lemma ieval_output_unique tau f n1 n2 r1 r2 :
  ieval tau f n1 = output r1 ->
  ieval tau f n2 = output r2 ->
  r1 = r2.
Proof.
  elim: n1 n2 tau => [| n1 ihn1] [| n2] /= [q | r i] // [] e1 [] e2; subst => //.
  by apply: ihn1; eauto.
Qed.

Definition seq_cont_interaction F :=
  exists τ : Itree, forall f : Q -> A, exists n : nat, ieval τ f n = output (F f).

(** ** Modulus continuity  *)

Definition modulus_at {R'} (F : (Q -> A) -> R') (f : Q -> A) (l : seq Q) :=
  forall g : Q -> A, map f l = map g l -> F f = F g.

Definition ex_modulus_cont {R'} (F : (Q -> A) -> R') :=
  forall f, exists L, modulus_at F f L.

Definition modulus {R'} (F : (Q -> A) -> R') (M : (Q -> A) -> list Q) :=
   forall f g,  map f (M f) = map g (M f) ->  F f = F g.

Definition comp_modulus_cont (F : (Q -> A) -> R) :=
  exists M, modulus F M.

Definition continuous_modulus_cont  (F : (Q -> A) -> R) :=
  exists M, modulus F M /\ ex_modulus_cont M.

Definition self_modulus_cont (F : (Q -> A) -> R) :=
  exists M,   modulus F M /\ modulus M M.

Definition uni_cont (F : (Q -> A) -> R) :=
  exists l : list Q, forall f : Q -> A, modulus_at F f l.

End continuity_principles.

Section nat_queries.

Notation Q := nat.
Variable A R : Type.

(* n first values of α *)
Definition pref (α : Q -> A) n :=
  map α (iota 0 n.+1).

Definition modulus_at_nat {R} (F : (Q -> A) -> R) α n :=
  forall β, pref α n = pref β n -> F α = F β.

Definition ex_modulus_cont_nat {R} (F : (Q -> A) -> R) :=
  forall α, exists n, modulus_at_nat F α n.

(* M is a modulus for F *)
Definition modulus_nat {R} (F : (nat -> A) -> R) M :=
  forall α β, pref α (M α) = pref β (M α) -> F α = F β. 

(* F has a continuous modulus *)
Definition continuous_modulus_cont_nat (F : (Q -> A) -> R) :=
  exists M, ex_modulus_cont_nat M /\ modulus_nat F M.

End nat_queries.

Section Intensional_Dialogue.

Variable Q A R : Type.

Implicit Type (F : (Q -> A) -> R).
Implicit Type d : @dialogue Q A R.

Lemma dialogue_is_dialogue d : is_dialogue (deval d).
Proof.
  elim: d => [| i k ke] //=; first by constructor.
  exact: (tbeta i ke).
Qed.

Lemma is_dialogue_to_dialogue_ext F :
  is_dialogue F -> {d & F =1 deval d}.
Proof.
  elim=> [o |q k ih1 ih2].
  - by exists (eta o).
  - exists (beta q (fun a => projT1 (ih2 a))) => f /=.
  by case: (ih2 (f q)) => /=.
Qed.

Theorem int_dialogue_cont_to_dialogue_cont F :
  int_dialogue_cont F -> dialogue_cont F.
Proof.
  case=> /is_dialogue_to_dialogue_ext [d H].
  by exists d.
Qed.

Variable funext : forall R B (f g : R -> B), f =1 g -> f = g.

Lemma is_dialogue_to_dialogue F : 
  int_dialogue_cont F -> exists d : @dialogue Q A R, F = deval d.
Proof.
  Proof.
  case=> /is_dialogue_to_dialogue_ext [d H].
  by exists d; exact: funext.
Qed.

Lemma dialogue_cont_to_is_dialogue F : 
  dialogue_cont F -> int_dialogue_cont F.
Proof.
  case=> d /funext ->.
  constructor.
  exact: dialogue_is_dialogue.
Qed.

End Intensional_Dialogue.

(** * Brouwer trees  *)

Section Brouwer.

(* In this section, we consider nat queries *)
Notation Q := nat.

Variables A R : Type.

Local Notation Brouwer := (@Btree A R).
Local Notation dialogue := (@dialogue nat A R).

Implicit Type (b : Brouwer) (d : dialogue) (n : nat).

(* From Brouwer trees to dialogue trees *)

Fixpoint Btree_to_dialogue_aux b n : dialogue :=
  match b with
  | spit a => eta a
  | bite k => beta n (fun q => Btree_to_dialogue_aux (k q) n.+1)
  end.

Definition Btree_to_dialogue b := Btree_to_dialogue_aux b 0.

(* Morally, n_comp is f \o (iter n S) but the next proof requires a definitional
   identity between n_comp f n.+1 S and (n_comp f n \o S), and 
   (iter n.+1 S) is defequal to S \o (iter n S) *)
Fixpoint n_comp (f : nat -> A) (n : nat) : nat -> A :=
  match n with
  | 0 => f
  | k.+1 => (n_comp f k) \o S
  end.

Lemma n_comp_n_plus f n k : 
  n_comp f n k = f (n + k).
Proof.
  elim: n k => [ |n ihn] // k /=.
  by rewrite ihn addnS.
Qed.

Lemma Btree_to_dialogueP_aux b alpha n :
  beval b (n_comp alpha n) = deval (Btree_to_dialogue_aux b n) alpha.
Proof.
  elim: b n => [ | k h] // n /=.
  by rewrite (h _ n.+1) n_comp_n_plus addn0.
Qed.

Lemma Btree_to_dialogueP b alpha :
  beval b alpha = deval (Btree_to_dialogue b) alpha.
Proof.
  exact: (Btree_to_dialogueP_aux b alpha 0).
Qed.

Lemma dialogue_cont_Brouwer_to_dialogue_cont (F : (nat -> A) -> R) :
  dialogue_cont_Brouwer F -> dialogue_cont F.
Proof.
  case=> b Hb.
  exists (Btree_to_dialogue b) => alpha.
  rewrite Hb.
  exact: Btree_to_dialogueP.
Qed.

(* From dialogue trees to Brouwer trees, in two different ways. *)

(* First, the proof by Sterling:
http://jonsterling.github.io/agda-effectful-forcing/Dialogue.Normalize.html *)


(* norm1 and norm2 specify when a dialogue tree is normalizable into a Brouwerian one *)
Inductive norm1 : list A -> dialogue -> Type :=
| normret : forall l (r : R), norm1 l (eta r)
| normask : forall l q k, norm2 l q k l -> norm1 l (beta q k)
with
  norm2 : list A -> nat -> (A -> dialogue) -> list A -> Type :=
| normzerocons : forall l k l' j,  norm1 l (k j) -> norm2 l 0 k (cons j l')
| normsucccons : forall l i k l' j, norm2 l i k l' -> norm2 l (S i) k (cons j l')
| normzeronil : forall l k,
    (forall a : A, norm1 (cons a l) (k a)) ->
    norm2 l 0 k nil
| normsuccnil : forall l i k,
    (forall a : A, norm2 (cons a l) i k nil) ->
    norm2 l (S i) k nil.


(* If a dialogue tree is normalizable, we can indeed retrieve a Brouwer tree *)
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
      exact (fun r => reify _ _ (ke r)).
    + eapply bite.
      exact (fun r => reify2 _ _ _ _ (ke r)).
Defined.

  (* rr is fun l a => reflect l (k a) *)

Fixpoint reflect2 (l1 : list A) (i : nat) (k : A -> dialogue) (l2 : list A) (rr : forall l a, norm1 l (k a)): norm2 l1 i k l2 :=
  match i, l2 with
  | 0, nil => normzeronil (fun a : A => rr (cons a l1) a) 
  |(S j), nil => normsuccnil (fun a => @reflect2 (cons a l1) j k nil rr) 
  | 0, (cons r l2) => normzerocons l2 (rr l1 r) 
  | (S j), (cons r l2) => normsucccons r (@reflect2 l1 j k l2 rr) 
  end.

(* Now all dialogue trees are normalizable *)
Fixpoint reflect1 (l : list A) (d : dialogue) : norm1 l d :=
  match d with
    |eta r => normret l r
    |beta n q => normask (@reflect2 l n q l (fun l2 a => @reflect1 l2 (q a)))
    end.  

Definition dialogue_to_Brouwer (d : dialogue) : Brouwer := reify (reflect1 (@nil A) d).

(* TODO: prove that they d and its image under dialogue_to_Brouwer evaluated the same. *)
Lemma dialogue_to_BrouwerP_sterling d alpha :
  deval d alpha = beval (dialogue_to_Brouwer d) alpha.
Proof.
rewrite /dialogue_to_Brouwer.
elim: d (@nil A) => [r | n k ihk] l //=.
Admitted.


(* This is the proof by Escardó and Oliva:
  https://www.cs.bham.ac.uk//~mhe/dialogue/dialogue-to-brouwer.agda *)

(* (follow n b) is the immediate subtree of b selected when alpha 0 = n,
   for any alpha *)
Definition follow (a : A) (b : Brouwer) : Brouwer :=
  match b with
  |spit _ => b (* reached answer *)
  |bite k => k a (* select the nth child tree *)
  end.

(* Resulting spec wrt to beval. Note the composition with successor, so
as to query alpha on n at depth n. *)
Lemma followP (alpha : nat -> A) (b : Brouwer) :
  beval b alpha = beval (follow (alpha 0) b) (alpha \o S).
Proof. by case: b. Qed.

(* (Bbeta k n) is an equivalent subtree to (k (alpha n)), constructed
   as a bite branching according to the value of (alpha n), for any alpha *)
Fixpoint Bbeta (k : A -> Brouwer) (n : nat) : Brouwer :=
  match n with
  |0 => bite (fun m => ((follow m) \o k) m)
  |n.+1 => bite (fun m => Bbeta ((follow m) \o k) n)
end.

Lemma BbetaP (alpha : nat -> A) n k :
  beval (k (alpha n)) alpha = beval (Bbeta k n) alpha.
Proof.
elim: n k alpha => [| n ihn] k alpha /=.
- by rewrite -followP.
- by rewrite -ihn -followP.
Qed.

(* Conversion from dialogue to Brouwer trees *)
Fixpoint dialogue_to_Btree (d : dialogue) : Brouwer :=
  match d with
  | eta r=> spit r
  | beta n k => Bbeta (dialogue_to_Btree \o k) n
  end.

Lemma dialogue_to_BtreeP d alpha :
  deval d alpha = beval (dialogue_to_Btree d) alpha.
Proof.
  elim: d alpha => [o | n k ihd] alpha //=.
  rewrite -BbetaP; exact: ihd.
Qed.

Lemma dialogue_to_btree_cont (F : (nat -> A) -> R) :
  dialogue_cont F -> dialogue_cont_Brouwer F.
Proof.
  intros [d Hd].
  exists (dialogue_to_Btree d).
  intros alpha ; rewrite (Hd alpha) ; now apply dialogue_to_BtreeP.
Qed.

End Brouwer.

Section Sequential.

Context {Q A R : Type}.

Implicit Type tau : @ext_tree Q A R.

Lemma eval_ext_tree_ext tau1 tau2 f n :
   tau1 =1 tau2 -> eval_ext_tree tau1 f n = eval_ext_tree tau2 f n.
Proof.
  rewrite /eval_ext_tree; elim: n [::] => [|n ihn] l tauE; rewrite /= tauE //.
  case: (tau2 l) => // q; exact: ihn.
Qed.

Lemma eval_ext_tree_constant tau (f : Q -> A) :
  forall n a l, tau l = output a -> eval_ext_tree_aux tau f n l = output a.
Proof.
  elim=> [| n hn] a l h //=.
  by rewrite h.
Qed.

Lemma eval_ext_tree_output_unique tau f l n1 n2 o1 o2 :
  eval_ext_tree_aux tau f n1 l = output o1 ->
  eval_ext_tree_aux tau f n2 l = output o2 ->
  o1 = o2.
Proof.
  elim: n1 n2 l=> [| n1 ihn1] [| n2] l /=.
  1, 2: by move=> -> [].
  1, 2: case: (tau l) => [q // | r -> [] //]; exact: ihn1.
Qed.

(* Sequence of questions asked while step-index evaluating tau via f at depth n *)

Fixpoint eval_ext_tree_trace_aux tau (f : Q -> A) (n : nat) (l : list A) : list Q :=
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
exact: eval_ext_tree_map_aux.
Qed.

Lemma eval_ext_tree_monotone tau f n k a l :
  eval_ext_tree_aux tau f n l = output a ->
  eval_ext_tree_aux tau f (n + k) l = output a.
Proof.
  elim: n l => [ |n ihn] l /=.
  - by apply: eval_ext_tree_constant.
  - case: (tau l) => // q; exact: ihn.
Qed.

Lemma eval_ext_tree_trace_monotone (tau : ext_tree) f n k a l :
  eval_ext_tree_aux tau f n l = output a ->
  eval_ext_tree_trace_aux tau f n l = eval_ext_tree_trace_aux tau f (n + k) l.
Proof.
  elim: n l => [ |n ihn] l /=.
  - by case: k => [| k] //= ->.
  - by case: (tau l) => // q h; rewrite ihn. 
Qed.


Lemma eval_ext_tree_trace_size_eval (tau : ext_tree) f n a l :
  eval_ext_tree_aux tau f n l = output a ->
  eval_ext_tree_aux tau f (size (eval_ext_tree_trace_aux tau f n l)) l = output a.
Proof.
  elim: n l => [ | n ihn] l //=.
  case e: (tau l) => [q | r /= <- //].
  by rewrite /= e; apply: ihn.
Qed.

Lemma eval_ext_tree_trace_size_eval_trace (tau : ext_tree) f n a l :
  eval_ext_tree_aux tau f n l = output a ->
  eval_ext_tree_trace_aux tau f n l =
    eval_ext_tree_trace_aux tau f (size (eval_ext_tree_trace_aux tau f n l)) l.
Proof.
  elim: n l => [ | n ihn] l //=.
  case e: (tau l) => [q | r /= <- //] /= h.
  by rewrite e -ihn.
Qed.

Definition ext_tree_for F tau :=
 forall f : Q -> A, exists n : nat, eval_ext_tree tau f n = output (F f).

(* May be require more than wf, but also possibly non_empty and/or valid *)
Definition seq_cont_wf F :=
  exists tau, wf_ext_tree tau /\ ext_tree_for F tau.

Definition valid_ext_tree tau :=
  forall l r, tau l = output r -> forall a, tau (rcons l a) = output r.
  
Definition seq_cont_valid (F : (Q -> A) -> R) :=
  exists tau, ext_tree_for F tau /\ valid_ext_tree tau.

Lemma seq_cont_wf_to_seq_cont F :
  seq_cont_wf F -> seq_cont F.
Proof.
  firstorder.
Qed.

Lemma valid_cat (tau : ext_tree) l l' r :
  valid_ext_tree tau -> tau l = output r -> tau (l ++ l') = output r.
Proof.
  move=> vtau.
  elim/last_ind: l' => [| l' s ihl'] ho; first by rewrite -ho cats0.
  rewrite -rcons_cat.
  apply: vtau. 
  exact: ihl'.
Qed.

(** *** Dialogue continuity implies sequential continuity  *)

(** From dialogue to extensional trees **)

Fixpoint dialogue_to_ext_tree d (l : seq A) : @result Q R :=
  match d with
   | eta r => output r
   | beta q k => if l is a :: l then dialogue_to_ext_tree (k a) l else ask q
  end.
  
(* Dialogue continuity implies any form of sequential continuity *)

Lemma dialogue_to_ext_tree_wf d : 
  wf_ext_tree (dialogue_to_ext_tree d).
Proof.
  elim: d => [r | n k ihd] f.
  - by exists 0; exists r.
  - have [m [r mP]] := ihd (f 0) (f \o S).
    exists m.+1; exists r.
    suff -> : [seq f i | i <- iota 0 m.+1] =
                                f 0 :: [seq (f \o succn) i | i <- iota 0 m] by [].
    by rewrite /=; congr (_ :: _); rewrite -[1]/(1 + 0) iotaDl -map_comp.
Qed.

Arguments eval_ext_tree {Q A R} tau f /.

Lemma dialogue_to_ext_tree_for d :
  ext_tree_for (deval d) (dialogue_to_ext_tree d).
Proof.
  elim: d => [o | q k ihd] f.
  - by exists 0.
  - have {ihd} [n hn] := ihd (f q) f.
    exists n.+1 => /=.
    move: hn; rewrite /eval_ext_tree.
    elim: n (@nil A) => [| n ihn] l //=.
    case: (dialogue_to_ext_tree (k (f q)) l) => * //.
    exact: ihn.
Qed.

Theorem dialogue_to_seq_cont  (F : (Q -> A) -> R) :
  dialogue_cont F -> seq_cont F.
Proof.
  case=> d hd.  
  exists (dialogue_to_ext_tree d) => f. 
  rewrite hd.
  exact: dialogue_to_ext_tree_for. 
Qed.

(** *** Sequential continuity is equivalent to sequential continuity with interrogations *)

Implicit Type f : Q -> A.
Implicit Type τ : @ext_tree Q A R.

Lemma inversion_ask f l τ a : 
  interrogation f (rcons l a) τ -> 
  exists q,
  [/\ f q = a, τ l = ask q & interrogation f l τ].
Proof.
move=> h.
inversion h as [tau e1 e2|ll tau qq a2 <- hi eask congr1 etau] => {h}.
- by move: (f_equal size e1); rewrite size_rcons. 
- have {congr1} [el ea] := rcons_inj congr1.
  by subst; exists qq.
Qed.

Lemma interrogation_plus τ f n ans a :
  interrogation f ans (fun l => τ (a ++ l)) ->
  eval_ext_tree_aux τ f (size ans + n) a =
    eval_ext_tree_aux τ f n (a ++ ans).
Proof.
   elim/last_ind: ans a n => [| l1 a1 ihl] l2 n.
   - by rewrite cats0.
   - case/inversion_ask => [q [<- e2 hi]].
     rewrite size_rcons -[_ + n]addnS.
     have /(_ n.+1) -> := ihl _ _ hi.
     by rewrite /= e2 rcons_cat.
Qed.


Lemma interrogation_cons q l τ (f : Q -> A) :
  τ nil = ask q ->
  interrogation f l (fun l => τ (f q :: l)) ->
  interrogation f (f q :: l) τ.
Proof.
  move=> e; elim/last_ind: l => [_ | l qq ihl].
  - rewrite -[[:: f q]]/(rcons [::] (f q)). 
    by apply: (Ask _ _ e) => //; constructor.
  - case/inversion_ask => [qqq [<- e2 hi]].
    rewrite -rcons_cons.
    apply: (Ask _ _ e2) => //; exact: ihl.
Qed.

(** HERE **)

Lemma interrogation_ext τ τ' a f :
  τ =1 τ' ->
  interrogation f a τ -> interrogation f a τ'.
Proof.
  intro; induction 1; econstructor; eauto; congruence.
Qed.


Lemma interrogation_app a1 a2 τ f :
  interrogation f a1 τ ->
  interrogation f a2 (fun l => τ (a1 ++ l)) ->
  interrogation f (a1 ++ a2) τ.
Proof.
  induction 1 in a2 |- *; cbn.
  - eauto.
  - intros. subst. rewrite cat_rcons.
    eapply IHinterrogation.
    eapply interrogation_cons.
    + by rewrite cats0.
    + eapply interrogation_ext; eauto => ?. cbn. by rewrite cat_rcons.
Qed.

Hint Resolve NoQuestions.

Lemma eval_ext_tree_to_interrogation τ f n r :
  eval_ext_tree τ f n = output r ->
  exists ans : list A, [/\ size ans <= n, interrogation f ans τ & τ ans = output r].
Proof.
rewrite /eval_ext_tree -[τ in X in _ -> X]/((fun l => τ ([::] ++ l))).
elim: n (@nil A) => [|n ihn] l /=.
- by exists [::]; split => //; rewrite cats0.
- case e : (τ l) => [q | r'] /=. 
  + case/ihn => ans [hs hi ha]; exists (f q :: ans).
    rewrite -cat_rcons; split => //.
    apply: interrogation_cons; first by rewrite cats0. 
    apply: interrogation_ext hi => ?. by rewrite cat_rcons.
  + case=> ero. subst.
    have : eval_ext_tree_aux τ f n l = output r by exact: eval_ext_tree_constant.
    case/ihn=> ans [].
    firstorder.
Qed.

Lemma interrogation_equiv_eval_ext_tree τ f r :
    (exists (ans : list A), interrogation f ans τ /\ τ ans = output r) <-> 
    (exists n : nat, eval_ext_tree τ f n = output r).
Proof.
  split.
  - case=> ans [Hi Hout].
    exists (size ans).+1.
    by rewrite /eval_ext_tree -addn1 interrogation_plus //= Hout.
  - case=> n /eval_ext_tree_to_interrogation. firstorder.
Qed.

Lemma continuous_via_interrogations_iff (F : (Q -> A) -> R) :
  seq_cont F <-> seq_cont_via_interrogations F.
Proof.
  split.
  - intros [τ H]. exists τ. intros f.
    eapply interrogation_equiv_eval_ext_tree. eapply H.
  - intros [τ H]. exists τ. intros f.
    eapply interrogation_equiv_eval_ext_tree. eapply H.
Qed.

(** *** Sequential continuity is equivalent to interaction tree continuity  *)

CoFixpoint ext_tree_to_int_tree (e : @ext_tree Q A R) (l : list A) : Itree :=
  match e l with
  | ask q => vis q (fun a => ext_tree_to_int_tree e (rcons l a))
  | output r => ret r
  end.

Lemma seq_cont_to_seq_cont_interaction (F : (Q -> A) -> R) :
  seq_cont F -> seq_cont_interaction F.
Proof.
  case=> e He.
  exists (ext_tree_to_int_tree e nil) => f.
  have {He} [n <-] := He f.
  exists n. rewrite /eval_ext_tree.
  by elim: n (@nil A) e => [| n ihn] l e /=; case: (e l).
Qed.

Fixpoint int_tree_to_ext_tree (i : Itree) (l : list A) : @result Q R :=
  match l with
  | nil => match i with
           | vis q k => ask q
           | ret r => output r
           end
  | cons a l' => match i with
                 | vis q k => int_tree_to_ext_tree (k a) l'
                 | ret r => output r
                 end
  end.

Lemma int_tree_to_ext_tree_one_step : forall n q k f l,
    eval_ext_tree_aux (int_tree_to_ext_tree (vis q k)) f n ((f q) :: l) =
      eval_ext_tree_aux (int_tree_to_ext_tree (k (f q))) f n l.
Proof.
elim=> [| n ihn] // q k f l /=.
by case: (int_tree_to_ext_tree _ _).
Qed.

Lemma seq_cont_interaction_to_seq_cont (F : (Q -> A) -> R) :
  seq_cont_interaction F -> seq_cont F.
Proof.
  case=> i hi.
  exists (int_tree_to_ext_tree i) => f.
  have {hi} [n <-] := hi f.
  exists n.
  elim: n i => [| n ihn] [r | q] // i.
  rewrite [LHS]int_tree_to_ext_tree_one_step.
  exact: ihn.
Qed.

Theorem seq_cont_iff_seq_cont_interaction (F : (Q -> A) -> R) :
  seq_cont F <-> seq_cont_interaction F.
Proof.
  split.
  - exact: seq_cont_to_seq_cont_interaction.
  - exact: seq_cont_interaction_to_seq_cont.
Qed.

(** Results about wf and valid trees  *)

Fixpoint ext_tree_valid_aux tau (l l' : list A) : @result Q R := 
  match l, tau l' with
  |cons a u, ask q => ext_tree_valid_aux tau u (rcons l' a)
  |_, _ => tau l'
  end.

Definition ext_tree_valid tau (l : list A) : @result Q R :=
  ext_tree_valid_aux tau l nil.

Lemma ext_tree_valid_valid tau l l' l'' a:
  ext_tree_valid_aux tau l l' = output a ->
  ext_tree_valid_aux tau (l ++ l'') l' = output a.
Proof.
  elim: l l' l'' => [| u ans ihl] /= l' l''.
  - by case: l'' =>> //= ->.
  - by case e : (tau l') => [q | r] // /ihl.
Qed.

Lemma ext_tree_valid_eqtau_ask tau (l l' : list A) q a :
  ext_tree_valid_aux tau l l' = ask q ->
  ext_tree_valid_aux tau (rcons l a) l' = tau (rcons (l' ++ l) a).
Proof.
  elim: l l' => [| a' ans ihl] /= l' e.
  - by rewrite e cats0.
  - case: (tau l') e => [q' | a''] //= /ihl.
    by rewrite -cat_rcons.
Qed.

Lemma eval_ext_tree_valid_eqtau tau (n : nat) (f : Q -> A) a :
  eval_ext_tree_aux tau f n nil = output a ->
  eval_ext_tree_aux (ext_tree_valid tau) f n nil = output a.
Proof.
have: forall j, ext_tree_valid tau (take j nil) = tau (take j nil) by [].
elim: n (@nil A) => [| n ihn] l h /= e.
- by rewrite -[l]take_size [LHS]h take_size.
- rewrite -[l]take_size h take_size.
  case e: (tau l) e => [q | r] //.
  apply: ihn=> k.
  case: (leqP (size l).+1 k) => hsize.
  + rewrite take_oversize ?size_rcons //.
    suff /ext_tree_valid_eqtau_ask <- : ext_tree_valid_aux tau l [::] = ask q by [].
    by rewrite -[l]take_size [LHS]h take_size.
  + by rewrite -cats1 takel_cat.
Qed.

Proposition seq_cont_to_seq_cont_valid F :
  seq_cont F -> seq_cont_valid F.
Proof.
case=> tau htau.
exists (ext_tree_valid tau); split.
- move=> alpha.
  have [n hn] := htau alpha.
  exists n.
  exact: eval_ext_tree_valid_eqtau.
- move=> l r e a.
  rewrite /ext_tree_valid -cats1.
  exact: ext_tree_valid_valid.
Qed.

End Sequential.

(** ** Modulus continuity  *)

Section Modulus.

Variable Q A R : Type.

(** *** Sequential continuity implies computable modulus continuity  *)

(*The trace of evaluation of an extensional tree is a modulus of continuity
 for the evaluation of that extensional tree.*)
Lemma eval_ext_tree_continuous (tau : @ext_tree Q A R) n l :
  modulus (fun alpha => eval_ext_tree_aux tau alpha n l)
    (fun alpha => eval_ext_tree_trace_aux tau alpha n l).
Proof.
  elim: n l => [| n ihn] l alpha beta /= eqab //=.
  case: (tau l) eqab => // i /= [<- e].
  exact: ihn.
Qed.

Lemma eval_ext_tree_trace_continuous (tau : @ext_tree Q A R) n l :
  modulus (fun alpha => eval_ext_tree_trace_aux tau alpha n l)
    (fun alpha => eval_ext_tree_trace_aux tau alpha n l).
Proof.
  elim: n l => [| n ihn] l alpha beta //= eqab.
  case: (tau l) eqab => // i [<- e]; congr (_ :: _).
  exact: ihn.
Qed.

(*Continuity via extensional trees implies continuity via moduli*)
Lemma seq_cont_to_self_modulus_cont (F : (Q -> A) -> R) : seq_cont F -> self_modulus_cont F.
Proof.
  move=> [] tau. intros [F_eq_eval] % Delta0_choice.
  2:{ intros f n. destruct eval_ext_tree eqn:E. 1: right. 1: congruence.
      left. destruct (p f).
      f_equal. eapply eval_ext_tree_output_unique; eauto.
  }
  exists (fun alpha => eval_ext_tree_trace_aux tau alpha (projT1 (F_eq_eval alpha)) nil).
  split.
  - intros alpha beta H.
    eapply (eval_ext_tree_output_unique (Q := Q)).
    + rewrite - (projT2 (F_eq_eval alpha)) ; unfold eval_ext_tree.
      now rewrite (@eval_ext_tree_continuous tau (projT1 (F_eq_eval alpha)) nil alpha beta H).
    + now eapply (projT2 (F_eq_eval beta)).
  - intros f g.
    destruct F_eq_eval as [n Hn], F_eq_eval as [m Hm]; cbn in *.
    revert m g Hm Hn.
    unfold eval_ext_tree.
    generalize (@nil A).
    clear. induction n; cbn; intros.
    + destruct m; cbn. 1: reflexivity. rewrite Hn. reflexivity.
    + destruct m; cbn in *.
      * destruct tau eqn:E. 1: exfalso; congruence.
        reflexivity.
      * destruct tau eqn:E. 2: reflexivity. cbn in H.
        inversion H. rewrite H1 in Hn, H2 |- *.
        f_equal. eapply IHn; eauto.
Qed.

(** *** Special case: If Q = nat then moduli can be nat *)

Lemma modulus_at_to_modulus_at_nat (F : (nat -> A) -> R) f l :
  modulus_at F f l -> modulus_at_nat F f (\max_(i <- l) i).
Proof.
  intros H g Hg. eapply H.
  rewrite <- eq_in_map.
  intros x Hx.
  eapply eq_in_map in Hg. eapply Hg.
  rewrite mem_iota ltnS leq_bigmax_seq => //.
Qed.

Lemma modulus_at_nat_to_modulus_at (F : (nat -> A) -> R) f n :
  modulus_at_nat F f n -> modulus_at F f (iota 0 n.+1).
Proof.
  intros H g Hg. eapply H.
  unfold pref.
  rewrite <- eq_in_map.
  intros x Hx.
  eapply eq_in_map in Hg. now eapply Hg.
Qed.

(** *** Self-modulating continuity implies sequential continuity for Q = nat *)

(* In this section, we assume queries are nat, and prove that self-modulating moduli
of standard continuity imply sequential continuity.*)

Implicit Type (F : (nat -> A) -> R).
Implicit Types (tau : @ext_tree nat A R).

Definition from_pref (a_dflt : A) (l : seq A) : nat -> A := nth a_dflt l.

(*The function that goes from a modulus to an extensional tree.*)

Definition modulus_to_ext_tree F (M : (nat -> A) -> seq nat) (l : seq A) :
  @result nat R :=
  match l with
  | nil => ask 0
  | x :: q => let g := from_pref x l in
              if \max_(i <- M g) i < size l
              then output (F g)
              else ask (size l)
  end.

Lemma eval_modulus_to_ext F M f m :  modulus M M ->
                                       eval_ext_tree_trace (modulus_to_ext_tree F M) f m =
                                         iota 0 (minn m (\max_(i <- M f) i).+1).
Proof.
  move=> MmodM; rewrite /eval_ext_tree_trace.
  suff aux : forall i,
      i <= (\max_(j <- M f) j).+1 ->
      iota 0 i ++ eval_ext_tree_trace_aux (modulus_to_ext_tree F M) f m (map f (iota 0 i)) =
        iota 0 (minn (i + m) (\max_(j <- M f) j).+1).
  1: by apply:  (aux 0).
  elim: m=> [|m ihm] i /= hi1.
  1: by rewrite cats0 addn0; move/minn_idPl: hi1 => ->.
  rewrite /modulus_to_ext_tree size_map size_iota.
  destruct i ; [now apply (ihm 1) | ].
  case: ifP=> hi2.
  - have eM : M (from_pref (f 0) [seq f i | i <- iota 0 i.+1]) = M f.
    { apply: MmodM.
      apply/eq_in_map=> x hx.
      have hi : x < i.+1 by apply: leq_ltn_trans hi2; exact: leq_bigmax_seq.
      by rewrite /from_pref (nth_map 0)  ?size_iota // nth_iota // add0n.
    }
    suff -> : i.+1 = (\max_(j <- M f) j).+1.
    + have /minn_idPr-> : (\max_(j <- M f) j).+1 <= (\max_(j <- M f) j).+1 + m.+1 by rewrite leq_addr.
      by rewrite cats0.
    + by move: hi1; rewrite -eM leq_eqVlt ltnNge hi2 orbF; move/eqP.
  - rewrite -/(modulus_to_ext_tree F M) -cat_rcons.
    have -> : rcons (iota 0 i.+1) i.+1 = iota 0 (i.+2).
    + rewrite -cats1 ; change [:: i.+1] with (iota i.+1 1).
      now rewrite - iotaD addn1.
    + have -> : rcons [seq f i | i <- iota 0 i.+1] (f i.+1) = [seq f i | i <- iota 0 i.+2].
      * rewrite -cats1 ; change [:: f i.+1] with (map f (iota i.+1 1)).
        now rewrite - map_cat - iotaD addn1.
      * rewrite addnS -addSn; apply: ihm.
        move: hi1; rewrite leq_eqVlt; case/orP=> // /eqP ei.
        suff : \max_(i <- M (from_pref (f 0) [seq f i | i <- iota 0 i.+1])) i < i.+1 by rewrite hi2.
        suff <- : M f = M (from_pref (f 0) [seq f i0 | i0 <- iota 0 i.+1]) by rewrite ei.
        apply: MmodM; apply/eq_in_map=> x hx.
        have hi : x < i.+1 by rewrite ei ltnS; apply: leq_bigmax_seq.
        rewrite /from_pref (nth_map 0)  ?size_iota // nth_iota // add0n.
Qed.

Lemma self_modulus_seq_cont F : 
  self_modulus_cont F -> seq_cont F.
Proof.
  intros (M & MmodF & MmodM).
  exists (modulus_to_ext_tree F M) => f.
  pose m := \max_(i <- M f) i.
  exists m.+1.
  rewrite eval_ext_tree_map.
  have -> := eval_modulus_to_ext F f m.+1 MmodM.
  rewrite /modulus_to_ext_tree size_map size_iota.
  have eqM : M f = M (from_pref (f 0) [seq f i | i <- iota 0 m.+1]).
  { apply: MmodM.
    set l := M _.
    apply/eq_in_map=> x hx.
    have {hx} hx : x < m.+1 by rewrite ltnS /m; apply: leq_bigmax_seq.
    by rewrite /from_pref (nth_map 0) ?size_iota // nth_iota. }
  rewrite minnSS.
  change ((if
       \max_(i <- M (from_pref (f 0) [seq f i | i <- iota 0 (minn m (\max_(i <- M f) i)).+1])) i <
       (minn m (\max_(i <- M f) i)).+1
      then output (F (from_pref (f 0) [seq f i | i <- iota 0 (minn m (\max_(i <- M f) i)).+1]))
      else ask (minn m (\max_(i <- M f) i)).+1) = output (F f)).
  rewrite minnn -eqM leqnn; congr output; apply: MmodF.
  apply/eq_in_map=> x hx.
  have {hx} hx : x < m.+1 by rewrite ltnS /m eqM; apply: leq_bigmax_seq.
  by rewrite /from_pref; rewrite (nth_map 0) ?size_iota // nth_iota // size_iota.
Qed.

End Modulus.

(** ** Sequential continuity is equivalent to self-modulating continuity when Q = nat *)

(* Analogues of eqseq_cons for non eqTypes *)
Lemma eq_cat {T : Type} (s1 s2 s3 s4 : seq T) :
  size s1 = size s2 -> (s1 ++ s3 = s2 ++ s4) -> (s1 = s2) /\ (s3 = s4).
Proof.
  elim: s1 s2 => [|x1 s1 IHs] [|x2 s2] //= [sz12].
  by case=> -> /(IHs _ sz12) [-> ->].
Qed.

Lemma eq_catl {T : Type} (s1 s2 s3 s4 : seq T) :
  size s1 = size s2 -> (s1 ++ s3 = s2 ++ s4) -> s1 = s2.
Proof. by move=> eqs12 /eq_cat; move/(_ eqs12) => []. Qed.

Lemma eq_catr {T : Type} (s1 s2 s3 s4 : seq T) :
  size s1 = size s2 -> (s1 ++ s3 = s2 ++ s4) -> s3 = s4.
Proof. by move=> eqs12 /eq_cat; move/(_ eqs12) => []. Qed.

Section sec.

Notation Q := nat.
Variables A R : Type.

Implicit Type Y : (Q -> A) -> R.
Implicit Types α β : Q -> A.
Implicit Types n : nat.
Implicit Types γ : list A -> bool.
Implicit Types s : list A.

Lemma pref_le_eq n m α β :
  n <= m ->
  pref α m = pref β m ->
  pref α n = pref β n.

Proof.
  rewrite /pref => lenm.
  have -> : m.+1 = n.+1 + (m.+1 - n.+1) by lia.
  rewrite iotaD !map_cat.
  apply: eq_catl.
  by rewrite !size_map size_iota.
Qed.

Definition padded_seq (s : seq A) (a : A) :=
  nth a s.

(* n first values of α, then deflt value a. Importantly defined in terms of
   pref, so as to avoid extensionality issues later on under a modulus *)
Definition padded_prefix α n :=
  padded_seq (pref α n) (α 0).

(* pref and the prefix of a padded prefix coincide*)
Lemma pref_padded_prefix α n k :
  k <= n -> pref (padded_prefix α n) k = pref α k.
Proof.
  move=> lekn.
  apply: (@eq_from_nth _ (α 0)); rewrite /pref !size_map !size_iota // /padded_prefix.
  move=> i ltin.
  congr (nth _ _ i).
  apply/eq_in_map=> j; rewrite mem_iota add0n /padded_seq => /andP[_ hj].
  rewrite (nth_map 0) ?nth_iota ?add0n ?size_iota //; lia.
Qed.



(* Name from Yannick + Fujiwara - Kawai *)
Lemma T14 Y :
  continuous_modulus_cont_nat Y -> exists N, modulus_nat Y N /\ modulus_nat N N.
Proof.
(* In a classical setting we would take 
M α := min {k | forall β, pref α k = pref β k -> Y α = Y β}
The following constructive proof replaces this minimum by an
observable variant:
M α := min {N (padded_prefix α n) | N (padded_prefix α n) < n}
or, rather the simpler
M α := min {n | N (padded_prefix α n) < n}
 *)
case=> N [ContN ModYN].
pose good_pref α n :=  N (padded_prefix α n) <= n.
(* This is the crux of the proof *)
have ex_good_pref α : exists n, good_pref α n.
{  case: (ContN α) => [n Hn].
  exists (N α + n.+1). 
  rewrite /good_pref -Hn; first by lia. 
  rewrite pref_padded_prefix //; lia. }
have Ygood_pref α n : good_pref α n -> Y (padded_prefix α n) = Y α.
{ move=> gpn.
  apply: ModYN.
  exact: pref_padded_prefix. }
have good_prefP α n : good_pref α n -> forall β, pref α n = pref β n -> Y α = Y β.
{ move=> gpn β eqpref.
  rewrite -(Ygood_pref _ _ gpn).
  apply: ModYN.
  rewrite pref_padded_prefix //. 
  exact: (pref_le_eq _ eqpref). }
(* The definition of M uses the constructive epsilon *)
pose M α : nat := ex_minn (ex_good_pref α).
have good_prefM α : good_pref α (M α) by rewrite /M; case: ex_minnP=> *.
have minM α n : good_pref α n -> (M α) <= n.
{ rewrite /M; case: ex_minnP=> m _ h; exact: h. }
have ModYM : modulus_nat Y M.
{ by move=> α β; apply: good_prefP. }
suff ModMM : modulus_nat M M by exists M; split.
move=> α β eq_pref.
(* Here is where extensionality matters *)                               
have eq_padded k : k <= M α -> padded_prefix α k = padded_prefix β k.
{ move=> lekMα.
  suff e : pref α k = pref β k.
  { rewrite /padded_prefix e.
    assert (α 0 = β 0) as Heq by (cbn in * ; now inversion e).
    now rewrite Heq. }
  exact: (pref_le_eq lekMα). }
have leMβα : M β <= M α.
{ apply: minM.
  rewrite /good_pref -eq_padded //; exact: good_prefM. }
suff leMαβ : M α <= M β by apply/eqP; rewrite eqn_leq leMαβ.
apply: minM.
rewrite /good_pref eq_padded //. 
exact: good_prefM.
Qed.

Lemma T41 Y :
  (exists N, modulus_nat Y N /\ modulus_nat N N) -> continuous_modulus_cont_nat Y.
Proof.
  case=> N [HN HNY]; exists N; split=> // α.
  exists (N α) => *; exact: HNY.
Qed.

Theorem seq_cont_equiv_self_modulus_cont (F : (Q -> A) -> R) :
  seq_cont F <-> continuous_modulus_cont F.
Proof.
  split.
  - intros contF. eapply seq_cont_to_self_modulus_cont in contF as (N & HF & HN). 
    eexists; split; eauto.
    intros f. exists (N f). red in HN. refine (HN f).
  - intros (N' & HF' & HN'). eapply self_modulus_seq_cont.
    edestruct T14 as (N & HF & HN).
    + eexists. split.
      2:{ intros f. eapply modulus_at_to_modulus_at_nat. exact (HF' f). }
      intros f. destruct (HN' f) as [l Hl].
      exists ( \max_(i <- l) i).
      eapply modulus_at_to_modulus_at_nat.
      intros g. specialize (Hl g). intros H.
      rewrite Hl => //.
    + eexists. split.
      * intros f. eapply modulus_at_nat_to_modulus_at. exact (HF f).
      * intros f g H. specialize (HN f g).
        rewrite HN => //.
Qed.

End sec.

(** ** Continuity for Cantor space  *)

Section Cantor.

Variable R : Type.
Implicit Type (F : (nat -> bool) -> R).
Implicit Type (d : @dialogue nat bool R).
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
  | cons i q => beta i (fun r => list_to_dialogue F q ((i, r) :: acc))
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
    1: exact Hfgl.
    now do 2 erewrite size_map.
  }
  { apply ke.
    do 2 erewrite map_cat in Hfgl.
    apply (f_equal (drop (size [seq f i | i <- dialogue_to_list (k true)]))) in Hfgl.
    do 2 erewrite drop_size_cat in Hfgl ; try reflexivity.
    1: exact Hfgl.
    now do 2 erewrite size_map.
  }
Qed.

(* TODO : following Andrej's comments, say something about compactness, this could be generalized to
   more compacts*)

End Cantor.
