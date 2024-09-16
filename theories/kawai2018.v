From mathcomp Require Import all_ssreflect.
Require Import Program.
From Equations Require Import Equations.
Require Import extra_principles.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Require Import Lia.

Require Import continuity_zoo_Prop.
Require Import Brouwer_ext.
Require Import BI.


Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".

(** Kawai's "Principles of bar induction and continuity on Baire space" has the notions of
    neighborhood function and Brouwer operation, and derives continuity notions based on them.
    Brouwer operations are an inductive _predicate_ on neighborhood functions.

Result 1: a neighborhood function is just a valid Brouwer extensional tree,
       thus neigh_cont is equivalent to Bseq_cont_valid. We prove this in 
            Theorem neigh_cont_Bseq_cont.

Result 2: a Brouwer operation can be turned into the existence of a Brouwer tree 
       (through the Acc trick used in extra_principles.v). 
       Thus, Bneigh_cont is equivalent to dialogue_cont_Brouwer.
       We prove this in
            Theorem Bneigh_cont_equiv_dialogue_cont_Brouwer.

       The underlying insight is: The existence of a Brouwer tree is equivalent to 
       the existence of an extensional tree that is inductively barred. 
       This equivalence only works in the Brouwer / Baire case, not in general.

 *)

(*We first define neighborhood functions and what it means to be
 continuous with respect to them.*)

Variables A R : Type.

Definition neighborhoodfunction (γ : list A -> option R) :=
  (forall α : nat -> A, exists n : nat, γ (map α (iota 0 n)) <> None) /\
    forall a b : list A, γ a <> None -> γ a = γ (a ++ b).


Definition neigh_realises γ (F : (nat -> A) -> R) :=
    forall α, exists m, γ (map α (iota 0 m)) = Some (F α) /\
              forall z, z < m -> γ (map α (iota 0 z)) = None.

Definition neigh_cont F :=
  exists γ, neighborhoodfunction γ /\ neigh_realises γ F.


(*In fact, we do not need the second hypothesis of neigh_realises in neigh_cont, 
  as it can be retrieved from neighborhoodfunction gamma.*)
 
Lemma useless_hypothesis (tau : list A -> option R) F :
  neighborhoodfunction tau ->
  (forall alpha, exists m, tau (map alpha (iota 0 m)) = Some (F alpha)) ->
  neigh_cont F.
Proof.
  intros Hneigh Hrel ; exists tau ; split ; [auto | ].
  intros alpha ; specialize (Hrel alpha) as [m Hm].
  unshelve eexists ; [ | split].
  - clear Hm.
    refine ((fix K (m : nat) :=
               match m with
               | 0 => 0
               | S k => match tau [seq alpha i | i <- iota 0 k] with
                        | None => S k
                        | Some _ => K k
                        end
               end) m).
  - revert Hm ; induction m as [ | m IHm] ; intros ; auto.
    remember (tau [seq alpha i | i <- iota 0 m]) as r ; destruct r as [r | ] ; [ | auto].
    apply IHm ; rewrite Heqr - Hm - addn1 iotaD map_cat.
    apply Hneigh ; rewrite - Heqr ; intros H ; now inversion H.
  - revert Hm ; induction m as [ | m IHm] ; intros Hm z Hz ; [now inversion Hz | ].
    remember (tau [seq alpha i | i <- iota 0 m]) as r ; destruct r as [r | ] ; [ | auto].
    + apply IHm ; auto ; rewrite Heqr - Hm - addn1 iotaD map_cat.
      apply Hneigh ; rewrite - Heqr ; intros H ; now inversion H.
    + remember (tau [seq alpha i | i <- iota 0 z]) as r' ; destruct r' as [r' | ] ; [ | auto].
      cbn in Hz ; rewrite Heqr' Heqr - (subnKC Hz) iotaD map_cat ; cbn.
      apply Hneigh ; rewrite - Heqr' ; intros H ; now inversion H.
Qed.
  

(*A first result is that neighborhood functions are well-founded, valid
 Brouwer extensional trees.*)
Lemma neighborhood_wf_valid_Bext_tree (tau : list A -> option R) :
  neighborhoodfunction tau <-> (wf_Bext_tree tau /\ Bvalid_ext_tree tau).
Proof.
  split ; intros [Hwf Hval].
  - split.
    + intros alpha ; specialize (Hwf alpha) as [n Htau].
      exists n.
      destruct (tau [seq alpha i | i <- iota 0 n]) as [m | ]; [ | exfalso ; now apply Htau].
      exists m ; reflexivity.
    + intros alpha n m Heq.
      rewrite <- addn1, iotaD, map_cat.
      erewrite <- Hval ; [assumption |].
      now rewrite Heq.
  - split.
    + intros alpha ; specialize (Hwf alpha) as [n [o Hno]].
      exists n ; now rewrite Hno.
    + intros u v Hneq.
      induction v as [ | v x IHv] using last_ind ; [now rewrite cats0 |].
      rewrite <- cats1.
      destruct (tau u) as [ y | ]; [ | exfalso ; now apply Hneq].
      unfold Bvalid_ext_tree in *.
      specialize (Hval (from_pref x (u ++ v ++ [::x])) (size (u ++ v)) y).
      have Heq: (size (u ++ v ++ [:: x])) = ((size (u ++ v)).+1) by
        repeat erewrite size_cat ; cbn ; lia.
      symmetry ; etransitivity ; [ | apply Hval] ; unfold from_pref.
      * erewrite map_nth_iota0 ; [now rewrite <- Heq, take_size |].
        rewrite Heq ; now apply ltnSn.
      * erewrite map_nth_iota0 ; [ | rewrite Heq ; now apply leqnSn].
        rewrite catA take_size_cat => //.
Qed.

(*Moreover, the notion of a neighborhood function realising F is similar
 to the use of Beval_ext_tree, albeit the natural number n must be the smallest
 one in the case of neighborhood functions, while it can be any large enough
 natural number in the case of Beval_ext_tree_aux. *)
Lemma neigh_realises_Beval_aux (tau : seq A -> option R) a alpha l i :
  (exists n, 
      (tau (l ++ [seq alpha i | i <- iota i n]) = Some a /\
         (forall z : nat, z < n -> tau (l ++ [seq alpha i | i <- iota i z]) = None)))
  <->
    exists n, Beval_ext_tree_aux tau alpha n l i = Some a.
Proof.
  split.
  - intros [n Hyp] ; exists n ; revert l i Hyp.
    induction n ; intros l i [Hsome Hinfn]  ; [ now rewrite cats0 in Hsome | ].
    cbn ; remember (tau l) as aux ; destruct aux as [r | ].
    + specialize (Hinfn 0) ; rewrite cats0 in Hinfn.
      now rewrite Hinfn in Heqaux ; [inversion Heqaux | ].
    + eapply IHn ; split ; [ now rewrite cat_rcons | ].
      intros z Hinfz ; rewrite cat_rcons.
      now apply (Hinfn z.+1).
  - intros [n Heq].
    exists (Beval_ext_tree_trace_aux tau alpha n l i).
    rewrite Beval_ext_tree_map_aux in Heq.
    split ; [assumption | ].
    revert l i Heq ; induction n ; intros l i Heq z Hinf ; cbn in * ; [now inversion Hinf | ].
    remember (tau l) as aux ; destruct aux as [r | ] ; [inversion Hinf | ].
    destruct z ; cbn in * ; [now rewrite cats0 | rewrite - cat_rcons].
    apply IHn ; auto ; now rewrite cat_rcons.
Qed.


Lemma neigh_realises_Beval (tau : seq A -> option R) F :
  neigh_realises tau F <->
  forall alpha, exists n, Beval_ext_tree tau alpha n = Some (F alpha).
Proof.
  split.
  - intros Hyp alpha ; specialize (Hyp alpha) as [n [Hsome Hinfn]].
    eapply neigh_realises_Beval_aux ; now eauto.
  - intros Hyp alpha ; specialize (Hyp alpha) as [n Heq].
    eapply (neigh_realises_Beval_aux _ _ _ nil).
    now exists n.
Qed.


(*We now get to Result 1.*)

Theorem neigh_cont_Bseq_cont F :
  neigh_cont F <-> Bseq_cont_valid F.
Proof.
  split.
  - intros [tau [Hneigh Hreal]].
    exists tau ; split ; [ | now eapply neighborhood_wf_valid_Bext_tree].
    now apply neigh_realises_Beval.
  - intros [tau [Hcont Hval] ].
    exists tau ; split ; [ | now apply neigh_realises_Beval].
    eapply neighborhood_wf_valid_Bext_tree.
    split ; [ | assumption].
    intros alpha ; specialize (Hcont alpha) as [n Heq].
    exists (Beval_ext_tree_trace_aux tau alpha n nil 0), (F alpha).
    now rewrite - (Beval_ext_tree_map_aux tau alpha n nil 0).
Qed.



(*Let us now define Brouwer_operation. As explained, it is 
 an inductive predicate on functions of type list nat -> option nat.*)

Inductive Brouwer_operation : (list A -> option R) -> Prop :=
| Bconst γ n : (forall a, γ a = Some n) -> Brouwer_operation γ
| Bsup γ : γ nil = None ->
           (forall n, Brouwer_operation (fun a => γ (n :: a))) ->
           Brouwer_operation γ.

(*Brouwer_operation lands in Prop but we can use decidability of 
 the result of γ applied to some list l to go from Prop to Type.
However, Brouwer_operation as it stands is too intensional.
 We thus start by defining Brouwer_operation_at, a variant of Brouwer_operation
 that does not require function extensionality.*)

Inductive Brouwer_operation_at : (list A -> option R) -> list A -> Prop :=
| Bconst_at l γ n : (forall a, γ (l ++ a) = Some n) -> Brouwer_operation_at γ l
| Bsup_at l γ : γ l = None ->
           (forall n, Brouwer_operation_at γ (rcons l n)) ->
           Brouwer_operation_at γ l.

(*Using Function Extensionality, the two predicates are equivalent.*)

Require Import FunctionalExtensionality.

Lemma Brouwer_operation_at_spec l γ :
  Brouwer_operation (fun a => γ (l ++ a)) <->
  Brouwer_operation_at γ l.
Proof.
  split.
  - intros H.
    remember (fun a : seq A => γ (l ++ a)) as γ_l.
    revert l Heqγ_l.
    induction H.
    + intros l ->.
      econstructor. eassumption.
    + intros l ->.
      rewrite cats0 in H.
      eapply Bsup_at => //.
      intros. eapply H1.
      eapply functional_extensionality_dep_good.
      intros. now rewrite cat_rcons.
  - induction 1.
    + eapply Bconst => //.
    + eapply Bsup.
      1: rewrite cats0 => //.
      intros.
      erewrite functional_extensionality_dep_good.
      1: eapply H1.
      intros. cbn. rewrite cat_rcons => //.
Qed.

(*We now define Brouwer_operation_at', similar to Brouwer_operation but with only
 one constructor, to be able to escape Prop.*)

Inductive Brouwer_operation_at' (γ : list A -> option R) (l : list A) : Prop :=
| Bsup_at' : (γ l = None \/ ~ (exists n, forall a, γ (l ++ a) = Some n) ->
                (forall n, Brouwer_operation_at' γ (rcons l n))) ->
                Brouwer_operation_at' γ l.

(*Brouwer_operation_at_Type is similar to Brouwer_operation_at', but lives in Type.*)
Inductive Brouwer_operation_at_Type (γ : list A -> option R) (l : list A) : Type :=
| Bsup_at_Type : (γ l = None ->
              (forall n, Brouwer_operation_at_Type γ (rcons l n))) ->
             Brouwer_operation_at_Type γ l.

(*As expected, we can go from Brouwer_operation_at to Brouwer_operation_at'.*)
Lemma Brouwer_operation_at'_spec1 γ l :
  Brouwer_operation_at γ l -> Brouwer_operation_at' γ l.
Proof.
  (* split. *)
  - induction 1.
    + econstructor. intros [Hnone | Hnex].
      * enough (None = Some n) by congruence.
        rewrite <- Hnone. erewrite <- H.
        erewrite cats0 => //.
      * exfalso ; apply Hnex.
        exists n ; now auto.
    + econstructor. intros. eauto.
Qed.

(*And we can go from Brouwer_operation_at' to Brouwer_operation_at_Type*)
Lemma Brouwer_operation_at_Type_spec γ l :
  Brouwer_operation_at' γ l -> Brouwer_operation_at_Type γ l.
Proof.
  (* split. *)
  - induction 1.
    econstructor. auto.
Qed.


(*We now define Brouwer operation continuity.*)
Definition Bneigh_cont F :=
  exists γ, Brouwer_operation_at γ nil /\ neigh_realises γ F.

(*Functions that are Brouwer operations are neighborhood functions.*)
Lemma K0K_aux γ l :
  Brouwer_operation_at γ l ->
  (forall α : nat -> A, exists n : nat, γ (l ++ (map α (iota 0 n))) <> None) /\
    forall a b : list A, γ (l ++ a) <> None -> γ (l ++ a) = γ (l ++ a ++ b).
Proof.
  induction 1.
  - split.
    + intros. exists 0. congruence.
    + congruence.
  - split. 
    + intros α. destruct (H1 (α 0)) as [H1' H2'].
      * destruct (H1' (fun n => α (S n))) as [n].
        exists (1 + n).
        rewrite iotaD.
        cbn.
        replace 1 with (1 + 0). 
        1: rewrite iotaDl.
        2: now rewrite addn0.
        now rewrite - map_comp - cat_rcons .
    + intros a b Ha.
      destruct a as [ | x a ]. 1: rewrite cats0 in Ha ; congruence.
      destruct (H1 x) as [H1' H2'].
      rewrite catA - cat_rcons - catA.
      eapply H2'.
      rewrite cat_rcons ; congruence.
Qed.

Lemma K0K γ :
  Brouwer_operation_at γ nil ->
  neighborhoodfunction γ.
Proof.
  unfold neighborhoodfunction.
  now apply K0K_aux.
Qed.

(*Hence, Brouwer operation continuity implies neighborhood function continuity.*)

Lemma Bneigh_continuous_neigh_continuous F :
  Bneigh_cont F -> neigh_cont F.
Proof.
  intros (γ & H1 % K0K & H2).
  firstorder.
Qed.

(*We now turn to Result 2, the fact that Brouwer operation continuity is equivalent
 to Brouwer trees continuity.*)

Theorem Bneigh_cont_equiv_dialogue_cont_Brouwer F :
  Bneigh_cont F <-> dialogue_cont_Brouwer F.
Proof.
  split.
  - intros (γ & H1 & H2).
    have Hvalid := Bvalid_every_list ((neighborhood_wf_valid_Bext_tree _).1 (K0K H1)).2.
    eapply Brouwer_operation_at'_spec1 in H1.
    eapply Brouwer_operation_at_Type_spec in H1.
    unshelve eexists.
    + induction H1 as [u k IHk ].
      destruct (γ u) eqn:E.
      -- now eapply spit.
      -- eapply bite. intros x.
         eapply (IHk (erefl) x).
    + cbn ; set (Brouwer_operation_at_Type_rect _) as f ; cbn in *.
      intros α.
      destruct (H2 α) as (m & Hm & Hinfm).
      suff: forall l (H1 : Brouwer_operation_at_Type γ l) (α : nat -> A) (m : nat)
                   (Hinfz : forall z : nat, z < m ->
                                            γ (l ++ [seq α i | i <- iota (size l) z]) = None),
          γ (l ++ [seq α i | i <- iota (size l) m]) = Some (F α) ->
          F α = beval (f l H1) (n_comp α (size l)) by (intros Hyp ; eapply Hyp ; eauto).
      clear H1 α m Hinfm Hm.
      intros l H1.
      induction H1 as [ l k IHk ] ; intros α m Hinfz Hm.
      generalize (@erefl _ (γ l)) ; generalize (γ l) at 2.
      intros aux Heqaux ; destruct aux as [n | ] ; cbn.
      * destruct m ; [rewrite cats0 in Hm | specialize (Hinfz 0) ; rewrite cats0 in Hinfz].
        -- now symmetry in Hm ; destruct Hm.
        -- now rewrite Hinfz in Heqaux ; [inversion Heqaux | ].
      * symmetry in Heqaux ; destruct Heqaux ; cbn.
        erewrite IHk with erefl (α (size l)) α m.-1 ; rewrite size_rcons ; auto.
        -- now rewrite n_comp_n_plus addn0.
        -- intros z Hinf ; rewrite cat_rcons.
           change (γ (l ++ [seq α i | i <- iota (size l) z.+1]) = None).
           apply Hinfz ; now destruct m ; [inversion Hinf | ].
        -- destruct m ; cbn in * ; [ | now rewrite cat_rcons].
           rewrite cats0 - cats1 ; rewrite cats0 in Hm.
           now eapply Hvalid.
  - intros [b Hb].
    unshelve eexists.
    + clear F Hb. induction b as [ | k IHk] ; intros [ | x l]  ;
        [ exact None | exact (Some r) | exact None | ].
      eapply (IHk x l).
    + split.
      * clear F Hb.
        generalize (@nil A) as l.
        induction b as [ | k IHk] ; intros.
        -- destruct l ; [ econstructor 2 | econstructor ] ; cbn ; eauto.
           intros n ; econstructor ; eauto ; intros a ; now eauto.
        -- revert IHk ; remember (Btree_rect _ _) as f ; intros IHk.
           destruct l as [ | a l] ; auto.
           ++ econstructor 2 ; [ rewrite Heqf ; auto | intros n ].
              specialize (IHk n nil).
              rewrite Heqf ; cbn ; rewrite - Heqf.
              remember (f (k n)) as tau.
              induction IHk as [ l tau m Hsome | l tau Hnone _ IHk].
              ** econstructor ; intros u ; cbn ; rewrite - Heqtau ; now apply Hsome. 
              ** econstructor 2 ; cbn ; [now rewrite - Heqtau | now eauto].
           ++ rewrite Heqf ; cbn ; rewrite - Heqf.
              specialize (IHk a l).
              remember (f (k a)) as tau.
              induction IHk as [ l tau m Hsome | l tau Hnone _ IHk].
              ** econstructor ; intros u ; cbn ; rewrite - Heqtau ; now apply Hsome.
              ** econstructor 2 ; cbn ; [now rewrite - Heqtau | eauto ].
      * intros alpha.
        set (f := Btree_rect _ _).
        suff: exists m, f b [seq alpha i | i <- iota 0 m] = Some (beval b alpha) /\
                          (forall z : nat, z < m -> f b [seq alpha i | i <- iota 0 z] = None).
        { intros [m [Hm1 Hm2]] ; exists m ; split ; [ now erewrite Hb | auto]. }
        clear F Hb ; revert alpha ; induction b as [ r | k IHk] ; intros.
        -- exists 1 ; split ; cbn ; auto.
           intros z eqz.
           destruct z ; cbn ; [auto | inversion eqz].
        -- have auxil : forall  (m n : nat) (f : nat -> A),
               [seq f i | i <- iota n.+1 m] = [seq (f \o succn) i | i <- iota n m].
           { clear ; induction m as [ | m IHm] ; cbn in * ; auto.
             intros n f ; f_equal ; now erewrite <- IHm.
           }
           specialize (IHk (alpha 0) (alpha \o succn)) as [m [Hm1 Hm2]].
           rewrite - Hm1.
           exists m.+1 ; split ; auto.
           ++ cbn ; now erewrite auxil.
           ++ intros z Hinfz.
              case: (leqP m z) ; intros Hinfz' ; destruct z ; cbn ; try reflexivity.
              ** now rewrite - (Hm2 z) ; [now rewrite auxil | ].
              ** rewrite - (Hm2 z) ; [now rewrite auxil | now apply ltnW].
Qed.                 


(** *** Neighborhood continuity is equivalent to interaction tree continuity  *)

(*It is quite straightforward to turn a neighborhood function into a coinductive
 Brouwer tree*)

CoFixpoint neigh_to_Bitree (e : list A -> option R) (l : list A) :
  @Bitree A R :=
  match e l with
  | None => Bvis (fun a => neigh_to_Bitree e (rcons l a))
  | Some o => Bret _ o
  end.


Lemma neigh_cont_to_Bseq_cont_interaction F :
  neigh_cont F -> Bseq_cont_interaction F.
Proof.
  intros [e [Hne Hrel]].
  exists (neigh_to_Bitree e nil).
  intros f ; specialize (Hrel f) as [n [Heq Hn]].
  exists n.
  rewrite <- Heq.
  suff: forall l, Bieval (neigh_to_Bitree e l) (n_comp f (size l)) n =
                    e (l ++ [seq f i | i <- iota (size l) n]).
  { intros Hyp ; now apply Hyp. }
  clear Heq Hn.
  revert f e Hne.
  induction n as [ | n IHn] ; intros.
  - cbn in * ; rewrite cats0.
    now destruct (e l).
  - cbn in *.
    remember (e l) as aux ; destruct aux as [o | ].
    + rewrite Heqaux ; apply Hne ; now rewrite - Heqaux.
    + specialize (IHn f e Hne (rcons l (f (size l)))).
      rewrite size_rcons - cats1 - catA in IHn.
      now rewrite - IHn n_comp_n_plus addn0 - cats1.
Qed.

(*To go from coinductive Brouwer continuity to neighborhood continuity, we need to find, for
 any argument alpha, the smallest n : nat such that Bieval i alpha n = Some (F alpha).
 We do it by defining a trace function.*)

Fixpoint Bieval_trace (i : Bitree A R) (alpha : nat -> A) (n : nat) : nat :=
  match n with
  | 0 => 0
  | S j => match i with
           | Bret o => 0
           | Bvis k => S (Bieval_trace (k (alpha 0)) (alpha \o S) j)
           end
  end.

(*The following two Lemmas show that Bieval_trace has the properties we expect: it is
 indeed the smallest n : nat such that Bieval i alpha n = Some y.
 *)


Lemma Bieval_trace_Some (i : Bitree A R) (alpha : nat -> A) (n : nat) (y : R) :
  Bieval i alpha n = Some y ->
  Bieval i alpha (Bieval_trace i alpha n) = Some y.
Proof.
  revert i alpha ; induction n as [ | n IHn] ; intros i alpha Heq ; [now auto | ].
  cbn in *.
  destruct i as [ | k] ; [now auto | ].
  cbn in *.
  now apply IHn.
Qed.

Lemma Bieval_trace_inf (i : Bitree A R) (alpha : nat -> A) (n m : nat) :
  m < (Bieval_trace i alpha n) ->
  Bieval i alpha m = None.
Proof.
  revert i alpha m ; induction n as [ | n IHn] ; intros i alpha m Hinf ; [now inversion Hinf | ].
  destruct i ; cbn in * ; [now inversion Hinf | ].
  destruct m ; [reflexivity | cbn ; now apply IHn].
Qed.

(*We conclude.*)
Lemma Bseq_cont_interaction_to_neigh_cont F :
  Bseq_cont_interaction F -> neigh_cont F.
Proof.
  intros [b Hb].
  suff: forall f, exists n, Bitree_to_option b [seq f i | i <- iota 0 n] = Some (F f) /\
                              forall z, z < n ->
                                        Bitree_to_option b [seq f i | i <- iota 0 z] = None.
  - intros Hyp.
    exists (Bitree_to_option b) ; split.
    + split ; [intros alpha | ].
      * specialize (Hyp alpha) as [n [Hn Hinf]].
        exists n ; now rewrite Hn.
      * clear Hb Hyp F ; intros a ; revert b ; induction a as [ | x q IHq] ; intros b v Heqv.
        -- cbn in * ; destruct b ; [now destruct v | now exfalso].
        -- cbn in * ; destruct b ; [reflexivity | now apply IHq].
    + intros alpha ; specialize (Hyp alpha) as [n [Hn Hinf]].
      exists n ; now split.
  - intros alpha ; specialize (Hb alpha) as [n Hn].
    exists (Bieval_trace b alpha n) ; split.
    + rewrite - Bitree_to_option_Bieval.
      now apply Bieval_trace_Some.
    + intros m Hinf ; rewrite - Bitree_to_option_Bieval.
      eapply Bieval_trace_inf ; eauto.
Qed.

Theorem neigh_cont_iff_Bseq_cont_interaction (F : (nat -> A) -> R) :
  neigh_cont F <-> Bseq_cont_interaction F.
Proof.
  split.
  - apply neigh_cont_to_Bseq_cont_interaction.
  - apply Bseq_cont_interaction_to_neigh_cont.
Qed.

