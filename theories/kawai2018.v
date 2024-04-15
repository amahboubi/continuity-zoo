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


(** Kawaii's "Principles of bar induction and continuity on Baire space" has the notions of neighborhood function and Brouwer operation, and derived continuity notions based on them. Brouwer operations are an inductive _predicate_ on neighborhood functions.

conjecture 1: a neighborhood function is just an extensional tree,
thus neigh_cont is equivalent to Bseq_cont

conjecture 2: a Brouwer operation can be turned into the existence of a Brouwer tree (through the Acc trick used in extra_principles.v). Thus, Bneigh_cont is equivalent to dialogue_cont_Brouwer.
The underlying insight is: The existence of a Brouwer tree is equivalent to the existence of an extensional tree that is inductively barred. This equivalence only works in the Brouwer / Baire case, not in general.

*)

Definition neighborhoodfunction (γ : list nat -> option nat) :=
  (forall α : nat -> nat, exists n : nat, γ (map α (iota 0 n)) <> None) /\
    forall a b : list nat, γ a <> None -> γ a = γ (a ++ b).

Lemma neighborhood_wf_valid_Bext_tree (tau : list nat -> option nat) :
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
      induction v using last_ind ; [now rewrite cats0 |].
      rewrite <- cats1.
      destruct (tau u) ; [ | exfalso ; now apply Hneq].
      unfold Bvalid_ext_tree in *.
      specialize (Hval (from_pref 0 (u ++ v ++ [::x])) (size (u ++ v)) n).
      have Heq: (size (u ++ v ++ [:: x])) = ((size (u ++ v)).+1) by
        repeat erewrite size_cat ; cbn ; lia.
      symmetry ; etransitivity ; [ | apply Hval] ; unfold from_pref.
      * erewrite map_nth_iota0 ; [now rewrite <- Heq, take_size |].
        rewrite Heq ; now apply ltnSn.
      * erewrite map_nth_iota0 ; [ | rewrite Heq ; now apply leqnSn].
        rewrite catA take_size_cat => //.
Qed.

Inductive Brouwer_operation : (list nat -> option nat) -> Prop :=
| Bconst γ n : (forall a, γ a = Some n) -> Brouwer_operation γ
| Bsup γ : γ nil = None ->
           (forall n, Brouwer_operation (fun a => γ (n :: a))) ->
           Brouwer_operation γ.

Inductive wf (P : nat -> bool) n :=
| wf_ok : P n = true -> wf P n
| wf_step : P n = false -> wf P (S n) -> wf P n.

Inductive wf' (P : nat -> bool) n :=
| wf_one : (P n = false -> wf' P (S n)) -> wf' P n.

Inductive Brouwer_operation_at : (list nat -> option nat) -> list nat -> Prop :=
| Bconst_at l γ n : (forall a, γ (l ++ a) = Some n) -> Brouwer_operation_at γ l
| Bsup_at l γ : γ l = None ->
           (forall n, Brouwer_operation_at γ (rcons l n)) ->
           Brouwer_operation_at γ l.

Inductive Brouwer_operation_at' (γ : list nat -> option nat) (l : list nat) : Prop :=
| Bsup_at' : (γ l = None \/ ~ (exists n, forall a, γ (l ++ a) = Some n) ->
                (forall n, Brouwer_operation_at' γ (rcons l n))) ->
                Brouwer_operation_at' γ l.

Inductive Brouwer_operation_at_Type (γ : list nat -> option nat) (l : list nat) : Type :=
| Bsup_at_Type : (γ l = None ->
              (forall n, Brouwer_operation_at_Type γ (rcons l n))) ->
             Brouwer_operation_at_Type γ l.

Lemma Brouwer_operation_at'_spec1 γ l :
  Brouwer_operation_at γ l -> Brouwer_operation_at' γ l.
Proof.
  (* split. *)
  - induction 1.
    + econstructor. intros. enough (None = Some n) by congruence.
      rewrite <- H0. erewrite <- H.
      erewrite cats0 => //.
    + econstructor. intros. eauto.
  (* - induction 1. *)
(*     destruct (γ l) eqn:E. *)
(*     + econstructor 1. *)
(*       admit. *)
(*     + econstructor 2; eauto. *)
(* Admitted. *)
Qed.

Lemma Brouwer_operation_at_Type_spec γ l :
  Brouwer_operation_at' γ l -> Brouwer_operation_at_Type γ l.
Proof.
  (* split. *)
  - induction 1.
    econstructor. auto.
    (* + econstructor. intros. enough (None = Some n) by congruence. *)
    (*   rewrite <- H0. erewrite <- H. *)
    (*   erewrite cats0 => //. *)
    (* + econstructor. intros. eauto. *)
      (* - induction 1. *)
      (*     destruct (γ l) eqn:E. *)
      (*     + econstructor 1. *)
      (*       admit. *)
      (*     + econstructor 2; eauto. *)
      (* Admitted. *)
Qed.

Require Import FunctionalExtensionality.

Lemma Brouwer_operation_at_spec l γ :
  Brouwer_operation (fun a => γ (l ++ a)) <->
  Brouwer_operation_at γ l.
Proof.
  split.
  - intros H.
    remember (fun a : seq nat => γ (l ++ a)) as γ_l.
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

Lemma K0K γ :
  Brouwer_operation γ -> neighborhoodfunction γ.
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
        rewrite <- map_comp. eassumption.
    + intros a b Ha.
      destruct a. 1: congruence.
      destruct (H1 n) as [H1' H2'].
      eapply H2'. congruence.
Qed.

Definition neigh_realises γ (F : (nat -> nat) -> nat) :=
    forall α, exists m, γ (map α (iota 0 m)) = Some (F α) /\
              forall z, z < m -> γ (map α (iota 0 m)) = None.

Definition neigh_cont F :=
  exists γ, neighborhoodfunction γ /\ neigh_realises γ F.

Definition Bneigh_cont F :=
  exists γ, Brouwer_operation γ /\ neigh_realises γ F.

Lemma Bneigh_continuous_neigh_continuous F :
  Bneigh_cont F -> neigh_cont F.
Proof.
  intros (γ & H1 % K0K & H2).
  firstorder.
Qed.

Lemma Bneigh_cont_equiv_dialogue_cont_Brouwer F :
  Bneigh_cont F <-> dialogue_cont_Brouwer F.
Proof.
  split.
  - intros (γ & H1 & H2).
    eapply Brouwer_operation_at_spec with (l := nil) in H1.
    revert H1. generalize (@nil nat) as l. intros l H1.
    eapply Brouwer_operation_at'_spec1 in H1.
    eapply Brouwer_operation_at_Type_spec in H1.
    unshelve eexists.
    + induction H1.
      destruct (γ l) eqn:E.
      -- eapply spit. exact n.
      -- eapply bite. intros n.
         eapply (X ltac:(reflexivity) n).
    + cbn.
      set (Brouwer_operation_at_Type_rect _) as f.
      cbn in *.
      intros α.
      destruct (H2 α) as (? & ? & ?).
      enuogh (Some (beval (f l H1) α) = (γ [seq α i | i <- iota 0 x])).
      { rewrite H in H3. now inversion H3. }
      symmetry. clear H. 
      induction H1. cbn.
      destruct (γ l) eqn:E.
      -- simpl in *.
         admit.
      -- admit.
  - intros [b Hb].
    unshelve eexists.
    + clear Hb. induction b.
      * exact (fun _ => Some r).
      * intros [].
        -- exact None.
        -- eapply (H n l).
    + induction b in F, Hb |- *; cbn in *.
      * split. 1: econstructor.
        (* intros α. *)
      (*   exists 0. split; auto. lia. *)
      (* * split. *)
      (*   -- econstructor => //. *)
      (*      intros. eapply H. *)
      (*   -- intros α. *)
Admitted.
