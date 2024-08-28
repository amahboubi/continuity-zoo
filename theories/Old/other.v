
From mathcomp Require Import all_ssreflect.
Require Import Program.
From Equations Require Import Equations.
Require Import extra_principles.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import continuity_zoo_Prop.

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


Section GBI_BI.
  Variables A B : Type.
Implicit Type (T : seq (nat * B) -> Type).

(*The code previously found in this section was moved to brede_herbelin.v*)





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
Admitted.



End GBI_BI.


Definition neighborhoodfunction (γ : list nat -> option nat) :=
  (forall α : nat -> nat, exists n : nat, γ (map α (iota 0 n)) <> None) /\
    forall a b : list nat, γ a <> None -> γ a = γ (a ++ b).

Inductive Brouwer_operation : (list nat -> option nat) -> Prop :=
| Bconst n : Brouwer_operation (fun a => Some n)
| Bsup γ : γ nil = None -> (forall n, Brouwer_operation (fun a => γ (n :: a))) -> Brouwer_operation γ.

Lemma K0K γ :
  Brouwer_operation γ -> neighborhoodfunction γ.
Proof.
  induction 1.
  - split.
    + intros. exists 0. congruence.
    + intros. reflexivity.
  - split. intros α.
    + destruct (H1 (α 0)) as [H1' H2'].
      * destruct (H1' (fun n => α (S n))) as [n].
        exists (1 + n).
        rewrite iotaD.
        cbn.
        replace 1 with (1 + 0).
        rewrite iotaDl.
        2: now rewrite addn0.
        rewrite <- map_comp. eassumption.
      * intros a b Ha.
        destruct a. congruence.
        destruct (H1 n) as [H1' H2'].
        eapply H2'. congruence.
Qed.

Definition neigh_realises γ (F : (nat -> nat) -> nat) :=
    forall α, exists m, γ (map α (iota 0 m)) = Some (F α) /\
              forall z, z < m -> γ (map α (iota 0 m)) = None.

Definition neigh_continuous F :=
  exists γ, neighborhoodfunction γ /\ neigh_realises γ F.

Definition Bneigh_continuous F :=
  exists γ, Brouwer_operation γ /\ neigh_realises γ F.

Lemma Bneigh_continuous_neigh_continuous F :
  Bneigh_continuous F -> neigh_continuous F.
Proof.
  intros (γ & H1 % K0K & H2).
  firstorder.
Qed.

Definition sequentially_continuous F :=
  exists τ : ext_tree nat nat nat, forall f : nat -> nat, exists n : nat, eval_ext_tree τ f n = output (F f).

Lemma neigh_continuous_equiv F : neigh_continuous F <-> sequentially_continuous F.
Proof.
  split.
  - intros (γ & H1 & H2).
