From mathcomp Require Import all_ssreflect.
Require Import extra_principles Util.
Require Import cantor.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Declare Scope bh_scope.
Delimit Scope bh_scope with BH.
Open Scope bh_scope.


Section Ord.
  Variables A B : Type.
Implicit Type (T : seq (nat * B) -> Type).

Fixpoint ord_aux {C} (u : list C) (n : nat) : list (nat * C) :=
  match u with
  | nil => nil
  | a :: q => (n, a) :: (ord_aux q (S n))
  end.

Definition ord {C} (u : seq C) := ord_aux u 0.

Lemma ordP {C} (u : seq C) n : ord_aux u n = zip (iota n (size u)) u.
Proof.
elim: u n => [| c u ihu] //= n. 
by rewrite ihu.
Qed.


Lemma ord_map_snd {C} n (u : list C) : map snd (ord_aux u n) = u.
Proof. by rewrite ordP -/unzip2 unzip2_zip // size_iota. Qed.

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
  elim: u n => [| c u ihu] n //=.
  by rewrite -[_ + n]addnS ihu.
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
elim: u n m => [| c u ihu] [| n] m //=.
by rewrite -[_ + m]addnS ihu.
Qed.


Lemma ord_size {C} n (u : list C) : size (ord_aux u n) = size u.
Proof.
  revert n ; induction u ; intro n ; [reflexivity |].
  cbn.
  f_equal ; now apply IHu.
Qed.

Lemma ord_rcons {C} n (u : list C) a : ord_aux (rcons u a) n = rcons (ord_aux u n) (size u + n, a).
Proof.
  elim: u n => [| c u ihu] n //=.
  by rewrite ihu addnS.
Qed.

Lemma ord_nth {C} b (u : list C) n m : (n + m, nth b u m) = nth (n + m, b) (ord_aux u n) m.
Proof.
  rewrite ordP nth_zip ?size_iota //.
  case: (ltnP m (size u)) => hs; first by rewrite nth_iota.
  by rewrite [in RHS]nth_default // size_iota.
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
  elim: u n m b => [| c u ihu] [| n] m b h //=; first by left.
  right. 
  rewrite -[n.+1 + m]addnS. 
  exact: ihu.
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

Lemma ord_dec (u : seq (nat * B)) : {v & { n & u = ord_aux v n} } +
                                      { forall v n, u = ord_aux v n -> False}.
Proof.
  induction u as [ | u b IHu] using last_ind.
  { left ; exists nil ; exists 0 ; reflexivity. }
  destruct IHu as [[v [n Heqvn]] | Hfalse] ; [ | right].
  2:{ intros v n Heq ; subst.
      destruct v as [ | v c _] using last_ind ; [ destruct u ; cbn in * ; inversion Heq | ].
      rewrite ord_rcons in Heq.
      assert (aux := f_equal (last b) Heq) ;  do 2 rewrite last_rcons in aux ; subst.
      eapply rcons_injl in Heq ; subst.
      now apply (Hfalse v n).
  }
  destruct b as [m b] ; subst.
  destruct v as [ | b' v] ; cbn in * ; [left |].
  { exists [:: b], m ; reflexivity. }
  case: (PeanoNat.Nat.eq_dec m ((size v) + n.+1)) ;
    [intros Heq ; subst ; left | intros Hnoteq ; right].
  { exists ((b' :: rcons v b)), n ; subst; cbn ; now rewrite ord_rcons. }
  intros w k Heq ; subst.
  destruct w as [ | b'' w] ; cbn in * ; [now inversion Heq | ].
  inversion Heq as [[H1 H2 Heq']] ; subst ; clear Heq.
  destruct w as [ | w c _] using last_ind ; [ destruct v ; cbn in * ; inversion Heq' | ].
  rewrite ord_rcons in Heq'.
  assert (aux := f_equal (last (m, b)) Heq') ; do 2 rewrite last_rcons in aux.
  inversion aux ; subst.
  eapply rcons_injl, ord_inj in Heq' ; subst. 
  now apply Hnoteq.
Qed.


Lemma unzip1_ord {T : Type} (u : list T) n : unzip1 (ord_aux u n) = iota n (size u).
Proof.
elim: u n => [ |t u ihu] n //=.
by rewrite -ihu.
Qed.

Lemma unzip2_ord {T : Type} (u : list T) n : unzip2 (ord_aux u n) = u.
Proof.
elim: u n => [ |t u ihu] n //=.
by rewrite ihu.
Qed.

Lemma size_ord  {T : Type} (u : list T) n : size (ord_aux u n) = size u.
Proof.
by rewrite ordP size_zip size_iota minnn.
Qed.
      
End Ord.

Section Technical.

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

End Technical.

Section GDC_GBI_Definition.
  Variables A B : Type.
  Implicit Type (T : seq (A * B) -> Prop).

Inductive ABUparborification T : list (A * B) -> Prop :=
| Tarbor l l' : T l -> List.incl l' l -> ABUparborification T l'.

Definition ABDownarborification T u : Prop :=
  forall v, List.incl v u -> T v.

Notation " ⇑⁻ T " := (ABUparborification T) (at level 80) : bh_scope.

Notation " ⇓⁻ T " := (ABDownarborification T) (at level 80) : bh_scope.
  
Definition ABchoicefun T :=
  exists alpha : A -> B, forall u : list A, T [seq (i, alpha i) | i <- u].

CoInductive ABapprox T : list (prod A B) -> Prop :=
  approx u : (⇓⁻ T) u ->
             (forall a : A, ~ List.In a (map fst u) ->
                              exists b : B, ABapprox T (rcons u (a, b))) ->
             ABapprox T u.

Definition GDC := forall T,  ABapprox T nil -> ABchoicefun T.

Definition ABbarred T :=
  forall α : A -> B, exists u : list A, T [seq (i, α i) | i <- u].

Inductive indbarred T : list (A * B) -> Prop :=
  | ieta u' u : T u -> List.incl u u' -> indbarred T u'
  | ibeta a v : ~ List.In a (map fst v) ->
              (forall b, indbarred T (v ++ [:: (a,b)])) -> indbarred T v.

Inductive indbarred_spec T :  list (A * B) -> Prop := 
 |Eta : forall u l, T (l ++ u) -> indbarred_spec T l
 |Beta : forall u' u a b, T u' -> indbarred_spec T (rcons (u' ++ u) (a, b)).

Arguments Eta {T} u l.

(* Generalized Bar Induction, phrased using the Herbelin-Brede way *)
Definition GBI T := ABbarred T -> indbarred T [::].



End GDC_GBI_Definition.

Section DC_GDC_BI_GBI.
  Variables B : Type.
  Implicit Type (T : seq (nat * B) -> Prop).

Notation " ⇑⁻ T " := (ABUparborification T) (at level 80) : bh_scope.

Notation " ⇓⁻ T " := (ABDownarborification T) (at level 80) : bh_scope.

Definition is_tree (P : list B -> Prop) :=
  forall u n, P u -> P (take n u).

Definition Downarborification (P : list B -> Prop) (u : list B) : Prop :=
  forall n, P (take n u).

Notation " ↓⁻ T " := (Downarborification T) (at level 80) : bh_scope.


CoInductive pruning (P : list B -> Prop) : list B -> Prop :=
  prune a u : P u -> pruning P (rcons u a) -> pruning P u.

Lemma pruning_cat P u n : pruning P u -> exists v, size v = n /\ pruning P (u ++ v).
Proof.
elim: n u => [| n ihn] u pru.
- by exists [::]; rewrite cats0.
- inversion pru as [b v Pu prub e].
  have {ihn} [w [sw pruw]] := ihn _ prub.
  exists (b :: w).
  by rewrite -sw -cat_rcons.
Qed.

Definition choicefun (P : list B -> Prop) :=
  exists alpha : nat -> B,  forall n : nat, P [seq (alpha i) | i <- iota 0 n].

Definition DC := forall (P : list B -> Prop), pruning P nil -> choicefun P.

Definition ABis_tree T :=
  forall u v, List.incl v u -> T u -> T v.

Definition monotone {C} (P : list C -> Prop) :=
  forall l l', P l -> P (l ++ l').

Inductive Upmonotonisation {C} (T : list C -> Prop) : list C -> Prop :=
| mon l l' : T l -> Upmonotonisation T (l ++ l').

Definition Downmonotonisation {C} (T : list C -> Prop) : list C -> Prop :=
  fun u => forall v, T (u ++ v).

Lemma UpmonotonisationP {C} (T : list C -> Prop) u :
  Upmonotonisation T u <->
  exists v, exists w, T v /\ u = v ++ w.
Proof.
split=> h.  
- case: h => v1 v2 Tv1.
  by exists v1; exists v2.
- by case: h => [w1 [w2 [Tw1 ->]]].
Qed.

Notation " ↑⁺ T " := (Upmonotonisation T) (at level 80) : bh_scope.

Notation " ↓⁺ T " := (Downmonotonisation T) (at level 80) : bh_scope.

Definition ABmonotone {C} (P : list C -> Prop) :=
  forall l l', List.incl l l' -> P l -> P l'.

Inductive ABUpmonotonisation {C} (T : list C -> Prop) : list C -> Prop :=
| Tmon l l' : T l -> List.incl l l' -> ABUpmonotonisation T l'.

Definition ABDownmonotonisation {C} (T : list C -> Prop) : list C -> Prop :=
  fun u => forall v, List.incl u v -> T v.

Notation " ⇑⁺ T " := (ABUpmonotonisation T) (at level 80) : bh_scope.

Notation " ⇓⁺ T " := (ABDownmonotonisation T) (at level 80) : bh_scope. 

Lemma Upmonot_monotone {C} P : @monotone C (↑⁺ P).
Proof.
  intros _ w [u v Hu].
  by rewrite -catA.
Qed.


Lemma monot_barred {C} (P : list C -> Prop) : barred P -> barred (Upmonotonisation P).
Proof.
  intros H alpha ; specialize (H alpha).
  destruct H as [l [Hpref HP]].
  exists l ; split ; [assumption |].
  now erewrite <- cats0 ; econstructor.
Qed.  

  
Lemma ABUpmonot_monotone {C} P : @ABmonotone C (⇑⁺ P).
Proof.
  intros l l' Hll' Hyp.
  inversion Hyp ; subst.
  econstructor.
  2: eapply List.incl_tran ; eassumption.
  assumption.
Qed.

Lemma ABDownmonot_monotone {C} P : @ABmonotone C (⇓⁺ P).
Proof.
  unfold ABDownmonotonisation ; intros u v Huv Hyp w Hvw.
  eapply Hyp, List.incl_tran ; now eassumption.
Qed.


Lemma ABmonot_barred T : ABbarred T -> ABbarred (⇑⁺ T).
Proof.
  intros H alpha. specialize (H alpha).
  destruct H as [l Hpref].
  exists l.
  econstructor ; [ eassumption |].
  now apply List.incl_refl.
Qed.  


Lemma arbor_is_tree P : is_tree (↓⁻ P).
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

Lemma DownABarbor_is_tree T : ABis_tree (⇓⁻ T).
Proof.
  intros u n Hu.
  unfold ABDownarborification in * ; intros Hyp v Hincl.
  apply Hyp.
  eapply List.incl_tran ; eassumption.
Qed.

Lemma UpABarbor_is_tree T : ABis_tree (⇑⁻ T).
Proof.
  intros u n Hu HT.
  induction HT.
  econstructor ; [eassumption | ].
  now eapply List.incl_tran ; eassumption.
Qed.


Definition TtoP (T : list (nat * B) -> Prop) (l : list B) : Prop :=
  T (ord l).

Notation " [| T |] " := (TtoP T) (at level 0) : bh_scope.


Inductive PtoT (P : list B -> Prop) : list (nat * B) -> Prop :=
| ptot : forall l, P l -> PtoT P (ord l).

Definition PtoT_dual (P : list B -> Prop) : list (nat * B) -> Prop :=
  fun u => forall v, u = ord v -> P v.

Notation " [ P ]ₐ " := (PtoT P) (at level 0) : bh_scope.
Notation " [ P ]ₑ " := (PtoT_dual P) (at level 0) : bh_scope.


Definition TtoP_PtoT_ret (P : list B -> Prop) : forall l, P l -> [| [ P ]ₐ |] l :=
  fun l Hl => ptot Hl.

Lemma TtoP_PtoT_inv (P : list B -> Prop) : forall l, [| [ P ]ₐ |] l -> P l.
Proof.
  intros u H.
  inversion H.
  now eapply ord_inj in H0 ; subst.
Qed.  


Lemma PtoT_TtoP_inv (T : list (nat * B) -> Prop) l :
  [ [| T |] ]ₐ l -> T l. 
Proof.
  unfold TtoP ; intros H.
  inversion H ; now subst.
Qed.

Lemma PtoT_TtoP_ret (T : list (nat * B) -> Prop) u :
  T (ord u) -> [ [| T |] ]ₐ (ord u). 
Proof.
  intro H ; econstructor.
  unfold TtoP ; assumption.
Qed.

Definition DCProp11 :=
  forall (P : list B -> Prop) u, P u ->  [| ⇑⁻ [ P ]ₐ |] u.

Definition BIProp11Down :=
  forall (P : list B -> Prop) u, monotone P -> P u -> [| ⇓⁺ [ P ]ₑ |] u.

Definition DCProp11_rev :=
  forall P u, is_tree P -> [| ⇑⁻ [ P ]ₐ |] u -> P u.

Definition BIProp11Down_rev :=
  forall P u, [| ⇓⁺ [ P ]ₑ |] u -> P u.

Definition DCProp12 :=
  forall T u, ABis_tree T -> ABapprox T (ord u) -> pruning [| T |] u.

Definition BIProp12 :=
  forall T u, ABmonotone T -> indbarred T (ord u) -> hereditary_closure [| T |] u.

Definition DCProp12_rev :=
  forall T u, ABis_tree T -> pruning [| T |] u -> ABapprox T (ord u).

Definition BIProp12_rev :=
  forall T u, hereditary_closure [| T |] u -> indbarred T (ord u).

Definition DCProp12_sym :=
  forall P u, pruning P u -> ABapprox (⇑⁻ [ P ]ₐ) (ord u).

Definition BIProp12_sym :=
  forall P u, indbarred (⇓⁺ [ P ]ₑ) (ord u) ->
  hereditary_closure P u.

Definition DCProp12_sym_rev :=
  forall P u, is_tree P -> ABapprox (⇑⁻ [ P ]ₐ) (ord u) -> pruning P u.

Definition BIProp12_sym_rev :=
  forall P u, monotone P -> hereditary_closure P u ->
              indbarred (⇓⁺ [ P ]ₑ) (ord u).

Definition DCProp13 :=
  forall T, ABchoicefun T -> choicefun [| T |].

Definition BIProp13 :=
  forall T, ABmonotone T -> ABbarred T -> barred [| T |].

Definition DCProp13_rev :=
  forall T, ABis_tree T -> choicefun [| T |] -> ABchoicefun T.

Definition BIProp13_rev :=
  forall T, barred [| T |] -> ABbarred T.

Definition DCProp13_sym :=
  forall P, is_tree P -> ABchoicefun (⇑⁻ [ P ]ₐ) -> choicefun P.

Definition BIProp13Down :=
  forall P, ABbarred (⇓⁺ [ P ]ₑ) -> barred P.

Definition DCProp13_sym_rev :=
  forall P, choicefun P  -> ABchoicefun (⇑⁻ [ P ]ₐ).

Definition BIProp13Down_rev :=
  forall P, monotone P -> barred P -> ABbarred (⇓⁺ [ P ]ₑ).


(*The next four Lemmas are Proposition 11 in Brede-Herbelin's Paper*)


Lemma P_Uparbor_PtoT : DCProp11.
Proof.
  unfold DCProp11.
  intros P HP ; unfold TtoP.
  econstructor ; [econstructor ; eassumption | ].
  now apply List.incl_refl.
Qed.

Lemma Uparbor_PtoT_P : DCProp11_rev.
Proof.
  intros P u Htree HP ; unfold TtoP in *.
  inversion HP ; subst.
  inversion H ; subst.
  apply ord_incl' in H0.
  rewrite - ord_take in H0 ; apply ord_inj in H0 ; rewrite H0.
  unfold is_tree in * ; now apply Htree.
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


Lemma ABDown_PtoT_P : BIProp11Down_rev.
Proof.
  intros P l Hl ; unfold TtoP, ABDownmonotonisation, PtoT_dual in *.
  now specialize (Hl (ord l) (List.incl_refl _) l erefl).
Qed.
  

(*The next eight Lemmas are Proposition 12 in Brede-Herbelin's paper.*)

(*We start with the four Lemmas that involve pruning and Abapprox.*)

Lemma ABapprox_pruning_TtoP : DCProp12.
Proof.
  intros T u Htree.
  generalize (@erefl _ (ord u)).
  generalize (ord u) at 2 3 ; intros l Heq Happ. revert l Happ u Heq. 
  refine (cofix aux l Happ := match Happ as H in ABapprox _ u0 return
                            forall u : seq B, ord u = u0 -> pruning (TtoP T) u with
                            | approx l Harb Hyp => _
                            end).
  intros u Heq ; subst.
  unshelve edestruct (Hyp (size u)) ; [exact (@ord_sizeu_notin _ u 0) | ].
  unshelve econstructor ; [assumption | | ].
  { unfold TtoP.
    now specialize (Harb (ord u) (List.incl_refl _)).
  }
  eapply (aux (rcons (ord u) (size u, x))) ; [assumption | ].
  unfold ord ; now rewrite -> ord_rcons, <- plus_n_O.
Qed.

Lemma pruning_TtoP_ABapprox : DCProp12_rev.
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
                               end). (* so far so good with prod *)
  clear u0 Hprun ; intros w Hincl ; subst.
  econstructor.
  { intros x Hincl'.
    eapply Htree ; [ | eassumption].
    eapply List.incl_tran ; eassumption.
  }
intros n _.
case: (leqP (size u) n)=> hns; last first.
- (* have [b hb] : {b : B & List.In (n, b) (ord u)} by apply: ord_inf_size.  *)
  assert ({b : B & List.In (n, b) (ord u)}) as [b hb].
    by apply: ord_inf_size.
  exists b; apply: (aux _ Hprun').
  rewrite /ord ord_rcons addn0 -!cats1.
  apply: List.incl_appl => //.
  apply: List.incl_app=> //.
  exact: List.incl_cons.
- (* have [v [sv pruv]] := pruning_cat (n - size u) Hprun'. *)
  pose v_etc := pruning_cat (n - size u) Hprun'.
  case v_etc => v [sv pruv].
(*  have [b hb] :  {b : B & List.In (n, b) (ord (rcons u c ++ v))}.*)
  assert ({b : B & List.In (n, b) (ord (rcons u c ++ v))}) as [b hb].
    apply: ord_inf_size.
    by rewrite size_cat size_rcons sv addSn subnKC.
  exists b; apply: (aux _ pruv).
  rewrite -cats1.
  apply: List.incl_app; last by apply: List.incl_cons.
  rewrite cat_rcons /ord ord_cat.
  exact: List.incl_appl.
Qed.

Lemma pruning_ABapprox_PtoT : DCProp12_sym.
Proof.
  intros P u Hprun.
  apply pruning_TtoP_ABapprox ; [now apply UpABarbor_is_tree | ].
  revert u Hprun.
  cofix aux.
  intros _ [b u Hu Hprun].
  econstructor ; [now eapply P_Uparbor_PtoT | ].
  apply aux.
  eassumption.
Qed.

Lemma ABapprox_PtoT_pruning : DCProp12_sym_rev.
Proof.
  intros P u Htree Happ.
  suff: pruning [| ⇑⁻ [P ]ₐ |] u.
  { clear Happ ; revert u ; cofix aux ; intros u Hprun ; destruct Hprun as [b u Hu Hprun ].
    econstructor ; [ | now apply (aux _ Hprun) ].
    apply Uparbor_PtoT_P ; eassumption.
  }
  apply ABapprox_pruning_TtoP ; [ | assumption].
  now apply UpABarbor_is_tree.
Qed.


(*Let us now tackle the dual Lemmas, focused on indbarred and hereditary_closure.*)


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
       eapply List.incl_app ; [assumption | ].
       eapply List.incl_cons ; [ assumption | now eapply List.incl_nil_l].
     }
     intros Hinf.
     exfalso.
     unshelve eapply (PeanoNat.Nat.sub_gt _ _ _ Heq).
     eapply (proj1 (PeanoNat.Nat.le_succ_l (size u) n.+1)).
     exact (@leP (size u).+1 n.+1 Hinf).
  }
  econstructor 2 ; intros b.
  eapply IHm ; [assumption | | ].
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
    econstructor ; [eassumption | ].
    now apply List.incl_refl.
  }
  unshelve econstructor 2.
  exact (size l).
  { unfold ord ; exact (@ord_sizeu_notin _ l 0). }
  unfold ord in * ; intros a ; specialize (IHl a).
  erewrite ord_rcons, <- plus_n_O in IHl.
  now rewrite cats1.
Qed.  


Lemma indbarred_inductively_barred_Down_dual : BIProp12_sym.
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

Lemma inductively_barred_indbarred_Down_dual : BIProp12_sym_rev.
Proof.
  intros P u Hmon Hered.
  apply inductively_barred_indbarred ; unfold TtoP, PtoT_dual, ABDownmonotonisation, ord.
  induction Hered as [ u Hu | u k IHk] ; [ | now econstructor 2 ].
  econstructor ; intros v Hincl w Heq ; subst.
  apply ord_incl' in Hincl ; rewrite - ord_take in Hincl ; apply ord_inj in Hincl.
  now erewrite <- (cat_take_drop (size u)), <- Hincl ; apply Hmon.
Qed.

(*The next eight Lemmas are Proposition 13 in Brede-Herbelin's paper.*)

(*We start with the four Lemmas that involve choicefun and ABchoicefun.*)


Lemma ABchoice_choice_TtoP : DCProp13.
Proof.
  intros T [alpha Halpha] ; exists alpha ; intros n.
  unfold TtoP.
  specialize (Halpha (iota 0 n)).
  unfold ord ; rewrite ord_map_aux ord_iota_aux - map_comp.
  erewrite eq_map ; [eassumption | ].
  now intros k.
Qed.

Lemma choice_TtoP_ABchoice : DCProp13_rev.
Proof.
  intros T Htree [alpha Halpha] ; exists alpha ; intros u.
  specialize (Halpha (List.list_max u).+1) ; unfold TtoP in Halpha.
  eapply Htree ; [ | eassumption].
  unfold ord ; rewrite ord_map_aux ord_iota_aux - map_comp.
  unshelve erewrite (eq_map (g:= fun i => (i, alpha i)) _ (iota 0 _)) ; [now intros k | ].
  now eapply map_incl, incl_iota_max.
Qed.

Lemma ABchoice_PtoT_choice : DCProp13_sym. 
Proof.
  intros P Htree [alpha Halpha] ; exists alpha ; intros n.
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

Lemma choice_ABchoice_PtoT : DCProp13_sym_rev.
Proof.
  intros T [alpha Halpha].
  apply choice_TtoP_ABchoice ; [ now apply UpABarbor_is_tree | ].
  exists alpha ; intros n.
  now apply P_Uparbor_PtoT, Halpha.
Qed.

(*Let us now tackle the dual Lemmas, focused on barred and ABbarred.*)


Lemma ABbarred_barred_TtoP : BIProp13. 
Proof.
  intros T Hmon HTbar alpha.
  specialize (HTbar alpha) as [u Hu].
  exists (map alpha (iota 0 (List.list_max u).+1)).
  split ; [ unfold prefix ; now rewrite -> size_map, size_iota | ].
  unfold TtoP, ord.
  erewrite ord_map_aux, ord_iota_aux, <- map_comp.
  unshelve erewrite (eq_map (g:= fun i => (i, alpha i))) ; [ | intros ? ; reflexivity].
  eapply Hmon ; [ | eassumption].
  intros [n b] Hin.
  eapply map_incl ; [ | eassumption ].
  now eapply incl_iota_max.
Qed.


Lemma barred_TtoP_ABbarred : BIProp13_rev.
Proof.
  intros T Hbar alpha.
  specialize (Hbar alpha) as [u [Hpref Hu]].
  unfold TtoP in Hu.
  exists (map fst (ord u)).
  set (l := map _ _).
  suff: ord u = l by (intro Heq; rewrite - Heq ; exact Hu).
  clear Hu ; rewrite {}/l.
  erewrite <- map_comp.
  unfold prefix, ord in * ; revert Hpref ; generalize 0.
  induction u ; cbn ;  intros ; [reflexivity | ].
  inversion Hpref as [H0] ; subst ; f_equal.
  now erewrite <- H, <- IHu ; [ | assumption].
Qed.


Lemma ABbarred_PtoT_barred : BIProp13Down.
Proof.
  intros P HTbar alpha.
  suff: barred [|⇓⁺ [P ]ₑ|].
  { intros Hbar ; specialize (Hbar alpha) as [u [Hpref Hu] ].
    exists u ; split ; [assumption | ].
    now apply ABDown_PtoT_P.
  }
  eapply ABbarred_barred_TtoP ; [ | assumption].
  now apply ABDownmonot_monotone.
Qed.


Lemma barred_ABbarred_PtoT : BIProp13Down_rev.
Proof.
  intros P Hmon Hbar.
  eapply barred_TtoP_ABbarred.
  intros alpha ; specialize (Hbar alpha) as [u [Hpref Hu] ].
  exists u ; split ; [assumption | ].
  now apply P_ABDown_PtoT .
Qed.

(*Let us now prove Theorem 5 for Dependent Choice.*)

(*We start with two crucial Lemmas linking choicefun and Downarborification
 for the first one, pruning and Downarborification for the second one.*)

Lemma choicefun_Downarbor_choicefun P :
  choicefun (Downarborification P) ->
  choicefun P.
Proof.
  intros [alpha Halpha] ; exists alpha.
  unfold Downarborification in Halpha.
  intros n ; specialize (Halpha n n).
  now rewrite <- map_take, take_iota, minnn in Halpha.
Qed.

Lemma pruning_pruning_Downarbor (P : list B -> Prop) l :
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
  apply aux ; [eassumption | ].
  intros Hu' n.
  case: (leqP n (size u)) ; intros Hinf.
  { erewrite <- cats1, takel_cat ; [now apply Htake | assumption]. }
  erewrite <- cats1, take_cat.
  erewrite <- (subnSK Hinf).
  apply ltnW, leq_gtF in Hinf ; rewrite Hinf ; cbn ; rewrite cats1.
  now destruct Hyp.
Qed.

(*For the first direction, we prove that GDC is equivalent to its restriction to
 predicates T : list (nat * B) -> Prop that are trees.*)


Lemma GDC_tree T :
  (forall T, ABis_tree T -> ABapprox T nil -> ABchoicefun T) ->
  ABapprox T nil ->
  ABchoicefun T.
Proof.
  intros HGDC Happ.
  suff: ABchoicefun (ABDownarborification T).
  { intros [alpha Hyp].
    exists alpha.
    intros u ; specialize (Hyp u).
    unfold ABDownarborification in *.
    now specialize (Hyp _ (List.incl_refl _)).
  }
  apply HGDC ; [now apply DownABarbor_is_tree | ].
  clear HGDC.
  revert Happ ; generalize (@nil (nat * B)).
  cofix H ; intros u Happ.
  destruct Happ as [u Hu Happ].
  econstructor.
  { intros v Hincl w Hincl'.
    apply Hu ; eapply List.incl_tran ; eassumption.
  }
  intros n Hnotin.
  specialize (Happ n Hnotin) as [b Happ].
  exists b.
  now apply H.
Qed.  


(*Then, from DC, it is possible to derive GDC for tree predicates.*)

Lemma Theorem5: DC -> forall T, ABis_tree T -> ABapprox T nil -> ABchoicefun T.
Proof.
  intros Hyp T Htree Happ.
  apply choice_TtoP_ABchoice ; [assumption | ].
  apply Hyp.
  now apply ABapprox_pruning_TtoP ; [assumption | ].
Qed.  


(*For the reverse direction, we mediate by Lemmas choicefun_Downarbor_choicefun
and pruning_pruning_Downarbor to only deal with arborifications of the predicates 
at hand.*)


Lemma Theorem5rev : (@GDC nat B) -> DC.
Proof.
  intros Hyp P Hprun.
  apply choicefun_Downarbor_choicefun.
  apply ABchoice_PtoT_choice; [apply arbor_is_tree | ].
  unfold GDC in Hyp ; apply Hyp.
  change (@nil (nat * B)) with (ord (@nil B)).
  apply pruning_ABapprox_PtoT.
  eapply pruning_pruning_Downarbor ; [ | assumption ]. 
  intros n ; cbn ; now destruct Hprun.
Qed.



(*For Theorem 5 for BI and GBI, we can try and start with the same technical Lemmas.*)

(*The first one, dual of choicefun_Downarbor_choicefun, goes though.*)

Lemma barred_barred_Upmon (P : list B -> Prop) :
  barred P ->
  barred (Upmonotonisation P).
Proof.
  unfold barred.
  intros Hyp alpha.
  specialize (Hyp alpha) as [u [Hpref Halpha]] ; exists u.
  split ; [assumption | ].
  now rewrite <- cats0 ; econstructor.
Qed.


(*Unfortunately, the second one, dual of pruning_pruning_Downarbor, does not seem
 provable. *)

Lemma hered_Upmon_hered (P : list B -> Prop) l :
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
  econstructor 2 ; intros b ; apply IHk.
  intros n.
  case: (leqP n (size u)) ; intros Hinf.
  2:{ erewrite <- cats1, take_cat.
      erewrite <- (subnSK Hinf).
      now apply ltnW, leq_gtF in Hinf ; rewrite Hinf ; cbn ; rewrite cats1.
  }
  erewrite <- cats1 , takel_cat ; [ | assumption].
  intros Hn ; apply HP in Hn.
  (*There is no way to derive P (u ++ [:: b])) from the hypotheses.*)
Abort.

(*A weaker version is true, assuming that the predicate P is decidable.*)

Lemma hered_Upmon_hered_dec (P : list B -> Prop) (l : list B) :
  (forall u, {P u} + {~ P u}) ->
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
  destruct (Hdec (rcons u b)) as [ | Hypnot] ; [now econstructor | ].
  apply IHk.
  intros n.
  erewrite <- cats1, take_cat.
  case: (leqP (size u) n) ; intros Hinf ; [ | now apply Hnot].
  case : (n - (size u)) ; cbn ; [rewrite cats0 - (take_size u) ; now apply Hnot | ].
  intros _ ; now rewrite cats1.
Qed.


(*We can still prove parts of Theorem 5, though. For instance, GBI is equivalent to its
 restriction to monotone predicates.*)
  
Lemma GBI_monot :
  (forall T : list (nat * B) -> Prop, ABmonotone T -> GBI T) ->
  forall (T : list (nat * B) -> Prop), GBI T.
Proof.
  intros HBI T Hbar.
  suff: forall l,
      indbarred (ABUpmonotonisation T) l ->
      indbarred T l. 
  { intros Hyp.
    apply Hyp.
    apply HBI ; [now apply ABUpmonot_monotone | ].
    apply ABmonot_barred, Hbar.
  }
  clear HBI ; intros l Hl.
  induction Hl.
  { inversion H as [l l' Hl Heq].
    subst.
    econstructor ; [eassumption | ].
    now eapply List.incl_tran ; eassumption.
  }
  econstructor 2. eassumption.
  eassumption.
Qed.

(*Thus BI implies GBI, mediating by the previous Lemma.*)


Lemma BI_GBI : 
  (forall P : list B -> Prop, BI_ind P) ->
  forall (T : list (nat * B) -> Prop), GBI T.
Proof.
  intros HBI.
  apply GBI_monot ; intros T Hmon HTbar.
  change (@nil (nat * B)) with (ord (@nil B)).
  apply inductively_barred_indbarred.
  apply HBI.
  apply ABbarred_barred_TtoP ; assumption.
Qed.


End DC_GDC_BI_GBI.


Section Additional_Lemmas.

  Variable B : Type.

  Notation " ⇑⁺ T " := (ABUpmonotonisation T) (at level 80) : bh_scope.

  Notation " ⇓⁺ T " := (ABDownmonotonisation T) (at level 80) : bh_scope.
  
  Notation " ↑⁺ T " := (Upmonotonisation T) (at level 80) : bh_scope.
  
  Notation " ↓⁺ T " := (Downmonotonisation T) (at level 80) : bh_scope.
  
  Notation " [| T |] " := (TtoP T) (at level 0) : bh_scope.
  
  Notation " [ P ]ₐ " := (PtoT P) (at level 0) : bh_scope.
  
  Notation " [ P ]ₑ " := (PtoT_dual P) (at level 0) : bh_scope.

  
(*These lemmas with Upmonotonisation are true, even though they do not appear
  in the proof of equivalence between GBI and BI in Brede-Herbelin's paper.*)
Definition BIProp11Up :=
  forall (P : list B -> Prop) l, P l -> [| ⇑⁺  [ P ]ₐ |] l.


Definition BIProp11Up_rev :=
  forall (P : list B -> Prop) l, monotone P -> [| ⇑⁺  [ P ]ₐ |] l -> P l.

Definition BIProp12Up :=
  forall (P : list B -> Prop) u,
    monotone P -> indbarred (⇑⁺ [ P ]ₐ) (ord u) ->
    hereditary_closure P u.

Definition BIProp12Up_rev :=
  forall (P : list B -> Prop) u, hereditary_closure P u ->
                                 indbarred (⇑⁺  [ P ]ₐ) (ord u).

Definition BIProp13Up_rev :=
  forall (P : seq B -> Prop), monotone P -> barred P -> ABbarred (⇑⁺ [ P ]ₐ).


Lemma P_ABUp_PtoTB : BIProp11Up.
Proof.
  intros P l Hl.
  unfold TtoP.
  econstructor ; [econstructor ; eassumption | ].
  now apply List.incl_refl.
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


Lemma indbarred_inductively_barred_dual : BIProp12Up.
Proof.
  intros P u Hmon Hbar.
  suff: hereditary_closure (TtoP (ABUpmonotonisation (PtoT P))) u.
  { clear Hbar.
    intros Hbar.
    induction Hbar as [u Hyp | u k IHk] ;
      [econstructor ; now eapply monotone_ABUp_PtoT_P | ].
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
  do 2 econstructor ; [now econstructor ; eassumption | ].
  now apply List.incl_refl.
Qed.

Lemma barred_ABbarred_PtoT_Up : BIProp13Up_rev.
Proof.
  intros P Hmon Hbar alpha ; specialize (Hbar alpha) as [u [Hpref Hu]].
  exists (iota 0 (size u)).
  econstructor ; [ | now eapply List.incl_refl ].
  erewrite (eq_map (g := (fun i => (i.1, alpha i.2)) \o (fun n => (n, n)))),
    map_comp, <- ord_iota_aux, <- ord_map_aux ; [ | now intro k].
  econstructor.
  unfold prefix in Hpref ; rewrite - Hpref.
  assumption.
Qed.

End Additional_Lemmas.


Section GBI_dec.

  Variables B : eqType.
  Implicit Type (T : seq (nat * B) -> Prop).

Notation " ⇑⁺ T " := (ABUpmonotonisation T) (at level 80) : bh_scope.

Notation " ⇓⁺ T " := (ABDownmonotonisation T) (at level 80) : bh_scope.

Notation " ↑⁺ T " := (Upmonotonisation T) (at level 80) : bh_scope.

Notation " ↓⁺ T " := (Downmonotonisation T) (at level 80) : bh_scope.

Notation " [| T |] " := (TtoP T) (at level 0) : bh_scope.

Notation " [ P ]ₐ " := (PtoT P) (at level 0) : bh_scope.

Notation " [ P ]ₑ " := (PtoT_dual P) (at level 0) : bh_scope.

Definition ABmonotone_size T :=
  (forall l l' : seq (nat * B), List.incl l l' -> size l <= size l' -> T l -> T l').

Inductive ABUpmonotonisation_size (C : Type) (T : seq C -> Prop) : seq C -> Prop :=
  Tmon_size : forall l l' : seq C, T l ->
                              List.incl l l' ->
                              size l <= size l' ->
                              (ABUpmonotonisation_size T) l'.

Notation " ⇑⁺s T " := (ABUpmonotonisation_size T) (at level 80) : bh_scope.

Lemma ABUpsize_monotone_size T :
  ABmonotone_size (⇑⁺s T).
Proof.
  intros u w Hincl Hsize HT ; destruct HT as [u v HT Hincl' Hsize'].
  econstructor ; [eassumption | | ].
  + eapply List.incl_tran ; eassumption.
  + eapply leq_trans ; eassumption.
Qed.

Lemma included_size {X : eqType} (v : seq X) :
  { L : seq (seq X) | forall (u : seq X),
      (List.incl u v /\ size u <= size v) <->
        u \in L}.
Admitted.

(*We first prove that monotonisation preserves decidability. *)

Lemma Upmono_dec {X} (P : list X -> Prop) :
  (forall u, {P u} + {~ P u}) ->
  (forall u, {(↑⁺ P) u} + {~ (↑⁺ P) u}).
Proof.
  intros Hdec u.
  suff: { exists v, exists w, u = v ++ w /\ P v } +
          { ~ exists v, exists w, u = v ++ w /\ P v }.
  { intros [Htrue | Hfalse] ; [left | right].
    { destruct Htrue as [v [w [Heq Hv]]] ; subst ; now econstructor. }
    intros HP ; inversion HP as [l l' Hl Heq] ; subst.
    apply Hfalse.
    exists l ; exists l' ; split ; trivial.
  }
  induction u as [ | u b IHu] using last_ind.
  { destruct (Hdec nil) as [Htrue | Hfalse] ; [left | right].
    { exists nil ; exists nil ; split ; now trivial. }
    intros [v [w [Heq Hv]]] ; apply Hfalse.
    symmetry in Heq ; apply List.app_eq_nil in Heq as [Heqv Heqw] ; now subst.
  }
  destruct (Hdec (rcons u b)) as [Htrue | Hfalse] ; [left | ].
  { exists (rcons u b) ; exists nil ; rewrite cats0 ; now split. }
  destruct IHu as [Hu | Hu] ; [left | right].
  { destruct Hu as [v [w [Heq Hv]]] ; subst ; rewrite <- cats1.
    exists v ; exists (w ++ (cons b nil)) ; split ; [ | assumption].
    now rewrite catA.
  }
  intros [v [w [Heq Hv]]].
  destruct w as [ | w c IHw] using last_ind.
  { apply Hfalse ; rewrite cats0 in Heq ; now subst. }
  apply Hu ; exists v ; exists w; split ; [ | assumption].
  rewrite <- rcons_cat in Heq.
  assert (aux := f_equal (last b) Heq) ;  do 2 rewrite last_rcons in aux ; subst.
  eapply rcons_injl.
  exact Heq.
Qed.

Lemma PtoT_dec (P : list B -> Prop) :
  (forall u, {P u} + {~ P u}) ->
  (forall u, {[P ]ₐ u} + {~ [P ]ₐ u}).
Proof.
  intros Hdec u.
  destruct u ; [destruct (Hdec nil) as [Htrue | Hfalse] ; [left | right] | ].
  { change (@nil (nat * B)) with (ord (@nil B)) ; now econstructor. }
  { intros Hyp ; inversion Hyp as [u Hu Heq] ; apply Hfalse.
    change (@nil (nat * B)) with (ord (@nil B)) in Heq ; unfold ord in *.
    now apply ord_inj in Heq ; subst.
  }
  case: (ord_dec (p :: u)) ; [intros [v [n Heq]] ; subst | intros Hnoteq].
  { destruct v as [ | b v ] ; cbn in * ; inversion Heq ; subst.
    destruct n ; [ | right].
    2:{ intros Hyp ; inversion Hyp ; unfold ord in *.
        destruct l ; cbn in * ; now inversion H. }
    clear Heq.
    change ((0, b) :: ord_aux v 1) with (ord (b :: v)). 
    destruct (Hdec (b :: v)) as [Htrue | Hfalse] ; [left ; now econstructor | right].
    intros Hyp ; inversion Hyp as [u Hu Heq] ; unfold ord in *.
    apply ord_inj in Heq ; subst ; now apply Hfalse.
  }
  right ; intros Hyp ; inversion Hyp as [v Hv Heq].
  apply (Hnoteq v 0) ; symmetry ; exact Heq.
Qed.


(*Finally, we conclude that GBI for decidable predicates implies
 BI for decidable predicates.*)

Lemma upP T u : (↑⁺ T) u -> (⇑⁺ T) u.
Proof.
case => l l' Tl.
apply: (Tmon Tl).
exact: List.incl_appl.
Qed.
  

Lemma ABUpmono_size_dec T :
  (forall u, {T u} + {~ T u}) ->
  forall u, {(⇑⁺s T) u} + {~ (⇑⁺s T) u}.
Proof.
  intros Hdec u.
  destruct (included_size u) as [L HL].
  suff: decidable (exists2 v : seq (nat * B), v \in L & T v).
  { intros [Hyp | Hnot]; [left | right].
    - destruct Hyp as [v Hin HT].
      apply HL in Hin as [Hincl Hsize].
      exists v ; easy.
    - intros HT ; destruct HT as [u v HT Hincl Hsize].
      apply Hnot.
      exists u ; auto.
      apply HL ; now split.
  }
  unshelve eapply decP ; [exact (has Hdec L) | ].
  apply hasPP ; intros x.
  now eapply sumboolP.
Qed.  

(* This is the crucial decidability argument for the next result *)
Lemma ABUp_Up_dec (P : list B -> Prop) u : 
  (forall v, decidable (P v)) -> decidable ((⇑⁺ [↑⁺ P ]ₐ) u).
Proof.
  move=> Hdec.
  set Q := (X in (X u)).
  pose Q1 w := exists v1, exists v2, P v1 /\ List.incl (ord (v1 ++ v2)) w.
  have Q1P w : Q1 w <-> Q w.
    split; last first.
    - by case=> w1 w2 [w3 [w4 w5 Pw5]] hi12; exists w4; exists w5.
    - case=> [w1 [w2 [Pw1 hi]]].
      econstructor; last by eassumption.
      constructor.
      by constructor.
  suffices {Q1P Q} : decidable (Q1 u) by apply: decidable_iff. 
  (* Q2 describes a decision algorithm for Q1 *)
  pose Q2 w := exists n :'I_(size w).+1, (* size of v1 ++ v2 *)
               exists m : (size w).-tuple bool, (* selecting the elements of ord (v1 ++ v2) in w *)
               exists v : seq (nat * B), 
               [/\ (v \in permutations (mask m w)), (* the actual ord (v1 ++ v2) *)
               (unzip1 v = iota 0 n) & (* unzip1 v1 ++ v2 should form a iota *)
               (exists k : 'I_n.+1, P (unzip2 (take k v)))]. (* a prefix v is in P *)
  have Q2P w : Q2 w <-> Q1 w.
  split; last first.
  - case=> v1 [v2 [Pv1 hi]].
    have p1 : size (v1 ++ v2) < (size w).+1.
      rewrite - (size_ord _ 0) ltnS. 
      apply: uniq_leq_size; last exact/inclP.
      by have /NoDupP := ord_NoDup 0 (v1 ++ v2). (* apply/NoDuP does not work ? *)
    exists (Ordinal p1) => /=.
    have /count_subseqP [vw /subseqP [m sm em] evw]: 
      forall x : nat * B, count_mem x (ord (v1 ++ v2)) <= count_mem x w.
       move=> x /=; apply: leq_uniq_count; last exact/inclP.
       apply/NoDupP; exact: ord_NoDup.
    have pm : size m == size w by apply/eqP.
    exists (Tuple pm).
    exists (ord (v1 ++ v2)).
    rewrite unzip1_ord mem_permutations -em; split=> //.
    have p2 : size v1 < (size (v1 ++ v2)).+1 by rewrite size_cat ltnS leq_addr.
    exists (Ordinal p2) => /=.
    by rewrite /ord ord_cat take_cat size_ord ltnn subnn take0 cats0 unzip2_ord.
  - case=> n [m [vw [pvw ivw [k hP]]]].
    exists (unzip2 (take k vw)).
    exists (unzip2 (drop k vw)).
    split=> //.
    have -> : unzip2 (take k vw) ++ unzip2 (drop k vw) = unzip2 vw.
      by rewrite -[LHS]map_cat cat_take_drop.
    apply/inclP=> /= x.
    rewrite /ord ordP size_map.
    have -> : size vw = n.
      by rewrite -[RHS](size_iota 0) -ivw size_map.
    rewrite -ivw zip_unzip.
    have /perm_mem-> : perm_eq vw (mask m w) by rewrite -mem_permutations.
    by move/mem_mask.
  suffices {Q2P Q1} : decidable (Q2 u) by apply: decidable_iff.
  (* Now really turn Q3 into a boolean test, using mathcomp's reflection infrastructure *)
  pose test n v : bool := 
    (unzip1 v == iota 0 n) && [exists k : 'I_n.+1, Hdec (unzip2 (take k v))].
  have testP n v: reflect (unzip1 v = iota 0 n /\ exists k: 'I_n.+1, P (unzip2 (take k v))) (test n v).
    apply: (iffP idP).
    - case/andP=> /eqP-> /existsP [k hP]; split=> //; exists k. 
      move: hP; case: (Hdec _)=> //.
    - rewrite /test; case=> -> [k Pk]; rewrite eqxx /=; apply/existsP; exists k. 
      by case: (Hdec _).
  pose Q3 w : bool := 
  [exists n : 'I_(size w).+1, [exists m : (size w).-tuple bool,
    has (test n) (permutations (mask m w))]]. 
  (* Should be a syntax directed proof, but no automation really works here *)
  suffices : reflect (Q2 u) (Q3 u) by exact: decP.
    apply: (iffP idP).
    - case/existsP=> /= n /existsP /= [m /hasP /= [v permv /testP [zip1v [k Pk]]]].
      by exists n; exists m; exists v; split=> //; exists k.
    - case=> n [m [vw [pvw ivw [k hP]]]].
      apply/existsP; exists n; apply/existsP; exists m; apply/hasP=> /=.
      exists vw => //.
      apply/testP; split=> //.
      by exists k.
Qed.

Lemma GBI_BI_dec :
  (forall (T : list (nat * B) -> Prop), (forall u, decidable (T u)) -> GBI T) ->
  forall P : list B -> Prop, (forall u, decidable (P u)) -> BI_ind P.
Proof.
  intros HGBI P Hdec Hbar.
  destruct (Hdec nil) as [Hnil | Hnotnil] ; [now econstructor | ].
  apply hered_Upmon_hered_dec ; [assumption | | intros n ; cbn ; eassumption ].
  apply indbarred_inductively_barred_dual ; [now apply Upmonot_monotone | ].
  apply HGBI; first by move=> u; apply: ABUp_Up_dec.
  apply barred_ABbarred_PtoT_Up ; [now apply Upmonot_monotone | ].
now apply monot_barred.
Qed.

Print GBI_monot.
(*
Lemma ABUpmono_dec T : (forall u, decidable (T u)) ->
                       forall u : seq (nat * B), decidable ((⇑⁺ T) u).
Proof.
  intros Hdec u.
  set Q := (X in (X u)).
  Print ABUpmonotonisation.
  pose Q1 w := exists v, T v /\ List.incl v w.
  have Q1P w : Q1 w <-> Q w.
    split; last first.
    - by case=> w1 w2 hi12 ; exists w1.
    - case=> [w1 [Pw1 hi]].
      now econstructor; last by eassumption.
  suffices {Q1P Q} : decidable (Q1 u) by apply: decidable_iff. 
  (* Q2 describes a decision algorithm for Q1 *)
  pose Q2 w := exists n :'I_(size w).+1, (* size of v1 ++ v2 *)
               exists m : (size w).-tuple bool, (* selecting the elements of ord (v1 ++ v2) in w *)
               exists v : seq (nat * B), 
                 [/\ (v \in permutations (mask m w)) & (* the actual ord (v1 ++ v2) *)
                   T v].
  have Q2P w : Q2 w <-> Q1 w.
  split; last first. *)

Lemma GBI_monot_dec :
  (forall T : seq (nat * B) -> Prop, ABmonotone_size T -> (forall u, decidable (T u)) -> GBI T) ->
  forall T : seq (nat * B) -> Prop, (forall u, decidable (T u)) -> GBI T.
Proof.
  intros HBI T Hdec Hbar.
  suff: forall l,
      indbarred (ABUpmonotonisation_size T) l ->
      indbarred T l. 
  { intros Hyp.
    apply Hyp.
    apply HBI ; [now eapply ABUpsize_monotone_size | | ].
    1: now eapply ABUpmono_size_dec.
    intros alpha ; specialize (Hbar alpha) as [u Hu].
    exists u ; econstructor ; [eassumption | | ].
    1: now eapply List.incl_refl.
    now eapply leqnn.
  }
  clear HBI ; intros l Hl.
  induction Hl.
  { inversion H as [v w Hv Hincl Hsize Heq] ; subst.
    econstructor ; [eassumption | ].
    now eapply List.incl_tran ; eassumption.
  }
  econstructor 2. eassumption.
  eassumption.
Qed.


Lemma ABbarred_barred_TtoP_size_inf :
  forall T,
    ABmonotone_size T ->
    ABbarred T ->
    barred [|T|].
Proof.
  intros T Hmon HTbar alpha.
  specialize (HTbar alpha) as [u Hu].
  exists (map alpha (iota 0 (addn (List.list_max u).+1 (size u)))).
  split ; [ unfold prefix ; now rewrite -> size_map, size_iota | ].
  unfold TtoP, ord.
  erewrite ord_map_aux, ord_iota_aux, <- map_comp.
  unshelve erewrite (eq_map (g:= fun i => (i, alpha i))) ; [ | intros ? ; reflexivity].
  eapply Hmon ; [ | | eassumption].
  + intros [n b] Hin.
    eapply map_incl ; [ | eassumption ].
    eapply List.incl_tran ; [ now eapply incl_iota_max | ].
    rewrite iotaD.
    now eapply List.incl_appl, List.incl_refl.
  + rewrite size_map size_map size_iota.
    now eapply leq_addl.
Qed.

Lemma BI_GBI_dec :
  (forall P : list B -> Prop, (forall u, decidable (P u)) -> BI_ind P) ->
  forall (T : list (nat * B) -> Prop), (forall u, decidable (T u)) -> GBI T.
Proof.
  intros HBI ; eapply GBI_monot_dec.
  intros T Hmon Hdec Hbar.  
  destruct (Hdec nil) as [Hnil | Hnotnil].
  1:{ econstructor ; [eassumption | now eapply List.incl_refl]. }
  change (@nil (nat * B)) with (ord (@nil B)).
  eapply inductively_barred_indbarred.
  apply HBI ; unfold TtoP.
  1: intros u ; now eapply Hdec.
  eapply ABbarred_barred_TtoP_size_inf ; eauto.
Qed.

End GBI_dec.

Section GDC_gen.

  (*The goal of this Section is to prove inconsistency of some forms of GDC and GBI.*)


  (*We start by proving that GDC on (nat -> Prop) and nat is inconsistent.
   The goal is to derive an injection from (nat -> Prop) to nat, which is 
   inconsistent by the Cantor Theorem for Prop, proven in cantor.v*)  
  Proposition GDC_inconsistent :
    @GDC (nat -> Prop) nat -> False.
  Proof.
    unfold GDC ; intros HypGDC.
    pose (T := fun (u : seq ((nat -> Prop) * nat)) =>
                 forall f f' n n', List.In (f, n) u ->
                                   List.In (f', n') u ->
                                   n = n' ->
                                   f = f').
    (*If T has a choice function F then F is an injection from (nat -> Prop) to nat,
     which is inconsistent.*)
    suff: ABchoicefun T.
    { intros [F HF].
      have Heq : forall alpha beta, F alpha = F beta -> alpha = beta.
      { intros alpha beta Heq.
        eapply (HF (alpha :: beta :: nil)) ; [left | right ; left | ] ; now trivial.
      }
      eapply Cantor_Prop.
      exact Heq.
    }
    apply HypGDC.
    (*We need to slightly generalize the goal.*)
    suff Happrox : forall u, T u ->
                        (forall f n, List.In (f,n) u -> n < size u) ->
                        ABapprox T u.
    { apply Happrox ; [intros f f' n n' Hinf Hinf' | intros f n Hinf] ; now inversion Hinf. }
    (*All that is left is to prove Happrox, via cofix reasoning. *)
    cofix aux.
    intros u Hu Hinf ; econstructor.
    { unfold ABDownarborification.
      intros v Hincl f f' n n' Hin Hin' Heqn.
      eapply Hu ; [ apply Hincl | apply Hincl | ] ; eassumption.
    }
    intros f Hnotin.
    exists (size u).
    apply aux.
    { intros g g' n n' Hin Hin' Heqn.
      rewrite <- cats1 in Hin, Hin'.
      apply List.in_app_or in Hin, Hin'.
      destruct Hin.
      { destruct Hin' ; [eapply Hu ; eassumption | ] ; cbn in *.
        destruct H0 ; [ | now exfalso].
        inversion H0 ; subst.
        apply Hinf in H ; rewrite -> subSnn in H ; now inversion H.
      }
      destruct H ; [ | now exfalso] ; inversion H ; subst ; clear H.
      destruct Hin' as [H | H] ; cbn in *.
      2:{ destruct H ; [ | now exfalso] ; now inversion H. }
      apply Hinf in H ; rewrite -> subSnn in H ; now inversion H.
    }
    intros g m Hinm ; rewrite size_rcons.
    rewrite <- cats1 in Hinm ; apply List.in_app_or in Hinm.
    destruct Hinm as [H | H].
    2:{ destruct H ; [ | now exfalso] ; inversion H ; subst.
        now apply ltnSn.
    }
    apply Hinf in H.
    now apply leqW.
  Qed.


  Lemma ABbarred_choicefun {A B}
    (DNE : forall P : Prop, ~ ~ P -> P)
    (T : seq (A * B) -> Prop) :
    ~ ABchoicefun (fun l => ~ T l) -> ABbarred T .
  Proof.
    intros Hyp.
    intros alpha ; unfold ABchoicefun in Hyp.
    apply DNE.
    intros H ; apply Hyp.
    exists alpha ; intros u Hu ; apply H ; now exists u.
  Qed.


  
  (*For GBI we need more, probably DNE.*)
  Proposition GBI_inconsistent
    (DNE : forall P : Prop, ~ ~ P -> P) :
    (forall T, @GBI (nat -> Prop) nat T) -> False.
  Proof.
    unfold GBI ; intros HGBI.
    pose (T:= fun (u : seq ((nat -> Prop) * nat)) =>
                (exists f f' n, ~ (f = f') /\ List.In (f, n) u /\ List.In (f', n) u)).
    have H1: ABbarred T.
    { apply ABbarred_choicefun ; auto.
      intros [F HF] ; unfold T in HF.
      have Heq : forall alpha beta, F alpha = F beta -> alpha = beta.
      { intros alpha beta Heq.
        eapply DNE ; intros Hneq ; eapply (HF (alpha :: beta :: nil)).
        exists alpha, beta, (F alpha) ; split ; [auto | split] ; cbn.
        + now left.
        + now right ; left ; rewrite Heq.
      }
      eapply Cantor_Prop.
      exact Heq.
    }
    apply (HGBI _) in H1.
    suff: forall u, ~ T u -> indbarred T u -> False.
    { intros Hyp.
      apply (Hyp nil) ; [ | assumption].
      intros [f [f' [m [Hneq [Hinf Hinf']]]]] ; inversion Hinf.
    }
    clear H1 ; unfold T ;clear T.
    intros u Hu Hind.
    revert Hu ; induction Hind as [u v [f [f' [m [Hneq [Hinf Hinf']]]]] | ]; intros Hu.
    { eapply Hu ; exists f, f', m ; split ; [trivial | split ; now apply H]. }
    suff: exists n : nat,  ~ List.In n [seq i.2 | i <- v].
    { intros [n Hn].
      apply (H1 n).
      intros [f [f' [m [Hneq [Hinf Hinf']]]]].
      apply List.in_app_or in Hinf, Hinf'.
      destruct Hinf as [Hf | Hf], Hinf' as [Hf' | Hf'].
      + eapply Hu ; eauto.
        exists f, f', m ; split ; now auto.
      + exfalso ; cbn in Hf' ; destruct Hf' as [Hf' | Hf'] ; auto.
        inversion Hf' ; subst.
        now apply Hn, (in_map (fun x => x.2) Hf).
      + exfalso ; cbn in Hf ; destruct Hf as [Hf | Hf] ; auto.
        inversion Hf ; subst.
        now apply Hn, (in_map (fun x => x.2) Hf').
      + cbn in Hf, Hf'.
        destruct Hf as [Hf | ], Hf' as [Hf' | ] ; try now exfalso.
        now inversion Hf ; inversion Hf' ; subst.
    }
    generalize [seq i.2 | i <- v] ; clear ; intros l.
    suff: exists n : nat, List.Forall (lt^~ n) l.
    { intros [n Hn] ; exists n ; intros Hin.
      induction l ; [now inversion Hin | ].
      destruct Hin as [Heq | Hin] ; subst ; cbn in *.
      + inversion Hn as [ | ? ? Hinf ?] ; subst ; eapply PeanoNat.Nat.lt_irrefl ; eauto.
      + inversion Hn as [ | ? ? ? Hinf] ; subst.
        exact (IHl Hinf Hin).
    }
    destruct l as [ | n l] ; [exists 0 ; auto | ].
    exists ((List.list_max (n :: l)).+1).
    eapply List.list_max_lt ; eauto ; intros Heq ; inversion Heq.
Qed.    
    
    

End GDC_gen.


Section BI_mon.
  Variable (B : Type).

    
Inductive hered_mon (T : list B -> Prop) : list B -> Prop :=
  | sefl_mon u u' : T u -> hered_mon T (u ++ u')
  | sons_mon u : (forall b, hered_mon T (rcons u b)) -> hered_mon T u.

Definition BI_alt P := barred P -> hered_mon P [::].


(*In this section, we show that a monotonised version of hereditary_closure
   is equivalent to GBI for predicates on natural numbers.*)
  
Lemma BI_GBI_alt : 
  (forall P : list B -> Prop, BI_alt P) ->
  forall (T : list (nat * B) -> Prop), GBI T.
Proof.
  intros HBI.
  apply GBI_monot.
  intros T Hmon HTbar.
  change (@nil (nat * B)) with (ord (@nil B)).
  suff: hered_mon (TtoP T) nil.
  { generalize (@nil B) ; clear.
    intros l ; induction 1 as [ u v Hyp | u k IHk].
    { unfold TtoP in Hyp ; econstructor ; [eassumption | ].
      unfold ord ; erewrite ord_cat.
      apply List.incl_appl ; now eapply List.incl_refl. }
    unshelve econstructor 2 ; [exact (size u) | | ].
    { unfold ord ; exact (@ord_sizeu_notin _ u 0). }
    unfold ord in * ; intros a ; specialize (IHk a).
    erewrite ord_rcons, <- plus_n_O in IHk.
    now rewrite cats1.
  }
  apply HBI ; unfold TtoP.
  apply ABbarred_barred_TtoP ; assumption.
Qed.

(*GBI for all predicates also implies BI for decidable predicates, making use of 
 barred_Upmon_barred and hered_Upmon_hered_dec. *)

Lemma GBI_BI_alt :
  (forall (T : list (nat * B) -> Prop), GBI T) ->
  forall (P : list B -> Prop), BI_alt P.
Proof.
  intros HGBI P Hbar.
  suff: hered_mon (Upmonotonisation P) nil.
  { generalize (@nil B) ; induction 1 as [u v Hyp | u k IHk].
    2: econstructor 2 ; now apply IHk.
    destruct Hyp ; rewrite <- catA.
    now econstructor.
  }
  have Hbar_alt: barred (Upmonotonisation P) ; [ | clear Hbar].
  { intros alpha ; specialize (Hbar alpha) as [u [Hpref Hu]].
    exists u ; split ; [assumption |].
    now rewrite <- cats0 ; econstructor.
  }
  apply barred_ABbarred_PtoT in Hbar_alt ; [ | now apply Upmonot_monotone].
  apply HGBI in Hbar_alt.
  change (@nil (nat * B)) with (ord (@nil B)) in Hbar_alt.
  apply indbarred_inductively_barred_Down_dual in Hbar_alt.
  induction Hbar_alt.
  { destruct H ; econstructor ; erewrite <- cats0 ; now  econstructor. }
  now econstructor 2.
Qed.  

  
End BI_mon.
