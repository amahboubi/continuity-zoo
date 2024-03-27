From mathcomp Require Import all_ssreflect.
Require Import extra_principles.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Section Ord.
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

Section DC_GDC_BI_GBI.
  Variables A B : Type.
Implicit Type (T : seq (nat * B) -> Type).

Definition is_tree (P : list B -> Type) :=
  forall u n, P u -> P (take n u).

Definition Downarborification (P : list B -> Type) (u : list B) : Type :=
  forall n, P (take n u).

Notation " ↓⁻ T " := (Downarborification T) (at level 80).


CoInductive pruning (P : list B -> Type) : list B -> Type :=
  prune a u : P u -> pruning P (rcons u a) -> pruning P u.

Definition choicefun (P : list B -> Type) :=
  {alpha : nat -> B & forall n : nat, P [seq (alpha i) | i <- iota 0 n] }.

Definition DC := forall (P : list B -> Type), pruning P nil -> choicefun P.

Definition ABis_tree T :=
  forall u v, List.incl v u -> T u -> T v.

Inductive ABUparborification T : list (nat * B) -> Type :=
| Tarbor l l' : T l -> List.incl l' l -> ABUparborification T l'.

Definition ABDownarborification T u : Type :=
  forall v, List.incl v u -> T v.

Notation " ⇑⁻ T " := (ABUparborification T) (at level 80).

Notation " ⇓⁻ T " := (ABDownarborification T) (at level 80).


Definition ABchoicefun T :=
  {alpha : nat -> B & forall u : list nat, T [seq (i, alpha i) | i <- u]}.

CoInductive ABapprox T : list (prod nat B) -> Type :=
  approx u : (⇓⁻ T) u ->
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

Notation " ↑⁺ T " := (Upmonotonisation T) (at level 80).

Notation " ↓⁺ T " := (Downmonotonisation T) (at level 80).


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

(* Generalized Bar Induction, phrased using the Herbelin-Brede way *)
Definition GBI T := ABbarred T -> indbarred T [::].


Definition ABmonotone {C} (P : list C -> Type) :=
  forall l l', List.incl l l' -> P l -> P l'.

Inductive ABUpmonotonisation {C} (T : list C -> Type) : list C -> Type :=
| Tmon l l' : T l -> List.incl l l' -> ABUpmonotonisation T l'.

Definition ABDownmonotonisation {C} (T : list C -> Type) : list C -> Type :=
  fun u => forall v, List.incl u v -> T v.

Notation " ⇑⁺ T " := (ABUpmonotonisation T) (at level 80).

Notation " ⇓⁺ T " := (ABDownmonotonisation T) (at level 80).

Lemma Upmonot_monotone {C} P : @monotone C (↑⁺ P).
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


Definition TtoP (T : list (nat * B) -> Type) (l : list B) : Type :=
  T (ord l).

Notation " [| T |] " := (TtoP T) (at level 8).

Inductive PtoT (P : list B -> Type) : list (nat * B) -> Type :=
| ptot : forall l, P l -> PtoT P (ord l).

Definition PtoT_dual (P : list B -> Type) : list (nat * B) -> Type :=
  fun u => forall v, u = ord v -> P v.

Notation " [ P ]ₐ " := (PtoT P) (at level 8).
Notation " [ P ]ₑ " := (PtoT_dual P) (at level 8).

Definition TtoP_PtoT_ret P : forall l, P l -> [| [ P ]ₐ |] l :=
  fun l Hl => ptot Hl.

Lemma TtoP_PtoT_inv P : forall l, [| [ P ]ₐ |] l -> P l.
Proof.
  intros u H.
  inversion H.
  now eapply ord_inj in H1 ; subst.
Qed.  


Lemma PtoT_TtoP_inv (T : list (nat * B) -> Type) l :
  [ [| T |] ]ₐ l -> T l. 
Proof.
  unfold TtoP ; intros H.
  inversion H ; now subst.
Qed.

Lemma PtoT_TtoP_ret (T : list (nat * B) -> Type) u :
  T (ord u) -> [ [| T |] ]ₐ (ord u). 
Proof.
  intro H ; econstructor.
  unfold TtoP ; assumption.
Qed.

Definition DCProp11 :=
  forall (P : list B -> Type) u, P u ->  [| ⇑⁻ [ P ]ₐ |] u.

Definition BIProp11Down :=
  forall (P : list B -> Type) u, monotone P -> P u -> [| ⇓⁺ [ P ]ₑ |] u.

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
  inversion X ; subst.
  apply ord_incl' in H.
  rewrite - ord_take in H ; apply ord_inj in H ; rewrite H.
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
    destruct u as [ | u b IHu] using last_ind ; [now inversion Heq | ] ; clear IHu.
    exists (nth b (rcons u b) n).
    eapply aux ; [ exact Hprun | ].
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
  (*Coq does not recognize this proof as productive, probably because of
   interaction between coinduction and induction. *)
Admitted.


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

Lemma pruning_pruning_Downarbor P l :
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
 predicates T : list (nat * B) -> Type that are trees.*)


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


Lemma Theorem5rev : GDC -> DC.
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

Lemma barred_barred_Upmon (P : list B -> Type) :
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

Lemma hered_Upmon_hered (P : list B -> Type) l :
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

Lemma hered_Upmon_hered_dec (P : list B -> Type) (l : list B) :
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
  destruct (Hdec (rcons u b)) ; [now econstructor | ].
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
  (forall T : list (nat * B) -> Type, ABmonotone T -> GBI T) ->
  forall (T : list (nat * B) -> Type), GBI T.
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
  { inversion t as [l l' Hl Heq].
    subst.
    econstructor ; [eassumption | ].
    now eapply List.incl_tran ; eassumption.
  }
  econstructor 2. eassumption.
  eassumption.
Qed.

(*Thus BI implies GBI, mediating by the previous Lemma.*)


Lemma BI_GBI : 
  (forall P : list B -> Type, BI_ind P) ->
  forall (T : list (nat * B) -> Type), GBI T.
Proof.
  intros HBI.
  apply GBI_monot ; intros T Hmon HTbar.
  change (@nil (nat * B)) with (ord (@nil B)).
  apply inductively_barred_indbarred.
  apply HBI.
  apply ABbarred_barred_TtoP ; assumption.
Qed.

(*GBI for all predicates also implies BI for decidable predicates, making use of 
 barred_Upmon_barred and hered_Upmon_hered_dec. *)

Lemma GBI_BI_mon :
  (forall (T : list (nat * B) -> Type), GBI T) ->
  forall P : list B -> Type, (forall u, (P u) + (P u -> False)) -> BI_ind P.
Proof.
  intros HGBI P Hdec Hbar.
  destruct (Hdec nil) as [Hnil | Hnotnil] ; [now econstructor | ].
  apply hered_Upmon_hered_dec ; [assumption | | intros n ; cbn ; eassumption ].
  apply indbarred_inductively_barred_Down_dual.
  apply HGBI.
  apply barred_ABbarred_PtoT ; [now apply Upmonot_monotone | ].
  now apply barred_barred_Upmon.
Qed.

(*We can probably strengthen the previous Lemma and prove that GBI for decidable predicates
 implies BI for decidable predicates. Indeed, all constructions seem to preserve decidability
 of the underlying predicates.*)


End DC_GDC_BI_GBI.


Section Additional_Lemmas.

Variable B : Type.
  
(*These lemmas with Upmonotonisation are true, even though they do not appear
  in the proof of equivalence between GBI and BI.*)
Definition BIProp11Up :=
  forall (P : list B -> Type) l, P l -> TtoP (ABUpmonotonisation (PtoT P)) l.

Definition BIProp11Up_rev :=
  forall (P : list B -> Type) l, monotone P -> TtoP (ABUpmonotonisation (PtoT P)) l -> P l.

Definition BIProp12Up :=
  forall (P : list B -> Type) u,
    monotone P -> indbarred (ABUpmonotonisation (PtoT P)) (ord u) ->
    hereditary_closure P u.

Definition BIProp12Up_rev :=
  forall (P : list B -> Type) u, hereditary_closure P u ->
              indbarred (ABUpmonotonisation (PtoT P)) (ord u).


Lemma P_ABUp_PtoTB : BIProp11Up.
Proof.
  intros P l Hl.
  unfold TtoP.
  econstructor ; [econstructor ; eassumption |].
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

End Additional_Lemmas.
