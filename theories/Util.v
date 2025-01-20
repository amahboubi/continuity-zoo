From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.



Lemma iota_rcons (i j : nat) : rcons (iota i j) (i + j) = iota i j.+1.
Proof.
have -> : iota i j.+1 = iota i (j + 1) by rewrite addn1.
by rewrite -cats1 iotaD.
Qed.

Lemma decidable_iff P Q : (P <-> Q) ->  decidable P -> decidable Q.
Proof.
by move=> h [hP | hQ]; [left | right]; apply/h.
Qed.


(* Boolean analogues of List predicates when the carrier type has a decidable eq *)
Lemma InP {X : eqType} (u : seq X) x : reflect (List.In x u) (x \in u).
Proof.
elim: u => [ |y u ihu]; apply: (iffP idP)=> //=.
- rewrite in_cons; case/orP=> h.
  + by rewrite (eqP h); left.
  + by right; apply/ihu.
- case=> [-> | /ihu]; rewrite in_cons.
  + by rewrite eqxx.
  + by move->; rewrite orbT.
Qed.

Lemma NoDupP {X : eqType} (u : seq X) : reflect (List.NoDup u) (uniq u).
Proof.
elim: u => [ |x u ihu]; apply: (iffP idP)=> //=.
- move=> _; constructor.
- case/andP=> nxu uu.
  constructor; last by apply/ihu.
  by apply/InP.
- move=> h; inversion h as [ |y w niyu uu hh].
  move/InP: niyu->. exact/ihu.
Qed.

Lemma inclP  {X : eqType} (u v : seq X) : (List.incl u v) <-> {subset u <= v}.
Proof.
by split=> h x /InP /h /InP.
Qed.

Lemma Notallin (l : seq nat) :
  {n : nat & prod (0 != n) (n \in l = false)}.
Proof.
  have {} aux : forall (l : seq nat) (n : nat),
    (\max_(i <- l) i) < n -> n \in l = false.
  { clear l ; induction l as [ | x l IHl] ; [reflexivity | intros n Hinfn].
    rewrite in_cons ; rewrite big_cons in Hinfn.
    rewrite gtn_max in Hinfn.
    apply andb_prop in Hinfn as [H1 H2].
    apply Bool.orb_false_intro.
    + now apply gtn_eqF.
    + now apply IHl.
  }
  exists (\max_(i <- l) i).+1.
  split ; [ | now apply aux, ltnSn].
  easy.
Qed.
