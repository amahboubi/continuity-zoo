From mathcomp Require Import all_ssreflect.
From mathcomp Require Import zify.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

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

Variables A O : Type.
Variable a : A.
Notation Q := nat.

Implicit Type Y : (Q -> A) -> O.
Implicit Types α β : Q -> A.
Implicit Types n : nat.
Implicit Types γ : list A -> bool.
Implicit Types s : list A.

(* n first values of α *)
Definition pref α n :=
  map α (iota 0 n).

Lemma pref_le_eq n m α β :
  n <= m ->
  pref α m = pref β m ->
  pref α n = pref β n.

Proof.
  rewrite /pref => lenm.
  have -> : m = n + (m - n) by lia.
  rewrite iotaD !map_cat.
  apply: eq_catl.
  by rewrite !size_map size_iota.
Qed.

Definition padded_seq (s : seq A) :=
  nth a s.

(* n first values of α, then deflt value a. Importantly defined in terms of
   pref, so as to avoid extensionality issues later on under a modulus *)
Definition padded_prefix α n :=
  padded_seq (pref α n).

(* pref and the prefix of a padded prefix coincide*)
Lemma pref_padded_prefix α n k :
  k <= n -> pref (padded_prefix α n) k = pref α k.
Proof.
  move=> lekn.
  apply: (@eq_from_nth _ a); rewrite /pref !size_map !size_iota // /padded_prefix.
  move=> i ltin.
  congr (nth a _ i).
  apply/eq_in_map=> j; rewrite mem_iota add0n /padded_seq => /andP[_ hj].
  rewrite (nth_map 0) ?nth_iota ?add0n ?size_iota //; lia.
Qed.

(* Y is continuous *)
Definition Cont {O} (Y : (Q -> A) -> O) :=
  forall α, exists n, forall β, pref α n = pref β n -> Y α = Y β.

(* N is a modulus for Y *)
Definition Mod {O} (Y : (nat -> A) -> O) N :=
  forall α β, pref α (N α) = pref β (N α) -> Y α = Y β. 

(* Y has a continuous modulus *)
Definition has_continuous_modulus Y :=
  exists N, Cont N /\ Mod Y N.

(* Name from Yannick + Fujiwara - Kawai *)
Lemma T14 Y :
  has_continuous_modulus Y -> exists N, Mod Y N /\ Mod N N.
Proof.
(* In a classical setting we would take 
M α := min {k | forall β, pref α k = pref β k -> Y α = Y β}
The following constructive proof replaces this minimum by an
observable variant:
M α := min {N (padded_prefix α n) | N (padded_prefix α n) < n}
or, rather the simpler
M α := min {n | N (padded_prefix α n) < n}

(to be confirmed)
 *)
case=> N [ContN ModYN].
pose good_pref α n :=  N (padded_prefix α n) <= n.
(* This is the crux of the proof *)
have ex_good_pref α : exists n, good_pref α n.
  case: (ContN α) => [n Hn].
  exists (N α + n.+1). 
  rewrite /good_pref -Hn; first by lia. 
  rewrite pref_padded_prefix //; lia.
have Ygood_pref α n : good_pref α n -> Y (padded_prefix α n) = Y α.
  move=> gpn.
  apply: ModYN.
  exact: pref_padded_prefix.
have good_prefP α n : good_pref α n -> forall β, pref α n = pref β n -> Y α = Y β.
  move=> gpn β eqpref.
  rewrite -(Ygood_pref _ _ gpn).
  apply: ModYN.
  rewrite pref_padded_prefix //. 
  exact: (pref_le_eq _ eqpref).
(* The definition of M uses the constructive epsilon *)
pose M α : nat := ex_minn (ex_good_pref α).
have good_prefM α : good_pref α (M α) by rewrite /M; case: ex_minnP=> *.
have minM α n : good_pref α n -> (M α) <= n.
  rewrite /M; case: ex_minnP=> m _ h; exact: h.
have ModYM : Mod Y M.
  by move=> α β; apply: good_prefP. 
suff ModMM : Mod M M by exists M; split.
move=> α β eq_pref.
(* Here is where extensionnality matters *)                               
have eq_padded k : k <= M α -> padded_prefix α k =  padded_prefix β k.
  move=> lekMα.
  suff e : pref α k = pref β k by rewrite /padded_prefix e.
  exact: (pref_le_eq lekMα).
have leMβα : M β <= M α.
  apply: minM.
  rewrite /good_pref -eq_padded //; exact: good_prefM.
suff leMαβ : M α <= M β by apply/eqP; rewrite eqn_leq leMαβ.
apply: minM.
rewrite /good_pref eq_padded //. 
exact: good_prefM.
Qed.

Lemma T41 Y :
  (exists N, Mod Y N /\ Mod N N) -> has_continuous_modulus Y.
Proof.
  case=> N [HN HNY]; exists N; split=> // α.
  exists (N α) => *; exact: HNY.
Qed.

End sec.





