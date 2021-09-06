(* General lemmas and definitions that don't belong anywhere *)

From mathcomp Require Import all_ssreflect.

Require Import FinMap.ordtype.
Require Import FinMap.finmap.

Set Implicit Arguments.
Unset Strict Implicit.
(* Import Prenex Implicits. *)
(* Unset Printing Implicit Defensive. *)

Lemma neqC {A : eqType} (x y : A) : x != y -> y != x.
Proof.
    by rewrite eq_sym.
Qed.

Lemma notin_cons {A : eqType} x y (L : seq A) : x \notin y :: L -> x != y /\ x \notin L.
Proof. by rewrite in_cons negb_or =>/andP. Qed.

(* TODO rename to notin_app or at least similarly to notin_cons (previous lemma) *)
Lemma not_in_app {A : eqType} (x : A) L L':
  x \notin L ++ L' -> x \notin L /\ x \notin L'.
Proof. by rewrite mem_cat negb_or => /andP. Qed.

(* Some lemmas about predicates (quite simple ones) *)

Lemma in_predU_l {T : eqType} (k : T) P Q : k \in P -> k \in predU P Q.
  do 2! rewrite/(_\in_).
  rewrite/predU.
  simpl=>->.
  by rewrite Bool.orb_true_l.
Qed.

Lemma in_predU_r {T : eqType}(k : T) P Q : k \in Q -> k \in predU P Q.
  do 2! rewrite/(_\in_).
  rewrite/predU.
  simpl=>->.
  by rewrite Bool.orb_true_r.
Qed.

Lemma notin_predU {T : eqType}(k : T) P Q : k \notin P -> k \notin Q -> k \notin predU P Q.
Proof.
  do !rewrite/(_\notin_)/predU/(_\in_) ; simpl.
  elim (P k)=>//.
Qed.

Lemma intersect_nil {K: ordType} {V: eqType}:
  forall D, intersect (K := K) (V := V) D (nil _ _) = (nil _ _).
Proof.
  intros.

  assert (supp (intersect (V:=V) D (nil K V)) = [::]).
  {
    rewrite supp_intersect.
    rewrite/intersect.
    rewrite fbk_nil.
    auto.
  }

  apply supp_nilE in H.
  auto.
Qed.

Lemma diff_nil_d {K: ordType} {V: eqType}:
  forall D, diff (K := K) (V := V) (nil _ _) D = (nil _ _).
Proof.
  intros.
  unfold diff.
  rewrite fbk_nil.
  reflexivity.
Qed.

Lemma diff_d_nil {K: ordType} {V: eqType}:
  forall D, diff (K := K) (V := V) D (nil _ _) = D.
Proof.
  intros.
  unfold diff.
  rewrite supp_nil.
  simpl.
  rewrite fmapE.
  rewrite seqof_fbk.
  simpl.
  rewrite filter_predT.
  reflexivity.
Qed.