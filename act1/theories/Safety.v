From mathcomp Require Import all_ssreflect seq.
Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.


Require Import FinMap.finmap.
Require Import FinMap.ordtype.

Require Import MiniEMTST.AtomScopes.

Require Import MiniEMTST.Env.
Require Import MiniEMTST.Syntax.
Require Import MiniEMTST.Types.

Definition comm (t : tp) : tp :=
  match t with
  | input _ T => T
  | output _ T => T
  | ended => t
  | bottom => t
  end.

Lemma dual_comm T : dual (comm T) = comm (dual T).
Proof. by case: T. Qed.

Reserved Notation "D ~~> E" (at level 60).
Inductive typ_red : tp_env -> tp_env -> Prop :=
| tred_none D : D ~~> D
| tred_head D k T :
    add k T D ~~>
        add k (comm T) D
| tred_next D D' k T :
    D ~~> D' ->
    add k T D ~~>
        add k T D'
where "D ~~> E" := (typ_red D E).


(* Derive Inversion typred_inv with (forall D E, D ~~> E) Sort Prop. *)

Lemma typred_def D D' :
  D ~~> D' -> def D = def D' /\ forall k, (k \in dom D) = (k \in dom D').
Proof.
  elim=>{D}{D'}//.
  + move=>D k0 T ; split ; first by rewrite !def_addb.
    move=> k.
    by do ! rewrite !in_addb.
  + intros D D' k T.
    intros Hred.
    intros HD.
    destruct HD.
    split.
    - unfold def.
      unfold add.
      rewrite <- H0.
      destruct (k \in dom D); auto.
      destruct D; simpl.
      + assert (D' = Undef _ _). {
          destruct D'.
          - auto.
          - inversion H.
        }
        rewrite H1. auto.
      + destruct D'; simpl; auto.
    - intro.
      repeat rewrite in_dom_add.
      destruct (D) eqn:H1;
      destruct (D') eqn:H2; auto;
      inversion H.

      destruct (k0 \in dom (Def f)) eqn: H3;
      rewrite H0 in H3; rewrite H3;
      destruct (k \in dom (Def f)) eqn:H4;
      unfold add; rewrite H4; rewrite H0 in H4; rewrite H4; auto.
  Qed.


(* Lemma typred_undef D : undef_env ~~> D -> D = undef_env. *)
(* Proof. by move=>/typred_def-/=[]; case: D. Qed. *)


(* Lemma typred_dom D D' : D ~~> D' -> dom D' =i dom D. *)
(* Proof. *)
(*   elim=>//{D}{D'}. *)
(*   + by move=> l D k p T x; rewrite !in_addb !def_addb. *)
(*   + move=> D D' k p T DD' IH x. *)
(*     by rewrite !in_addb !def_addb !IH !(proj1 (typred_def DD')). *)
(* Qed. *)

Theorem CongruencePreservesOft G P Q D :
  P === Q -> oft G P D -> oft G Q D.
Proof.
  elim=>{P}{Q}//.
  { (* c_inact *)
    move=> P /oft_par_inv []D1 []D2 []Hdef []<- []Oinact Oq.
    elim/oft_inv: Oinact =>// Oinact G0 D0 cD1 dG _{G0} _ _{D0}.
    by apply: Weakening.
  }
  { (* c_comm *)
    intros.
    inversion H.
    rewrite composeC.
    apply t_par; auto.
    apply compatibleC; auto.
  }
  { (* c_asoc *)
    admit.
  }
  { (* c_nu *)
    admit.
  }
  {
    (* c_nu_inact *)
    intro.
    inversion H; auto.
    apply t_inact;
    move: (CH.fresh _) (CH.fresh_not_in L) => ki ki_L;
    assert (oft G (open_k0 inact ki) (add ki T (add ki (dual T) D))); try
    exact (H2 _ ki_L);
    unfold open_k0 in H4; unfold open_k in H4;
    inversion H4; auto.
    inversion H5.
    repeat apply weaken_completed in H5; auto.
  }
  { (* c_bang *)
    intros.
    inversion H.
    rewrite <- compose0.
    rewrite composeC.
    apply t_par; auto.
    inversion H1.
    inversion H5.
    destruct D.
    inversion H8.
    apply compatible_nil_def.
  }
(* Qed. *)
Admitted.

Theorem SubjectReductionStep G P Q D:
  oft G P D -> P --> Q -> exists D', D ~~> D' /\ oft G Q D'.
Proof.
  move=> Op PQ.
  elim: PQ G D Op => {P} {Q}.
  { (* r_com *)
    admit.
  }

  { (* r_cong *)
    (* will make use of CongruencePreservesOft *)
    intros.
    assert (exists D' : tp_env, D ~~> D' /\ oft G Q' D').
    {
      apply H3.
      apply CongruencePreservesOft with (P := P); auto.
    }
    destruct H5 as [D'].
    exists D'.
    destruct H5.
    split; auto.
    apply CongruencePreservesOft with (P := Q'); auto.
  }
  { (* r_scop *)
    admit.
  }

  { (* r_par *)
    admit.
  }

  { (* r_if_tt *)
    move=> P Q G D Ho.
    by exists D; split; first (by apply: tred_none); move: Ho=>/oft_ife_inv-[].
  }

  { (* r_if_ff *)
    move=> P Q G D Ho.
    exists D.
    split ; [by apply: tred_none| ].
    by move: Ho=>/oft_ife_inv-[].
  }
(* Qed. *)
Admitted.

Theorem SubjectReduction G P Q D:
  oft G P D -> P -->* Q -> exists D', oft G Q D'.
Proof.
  move => Hoft PQ; elim: PQ D Hoft => {P} {Q} P.
  + by move=> D Hoft; exists D.
  + move=> Q R Step QR IH D Hoft.
    move: (SubjectReductionStep Hoft Step) => []D' []bD' Hoft'.
    by move: (IH D' Hoft').
Qed.

(* Print Assumptions SubjectReduction. *)
