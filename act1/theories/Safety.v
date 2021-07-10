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
  + move=> D D' k0 T DD' []-IhD Ih_k.
    do ! rewrite ?def_addb ?in_addb ?negb_and ?negb_or.
    do ! rewrite  !IhD !Ih_k; split=>//.
    move=> k; move: IhD; case: D DD' Ih_k; case: D' =>// f f' _.
    rewrite /dom => Ih _; rewrite /add/look/dom/upd.
    case: suppP=>[v /eqP/in_supp_fnd|/eqP/notin_supp_fnd];
                   first by rewrite Ih =>->/=.
    rewrite Ih => /negPf->.
    (* rewrite !supp_ins !inE (* ke_eqE *) eq_refl /=. *)
    (* rewrite (negPf (pol_dual_noteq _))/=; last by rewrite dual_polK. *)
    (* case: suppP=>[v /eqP/in_supp_fnd|/eqP/notin_supp_fnd]; *)
    (*                first by rewrite Ih=>->. *)
    (* rewrite Ih => /negPf->. *)
    (* by do ! rewrite !supp_ins !inE; rewrite Ih. *)
(* Qed. *)
Admitted.


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
    admit.
  }
  { (* c_asoc *)
    admit.
  }
  { (* c_nu *)
    admit.
  }
  { (* c_nu_inact *)
    admit.
  }
  { (* c_bang *)
    admit.
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
    admit.
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
