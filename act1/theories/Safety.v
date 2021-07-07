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

(* Lemma tred_step_add k p T D D' : *)
(*   balanced D -> *)
(*   add (ke (k, p)) T (add (ke (k, dual_pol p)) (dual T) D) ~~> D' -> *)
(*   exists T' D'', *)
(*     D' = add (ke (k, p)) T' (add (ke (k, dual_pol p)) (dual T') D''). *)
(* Proof. *)
(*   move => Bal; case: (boolP (def D')); *)
(*             last by case: D'=>// _ _; exists T, undef_env. *)
(*   move => defD' Hstep; move: (typred_def Hstep). *)
(*   rewrite defD' -/(is_true _)=>[][Def1 Hdom]. *)
(*   move: Bal => /(add_dual_bal Def1)/(typred_bal Hstep)=>{Hstep}[][DefD' BD']. *)
(*   move: BD'; rewrite /binds=> BD'. *)
(*   move: (def_nested Def1) => Def2; move: (def_nested Def2) => Def3. *)
(*   have : (ke (k, p)) \in dom D' *)
(*     by move: (Hdom (ke (k, p))); rewrite in_add // eq_refl. *)
(*   have : (ke (k, dual_pol p)) \in dom D' *)
(*     by move: (Hdom (ke (k, dual_pol p))); *)
(*     rewrite in_add// ke_eqE eq_refl (negPf (dualpol_neql _))/= in_add// eq_refl. *)
(*   move=>/in_domP-[T2 /eqP-H1] /in_domP-[T1 /eqP-H2]. *)
(*   move: (BD' k T1 T2 p (dual_pol p)) =>{BD'}. *)
(*   rewrite dual_polK eq_refl =>/(_ is_true_true H2 H1) => /eqP-T21. *)
(*   have {T21}T21: T2 = dual T1 by rewrite T21 dualK. *)
(*   move: T21 H1 H2 =>-> H1 H2{T2}{DefD'}{Def1}{Def2}{Def3}{D}{T}{Hdom}. *)
(*   exists T1, (rem (ke (k, p)) (rem (ke (k, dual_pol p)) D')). *)
(*   by rewrite -rem_add ?add_rem_id // ke_eqE eq_refl negb_and dualpol_neql. *)
(* Qed. *)

(* Lemma typred_dom D D' : D ~~> D' -> dom D' =i dom D. *)
(* Proof. *)
(*   elim=>//{D}{D'}. *)
(*   + by move=> l D k p T x; rewrite !in_addb !def_addb. *)
(*   + move=> D D' k p T DD' IH x. *)
(*     by rewrite !in_addb !def_addb !IH !(proj1 (typred_def DD')). *)
(* Qed. *)

(* (* *)
(* Ltac rw_impl := *)
(*   match goal with *)
(*   | [ |- (is_true (?L || ?R)) -> _] => move=>/orP-[|]; rw_impl *)
(*   | [ |- (is_true (?L && ?R)) -> _] => move=>/andP-[]; rw_impl *)
(*   | [ |- is_true (?k == ?k) -> _ ] => move=> _; rw_impl *)
(*   | [ |- is_true (?k != ?k) -> _ ] => rewrite eq_refl *)
(*   | [ |- is_true (?k == dual_pol ?k) -> _ ] => rewrite (negPf (dualpol_neqr k)); rw_impl *)
(*   | [ |- is_true (dual_pol ?k == ?k) -> _ ] => rewrite (negPf (dualpol_neql k)); rw_impl *)
(*   | [ |- is_true (_ \notin _) -> _ ] => first [move=>->; rw_impl | move=>/negPf->; rw_impl | move=>_; rw_impl] *)
(*   | [ |- (is_true (~~ ?L)) -> _ ] => first[move=>->; rw_impl | move=>/negPf->; rw_impl|move=>_; rw_impl] *)
(*   | [ |- (?L = false) -> _ ] => first [move=>->|move=> _; rw_impl] *)
(*   | [ |- is_true (_ \in _) -> _ ] => first [move=>-> | move=>_]; rw_impl *)
(*   | [ |- _ ] => idtac *)
(*   end. *)
(* *) *)


(* Lemma tred_step_rem k p D D' : *)
(*   D ~~> D' -> *)
(*   rem (ke (k, p)) (rem (ke (k, dual_pol p)) D) *)
(*       ~~> (rem (ke (k, p)) (rem (ke (k, dual_pol p)) D')). *)
(* Proof. *)
(*   case: (boolP (def D)); *)
(*     last by case: D=>/=// _ /typred_undef->/=; apply: tred_none. *)
(*   move=> Def Hstep; move: (proj1 (typred_def Hstep)); rewrite Def. *)
(*   move=>/eqP; rewrite eq_sym => /eqP; rewrite -/(is_true _) => Def'. *)
(*   elim: Hstep Def Def'. *)
(*   + by move=> D0 _ _; apply: tred_none. *)
(*   + move=> l D0 k0 p0 T Def1 Def2. *)
(*     have Def_p0: forall T, def (add (ke (k0, p0)) T D0) by *)
(*         move=> T0; move: Def1; rewrite add_swap=>/def_nested/def_diff_value. *)
(*     have Def_dp0: forall T, def (add (ke (k0, dual_pol p0)) T D0) by *)
(*         move=>T0; move: Def1=>/def_nested/def_diff_value. *)
(*     move: (def_nested (Def_p0 T)) Def2 => Def0 _. *)
(*     have {Def1}Def1: forall T T', *)
(*         def (add (ke (k0, p0)) T (add (ke (k0, dual_pol p0)) T' D0)). *)
(*       move=> T0 T'; rewrite def_addb Def_dp0 in_addb Def0 negb_and !negbK *)
(*                             ke_eqE eq_refl negb_or /= dualpol_neqr. *)
(*       by move: (Def_p0 T); rewrite def_addb orbC=>/andP-[_->]. *)
(*     case: (boolP (k == k0)) => kk0. *)
(*     - move: kk0 Def1 Def_p0 Def_dp0; move=>/eqP<-{k0}; case: (boolP (p == p0)). *)
(*       * move=> /eqP<-{p0} Def1 Def2 Def3; rewrite rem_add; last by *)
(*             rewrite ke_eqE negb_and eq_refl dualpol_neqr. *)
(*         rewrite -!rem_add_id //. *)
(*         rewrite rem_add; last by *)
(*             rewrite ke_eqE negb_and eq_refl dualpol_neqr. *)
(*         by rewrite -!rem_add_id //; apply: tred_none. *)
(*       * move=> /pol_noteq_dual->; rewrite dual_polK => Def1 Def2 Def3. *)
(*         by rewrite -!rem_add_id //; apply: tred_none. *)
(*     - have neq : forall p1 p2, ke (k0, p1) != ke (k, p2) by *)
(*           move=>p1 p2; rewrite ke_eqE eq_sym negb_and kk0. *)
(*       rewrite !rem_add //. *)
(*       by apply: tred_head. *)
(*   + move=> {D}{D'} D D' k0 p0 T Hstep IH Def1 Def2. *)
(*     have: forall T, def (add (ke (k0, p0)) T D) by *)
(*         move=> T0; move: Def1; rewrite add_swap=>/def_nested/def_diff_value. *)
(*     have: forall T, def (add (ke (k0, dual_pol p0)) T D) by *)
(*         move=>T0; move: Def1=>/def_nested/def_diff_value. *)
(*     have: forall T, def (add (ke (k0, p0)) T D') by *)
(*         move=> T0; move: Def2; rewrite add_swap=>/def_nested/def_diff_value. *)
(*     have: forall T, def (add (ke (k0, dual_pol p0)) T D') by *)
(*         move=>T0; move: Def2=>/def_nested/def_diff_value. *)
(*     case: (boolP (k == k0)) => kk0. *)
(*     - move: kk0 Def1 Def2; move=>/eqP<-{k0}; case: (boolP (p == p0)). *)
(*       * move=> /eqP<-{p0} Def1 Def2; rewrite rem_add; last by *)
(*             rewrite ke_eqE negb_and eq_refl dualpol_neqr. *)
(*         move=> Def3 Def4 Def5 Def6; rewrite -!rem_add_id //. *)
(*         rewrite rem_add; last by *)
(*             rewrite ke_eqE negb_and eq_refl dualpol_neqr. *)
(*         by rewrite -!rem_add_id. *)
(*       * move=> /pol_noteq_dual->; rewrite dual_polK => Def1 Def2 Df3 Df4 Df5 Df6. *)
(*         by rewrite -!rem_add_id //. *)
(*     - have neq : forall p1 p2, ke (k0, p1) != ke (k, p2) by *)
(*           move=>p1 p2; rewrite ke_eqE eq_sym negb_and kk0. *)
(*       move=> Df1 Df2 Df3 Df4. *)
(*       rewrite !rem_add //; apply: tred_next; apply: IH. *)
(*       by apply: (def_nested (def_nested Def1)). *)
(*       by apply: (def_nested (def_nested Def2)). *)
(* Qed. *)


(* Lemma step_union_l D1 D1' D2 : *)
(*   D1 ~~> D1' -> (D1 \:/ D2) ~~> (D1' \:/ D2). *)
(* Proof. *)
(*   elim=>{D1} {D1'}. *)
(*   + by move=> D; apply: tred_none. *)
(*   + by move=> l D k p T; rewrite !add_union; apply: tred_head. *)
(*   + by move=> D D' k p T DD' IH; rewrite !add_union; apply: tred_next. *)
(* Qed. *)

(* Lemma tred_step_tail k p T T' D D' : *)
(*   def (add (ke (k, p)) T (add (ke (k, dual_pol p)) (dual T) D)) -> *)
(*   add (ke (k, p)) T (add (ke (k, dual_pol p)) (dual T) D) *)
(*       ~~> (add (ke (k, p)) T' (add (ke (k, dual_pol p)) (dual T') D')) -> *)
(*   D ~~> D'. *)
(* Proof. *)
(*   move=> Hdef Hstep. *)
(*   move: (typred_def Hstep) =>[]; rewrite Hdef =>/eqP; rewrite eq_sym=>/eqP. *)
(*   rewrite -/(is_true _) => Hdef' _ ; move: Hstep. *)
(*   move=>/(tred_step_rem k p). *)
(*   rewrite rem_add; last by *)
(*       rewrite ke_eqE negb_and eq_refl dualpol_neqr. *)
(*   have Df1: forall T, def (add (ke (k, p)) T D) by *)
(*         move=> T0; move: Hdef; rewrite add_swap=>/def_nested/def_diff_value. *)
(*   have Df2: forall T, def (add (ke (k, dual_pol p)) T D) by *)
(*         move=>T0; move: Hdef =>/def_nested/def_diff_value. *)
(*   have Df1': forall T, def (add (ke (k, p)) T D') by *)
(*         move=> T0; move: Hdef'; rewrite add_swap=>/def_nested/def_diff_value. *)
(*   have Df2': forall T, def (add (ke (k, dual_pol p)) T D') by *)
(*         move=>T0; move: Hdef' =>/def_nested/def_diff_value. *)
(*   rewrite -!rem_add_id //. *)
(*   rewrite rem_add; last by *)
(*       rewrite ke_eqE negb_and eq_refl dualpol_neqr. *)
(*   by rewrite -!rem_add_id. *)
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
  oft G P D -> (* balanced D -> *) P -->* Q -> exists D', (* balanced D' /\ *) oft G Q D'.
Proof.
  move => Hoft (* bD *) PQ; elim: PQ D (* bD *) Hoft => {P} {Q} P.
  + by move=> D (* bD *) Hoft; exists D.
  + move=> Q R Step QR IH D (* bD *) Hoft.
    move: (SubjectReductionStep Hoft Step) => []D' []bD' Hoft'.
    by move: (IH D' (* (typred_bal bD' bD) *) Hoft').
Qed.

(* Print Assumptions SubjectReduction. *)
