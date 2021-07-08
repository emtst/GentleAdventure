From mathcomp Require Import all_ssreflect seq.
Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Require Import FinMap.finmap.
Require Import FinMap.ordtype.

Require Import MiniEMTST.OddsAndEnds.
Require Import MiniEMTST.AtomScopes.
Require Import MiniEMTST.Syntax.
Require Import MiniEMTST.Env.

(* syntax of types *)

(** expression sorts **)

Inductive sort : Set :=
  | boole (* boolean expression *)
  | unite (* unit types *)
.

Fixpoint eq_sort (s s' : sort) : bool :=
  match s, s' with
  | boole, boole => true
  | unite, unite => true
  | _, _ => false
  end.

Lemma eq_sortP : Equality.axiom eq_sort.
Proof.
  move=> x y.
  apply: (iffP idP)=>[|<-].
  by elim x ; elim y.
  by elim x.
Qed.

Canonical sort_eqMixin := EqMixin eq_sortP.
Canonical sort_eqType := Eval hnf in EqType sort sort_eqMixin.

(* process types *)

Inductive tp : Set :=
  | input : sort -> tp -> tp
  | output : sort -> tp -> tp
  | ended : tp
  | bottom : tp
.

Fixpoint dual (T : tp) : tp :=
  match T with
  | input s T => output s (dual T)
  | output s T => input s (dual T)
  | ended => ended
  | bottom => bottom
  end
.

Lemma dual_is_dual t : dual (dual t) = t.
  elim t=>// ; rewrite/dual ; move=>//; rewrite-/dual ;
    do ? (move=> s t0 =>->) ;
    do ? (move=> t0 R' t1 =>->) ;
    rewrite ?R' ;
   easy.
Qed.

Fixpoint eq_tp (T T': tp) : bool :=
  match T, T' with
  | input s T, input s' T' => eq_sort s s' && eq_tp T T'
  | output s T, output s' T' => eq_sort s s' && eq_tp T T'
  | ended, ended => true
  | bottom, bottom => true
  | _, _ => false
  end.

Lemma eq_imp_eq : forall x y, eq_tp x y -> x = y.
Proof. Admitted.
(*   apply tp_sort_mutind ; intros; try destruct y  ; try destruct s'; try easy ; *)
(*   inversion H1 ; apply Bool.andb_true_iff in H3 ; destruct H3 ; *)
(*   try(move:H3 ; move/H0=>H3 ; move:H2 ; move/H=>H4 ; by rewrite H3 H4). *)
(* Qed. (* more ssreflect can make this better *) *)

Lemma eq_tp_refl x : eq_tp x x.
Proof.
  elim x ;
    try
      move=>s t H ;
      rewrite/eq_tp=>// ;
      fold eq_tp ;
      rewrite H=>//= ;
      elim s=>//.
Qed.


Lemma eq_tpP : Equality.axiom eq_tp.
Proof.
  move=>x y.
  apply: (iffP idP)=>[|<-].
  apply eq_imp_eq.
  apply eq_tp_refl.
Qed.


Canonical tp_eqMixin := EqMixin eq_tpP.
Canonical tp_eqType := Eval hnf in EqType tp tp_eqMixin.

(* judgements *)

(* environments *)
Definition sort_env_entry := EV_atom_ordType.
Definition sort_env := @env sort_env_entry sort_eqType.

Inductive oft_exp (G : sort_env) : exp -> sort -> Prop :=
| t_tt : def G -> oft_exp G tt boole
| t_ff : def G -> oft_exp G ff boole
| t_unit : def G -> oft_exp G one unite
| t_var : forall x (S : sort),
    binds x S G ->
    oft_exp G (V (EV.Free x)) S
.

Definition tp_env_entry := CH_atom_ordType. (* TODO CLEANUP *)
Definition tp_env := @env tp_env_entry tp_eqType.

Definition completed (D : tp_env) : Prop :=
  def D /\ forall a, a \in dom D -> binds a ended D.

Definition chan_of_entry (c : tp_env_entry) : CH.var := c. (* TODO REMOVE *)

(* compatible environments *)

(* lift dual to option *)
Definition option_dual (d : option tp) : option tp :=
  match d with
  | None => None
  | Some T => Some (dual T)
  end.

Inductive compatible : forall (E1 E2 : tp_env), Prop :=
| compatible_disj E1 E2: disjoint E1 E2 -> compatible E1 E2
| compatible_add E1 E2 k t:
    compatible E1 E2 ->
    compatible (add k t E1) (add k (dual t) E2)
.
Hint Constructors compatible.

Definition compatible_nil : compatible nil nil.
  apply compatible_disj.
  apply disjoint_nil.
Defined.

Lemma compatibleC E1 E2 : compatible E1 E2 -> compatible E2 E1.
  elim=>//.
  move=> E0 E3.
  rewrite disjointC.
  apply compatible_disj.
  move=> E0 E3 k t D. (* D1 D2. *)
  move/compatible_add.
  move=>H.
  have H':= H k (dual t).
  move:H'.
  by rewrite dual_is_dual.
Qed.

Definition compose (E1 E2 : tp_env) : tp_env :=
  if (E1, E2) is (Def f1, Def f2) then
    let: (f1, f12, f2) := spl f1 f2 in
    Def (fcat f1 (fcat (fmap_map (fun _ => bottom) f12) f2))
  else
    undef_env.

Notation "A 'o' B" := (compose A B) (at level 60, right associativity).  (* : env_scope. *)

Lemma compose_undef D:
  D o undef_env = undef_env.
Proof.
  elim D=>//.
Qed.

Lemma composeC D D': D o D' = D' o D.
Proof.
  elim D=>// ; elim D'=>// f f'.
  (* Disjointness *)
  have: all_disj (spl f f') by apply: disj_spl.
  move=>/andP-[/andP-[di dd] id].
  have dmi :
    disj (diff f' f) (fmap_map (fun _ : tp_eqType => bottom) (intersect f f'))
    by rewrite /disj supp_map -/(disj _ _) disjC.
  have mid :
    disj (fmap_map (fun _ : tp_eqType => bottom) (intersect f f')) (diff f f')
    by rewrite /disj supp_map -/(disj _ _) disjC.
  have dmid :
    disj (fcat (diff f' f)
               (fmap_map (fun _ : tp_eqType => bottom) (intersect f f')))
         (diff f f')
    by rewrite disjC disj_fcat dd Bool.andb_true_l /disj supp_map.
  have eq_supp :
    supp (intersect f' f) == supp (intersect f f')
    by rewrite (supp_intersect f' f).
  (* End disjointness *)
  rewrite /compose/spl.
  rewrite (fmap_const_eq bottom eq_supp).
    by rewrite -fcatA // fcatC // [fcat (diff f' f) _]fcatC.
Qed.

(* some properties of compatible environments and of defined envirnments *)
Lemma compatible_hd k t t' E1 E2:
  def (add k t E1) -> def (add k t' E2) -> t == dual t'
  -> compatible E1 E2 -> compatible (add k t E1) (add k t' E2).
Proof.
  elim: E1; elim: E2 => // => f f0.
  move=>D1 D2.
  move/eqP=>R. rewrite R.
  move/compatible_add.
  move=>H.
  have H':= H k (dual t'). move:H'.
  by rewrite dual_is_dual.
Qed.

Lemma compatible_swap_left k k' s t E1 E2:
  def (add k t (add k' s E1)) -> def E2 -> (* we may not need/want these*)
  compatible (add k t (add k' s E1)) E2 ->
  compatible (add k' s (add k t E1)) E2.
Proof. by rewrite add_swap. Qed.

(* typing judgment *)

Inductive oft : sort_env -> proc -> tp_env -> Prop :=
| t_send : forall G kt e P D S T,
    oft_exp G e S ->
    oft G P (add kt T D) ->
    oft G (send (chan_of_entry kt) e P) (add kt (output S T) D)

| t_receive : forall (L : seq EV.atom) G kt P D S T,
    (forall x, x \notin L ->
          oft (add x S G) (open_e0 P (V (EV.Free x))) (add kt T D)) -> (* the V should be a coercion *)
    oft G (receive (chan_of_entry kt) P) (add kt (input S T) D)

| t_ife : forall G e P Q D,
    oft_exp G e boole ->
    oft G P D ->
    oft G Q D ->
    oft G (ife e P Q) D

| t_par : forall G P Q D1 D2,
    oft G P D1 ->
    oft G Q D2 ->
    (* def (D1 \:/ D2) -> *)
    compatible D1 D2 ->
    oft G (par P Q) (D1 o D2)

| t_inact : forall G D,
    completed D ->
    def G -> (* we need this to be able to argue that well typed derivations have def G *)
    oft G inact D

| t_nu G P D T (L: seq CH.atom):
    (forall ki,
        ki \notin L ->
        oft G (open_k0 P ki) (add ki T (add ki (dual T)  D))) ->
        (* oft G (open_k0 P ki) (add (ke ki) T (add (ke ki) (dual T)  D))) -> *)
    oft G (nu P) D

(* this is the case when ki is not used, because we don't add it to
    the typing, however we still need to "open" the term,
    because morally it contains a binder. If one where to
    apply t_nu_ch when t_nu_ch' is needed the derivation would
    get stuck because ki is not on the typing.
*)
| t_nu' G P D :
    oft G P D ->
    oft G (nu P) D

| t_bang G P D:
    completed D -> oft G P nil -> oft G (bang P) D
.

(*****************************)

(* shorthand to have induction over oft with consistent naming *)
Ltac induction_oft :=
  let L := fresh "L" in
  let L' := fresh "L" in
  let a := fresh "a" in
  let D1 := fresh "D1" in
  let D2 := fresh "D2" in
  let s := fresh "s" in
  let t := fresh "t" in
  let T := fresh "T" in
  let T' := fresh "T'" in
  let k := fresh "k" in
  let kt := fresh "kt" in
  let k0 := fresh "k0" in
  let k1 := fresh "k1" in
  let Bnd := fresh "Bnd" in
  let Oft_e := fresh "Oft_e" in
  let OftP := fresh "OftP" in
  let CompD := fresh "CompD" in
  let OftQ := fresh "OftQ" in
  let Def_kk'D := fresh "Def_kk'D" in
  let Def_G := fresh "Def_G" in
  let Ih := fresh "Ih" in
  let IhP := fresh "IhP" in
  let IhQ := fresh "IhQ" in
  match goal with
  | [ |- oft ?G ?P ?D -> _ ] =>
    elim
    => {G}{P}{D}
          [ L L' G a P D t Bnd OftP Ih
          | L L' G a P D t Bnd OftP Ih
          | G kt e P D S T Oft_e OftP Ih
          | L G kt P D S T OftP Ih
          | G k0 P D T T' OftP Ih
          | G k0 P D T T' OftP Ih
          | G k0 P Q D T T' OftP IhP OftQ IhQ
          | G k0 k1 P D T T' OftP Ih Def_kk'D
          | L L' G k0 P D T T' OftP Ih
          | G e P Q D Oft_e OftP IhP OftQ IhQ
          | G P Q D1 D2 OftP IhP OftQ IhQ Def_D12
          | G D CompD DefG
          | L G s P D OftP Ih
          | G P D T L OftP Ih
          | G P D OftP Ih
          | G P D CompD OftP Ih
          ] /=
  end.

Derive Inversion oft_inv with (forall G P D, oft G P D) Sort Prop.
Derive Inversion oft_inv_par with (forall G P Q D, oft G (par P Q) D) Sort Prop.

Lemma oft_par_inv G P Q D :
  oft G (par P Q) D -> exists D1 D2,
    compatible D1 D2 /\ (* def (D1 o D2) /\ *) (D1 o D2 = D) /\ oft G P D1 /\ oft G Q D2.
Proof.
  elim/oft_inv_par => _ G0 P1 Q0 D1 D2 oftP oftQ Hdef _ _ _ _.
  by exists D1, D2.
Qed.

(* Lemma oft_par_inv G P Q D : *)
(*   oft G (par P Q) D -> exists D1 D2, *)
(*     def (union D1 D2) /\ (union D1 D2 = D) /\ oft G P D1 /\ oft G Q D2. *)
(* Proof. *)
(*   elim/oft_inv_par => _ G0 P1 Q0 D1 D2 oftP oftQ Hdef _ _ _ _. *)
(*   by exists D1, D2. *)
(* Qed. *)


Lemma oft_send_inv c e P D G :
  oft G (send c e P) D ->
  exists k S T D',
    chan_of_entry k = c /\
    D = add k (output S T) D' /\
    oft_exp G e S /\ oft G P (add k T D').
Proof.
  elim/oft_inv => // _ G0 k' e0 P1 D0 S0 T0 Oe O _ [] Eq<-<-_.
  by exists k', S0, T0, D0; split.
Qed.

(* Lemma oft_receive_inv c P D G : *)
(*   oft G (receive c P) D -> *)
(*   exists k S T D', *)
(*     chan_of_entry k = c /\ *)
(*     D = add k (input S T) D' *)
(*     /\ exists L : seq EV.atom, *)
(*       (forall (x : EV.atom), x \notin L -> *)
(*        oft (add (inr x) S G) (open_e0 P (EV.Free x)) (add k T D')). *)
(* Proof. *)
(*   elim /oft_inv => // _ L G0 k0 P1 D0 S0 T0 O _ [] Eq<-_. *)
(*   exists k0,S0,T0,D0;do ! split =>//. *)
(*   by exists L. *)
(* Qed. *)


Lemma oft_ife_inv G e P Q D :
  oft G (ife e P Q) D ->
  oft G P D /\ oft G Q D.
Proof.
  by elim/oft_inv => // _ G0 e' P1 Q0 D0 _ Hoft1 Hoft2 _ {G0} [] _ <- <-.
Qed.

Lemma oft_exp_lc G E S:
  oft_exp G E S -> lc_exp E.
Proof.
  elim ; try by [].
Qed.

Lemma oft_lc G P D:
  oft G P D -> lc P.
Proof.
(*   elim ; intros. *)
(*   by apply: lc_send ; [apply: lc_chanofentry | apply: oft_exp_lc ; apply H|]. *)
(*   by apply: lc_receive ; [ apply: lc_chanofentry | apply H0]. *)
(*   by apply: lc_ife ; first (apply: oft_exp_lc ; apply H) ; assumption. *)
(*   by apply: lc_par ; assumption. *)
(*   by apply: lc_inact ; assumption. *)
(*   by apply: lc_nu ; apply H0. *)
(*   (* by apply: lc_nu_ch ; apply H0. *) *)
(*   (* by apply: (lc_nu_ch (L:=[::]))=> k k_ninL; rewrite /open_k0 -opk_lc. *) *)
(*   by apply: lc_bang. *)
(* Qed. *)
Admitted.

Lemma oft_def G P D:
  oft G P D -> def D.
Proof.
(*   induction_oft; try (move: Ih); try (move: IhQ); *)
(*    try (move => /(_ (LC.fresh L) (LC.fresh_not_in L))); *)
(*    try (move => /(_ (inl (LC.fresh L)) (LC.fresh_not_in L))); *)
(*    try (move => /(_ (EV.fresh L) (EV.fresh_not_in L))); *)
(*    try (move => /(_ (SC.fresh L) (SC.fresh_not_in L))); *)
(*    try (move => /(_ (CN.fresh L) (CN.fresh_not_in L))); *)
(*    try easy; *)
(*    try (by move/def_diff_value); *)
(*    try (by move/def_nested); *)
(*    try (by move/def_nested/def_nested); *)
(*    try (by move/def_nested/def_diff_value); *)
(*    try (by move: CompD; rewrite /completed =>[][]). *)
(* Qed. *)
Admitted.


Lemma oft_def_ctx G P D:
  oft G P D -> def G.
Proof.
(*   induction_oft=>//; try (move: Ih); try (move: IhQ); *)
(*   try (move => /(_ (inl (LC.fresh L)) (LC.fresh_not_in L))); *)
(*   try (move => /(_ (LC.fresh L) (LC.fresh_not_in L))); *)
(*   try (move => /(_ (EV.fresh L) (EV.fresh_not_in L))); *)
(*   try (move => /(_ (SC.fresh L) (SC.fresh_not_in L))); *)
(*   try (move => /(_ (CN.fresh L) (CN.fresh_not_in L))); *)
(*   try (by move/def_nested); *)
(*   try easy. *)
(* Qed. *)
Admitted.

Lemma oft_exp_def_ctx G E S:
  oft_exp G E S -> def G.
Proof.
  elim ; try by [].
  move=> x S'.
  by apply: binds_def.
Qed.

(* Meta-theory *)

(* NEIN *)
(* Lemma subst_exp_proc_open_var x y e P: *)
(*   lc_exp e -> *)
(*   (s[ x ~> e ]pe open_c0 P y) = (open_c0 (s[ x ~> e ]pe P) y). *)
(* Proof. *)
(*   by move=> lc_e; rewrite /open_c0; move: 0 => n; by_proc_induction2 P n y. *)
(* Qed. *)

Lemma subst_ch_same c c' : s[ c ~> c ]c c' = c'.
Proof.
  by case: c'=>// ; rewrite /subst_ch=> a ; case: ifP =>// /eqP->.
Qed.

Lemma subst_chan_same c P : s[c ~> c]p P = P.
(* Proof. *)
(*   by_proc_induction0 P; rewrite !subst_ch_same=>//. *)
(* Qed. *)
Admitted.

Lemma subst_exp_proc_open_exp x y e P:
  x != y ->
  lc_exp e ->
  (s[ x ~> e ]pe open_e0 P y) = (open_e0 (s[ x ~> e ]pe P) y).
Proof.
(*   move=> xy lc_e; rewrite /open_e0; move: 0 => n; by_proc_induction P n =>//. *)
(*   + rewrite /ope; case: H4 =>//; *)
(*       rewrite /EV.open_var /subst_exp; case=>// an; case: ifP=>///eqP->. *)
(*     by case: lc_e=>//. *)
(*     by move: xy => /negPf->. *)
(*   + rewrite /ope; case: H4 =>//; *)
(*       rewrite /EV.open_var /subst_exp; case=>// an; case: ifP=>///eqP->. *)
(*     by case: lc_e=>//. *)
(*     by move: xy => /negPf->. *)
(* Qed. *)
Admitted.

Lemma subst_exp_ope x y n e :
  x \notin fv_exp e ->
  s[ x ~> y ]e open_exp n x e = open_exp n y e.
Proof.
  case: e =>// [][a|m _] /=//; last by case: ifP => ///=; rewrite eq_refl.
  by rewrite in_cons negb_or=>/andP-[/negPf->].
Qed.

Lemma subst_exp_open_e x y P :
  x \notin fev_proc P ->
  s[ x ~> y ]pe open_e0 P x = open_e0 P y.
(* Proof. *)
(*   rewrite /open_e0; move: 0. *)
(*   elim: P *)
(*   => [ c e p IH *)
(*      | c p IH *)
(*      | e p1 IH1 p2 IH2 *)
(*      | p1 IH1 p2 IH2 *)
(*      | *)
(*      | p IH *)
(*      | p IH] n /=. *)
(*   try (rewrite !mem_cat !negb_or); *)
(*   try (move => /andP-[nin1 /andP-[nin2 nin3]]); *)
(*   try (move => /andP-[nin1 nin2]); *)
(*   try (move=>x_notin); *)
(*   try (rewrite IH =>//); *)
(*   try (rewrite IH1 =>//); *)
(*   try (rewrite IH2 =>//); *)
(*   try (rewrite subst_exp_ope =>//); *)
(*   easy. *)
(* Qed. *)
Admitted.


Lemma subst_chan_openk_var x u n k ch :
  CH.lc u -> s[ x ~> u ]c opk n k ch = opk n k (s[ x ~> u ]c ch).
Proof.
(*   rewrite /opk/subst_ch; case: ch =>//[[]|]// []// a. *)
(*   case: ifP=>// _; elim=>//. *)
(* Qed. *)
Admitted.

Lemma subst_proc_openk_var x k u P:
  (* x != y -> *) CH.lc u ->
  (s[ x ~> u ]p open_k0 P k) = (open_k0 (s[ x ~> u ]p P) k).
(* Proof. *)
(*   move=> lc_ch; rewrite /open_k0; move: 0 => n; by_proc_induction P n =>//; *)
(*   rewrite !subst_chan_openk_var //. *)
(* Qed. *)
Admitted.

Lemma subst_exp_openk_var x k e P:
  (* x != y -> *) lc_exp e ->
  (s[ x ~> e ]pe open_k0 P k) = (open_k0 (s[ x ~> e ]pe P) k).
(* Proof. *)
(*   move=> lc_ch; rewrite /open_k0; move: 0 => n; by_proc_induction P n =>//. *)
(* Qed. *)
Admitted.

Lemma subst_proc_open_e x k u P:
  (s[ x ~> u ]p open_e0 P k) = (open_e0 (s[ x ~> u ]p P) k).
(* Proof. *)
(*   by rewrite /open_e0; move: 0 => n; by_proc_induction P n. *)
(* Qed. *)
Admitted.

(* Some weakening lemmas *)
Lemma wkn_ctx_oft_exp G E x S S':
  oft_exp G E S -> def (add x S' G) -> oft_exp (add x S' G) E S.
Proof.
  elim ; intros ; constructor ; try assumption.
  apply: binds_add.
  by apply: H.
  apply: def_diff_value.
  by apply H0.
Qed.

(* Lemma str_ctx_oft_exp G E x S S': *)
(*   x \notin fv_exp E -> *)
(*   oft_exp (add (inr x) S' G) E S -> oft_exp G E S. *)
(* Proof. *)
(*   move=>nin Hoft; move: Hoft nin. *)
(*   case=>[/def_nested/t_tt|/def_nested/t_ff|y S'' hBinds]/=//. *)
(*   rewrite in_cons negb_or=>/andP-[neq _]. *)
(*   by apply:t_var;apply:(binds_next _ hBinds);rewrite -[inr _==_]/(y==x) eq_sym. *)
(* Qed. *)

(* Lemma str_ctx_nm_oft_exp G E x S S': *)
(*   oft_exp (add (inl x) S' G) E S -> oft_exp G E S. *)
(* Proof. *)
(*   case=>[/def_nested/t_tt|/def_nested/t_ff|y S'' hBinds]/=//. *)
(*   by apply:t_var;apply:(binds_next _ hBinds). *)
(* Qed. *)

(* Lemma str_ctx_oft_proc x S S' P G : *)
(*   x \notin fv_e P -> *)
(*   oft (add (inr x) S' G) P S -> oft G P S. *)
(* Proof. *)
(*   move Eq: (add (inr x) S' G) => G' notin Hoft. *)
(*   elim: Hoft notin G Eq =>/=//; rewrite ?mem_cat ?negb_or. *)
(*   + move=> L L' {G'} G0 a {P} P D t Hbinds Hoft IH notin G Eq. *)
(*     have ax : inl a != inr x by []. *)
(*     move: Eq Hoft IH Hbinds =><- {G0} Hoft IH /(binds_next ax)-Hbnd. *)
(*     apply: (t_request Hbnd (L:=L) (L':=L')) => c fc; apply: (IH _ fc)=>//. *)
(*     by rewrite fve_openc. *)
(*   + move=> L L' {G'} G0 a {P} P D t Hbinds Hoft IH notin G Eq. *)
(*     have ax : inl a != inr x by []. *)
(*     move: Eq Hoft IH Hbinds =><- {G0} Hoft IH /(binds_next ax)-Hbnd. *)
(*     apply: (t_accept Hbnd (L:=L) (L':=L')) => c fc; apply: (IH _ fc)=>//. *)
(*     by rewrite fve_openc. *)
(*   + move=> G0 k e P0 D S0 T Oe Op IH nin G EqG. *)
(*     move: EqG Oe Op IH =><- Oe Op IH. *)
(*     move: nin; rewrite mem_cat negb_or=>/andP-[nin1 nin2]. *)
(*     apply: t_send; first by apply: (str_ctx_oft_exp nin1 Oe). *)
(*     by apply: IH. *)
(*   + move=> L G k P0 D S0 T Hoft IH nin G0 EqG; move: EqG Hoft IH =><- Hoft IH. *)
(*     apply: (t_receive (L:=fv_e P0 ++ L)) => x0. *)
(*     rewrite mem_cat negb_or=>/andP-[nin1 nin2]. *)
(*     move: (Hoft x0 nin2) => /oft_def_ctx; rewrite def_add =>[][neq Da]. *)
(*     move: neq; rewrite notin_add // -[inr _ == _]/(x0 == x) => /andP-[neq _]. *)
(*     move: neq; rewrite [in x0 != _](eq_sym)=>neq. *)
(*     have nix: x \notin fv_exp x0 by rewrite in_cons in_nil negb_or andbC /= neq. *)
(*     by move: (IH x0 nin2 (fve_opene nix nin)) => I; apply: I; apply/add_swap. *)
(*   + move=> G k P0 D T T' Hoft IH nin G0 EqG. *)
(*     move: EqG IH Hoft =><- /(_ nin G0 (eqP (eq_refl _)))-IH Hoft. *)
(*     by apply: t_select_l. *)
(*   + move=> G k P0 D T T' Hoft IH nin G0 EqG. *)
(*     move: EqG IH Hoft =><- /(_ nin G0 (eqP (eq_refl _)))-IH Hoft. *)
(*     by apply: t_select_r. *)
(*   + move=> G k P0 Q D T T' _ IH1 _ IH2. *)
(*     rewrite mem_cat negb_or=>/andP-[/IH1-{IH1}IH1 /IH2-{IH2}IH2] G0 Eq. *)
(*     move: Eq IH1 IH2=><-/(_ G0)-IH1 /(_ G0)-IH2. *)
(*     by apply: t_branch; [apply: IH1 | apply: IH2]. *)
(*   + move=> G k k' P0 D T T' Hoft1 IH1 Hdef /IH1-{IH1}IH1 G0 EqG. *)
(*     by move: EqG IH1=><- IH1; apply: t_throw =>//; apply: IH1. *)
(*   + move=> L L' G k P0 D T T' _ IH nin G0 Eq. *)
(*     move: Eq IH=><-IH; apply: (t_catch (L:=L) (L':=L')) => x0 nin0. *)
(*     by move: (IH x0 nin0); rewrite fve_openc => /(_ nin G0)-{IH}IH; apply:IH. *)
(*   + move=> G e P0 Q D Oe Op IH1 Oq IH2. *)
(*     rewrite !mem_cat !negb_or =>/andP-[nin1 /andP-[nin2 nin3]] G0 Eq. *)
(*     move: Eq Oe IH1 IH2=><- Oe IH1 IH2. *)
(*     by apply: t_ife; [apply: (str_ctx_oft_exp nin1 Oe)|apply: IH1|apply: IH2]. *)
(*   + move=> G P0 Q D1 D2 _ IH1 _ IH2 Hdef. *)
(*     rewrite mem_cat negb_or=>/andP-[/IH1-{IH1}IH1 /IH2-{IH2}IH2] => G0 Eq. *)
(*     by move: (IH1 G0 Eq) (IH2 G0 Eq) => {IH1}IH1 {IH2}IH2; apply: t_par. *)
(*   + move=> G D Hc Hdef _ G0 Eq0; apply: t_inact=>//. *)
(*     by move: Eq0 Hdef=><- /def_nested-Hdef. *)
(*   + move=>L G s P0 D _ IH xnotin G0 Eq; apply: (t_nu_nm (L:=L) (s:=s))=> x0 nin. *)
(*     move: IH => /(_ x0 nin); rewrite fve_openn => /(_ xnotin)-IH. *)
(*     by move: Eq IH=><-/(_ (add (ne x0) s G0))-IH; apply: IH; apply/add_swap. *)
(*   + move=> G P0 D T L _ IH nin G0 Eq; apply: (t_nu_ch (L:=L) (T:=T))=> ki ki_nin. *)
(*     by move: (IH ki ki_nin); rewrite fve_openk =>/(_ nin G0 Eq). *)
(*   + by move=> G P0 D _ IH nin G0 Eq; apply: t_nu_ch'; apply: IH. *)
(*   + by move=> G P0 D comp borr IH  nin G0 Eq'; apply: t_bang ; [easy| apply: IH]. *)
(* Qed. *)

Lemma wkn_ctx_oft G P D y S:
  oft G P D -> def (add y S G) -> oft (add y S G) P D.
(* Proof. *)
(*   move=> H. move: H S y. *)
(*   elim ; intros. *)
(*   { (* t_send *) *)
(*     apply t_send. *)
(*     apply: wkn_ctx_oft_exp. *)
(*     by apply: H. *)
(*     assumption. *)
(*     apply H1. *)
(*     assumption. *)
(*   } *)
(*   { (* t_receive *) *)
(*     apply: (t_receive (L:=ea_dom (add y S0 G0) ++ L))=>x /not_in_app-[xy xL]. *)
(*     move:(add_swap (ee x) y S S0 G0)=>->. *)
(*     apply H0=>//. *)
(*     move:(add_swap y (inr x) S0 S G0)=>->. *)
(*     apply def_add_assumption with (k:=inr x)(T:=S) in H1=>//. *)
(*     by apply: notin_eadom_dom. *)
(*   } *)
(*   { (* t_ife *) *)
(*     apply: t_ife. *)
(*     apply: wkn_ctx_oft_exp. *)
(*     assumption. *)
(*     assumption. *)
(*     apply: H1 ; assumption. *)
(*     apply: H3 ; assumption. *)
(*   } *)
(*   { (* t_par *) *)
(*     apply: t_par. *)
(*     apply: H0 ; assumption. *)
(*     apply: H2 ; assumption. *)
(*     assumption. *)
(*   } *)
(*   { (* inact *) *)
(*     apply:t_inact ; assumption. *)
(*   } *)
(*   (* { (* t_nu_nm *) *) *)
(*   (*   apply: t_nu_nm. *) *)
(*   (*   intros. *) *)
(*   (*   move:(add_swap (ne x) y s S G0)=>HH;erewrite HH. *) *)
(*   (*   apply H0. *) *)
(*   (*   have H2': x\notin (na_dom(add y S G0) ++ L) by apply: H2. *) *)
(*   (*   move:H2' ; move/not_in_app. *) *)
(*   (*   by intuition. *) *)
(*   (*   move:(add_swap y (ne x) S s G0)=>->. *) *)
(*   (*   apply: def_add_assumption =>//. *) *)
(*   (*   move:H2 ; move/not_in_app. *) *)
(*   (*   by move=>[[/notin_nadom_dom-dd _]]. *) *)
(*   (* } *) *)
(*   (* { (* t_nu_ch *) *) *)
(*   (*   apply: t_nu_ch. *) *)
(*   (*   intros. *) *)
(*   (*   apply: H0. *) *)
(*   (*   apply: H2. *) *)
(*   (*   assumption. *) *)
(*   (* } *) *)
(*   (* { (* t_nu_ch' *) *) *)
(*   (*   apply: t_nu_ch'. *) *)
(*   (*   by apply: H0. *) *)
(*   (* } *) *)
(*   { (* t_bang *) *)
(*     by constructor;[easy| apply: H1]. *)
(*   } *)
(* Qed. *)
Admitted.

Lemma TypeUniquenessExp G e S S':
  oft_exp G e S -> oft_exp G e S' -> S = S'.
Proof.
  elim=>Hdef H ;  try by inversion H.
  intros.
  inversion H1.
  apply: UniquenessBind ; [ apply: H0 | apply: H3].
Qed.

(* this is somewhat sloppy as in we weaken G to still have x after the
  elim Hp ; introssubstitution *)
Lemma SubstitutionLemmaExp G x S S' e e':
  binds x S' G ->
  oft_exp G e' S' ->
  oft_exp G e S -> oft_exp G (s[ x ~> e']e e) S.
Proof.
  move=>Hbind Hde' Hde.
  move:Hde'.
  elim Hde ; try constructor ; try assumption.
  intros.
  case: (EV.eq_reflect x x0).
  move=>Sub.
  subst.
  simpl.
  rewrite eq_refl.
  have Heq : S' = S0 by apply: UniquenessBind ; [apply: Hbind | apply: H].
  rewrite-Heq.
  assumption.

  case/eqP=>Hdiff=>//=.
  rewrite ifN_eq ; try assumption.
  by constructor.
Qed.

Theorem ExpressionReplacement G P x E S D:
  binds x S G ->
  oft_exp G E S ->
  oft G P D ->
  oft G (s[ x ~> E]pe P) D.
(* Proof. *)
(*   move=>Def Hd Hp. move: Def Hd. *)
(*   elim Hp; intros ; *)
(*   try (by constructor ; rewrite-/subst_proc_exp); *)
(*   try (constructor ; rewrite-/subst_proc_exp //; by apply H1); *)
(*   try (constructor ; rewrite-/subst_proc_exp //; by apply H2); *)
(*   try (constructor ; rewrite-/subst_proc_exp //; by apply H3); *)
(*   try (constructor ; rewrite-/subst_proc_exp //; by apply H0). *)
(*   { (* send *) *)
(*     constructor ; rewrite-/subst_proc_exp //; *)
(*     intros. *)
(*     rewrite/subst_proc_exp=>//. rewrite-/subst_proc_exp. (* do one step of subst_proc_exp *) *)
(*     apply: SubstitutionLemmaExp. *)
(*     apply: Def. *)
(*     apply: Hd. *)
(*     apply: H. *)
(*     by apply: H1. *)
(*   } *)
(*   { (* receive *) *)
(*     apply: t_receive. *)
(*     rewrite-/subst_proc_exp. *)
(*     intros. *)
(*     have H1': x0\notin (x :: L) by apply: H1. *)
(*     move: H1'. move/notin_cons. case=>Hdiff Hnotin. *)

(*     (* rewrite-add_union. *) *)
(*     rewrite-subst_exp_proc_open_exp. *)
(*     + have def_add_x0: def (add x0 S0 G0) by  apply: oft_def_ctx; apply: H. *)
(*       apply H0 =>//; first by apply: add_binds =>//; apply: neqC. *)
(*       apply: wkn_ctx_oft_exp =>//. *)
(*     + by apply: neqC. *)
(*     + apply: oft_exp_lc. *)
(*       apply Hd. *)
(*   } *)
(*   {constructor ; rewrite-/subst_proc_exp //; intros. *)
(*    apply: H0 => //. *)
(*    apply: H2 => //. *)
(*   } *)
(*   { constructor ; rewrite-/subst_proc_exp //; intros. *)
(*       by apply: (SubstitutionLemmaExp Def). *)
(*         by apply: H1. *)
(*         by apply: H3. *)
(*   } *)
(*   {constructor ; rewrite-/subst_proc_exp //; intros. *)
(*         by apply: H0. *)
(*         by apply: H2. *)
(*   } *)
(*   { apply: (@t_nu_nm L); rewrite -/subst_proc_exp. *)
(*     move => x0 x_nin_L. *)
(*     rewrite -subst_exp_proc_open_name // ; [| apply: (oft_exp_lc Hd)]. *)
(*     have def_add_x0_G0 : def (add (ne x0) s G0) by apply: oft_def_ctx; apply: H. *)
(*     apply: H0 =>//; first by apply: binds_add =>//. *)
(*     by apply: wkn_ctx_oft_exp. *)
(*   } *)
(*   { *)
(*     apply: (t_nu_ch (L:=L)). rewrite -/subst_proc_exp => ki ki_nin. *)
(*     rewrite -subst_exp_openk_var; [| apply: (oft_exp_lc Hd)]. *)
(*     by apply: (H0 ki ki_nin). *)
(*   } *)
(* Qed. *)
Admitted.

Ltac split_notin i H1 H2:=
  move: i; erewrite mem_cat; rewrite negb_or => /andP-[H1 H2].

Ltac inst_notin_cat i :=
  let H1 := fresh i in
  let H2 := fresh i in
  split_notin i H1 H2;
  first [ move: H1 => _; apply: H2; move: H2 => _
        | move: H2 => _; inst_notin_cat H1
        ].

Ltac inst_notin i :=
  first [ apply: i; move: i => _
        | let H1 := fresh i in
          let H2 := fresh i in
          split_notin i H1 H2;
          move: H2 => _;
          inst_notin H1 ].

Lemma subst_nm_oft_exp a a' G e S :
  def (subst_env a a' G) ->
  oft_exp G e S ->
  oft_exp (subst_env a a' G) e S.
(* Proof. *)
(*   move=> Hdef; case=>[_|_|x Sx Hbnd]. *)
(*   by apply: t_tt. *)
(*   by apply: t_ff. *)
(*   apply: t_var; move: Hbnd; case: G Hdef=>//f. *)
(*   rewrite /binds/subst_env/rem/add/upd/look/dom supp_rem !inE. *)
(*   case: (suppP (ne a) f)=>[v|]-H; rewrite H //. *)
(*   rewrite andbC; case: suppP=>[v'|]-H'=>/=. *)
(*   + by case: ifP=>//; rewrite fnd_ins /= fnd_rem /=. *)
(*   + by rewrite fnd_ins /= fnd_rem /=. *)
(* Qed. *)
Admitted.

Lemma completed_means_completed D k T:
  completed D -> look k D = Some T -> T != ended -> False.
  move=>Hcomp Hlook/eqP.
  case Hcomp =>Hfoo Hended.
  move:(look_some_in Hlook)=>/(Hended k).
  rewrite/binds Hlook=>/eqP.
  by case=>->;case.
Qed.


Lemma Weakening G P D1 D2 :
  oft G P D2 -> compatible D1 D2 -> completed D1 -> oft G P (D1 o D2).
Admitted.

(* Lemma Weakening' G P D1 D2 : *)
(*   oft G P D2 -> def (D1 \:/ D2) -> completed D1 -> oft G P (D1 \:/ D2). *)
(* Proof. *)
(*   induction_oft => Def cD1. *)
(*   + apply: (t_request (L:= va_dom D1 ++ va_dom D2 ++ L) *)
(*                       (L':= ch_dom D1 ++ ch_dom D2 ++ L0) (t:=t)) =>// c. *)
(*     move=>/freechan_cat_c-[/freechan_cat_k-[/freechan_dom-c_D1 _] *)
(*                           /freechan_cat_k-[_]]. *)
(*     move=>/freechan_cat_c-[/freechan_cat_k-[/freechan_dom-c_D2 _] *)
(*                           /freechan_cat_k-[_ free_c]]. *)
(*     rewrite unionC -add_union unionC; apply: Ih=>//. *)
(*     rewrite unionC add_union unionC; rewrite def_addb Def /=. *)
(*     by rewrite dom_union Def /= negb_or c_D1 c_D2. *)
(*   + apply: (t_accept (L:= va_dom D1 ++ va_dom D2 ++ L) *)
(*                       (L':= ch_dom D1 ++ ch_dom D2 ++ L0) (t:=t)) =>// c. *)
(*     move=>/freechan_cat_c-[/freechan_cat_k-[/freechan_dom-c_D1 _] *)
(*                           /freechan_cat_k-[_]]. *)
(*     move=>/freechan_cat_c-[/freechan_cat_k-[/freechan_dom-c_D2 _] *)
(*                           /freechan_cat_k-[_ free_c]]. *)
(*     rewrite unionC -add_union unionC; apply: Ih=>//. *)
(*     rewrite unionC add_union unionC; rewrite def_addb Def /=. *)
(*     by rewrite dom_union Def /= negb_or c_D1 c_D2. *)
(*   + rewrite unionC add_union unionC. *)
(*     apply: t_send =>//. *)
(*     rewrite unionC -add_union unionC. *)
(*     apply: Ih=>//. *)
(*     rewrite unionC add_union unionC. *)
(*     move: Def; rewrite unionC add_union unionC. *)
(*     by rewrite def_addb def_addb. *)
(*   + rewrite unionC add_union unionC. *)
(*     apply: (t_receive (L:=L)) =>// x x_L. *)
(*     rewrite unionC -add_union unionC. *)
(*     apply: (Ih x x_L)=>//. *)
(*     rewrite unionC add_union unionC. *)
(*     move: Def; rewrite unionC add_union unionC. *)
(*     by rewrite def_addb def_addb. *)
(*   + rewrite unionC add_union unionC. *)
(*     apply: t_select_l. *)
(*     rewrite unionC -add_union unionC. *)
(*     apply: Ih=>//. *)
(*     rewrite unionC add_union unionC. *)
(*     move: Def; rewrite unionC add_union unionC. *)
(*     by rewrite def_addb def_addb. *)
(*   + rewrite unionC add_union unionC. *)
(*     apply: t_select_r. *)
(*     rewrite unionC -add_union unionC. *)
(*     apply: Ih=>//. *)
(*     rewrite unionC add_union unionC. *)
(*     move: Def; rewrite unionC add_union unionC. *)
(*     by rewrite def_addb def_addb. *)
(*   + rewrite unionC add_union unionC. *)
(*     apply: t_branch; rewrite unionC -add_union unionC. *)
(*     - apply: IhP =>//. *)
(*       rewrite unionC add_union unionC. *)
(*       move: Def; rewrite unionC add_union unionC. *)
(*       by rewrite def_addb def_addb. *)
(*     - apply: IhQ =>//. *)
(*       rewrite unionC add_union unionC. *)
(*       move: Def; rewrite unionC add_union unionC. *)
(*       by rewrite def_addb def_addb. *)
(*   + move: Def; rewrite unionC !add_union unionC => Def. *)
(*     apply: t_throw=>//. *)
(*     rewrite unionC -!add_union unionC. *)
(*     apply: Ih=>//. *)
(*     move: Def. *)
(*     rewrite add_swap =>/def_nested-Def. *)
(*     rewrite unionC add_union unionC; move: Def. *)
(*     by rewrite def_addb def_addb. *)
(*   + rewrite unionC add_union unionC. *)
(*     apply: (t_catch (L:= va_dom D1 ++ va_dom D2 ++ L) *)
(*                    (L':= ch_dom D1 ++ ch_dom D2 ++ L0)) =>// c. *)
(*     move=>/freechan_cat_c-[/freechan_cat_k-[/freechan_dom-c_D1 _] *)
(*                           /freechan_cat_k-[_]]. *)
(*     move=>/freechan_cat_c-[/freechan_cat_k-[/freechan_dom-c_D2 _] *)
(*                           /freechan_cat_k-[_ free_c]]. *)
(*     rewrite unionC -!add_union unionC; apply: Ih=>//. *)
(*     rewrite unionC !add_union unionC. *)
(*     move: Def. *)
(*     rewrite unionC !add_union unionC=>Def. *)
(*     rewrite def_addb (def_diff_value T' Def) /=. *)
(*     move: (oft_def (OftP c free_c)) => /def_add_twice-ck0. *)
(*     rewrite in_addb. *)
(*     move: Def; rewrite def_addb =>/andP-[->->]/=. *)
(*     by rewrite negb_or ck0 /= dom_union negb_and orbC negb_or c_D1 c_D2. *)
(*   + apply: t_ife=>//. *)
(*     by apply: IhP. *)
(*     by apply: IhQ. *)
(*   + rewrite unionA; apply: t_par=>//. *)
(*     by apply: IhP=>//; move: Def; rewrite unionA =>/union_def-[]. *)
(*     by move: Def; rewrite unionA. *)
(*   + apply: t_inact=>//. *)
(*     move: CompD cD1; rewrite /completed/binds=>[][_ H1] [_ H2]. *)
(*     split=>// a. *)
(*     rewrite dom_union Def/= =>/orP-[|]H. *)
(*     - by move: Def;  rewrite unionC => Def; rewrite look_union Def H H2. *)
(*     - by rewrite look_union Def H H1. *)
(*   + apply: (t_nu_nm (L:=L) (s:=s))=> x x_L. *)
(*     by apply: Ih. *)
(*   + apply: (t_nu_ch (L:= ch_dom D1 ++ L) (T:=T)) => x. *)
(*     rewrite mem_cat negb_or =>/andP-[/notin_chdom_dom-x_D1 x_L]. *)
(*     move: (oft_def (OftP x x_L)) => Def'. *)
(*     rewrite unionC -!add_union unionC. *)
(*     apply: Ih=>//. *)
(*     rewrite unionC !add_union unionC. *)
(*     rewrite !def_addb  in_addb !dom_union ke_eqE eq_refl *)
(*     Def !(negPf (x_D1 _)) /= negb_and negbK. *)
(*     by move: Def'; rewrite !def_addb !in_addb ke_eqE eq_refl *)
(*     (proj2 (union_def Def)) /= negb_and negbK. *)
(*   + by apply: t_nu_ch'; apply: Ih. *)
(*   + (* move=> Def' CompD; *) apply: t_bang. *)
(*     move: CompD cD1; rewrite /completed/binds. (* =>[][_ H1] [_ H2]. *) *)
(*     move=> A B . *)
(*     split=>// a. *)
(*     rewrite dom_union Def/= =>/orP-[|]H. *)
(*     - (* move: Def; *) *)
(*       by rewrite unionC look_union unionC Def  H ; *)
(*       move: B ; case ; move=>_ ; apply. *)
(*     - by rewrite look_union Def H ; *)
(*       move: A ; case; move=>_ ; apply. *)
(*     (* - by apply Ih. *) *)
(*     - by apply OftP. *)
(* Qed. *)

(*************************************************************)
Definition subst_k_env k k' (D : tp_env) := subst_env k k' D. (* TODO remove the _env *)

Definition subst_entryk k k' (x : tp_env_entry) := if x == k then k' else x.

Ltac simpl_def :=
  do ! match goal with
       (* | [ |- context[ke _ == ke _] ] => rewrite !ke_eqE *)
       | [ |- context[?k == ?k] ] => rewrite !eq_refl
       (* | [ |- context[?k == dual_pol ?k] ] => rewrite !dualpol_neqr *)
       (* | [ |- context[dual_pol ?k == ?k] ] => rewrite !dualpol_neql *)
       (* | [ |- context[Pos == Neg] ] => rewrite -[Pos == Neg]/(false) *)
       (* | [ |- context[Neg == Pos] ] => rewrite -[Neg == Pos]/(false) *)
       (* | [ |- context[Neg == Neg] ] => rewrite -[Neg == Neg]/(true) *)
       (* | [ |- context[Pos == Pos] ] => rewrite -[Pos == Pos]/(true) *)
       | [ |- context[~~ (_ && _)] ] => rewrite !negb_and
       | [ |- context[~~ (_ || _)] ] => rewrite !negb_or
       | [ |- context[~~ (~~ _)] ] => rewrite !negbK
       | [ |- context[_ && false] ] => rewrite !Bool.andb_false_r
       | [ |- context[_ && true ] ] => rewrite !Bool.andb_true_r
       | [ |- context[_ || false] ] => rewrite !Bool.orb_false_r
       | [ |- context[_ || true ] ] => rewrite !Bool.orb_true_r
       end=>/=.


Lemma ChannelReplacement G P c c' D :
  oft G P D ->
  def (subst_env c c' D) ->
  oft G (s[ c ~> chan_of_entry c' ]p P) (subst_env c c' D).
Proof.
  case: (boolP (c' == c)) =>[/eqP->/=|c_neq_c'];
     first by move=> Hd Ho; rewrite subst_chan_same subst_envK.
  elim.
  { (* t_send *)
    move=> G0 kt e P0 D0 S T Oe Op IH Hdef.
    move: (def_addG (oft_def Op)) => def_kt_D0.
    rewrite -subst_addC /= /subst_ch; last by apply: def_kt_D0.
    rewrite -fun_if. apply: t_send =>//.
    rewrite subst_addC; last by apply: def_kt_D0.
    apply: IH; move: Hdef; rewrite !def_subst_dom //.
    by rewrite !in_dom_rem // (dom_diff_eq _ _ T).
  }
  { (* t_receive *)
    move=> L G0 kt P0 D0 S T Op IH Hdef.
    move: (def_addG (oft_def (Op (EV.fresh L) (EV.fresh_not_in L)))) => def_kt_D0.
    rewrite -subst_addC /= /subst_ch; last by apply: def_kt_D0.
    rewrite -fun_if; apply: (t_receive (L:=L))=>//.
    rewrite subst_addC; last by apply: def_kt_D0.
    move=>x x_notin; rewrite -subst_proc_open_e.
    apply: (IH x x_notin); move: Hdef; rewrite !def_subst_dom //.
    by rewrite !in_dom_rem // (dom_diff_eq _ _ T).
  }
  { (* t_ife *)
    move=> G0 e P0 Q D0 Oe O_P IHp O_Q IHq Hdef/=.
    by apply: t_ife => //; [apply: IHp|apply: IHq].
  }
  { (* t_par *)
    admit.
  }
  { (* t_inact *)
  + move=> G0 D0 C0 Df Hdef; apply: t_inact =>//.
    move: C0; rewrite /completed => [][DD0 Bnd]; split=>// x H.
    move: Bnd; rewrite /binds=> Bnd.
    rewrite look_subst //.
    move: H=>/in_dom_subst-/orP-[/andP-[cD0 /orP-[xc'|]]|] //.
    - by rewrite xc' cD0; apply: Bnd.
    - rewrite cD0; move=>/andP[/negPf->].
      case: D0 DD0 Bnd cD0 Hdef => // f _ ; rewrite /rem/dom => Bnd cD0 _.
      rewrite supp_rem !inE /look fnd_rem -/(look _ (Def f))=> /andP-[/negPf->].
      by apply: Bnd.
    - by move=>/andP-[/negPf->]; apply: Bnd.
  }
  { (* t_nu *)
    admit.
  }
  { (* t_nu' *)
    move=> G0 P0 D0 Hoft IH Hdef/=; move: (IH Hdef) => Hoft'.
    by apply: t_nu'.
  }
  { (* t_bang *)
  + move=> G0 P0 D0 C0 Df IH Hdef ; apply: t_bang =>//.
    move: C0; rewrite /completed => [][DD0 Bnd]; split=>// x H.
    move: Bnd; rewrite /binds=> Bnd.
    rewrite look_subst //.
    move: H=>/in_dom_subst-/orP-[/andP-[cD0 /orP-[xc'|]]|] //.
    - by rewrite xc' cD0; apply: Bnd.
    -
      rewrite cD0; move=>/andP[/negPf->].
      case: D0 Df DD0 Bnd cD0 IH Hdef => // f _ ; rewrite /rem/dom => Bnd cD0 _.
      rewrite supp_rem !inE /look fnd_rem -/(look _ (Def f))=>//.
      move=> _ _ /andP -[/negPf->] => HH.
      by rewrite cD0.
    - by move=>/andP-[/negPf->]; apply: Bnd.
    - by apply IH.
  }
(* Qed. *)
Admitted.
