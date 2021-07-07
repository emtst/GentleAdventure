From mathcomp Require Import all_ssreflect seq.
Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Require Import FinMap.ordtype.

Require Import MiniEMTST.AtomScopes.
Require Import MiniEMTST.Syntax.
Require Import MiniEMTST.Env.

Definition sort_env_entry := EV_atom_ordType.
Definition sort_env := @env sort_env_entry sort_eqType.

Inductive oft_exp (G : sort_env) : exp -> sort -> Prop :=
| t_tt : def G -> oft_exp G tt boole
| t_ff : def G -> oft_exp G ff boole
| t_var : forall x (S : sort),
    binds x S G ->
    oft_exp G (V (EV.Free x)) S
.

Definition tp_env_entry := CH_atom_ordType. (* TODO CLEANUP *)
Definition tp_env := @env tp_env_entry tp_eqType.

Definition completed (D : tp_env) : Prop :=
  def D /\ forall a, a \in dom D -> binds a ended D.

Definition chan_of_entry (c : tp_env_entry) : channel := c. (* TODO REMOVE *)


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
    def (D1 \:/ D2) ->
    oft G (par P Q) (D1 \:/ D2)

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
    def (union D1 D2) /\ (union D1 D2 = D) /\ oft G P D1 /\ oft G Q D2.
Proof.
  elim/oft_inv_par => _ G0 P1 Q0 D1 D2 oftP oftQ Hdef _ _ _ _.
  by exists D1, D2.
Qed.

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

(*NEIN*)
(* Lemma subst_opc (x : LC.atom) u n (y : channel) (c : channel) : *)
(*   y != x -> *)
(*   lcb_ch u -> *)
(*   s[ x ~> u ]c opc n y c = opc n y (s[ x ~> u ]c c). *)
(* Proof. *)
(*   move=>neq; case: c=>[[k v]|i]/=//; case: i=>[a|m]//; rewrite /subst_ch /=. *)
(*   + move=>/lcb_chP; case: ifP=>// _; case=>//. *)
(*   + move=>/lcb_chP; case: (ifP (n == m))=>//_; case: y neq=>[[ky py]|[b|f]]///=-Eq _. *)
(*     by move:Eq=>/negPf->. *)
(* Qed. *)

(* Lemma neq_step x y : lc_ch y -> x != y -> shift_ch x != y. *)
(* Proof. by case=>/=; case: x =>// [[[]//k p]]. Qed. *)

(* NEIN *)
(* Lemma subst_proc_open_var (x : LC.atom) (y : channel) u P: *)
(*   y != x -> lcb_ch u -> *)
(*   (s[ x ~> u ]p open_c0 P y) = (open_c0 (s[ x ~> u ]p P) y). *)
(* Proof. *)
(*   move=> xy lc_e; rewrite /open_c0; move: 0 => n. *)
(*   elim: P n y xy lc_e *)
(*   => [ v p IH *)
(*      | v p IH *)
(*      | c e p IH *)
(*      | c p IH *)
(*      | c l p IH *)
(*      | c p1 IH1 p2 IH2 *)
(*      | c1 c2 p IH *)
(*      | c p IH *)
(*      | e p1 IH1 p2 IH2 *)
(*      | p1 IH1 p2 IH2 *)
(*      | *)
(*      | p IH *)
(*      | p IH *)
(*      | p IH] n y xy lc_y /=; *)
(*   try (rewrite IH =>//); *)
(*   try (rewrite IH1 =>//); *)
(*   try (rewrite IH2 =>//); *)
(*   try (rewrite !subst_opc=>//); *)
(*   try (apply: lcch_step=>//); *)
(*   try (apply: neq_step=>//); *)
(*   try easy. *)
(* Qed. *)

(* Lemma subst_exp_proc_open_var x y e P: *)
(*   lc_exp e -> *)
(*   (s[ x ~> e ]pe open_c0 P y) = (open_c0 (s[ x ~> e ]pe P) y). *)
(* Proof. *)
(*   by move=> lc_e; rewrite /open_c0; move: 0 => n; by_proc_induction2 P n y. *)
(* Qed. *)

(* Lemma subst_ch_same c c' : s[ c ~> c ]c c' = c'. *)
(* Proof. *)
(*   case: c'=> [[k p]|] //; case=>// /= a. *)
(*   by rewrite /subst_ch; case: ifP =>// /eqP->. *)
(* Qed. *)

(* Lemma subst_chan_same c P : s[c ~> c]p P = P. *)
(* Proof. *)
(*   by_proc_induction0 P; rewrite !subst_ch_same=>//. *)
(* Qed. *)

(* Lemma subst_exp_proc_open_exp x y e P: *)
(*   x != y -> *)
(*   lc_exp e -> *)
(*   (s[ x ~> e ]pe open_e0 P y) = (open_e0 (s[ x ~> e ]pe P) y). *)
(* Proof. *)
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

(* Lemma subst_exp_ope x y n e : *)
(*   x \notin fv_exp e -> *)
(*   s[ x ~> y ]e ope n x e = ope n y e. *)
(* Proof. *)
(*   case: e =>// [][a|m _] /=//; last by case: ifP => ///=; rewrite eq_refl. *)
(*   by rewrite in_cons negb_or=>/andP-[/negPf->]. *)
(* Qed. *)

(* Lemma subst_exp_open_e x y P : *)
(*   x \notin fv_e P -> *)
(*   s[ x ~> y ]pe open_e0 P x = open_e0 P y. *)
(* Proof. *)
(*   rewrite /open_e0; move: 0. *)
(*   elim: P *)
(*   => [ v p IH *)
(*      | v p IH *)
(*      | c e p IH *)
(*      | c p IH *)
(*      | c l p IH *)
(*      | c p1 IH1 p2 IH2 *)
(*      | c1 c2 p IH *)
(*      | c p IH *)
(*      | e p1 IH1 p2 IH2 *)
(*      | p1 IH1 p2 IH2 *)
(*      | *)
(*      | p IH *)
(*      | p IH *)
(*      | p IH] n /=; *)
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

(* NEIN *)
(* Lemma subst_open_n a a' P : *)
(*   a \notin fn P -> subst_ept a a' (open_n0 P a) = open_n0 P a'. *)
(* Proof. *)
(*   rewrite /open_n0; move: 0. *)
(*   elim: P *)
(*   => [ v p IH *)
(*      | v p IH *)
(*      | c e p IH *)
(*      | c p IH *)
(*      | c l p IH *)
(*      | c p1 IH1 p2 IH2 *)
(*      | c1 c2 p IH *)
(*      | c p IH *)
(*      | e p1 IH1 p2 IH2 *)
(*      | p1 IH1 p2 IH2 *)
(*      | *)
(*      | p IH *)
(*      | p IH *)
(*      | p IH] n /=; *)
(*   try (rewrite !mem_cat !negb_or); *)
(*   try (move => /andP-[nin1 /andP-[nin2 nin3]]); *)
(*   try (move => /andP-[nin1 nin2]); *)
(*   try (move=>x_notin); *)
(*   try (rewrite IH =>//); *)
(*   try (rewrite IH1 =>//); *)
(*   try (rewrite IH2 =>//); *)
(*   try easy; *)
(*   try (move: nin1; case: v=>[a0|n0]/=; *)
(*          first (by rewrite -[SC.Free _ == _]/(a0 == a) in_cons *)
(*                             negb_or eq_sym=>/andP-[/negPf->]// _); *)
(*        by move=>_; case: ifP=>//; case: ifP=>//; rewrite eq_refl). *)
(* Qed. *)

(* Lemma subst_exp_proc_open_name x y e P: *)
(*   lc_exp e -> *)
(*   (s[ x ~> e ]pe open_n0 P y) = (open_n0 (s[ x ~> e ]pe P) y). *)
(* Proof. *)
(*   move=> lc_e; rewrite /open_n0; move: 0 => n; by_proc_induction P n =>//. *)
(* Qed. *)

(* Lemma subst_proc_open_name x y e P: *)
(*   (s[ x ~> e ]p open_n0 P y) = (open_n0 (s[ x ~> e ]p P) y). *)
(* Proof. *)
(*   rewrite /open_n0; move: 0 => n; by_proc_induction P n =>//. *)
(* Qed. *)

(* Lemma subst_chan_openk_var x u n k ch : *)
(*   lc_ch u -> s[ x ~> u ]c opk n k ch = opk n k (s[ x ~> u ]c ch). *)
(* Proof. *)
(*   rewrite /opk/subst_ch; case: ch =>//[[]|]// []// a. *)
(*   case: ifP=>// _; elim=>//. *)
(* Qed. *)

(* Lemma subst_proc_openk_var x k u P: *)
(*   (* x != y -> *) lc_ch u -> *)
(*   (s[ x ~> u ]p open_k0 P k) = (open_k0 (s[ x ~> u ]p P) k). *)
(* Proof. *)
(*   move=> lc_ch; rewrite /open_k0; move: 0 => n; by_proc_induction P n =>//; *)
(*   rewrite !subst_chan_openk_var //. *)
(* Qed. *)

(* Lemma subst_exp_openk_var x k e P: *)
(*   (* x != y -> *) lc_exp e -> *)
(*   (s[ x ~> e ]pe open_k0 P k) = (open_k0 (s[ x ~> e ]pe P) k). *)
(* Proof. *)
(*   move=> lc_ch; rewrite /open_k0; move: 0 => n; by_proc_induction P n =>//. *)
(* Qed. *)

(* Lemma subst_proc_open_e x k u P: *)
(*   (s[ x ~> u ]p open_e0 P k) = (open_e0 (s[ x ~> u ]p P) k). *)
(* Proof. *)
(*   by rewrite /open_e0; move: 0 => n; by_proc_induction P n. *)
(* Qed. *)

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
(* Lemma SubstitutionLemmaExp G x S S' e e': *)
(*   binds (ee x) S' G -> *)
(*   oft_exp G e' S' -> *)
(*   oft_exp G e S -> oft_exp G (s[ x ~> e']e e) S. *)
(* Proof. *)
(*   move=>Hbind Hde' Hde. *)
(*   move:Hde'. *)
(*   elim Hde ; try constructor ; try assumption. *)
(*   intros. *)
(*   case: (EV.eq_reflect x x0). *)
(*   move=>Sub. *)
(*   subst. *)
(*   simpl. *)
(*   rewrite eq_refl. *)
(*   have Heq : S' = S0 by apply: UniquenessBind ; [apply: Hbind | apply: H]. *)
(*   rewrite-Heq. *)
(*   assumption. *)

(*   case/eqP=>Hdiff=>//=. *)
(*   rewrite ifN_eq ; try assumption. *)
(*   by constructor. *)
(* Qed. *)

(* Theorem ExpressionReplacement G P x E S D: *)
(*   binds (ee x) S G -> *)
(*   oft_exp G E S -> *)
(*   oft G P D -> *)
(*   oft G (s[ x ~> E]pe P) D. *)
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
(*     + have def_add_x0: def (add (ee x0) S0 G0) by  apply: oft_def_ctx; apply: H. *)
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

(* Lemma subst_nm_oft_exp a a' G e S : *)
(*   def (subst_env (ne a) (ne a') G) -> *)
(*   oft_exp G e S -> *)
(*   oft_exp (subst_env (ne a) (ne a') G) e S. *)
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

Lemma completed_means_completed D k T:
  completed D -> look k D = Some T -> T != ended -> False.
  move=>Hcomp Hlook/eqP.
  case Hcomp =>Hfoo Hended.
  move:(look_some_in Hlook)=>/(Hended k).
  rewrite/binds Hlook=>/eqP.
  by case=>->;case.
Qed.



Lemma Weakening G P D1 D2 :
  oft G P D2 -> def (D1 \:/ D2) -> completed D1 -> oft G P (D1 \:/ D2).
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
Admitted.

(* Theorem EndpointReplacement G P D a a' : *)
(*   oft G P D -> *)
(*   def (subst_env (ne a) (ne a') G) -> *)
(*   oft (subst_env (ne a) (ne a') G) (subst_ept a a' P) D. *)
(* Proof. *)
(*   elim=>/=. *)
(*   + move=> L L' G0 a0 P0 D0 t Hbinds Hp IH Hdef. *)
(*     rewrite -fun_if; apply: (t_request (L:=L) (L':=L') (t:=t)); *)
(*       first by rewrite fun_if; apply: binds_subst. *)
(*     by move=> c fc; rewrite openc_subst_ept; apply: IH. *)
(*   + move=> L L' G0 a0 P0 D0 t Hbinds Hp IH Hdef. *)
(*     rewrite -fun_if; apply: (t_accept (L:=L) (L':=L') (t:=t)); *)
(*       first by rewrite fun_if; apply: binds_subst. *)
(*     by move=> c fc; rewrite openc_subst_ept; apply: IH. *)
(*   + move=> G0 kt e P0 D0 S T Oe OP0 H Def; move: (H Def) => {H}-H. *)
(*     by apply: t_send; first by apply: subst_nm_oft_exp. *)
(*   + move=> L G0 kt P0 D0 S T OP0 H Def. *)
(*     apply (t_receive (L:=(ea_dom G0) ++ L))=>ki; rewrite mem_cat negb_or. *)
(*     move=>/andP-[k_free k_L]; rewrite opene_subst_ept neq_add_substC //. *)
(*     apply: H =>//; rewrite -neq_add_substC // def_addb Def /=. *)
(*     move: (def_subst_nested Def)=>DD0; apply/negP=>/in_dom_subst /=. *)
(*     by rewrite in_dom_rem ///= (negPf (notin_eadom_dom k_free)) andbC /= andbC. *)
(*   + move=> G0 k P0 D0 T T' OP0 IH Hdef; move: (IH Hdef) => {IH} IH. *)
(*     by apply: t_select_l. *)
(*   + move=> G0 k P0 D0 T T' OP0 IH Hdef; move: (IH Hdef) => {IH} IH. *)
(*     by apply: t_select_r. *)
(*   + move=> H0 k P0 Q D0 T T' OP0 IH1 OQ IH2 Hdef. *)
(*     move: (IH1 Hdef) (IH2 Hdef) => {IH1}IH1 {IH2}IH2. *)
(*     by apply: t_branch. *)
(*   + move=> G0 k k' P0 D0 T T' OP0 IH Def1 Def2; move: (IH Def2)=>{IH}IH. *)
(*     by apply: t_throw. *)
(*   + move=> L L' G0 k P0 D0 T T' OP0 IH Def. *)
(*     apply: (t_catch (L:=L) (L':=L')) => x x_L. *)
(*     by rewrite openc_subst_ept; apply: IH. *)
(*   + move=> G0 e P0 Q D0 Oe OP0 IH1 OQ IH2 Df. *)
(*     move: (IH1 Df) (IH2 Df)=>{IH1}IH1{IH2}IH2. *)
(*     by apply: t_ife;  first by apply: subst_nm_oft_exp. *)
(*   + move=> G0 {P}P Q D1 D2 OP H1 OQ H2 Df1 Df2. *)
(*     move: (H1 Df2) (H2 Df2) => {H1}{H2} H1 H2. *)
(*     by apply: t_par. *)
(*   + by move=> G0 D0 CD0 Df; apply: t_inact. *)
(*   + move=> L {G}G s {P}P {D}D OP IH Def. *)
(*     apply: (t_nu_nm (L:=a::a':: (na_dom G ++ L))) => x. *)
(*     rewrite !in_cons mem_cat !negb_or=>/andP[xa /andP-[xa' /andP-[x_free x_L]]]. *)
(*     rewrite neq_add_substC; last by rewrite -[ne _ == _]/(x == a). *)
(*     rewrite openn_subst_ept //; apply: IH=>//. *)
(*     rewrite -neq_add_substC; last by rewrite -[ne _ == _]/(x == a). *)
(*     rewrite def_addb Def /=; apply/negP=>/in_dom_subst. *)
(*     move: (def_subst_nested Def)=> DD. *)
(*     rewrite in_dom_rem // -[ne x == _]/(x == a'). *)
(*     by rewrite (negPf xa') (negPf (notin_nadom_dom x_free))/= andbA andbC/= andbC. *)
(*   + move=>{G}G {P}P {D}D T L OP IH Def. *)
(*     by apply: (t_nu_ch (L:=L))=> ki ki_L; rewrite openk_subst_ept; apply: IH. *)
(*   + by move=> {G}G {P}P{D}D OP IH Def; apply: t_nu_ch'; apply: IH. *)
(*   + by move=> {G}G {P}P{D}D Comp OP IH Def ; *)
(*     apply: t_bang; [easy| apply: IH]. *)
(* Qed. *)

(* Definition subst_k_env k k' (D : tp_env) := *)
(*   subst_env (ke (k, Pos)) (ke (k', Pos)) *)
(*             (subst_env (ke (k, Neg)) (ke (k', Neg)) D). *)

(* Definition subst_entryk k k' (e : tp_env_entry) := *)
(*   match e with *)
(*   | inl _ => e *)
(*   | inr (x, p) => if x == k then inr (k', p) else e *)
(*   end. *)


(* Lemma subst_chk_entry k k' kt : *)
(*   subst_chk k k' (chan_of_entry kt) *)
(*   = chan_of_entry (subst_entryk k k' kt). *)
(* Proof. *)
(*   move: kt; do ! case=>///=. *)
(*   by move=> a b; case: ifP=>[/eqP->|]; [rewrite eq_refl|rewrite eq_sym=>->]. *)
(* Qed. *)

(* Lemma dualpol_neqr p : p != dual_pol p. *)
(* Proof. by rewrite (negPf (pol_dual_noteq _)) //; last by rewrite dual_polK. Qed. *)

(* Lemma dualpol_neql p : dual_pol p != p. *)
(* Proof. by rewrite (negPf (pol_dual_noteq _)). Qed. *)

(* Ltac simpl_def := *)
(*   do ! match goal with *)
(*        | [ |- context[ke _ == ke _] ] => rewrite !ke_eqE *)
(*        | [ |- context[?k == ?k] ] => rewrite !eq_refl *)
(*        | [ |- context[?k == dual_pol ?k] ] => rewrite !dualpol_neqr *)
(*        | [ |- context[dual_pol ?k == ?k] ] => rewrite !dualpol_neql *)
(*        | [ |- context[Pos == Neg] ] => rewrite -[Pos == Neg]/(false) *)
(*        | [ |- context[Neg == Pos] ] => rewrite -[Neg == Pos]/(false) *)
(*        | [ |- context[Neg == Neg] ] => rewrite -[Neg == Neg]/(true) *)
(*        | [ |- context[Pos == Pos] ] => rewrite -[Pos == Pos]/(true) *)
(*        | [ |- context[~~ (_ && _)] ] => rewrite !negb_and *)
(*        | [ |- context[~~ (_ || _)] ] => rewrite !negb_or *)
(*        | [ |- context[~~ (~~ _)] ] => rewrite !negbK *)
(*        | [ |- context[_ && false] ] => rewrite !Bool.andb_false_r *)
(*        | [ |- context[_ && true ] ] => rewrite !Bool.andb_true_r *)
(*        | [ |- context[_ || false] ] => rewrite !Bool.orb_false_r *)
(*        | [ |- context[_ || true ] ] => rewrite !Bool.orb_true_r *)
(*        end=>/=. *)

(* Ltac simpl_ke := *)
(*   do ! ( rewrite /subst_k_env/can_subst; *)
(*          crush_def; *)
(*          match goal with *)
(*          | [ H: ke _ = ke _ |- _ ] => *)
(*            let H1 := fresh in *)
(*            let H2 := fresh in *)
(*            move: H=>/eqP; rewrite ke_eqE=>/andP-[H1 H2] *)
(*          | [ |- context [ ke _ == ke _ ] ] => rewrite !ke_eqE *)
(*          | [ |- _ ] => idtac *)
(*          end=>///=; rw_step). *)

(* Theorem ChannelNameReplacement G P D k k' : *)
(*   oft G P D -> *)
(*   def (subst_k_env k k' D) -> *)
(*   oft G (subst_prock k k' P) (subst_k_env k k' D). *)
(* Proof. *)
(*   case: (boolP (k == k')) =>[/eqP->/=|]; first by *)
(*       rewrite /subst_k_env !subst_envK substk_same. *)
(*   rewrite eq_sym=> kk'; elim=>/=. *)
(*   + move=> L L' G0 a0 P0 D0 t Hbinds Hp IH Hdef. *)
(*     apply: (t_request (L:=va_dom D0++L) (L':=k::k'::ch_dom D0++L') (t:=t))=>// c fc. *)
(*     move: (freechan_cons_k fc) (freechan_neq_k fc) => {fc} fc ck. *)
(*     move: (freechan_cons_k fc) (freechan_neq_k fc) => {fc} fc ck'. *)
(*     move: (freechan_cat_c fc) => *)
(*     {fc} [/freechan_cat_k-[/freechan_dom-cD0 _] /freechan_cat_k-[_ fc]]. *)
(*     have kfv: k \notin fv_k (chan_of_entry c) by *)
(*         case: c ck fc ck' cD0 => //; case=>// a b/= /(_ b); *)
(*         rewrite ke_eqE in_cons negb_and eq_sym orbC eq_refl/= => /negPf->. *)
(*     have kfv' : k' \notin fv_k (chan_of_entry c) by *)
(*         case: c ck' fc ck cD0 kfv => //; case=>// a b/= /(_ b); *)
(*         rewrite ke_eqE !in_cons negb_and eq_sym orbC eq_refl /= => /negPf->. *)
(*     rewrite openc_substk // /subst_k_env. *)
(*     rewrite !neq_add_substC //; apply: IH =>//. *)
(*     move: (def_subst_nested Hdef) => Hdef'. *)
(*     move: (def_subst_nested Hdef') => Hdef''. *)
(*     have Hdef_c: forall T, (def (add c T D0)) *)
(*         by move=>T; rewrite def_addb Hdef'' cD0. *)
(*     have k'k : k != k' by rewrite eq_sym. *)
(*     have cks : forall p : polarity, ke (k, p) != c *)
(*       by move=>pl; move: (negPf (ck pl)); rewrite eq_sym=>->. *)
(*     have cks' : forall p : polarity, ke (k', p) != c *)
(*       by move=>pl; move: (negPf (ck' pl)); rewrite eq_sym=>->. *)
(*     rewrite /subst_k_env. *)
(*     move: Hdef; rewrite /subst_k_env. *)
(*     rewrite !def_substb !def_addb /can_subst !dom_substb /can_subst !in_addb. *)
(*     rewrite  !ke_eqE Hdef'' (negPf k'k) /= eq_refl (negPf kk') cD0 eq_refl. *)
(*     by do ! rewrite (negPf (cks' _)) (negPf (cks _)) /=. *)
(*   + move=> L L' G0 a0 P0 D0 t Hbinds Hp IH Hdef. *)
(*     apply: (t_accept (L:=va_dom D0++L) (L':=k::k'::ch_dom D0++L') (t:=t))=>// c fc. *)
(*     move: (freechan_cons_k fc) (freechan_neq_k fc) => {fc} fc ck. *)
(*     move: (freechan_cons_k fc) (freechan_neq_k fc) => {fc} fc ck'. *)
(*     move: (freechan_cat_c fc) => *)
(*     {fc} [/freechan_cat_k-[/freechan_dom-cD0 _] /freechan_cat_k-[_ fc]]. *)
(*     have kfv: k \notin fv_k (chan_of_entry c) by *)
(*         case: c ck fc ck' cD0 => //; case=>// a b/= /(_ b); *)
(*         rewrite ke_eqE in_cons negb_and eq_sym orbC eq_refl/= => /negPf->. *)
(*     have kfv' : k' \notin fv_k (chan_of_entry c) by *)
(*         case: c ck' fc ck cD0 kfv => //; case=>// a b/= /(_ b); *)
(*         rewrite ke_eqE !in_cons negb_and eq_sym orbC eq_refl /= => /negPf->. *)
(*     rewrite openc_substk // /subst_k_env. *)
(*     rewrite !neq_add_substC //; apply: IH =>//. *)
(*     move: (def_subst_nested Hdef) => Hdef'. *)
(*     move: (def_subst_nested Hdef') => Hdef''. *)
(*     have Hdef_c: forall T, (def (add c T D0)) *)
(*         by move=>T; rewrite def_addb Hdef'' cD0. *)
(*     have k'k : k != k' by rewrite eq_sym. *)
(*     have cks : forall p : polarity, ke (k, p) != c *)
(*       by move=>pl; move: (negPf (ck pl)); rewrite eq_sym=>->. *)
(*     have cks' : forall p : polarity, ke (k', p) != c *)
(*       by move=>pl; move: (negPf (ck' pl)); rewrite eq_sym=>->. *)
(*     move: Hdef; rewrite /subst_k_env. *)
(*     rewrite !def_substb /can_subst !dom_substb /can_subst !in_addb !def_addb. *)
(*     rewrite Hdef'' !ke_eqE (negPf k'k) !eq_refl (negPf kk') !(negPf (cks _)). *)
(*     by rewrite !(negPf (cks' _)) cD0 /=. *)
(*   + move=> G0 kt e P0 D0 S T Oe OP0 IH Def. *)
(*     rewrite substk_add // subst_chk_entry; apply: t_send =>//. *)
(*     suff Hdef : def (subst_k_env k k' (add kt T D0)) *)
(*       by rewrite -substk_add //; apply: IH. *)
(*     move: Def; rewrite /subst_k_env !def_substb !def_addb /can_subst. *)
(*     by rewrite !dom_substb /can_subst !in_addb. *)
(*   + move=> L G0 kt P0 D0 S T OP0 H Def. *)
(*     rewrite substk_add // subst_chk_entry; apply: (t_receive (L:=L)) =>// x x_L. *)
(*     suff Hdef : def (subst_k_env k k' (add kt T D0)) *)
(*       by rewrite -substk_add // opene_substk; apply: (H x x_L). *)
(*     move: Def; rewrite /subst_k_env !def_substb /can_subst !dom_substb. *)
(*     by rewrite /can_subst !in_addb !def_addb. *)
(*   + move=> G0 k0 P0 D0 T T' OP0 IH Hdef. *)
(*     rewrite substk_add // subst_chk_entry; apply: t_select_l. *)
(*     suff Hdef' : def (subst_k_env k k' (add k0 T D0)) *)
(*       by rewrite -substk_add //; apply: IH. *)
(*     move: Hdef; rewrite /subst_k_env !def_substb /can_subst !dom_substb. *)
(*     by rewrite /can_subst !in_addb !def_addb. *)
(*   + move=> G0 k0 P0 D0 T T' OP0 IH Hdef. *)
(*     rewrite substk_add // subst_chk_entry; apply: t_select_r. *)
(*     suff Hdef' : def (subst_k_env k k' (add k0 T' D0)) *)
(*       by rewrite -substk_add //; apply: IH. *)
(*     move: Hdef; rewrite /subst_k_env !def_substb /can_subst !dom_substb. *)
(*     by rewrite /can_subst !in_addb !def_addb. *)
(*   + move=> H0 k0 P0 Q D0 T T' OP0 IH1 OQ IH2 Hdef. *)
(*     rewrite substk_add // subst_chk_entry. *)
(*     suff Hdef' Tn : def (subst_k_env k k' (add k0 Tn D0)) *)
(*       by apply: t_branch; rewrite -substk_add //; [apply: IH1 | apply: IH2]. *)
(*     move: Hdef; rewrite /subst_k_env !def_substb /can_subst !dom_substb. *)
(*     by rewrite /can_subst !in_addb !def_addb. *)
(*   + move=> G0 k0 k0' P0 D0 T T' OP0 IH Def1 Def2. *)
(*     suff [Hdef' Hdef''] : *)
(*       (forall T, def (subst_k_env k k' (add k0' T D0))) /\ *)
(*       (forall T, def (subst_k_env k k' (add k0 T D0))) *)
(*       by rewrite substk_add // substk_add //  !subst_chk_entry; *)
(*       apply: t_throw; rewrite -!substk_add //; first by apply: IH. *)
(*     move: Def2; rewrite /subst_k_env => Def2. *)
(*     move: (def_subst_nested Def2) => Def3; move: (def_subst_nested Def3) => Def4. *)
(*     move: (def_nested Def4) => /def_diff_value-Def7. *)
(*     have Def5 : forall T, def (add k0 T D0) by *)
(*         move: Def4; rewrite add_swap => /def_nested/def_diff_value. *)
(*     have Def6 : (k0' \notin dom (add k0 (ch_output T T') D0)) by *)
(*         move: Def4; rewrite add_swap def_addb=>/andP-[_]. *)
(*     have Def8 : (k0 \notin dom (add k0' T D0)) by *)
(*         move: Def4; rewrite def_addb=>/andP-[_]. *)
(*     split => T0. *)
(*     - apply: (def_subst_swap _ _ Def2). *)
(*       * apply: (dom_subst_swap) => [_|x]; first by apply: (def_cansubst Def3). *)
(*         rewrite add_swap; apply dom_add_swap =>//; apply: sub_dom_add. *)
(*         by move: (Def5 T); rewrite def_addb=>/andP-[_]. *)
(*       * apply: def_subst_swap =>// x. *)
(*         rewrite add_swap; apply dom_add_swap =>//; apply: sub_dom_add. *)
(*         by move: (Def5 T); rewrite def_addb=>/andP-[_]. *)
(*     - apply: (def_subst_swap _ _ Def2). *)
(*       * apply: (dom_subst_swap) => [_|x]; first by apply: (def_cansubst Def3). *)
(*         apply dom_add_swap =>//; apply: sub_dom_add. *)
(*         by move: (Def7 T); rewrite def_addb=>/andP-[_]. *)
(*       * apply: def_subst_swap =>// x. *)
(*         apply dom_add_swap =>//; apply: sub_dom_add. *)
(*         by move: (Def7 T); rewrite def_addb=>/andP-[_]. *)
(*   + move=> L L' G0 k0 P0 D0 T T' OP0 IH Def. *)
(*     have Hdef : forall T, def (subst_k_env k k' (add k0 T D0)). *)
(*       move=>T0; move: Def; do ! apply: def_subst_swap. *)
(*       move=>k1; apply: dom_subst_swap; first by apply: cansubst_add. *)
(*       by move=> x; rewrite !in_addb. *)
(*       by move=> x; rewrite !in_addb. *)
(*       by rewrite !def_addb. *)
(*     rewrite substk_add // subst_chk_entry. *)
(*     apply: (t_catch (L:=va_dom D0 ++ ca_of_entry k0 ++ L) *)
(*                     (L':=ch_dom D0 ++ ka_of_entry k0 ++ k'::k::L')) => x. *)
(*     move => /freechan_cat_c-[/freechan_cat_k-[/freechan_dom-x_D0 _] *)
(*                              /freechan_cat_k-[_]]. *)
(*     move => /freechan_cat_c-[/freechan_cat_k-[/freechan_entry-x_k0 _] *)
(*                              /freechan_cat_k-[_ x_L]]. *)
(*     move: (freechan_cons_k x_L) (freechan_neq_k x_L) =>{x_L}x_L x_k'. *)
(*     move: (freechan_cons_k x_L) (freechan_neq_k x_L) =>{x_L}x_L x_k. *)
(*     have x_fvk: k \notin fv_k (chan_of_entry x). *)
(*       move: x_k; case: x x_k' x_k0 x_D0 x_L=>//[][kx px] _ _ _ _ /(_ px)/=. *)
(*       by rewrite in_cons ke_eqE eq_refl negb_or in_nil Bool.andb_true_r eq_sym=>->. *)
(*     rewrite -substk_add // openc_substk // /subst_k_env !neq_add_substC //. *)
(*     rewrite -/(subst_k_env _ _ _); apply: (IH x x_L _). *)
(*     rewrite /subst_k_env -neq_add_substC // -neq_add_substC // *)
(*             -/(subst_k_env _ _ _). *)
(*     apply: def_add_assumption =>//. *)
(*     rewrite dom_substb (def_cansubst (Hdef T')) /= !negb_or !negb_and negbK. *)
(*     rewrite x_k' /= (negPf (x_k _)) /=. *)
(*     rewrite dom_substb (def_cansubst (def_subst_nested (Hdef T'))) /=. *)
(*     rewrite  !negb_or !negb_and negbK x_k' /= (negPf (x_k _)) /=. *)
(*     rewrite in_addb !negb_and negb_or negb_and negbK x_k0 (negPf x_D0). *)
(*     by rewrite !Bool.orb_true_r. *)
(*   + move=> G0 e P0 Q D0 Oe OP0 IH1 OQ IH2 Df. *)
(*     move: (IH1 Df) (IH2 Df)=>{IH1}IH1{IH2}IH2. *)
(*     by apply: t_ife. *)
(*   + move=> G0 {P}P Q D1 D2 OP H1 OQ H2 Df1 Df2. *)
(*     move: Df2; rewrite /subst_k_env !subst_union -!/(subst_k_env _ _ _) =>Def. *)
(*     move : (union_def Def) => [Df2 Df3]. *)
(*     move: (H1 Df2) (H2 Df3) => {H1}{H2} H1 H2. *)
(*     by apply: t_par. *)
(*   + move=> G0 D0 CD0 Df. *)
(*     rewrite /subst_k_env => Def1; move: (def_subst_nested Def1)=> Def2. *)
(*     apply: t_inact =>//. *)
(*     by do 2 apply: completed_subst => //. *)
(*   + move=> L {G}G s {P}P {D}D OP IH Def. *)
(*     apply: (t_nu_nm (L:=L) (s:=s)) => x x_L. *)
(*     by rewrite openn_substk; apply: IH. *)
(*   + move=>{G}G {P}P {D}D T L OP IH Def. *)
(*     apply: (t_nu_ch (L:=ch_dom D ++ k'::k::L))=> ki. *)
(*     rewrite mem_cat !inE !negb_or=>/andP-[kiD /andP-[kik' /andP-[kik kiL]]]. *)
(*     move: kiD=> /notin_chdom_dom-kiD. *)
(*     rewrite openk_substk // !neq_add_substC ?ke_eqE ?(negPf kik)//. *)
(*     apply: IH =>//. *)
(*     rewrite /subst_k_env -!neq_add_substC ?ke_eqE ?(negPf kik)//. *)
(*     rewrite -/(subst_k_env _ _ _). *)
(*     rewrite !def_addb Def /= dom_substb !ke_eqE (negPf kik') (negPf kik)/=. *)
(*     rewrite (def_cansubst Def) /= in_addb !ke_eqE eq_refl /= negb_and negbK. *)
(*     rewrite negb_or negb_and Def /= /subst_k_env !dom_substb (def_cansubst Def). *)
(*     rewrite (def_cansubst (def_subst_nested Def)) /=. *)
(*     by rewrite !ke_eqE (negPf kik') (negPf kik)/= !kiD orbC. *)
(*   + by move=> {G}G {P}P{D}D OP IH Def; apply: t_nu_ch'; apply: IH. *)
(*   + move=> {G}G {P}P{D}D Comp OP IH. *)
(*     rewrite /subst_k_env => Def1; move: (def_subst_nested Def1)=> Def2. *)
(*     by apply: t_bang =>// ; *)
(*       [do 2 apply: completed_subst=>//|apply:IH=>//]. *)
(* Qed. *)

(* Lemma ChannelReplacement G P c c' D : *)
(*   oft G P D -> *)
(*   def (subst_env (ce c) c' D) -> *)
(*   oft G (s[ c ~> chan_of_entry c' ]p P) (subst_env (ce c) c' D). *)
(* Proof. *)
(*   case: (boolP (c' == ce c)) =>[/eqP->/=|c_neq_c']; *)
(*      first by move=> Hd Ho; rewrite subst_chan_same subst_envK. *)
(*   elim. *)
(*   + move=> L L' G0 a P0 D0 t B_a_G0 _ IH Hdef/=. *)
(*     apply: (t_request B_a_G0 *)
(*                       (L := ca_of_entry c' ++ va_dom D0 ++ c::L) *)
(*                       (L':= ka_of_entry c' ++ ch_dom D0 ++ L')) => c0 kf. *)
(*     move: (freechan_cat_c kf) => {kf}[c0c' kf]. *)
(*     move: (freechan_cat_k c0c') => {c0c'}[/freechan_entry-c0c' _]. *)
(*     move: (freechan_cat_k kf) => {kf}[_ kf]. *)
(*     move: (freechan_cat_c kf) => {kf}[c0D0 kf]. *)
(*     move: (freechan_cat_k c0D0) => {c0D0}[/freechan_dom-c0D0 _]. *)
(*     move: (freechan_cat_k kf) => {kf}[_ kf]. *)
(*     move: (freechan_neq_c kf) (freechan_cons_c kf) => c0c {kf}kf. *)
(*     move: (chanofentry_neq c0c) => ch_c0c. *)
(*     move: (def_subst_nested Hdef) => DD0. *)
(*     rewrite -subst_proc_open_var//; last by apply/lcb_chP; apply: lc_chanofentry. *)
(*     rewrite neq_add_substC //; apply: IH =>//. *)
(*     rewrite -neq_add_substC // def_addb Hdef /= dom_substb (def_cansubst Hdef)/=. *)
(*     by rewrite negb_or !negb_and c0c' c0c c0D0 /=. *)
(*   + move=> L L' G0 a P0 D0 t B_a_G0 _ IH Hdef/=. *)
(*     apply: (t_accept B_a_G0 *)
(*                       (L := ca_of_entry c' ++ va_dom D0 ++ c::L) *)
(*                       (L':= ka_of_entry c' ++ ch_dom D0 ++ L')) => c0 kf. *)
(*     move: (freechan_cat_c kf) => {kf}[c0c' kf]. *)
(*     move: (freechan_cat_k c0c') => {c0c'}[/freechan_entry-c0c' _]. *)
(*     move: (freechan_cat_k kf) => {kf}[_ kf]. *)
(*     move: (freechan_cat_c kf) => {kf}[c0D0 kf]. *)
(*     move: (freechan_cat_k c0D0) => {c0D0}[/freechan_dom-c0D0 _]. *)
(*     move: (freechan_cat_k kf) => {kf}[_ kf]. *)
(*     move: (freechan_neq_c kf) (freechan_cons_c kf) => c0c {kf}kf. *)
(*     move: (chanofentry_neq c0c) => ch_c0c. *)
(*     move: (def_subst_nested Hdef) => DD0. *)
(*     rewrite -subst_proc_open_var//; last by apply/lcb_chP; apply: lc_chanofentry. *)
(*     rewrite neq_add_substC //; apply: IH =>//. *)
(*     rewrite -neq_add_substC // def_addb Hdef /= dom_substb (def_cansubst Hdef)/=. *)
(*     by rewrite negb_or !negb_and c0c' c0c c0D0 /=. *)
(*   + move=> G0 kt e P0 D0 S T Oe Op IH Hdef. *)
(*     move: (def_addG (oft_def Op)) => def_kt_D0. *)
(*     rewrite -subst_addC /= /subst_ch; last by apply: def_kt_D0. *)
(*     rewrite chanofentry_var -fun_if; apply: t_send =>//. *)
(*     rewrite subst_addC; last by apply: def_kt_D0. *)
(*     apply: IH; move: Hdef; rewrite !def_subst_dom //. *)
(*     by rewrite !in_dom_rem // (dom_diff_eq _ _ T). *)
(*   + move=> L G0 kt P0 D0 S T Op IH Hdef. *)
(*     move: (def_addG (oft_def (Op (EV.fresh L) (EV.fresh_not_in L)))) => def_kt_D0. *)
(*     rewrite -subst_addC /= /subst_ch; last by apply: def_kt_D0. *)
(*     rewrite chanofentry_var -fun_if; apply: (t_receive (L:=L))=>//. *)
(*     rewrite subst_addC; last by apply: def_kt_D0. *)
(*     move=>x x_notin; rewrite -subst_proc_open_e. *)
(*     apply: (IH x x_notin); move: Hdef; rewrite !def_subst_dom //. *)
(*     by rewrite !in_dom_rem // (dom_diff_eq _ _ T). *)
(*   + move=> G0 k P0 D0 T T' Op IH Hdef /=. *)
(*     move: (def_addG (oft_def Op)) => def_kt_D0. *)
(*     rewrite /subst_ch chanofentry_var -fun_if -subst_addC; last by apply def_kt_D0. *)
(*     apply: t_select_l; rewrite subst_addC; last by apply def_kt_D0. *)
(*     apply: IH; move: Hdef; rewrite !def_subst_dom //. *)
(*     by rewrite !in_dom_rem // (dom_diff_eq _ _ T). *)
(*   + move=> G0 k P0 D0 T T' Op IH Hdef /=. *)
(*     move: (def_addG (oft_def Op)) => def_kt_D0. *)
(*     rewrite /subst_ch chanofentry_var -fun_if -subst_addC; last by apply def_kt_D0. *)
(*     apply: t_select_r; rewrite subst_addC; last by apply def_kt_D0. *)
(*     apply: IH; move: Hdef; rewrite !def_subst_dom //. *)
(*     by rewrite !in_dom_rem // (dom_diff_eq _ _ T) (dom_diff_eq _ _ T'). *)
(*   + move=> G0 k P0 Q D0 T T' Op IHp Oq IHq Hdef /=. *)
(*     move: (def_addG (oft_def Op)) => def_kt_D0. *)
(*     rewrite /subst_ch chanofentry_var -fun_if -subst_addC; last by apply def_kt_D0. *)
(*     apply: t_branch; (rewrite subst_addC; last by apply def_kt_D0). *)
(*     apply: IHp; move: Hdef; rewrite !def_subst_dom //. *)
(*     by rewrite !in_dom_rem // (dom_diff_eq _ _ T). *)
(*     apply: IHq; move: Hdef; rewrite !def_subst_dom //. *)
(*     by rewrite !in_dom_rem // (dom_diff_eq _ _ T'). *)
(*   + move=> G0 k k' P0 D0 T T' Op IHp Df Hdef /=. *)
(*     move: (def_addG (def_nested Df)) => Df_k'. *)
(*     move: (def_addG (oft_def Op)) => Df_k. *)
(*     rewrite !/subst_ch !chanofentry_var -!fun_if -!subst_addC //. *)
(*     apply: t_throw; last by rewrite !subst_addC. *)
(*     rewrite subst_addC //; apply: IHp. *)
(*     move: Hdef; rewrite add_swap. *)
(*     rewrite -subst_addC; last by rewrite add_swap. *)
(*     move=>/def_nested; rewrite !def_subst_dom //. *)
(*     by rewrite !in_dom_rem  // (dom_diff_eq _ _ T'). *)
(*   + move=> L L' G0 k P0 D0 T T' Op  IH Hdef /=. *)
(*     move: (def_addG (def_subst_nested Hdef)) => Dk. *)
(*     rewrite -subst_addC // /subst_ch chanofentry_var -fun_if. *)
(*     apply: (t_catch (L := ca_of_entry c' ++ va_dom D0 ++ c::L) *)
(*                     (L':= ka_of_entry c' ++ ch_dom D0 ++ L')) => c0 kf. *)
(*     move: (freechan_cat_c kf) => {kf}[c0c' kf]. *)
(*     move: (freechan_cat_k c0c') => {c0c'}[/freechan_entry-c0c' _]. *)
(*     move: (freechan_cat_k kf) => {kf}[_ kf]. *)
(*     move: (freechan_cat_c kf) => {kf}[c0D0 kf]. *)
(*     move: (freechan_cat_k c0D0) => {c0D0}[/freechan_dom-c0D0 _]. *)
(*     move: (freechan_cat_k kf) => {kf}[_ kf]. *)
(*     move: (freechan_neq_c kf) (freechan_cons_c kf) => c0c {kf}kf. *)
(*     move: (chanofentry_neq c0c) => ch_c0c. *)
(*     rewrite subst_addC // neq_add_substC //. *)
(*     rewrite -subst_proc_open_var//; last by apply/lcb_chP; apply: lc_chanofentry. *)
(*     apply: IH =>//. *)
(*     move: (Op c0 kf) => /oft_def-Df1. *)
(*     have c0k : c0 != k  by apply: (def_add_twice Df1). *)
(*     move: Hdef; rewrite !def_subst_dom //. *)
(*     rewrite !dom_add // !inE !negb_or /= !in_dom_rem // !negb_and c_neq_c' /=. *)
(*     rewrite !dom_add // !inE !negb_or /=. *)
(*     move: c0c; rewrite eq_sym=>c0c; rewrite c0c /=. *)
(*     rewrite !dom_add // !inE !negb_or /=. *)
(*     by rewrite (negPf c0c) [in c' == c0](eq_sym) c0c' /=. *)
(*   + move=> G0 e P0 Q D0 Oe O_P IHp O_Q IHq Hdef/=. *)
(*     by apply: t_ife => //; [apply: IHp|apply: IHq]. *)
(*   + move=> G0 P0 Q D1 D2 O_P IHp O_Q IHq Df1 Hdef. *)
(*     rewrite subst_union /=; apply: t_par => //; last by rewrite -subst_union. *)
(*     by move: Hdef; rewrite subst_union => /union_def-[/IHp]. *)
(*     by move: Hdef; rewrite subst_union => /union_def-[_ /IHq]. *)
(*   + move=> G0 D0 C0 Df Hdef; apply: t_inact =>//. *)
(*     move: C0; rewrite /completed => [][DD0 Bnd]; split=>// x H. *)
(*     move: Bnd; rewrite /binds=> Bnd. *)
(*     rewrite look_subst //. *)
(*     move: H=>/in_dom_subst-/orP-[/andP-[cD0 /orP-[xc'|]]|] //. *)
(*     - by rewrite xc' cD0; apply: Bnd. *)
(*     - rewrite cD0; move=>/andP[/negPf->]. *)
(*       case: D0 DD0 Bnd cD0 Hdef => // f _ ; rewrite /rem/dom => Bnd cD0 _. *)
(*       rewrite supp_rem !inE /look fnd_rem -/(look _ (Def f))=> /andP-[/negPf->]. *)
(*       by apply: Bnd. *)
(*     - by move=>/andP-[/negPf->]; apply: Bnd. *)
(*   + move=> L G0 s P0 D0 Hoft IH Hdef /=. *)
(*     by apply: (t_nu_nm (L:=L)) => x HL; rewrite -subst_proc_open_name; apply: (IH x HL). *)
(*   + move=> G0 P0 D0 T L Hoft IH Hdef /=. *)
(*     apply: (t_nu_ch (T:=T)) => ki EHL; rewrite -subst_proc_openk_var; *)
(*                                  last by apply: lc_chanofentry. *)
(*     have kic' : ki \notin ka_of_entry c' by inst_notin_cat EHL. *)
(*     have HL : ki \notin L by inst_notin EHL. *)
(*     move: (oft_def (Hoft ki HL)) => Hdef'; move: (def_nested Hdef')=>Hdef''. *)
(*     rewrite !neq_add_substC //; apply: IH => //. *)
(*     rewrite def_subst_dom //; do ! (rewrite ?dom_add ?in_dom_rem ?inE //). *)
(*     do ! (rewrite ?negb_or ?negb_and ?negbK); rewrite (negPf c_neq_c') orbC /=. *)
(*     have Heq: forall p, c' != ke (ki, p). *)
(*     - move: kic'; case c'=>//[[a b]]/=; rewrite in_cons negb_or=>/andP-[kc' _] p. *)
(*       by rewrite -[inr _ == _]/((a,b) == (ki,p)) xpair_eqE negb_and eq_sym kc'. *)
(*     move: Hdef; rewrite !Heq /= =>/(def_subst c_neq_c' (def_nested Hdef'')). *)
(*     by case: (boolP (ce c \in dom D0))=> /= [_->|_ _]//; rewrite orbC. *)
(*   + move=> G0 P0 D0 Hoft IH Hdef/=; move: (IH Hdef) => Hoft'. *)
(*     by apply: t_nu_ch'. *)

(*   + move=> G0 P0 D0 C0 Df IH Hdef ; apply: t_bang =>//. *)
(*     move: C0; rewrite /completed => [][DD0 Bnd]; split=>// x H. *)
(*     move: Bnd; rewrite /binds=> Bnd. *)
(*     rewrite look_subst //. *)
(*     move: H=>/in_dom_subst-/orP-[/andP-[cD0 /orP-[xc'|]]|] //. *)
(*     - by rewrite xc' cD0; apply: Bnd. *)
(*     - *)
(*       rewrite cD0; move=>/andP[/negPf->]. *)
(*       case: D0 Df DD0 Bnd cD0 IH Hdef => // f _ ; rewrite /rem/dom => Bnd cD0 _. *)
(*       rewrite supp_rem !inE /look fnd_rem -/(look _ (Def f))=>//. *)
(*       move=> _ _ /andP -[/negPf->] => HH. *)
(*       by rewrite cD0. *)
(*     - by move=>/andP-[/negPf->]; apply: Bnd. *)
(*     - by apply IH. *)
(* Qed. *)
