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


Derive Inversion oft_inv with (forall G P D, oft G P D) Sort Prop.
Derive Inversion oft_inv_par with (forall G P Q D, oft G (par P Q) D) Sort Prop.

Lemma oft_par_inv G P Q D :
  oft G (par P Q) D -> exists D1 D2,
    compatible D1 D2 /\ (* def (D1 o D2) /\ *) (D1 o D2 = D) /\ oft G P D1 /\ oft G Q D2.
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
Admitted.

Lemma oft_def G P D:
  oft G P D -> def D.
Proof.
Admitted.


Lemma oft_def_ctx G P D:
  oft G P D -> def G.
Proof.
Admitted.

Lemma oft_exp_def_ctx G E S:
  oft_exp G E S -> def G.
Proof.
  elim ; try by [].
  move=> x S'.
  by apply: binds_def.
Qed.

(* Meta-theory *)

Lemma subst_ch_same c c' : s[ c ~> c ]c c' = c'.
Proof.
  by case: c'=>// ; rewrite /subst_ch=> a ; case: ifP =>// /eqP->.
Qed.

Lemma subst_chan_same c P : s[c ~> c]p P = P.
Admitted.

Lemma subst_exp_proc_open_exp x y e P:
  x != y ->
  lc_exp e ->
  (s[ x ~> e ]pe open_e0 P y) = (open_e0 (s[ x ~> e ]pe P) y).
Proof.
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
Admitted.


Lemma subst_chan_openk_var x u n k ch :
  CH.lc u -> s[ x ~> u ]c opk n k ch = opk n k (s[ x ~> u ]c ch).
Proof.
Admitted.

Lemma subst_proc_openk_var x k u P:
  (* x != y -> *) CH.lc u ->
  (s[ x ~> u ]p open_k0 P k) = (open_k0 (s[ x ~> u ]p P) k).
Admitted.

Lemma subst_exp_openk_var x k e P:
  (* x != y -> *) lc_exp e ->
  (s[ x ~> e ]pe open_k0 P k) = (open_k0 (s[ x ~> e ]pe P) k).
Admitted.

Lemma subst_proc_open_e x k u P:
  (s[ x ~> u ]p open_e0 P k) = (open_e0 (s[ x ~> u ]p P) k).
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


Lemma wkn_ctx_oft G P D y S:
  oft G P D -> def (add y S G) -> oft (add y S G) P D.
Proof.
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
Proof.
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
Proof.
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


(*************************************************************)

Definition subst_k_env k k' (D : tp_env) := subst_env k k' D. (* TODO remove the _env *)

Definition subst_entryk k k' (x : tp_env_entry) := if x == k then k' else x.

Ltac simpl_def :=
  do ! match goal with
       | [ |- context[?k == ?k] ] => rewrite !eq_refl
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
