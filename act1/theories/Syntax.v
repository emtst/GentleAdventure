From mathcomp Require Import all_ssreflect seq.
Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Require Import FinMap.ordtype.

Require Import MiniEMTST.AtomScopes.


(******************************************************************************)
(**  NAMESPACES  **************************************************************)
(******************************************************************************)

Module EV := AtomScope Atom.Atom. (* Module of the atoms for expressions *)
Canonical EV_atom_eqType := EqType EV.atom EV.atom_eqMixin.
Canonical EV_atom_ordType := OrdType EV.atom EV.atom_ordMixin.
Coercion EV.Free : EV.atom >-> EV.var.
Coercion EV.Bound : nat >-> EV.var.
Canonical EV_var_eqType := EqType _ EV.var_eqMixin.
Notation evar := (EV.var).

Module CH := AtomScope Atom.Atom. (* Module of the atoms for channel name *)
Canonical CH_atom_eqType := EqType CH.atom CH.atom_eqMixin.
Canonical CH_atom_ordType := OrdType CH.atom CH.atom_ordMixin.
Coercion CH.Free : CH.atom >-> CH.var.
Coercion CH.Bound : nat >-> CH.var.
Canonical CH_var_eqType := EqType _ CH.var_eqMixin.


(* expressions and processes *)

Inductive exp : Set :=
  | tt
  | ff
  | V of evar
.

(* CoInductive just because we don't need an induction principle *)
(* CoInductive polarity := Pos | Neg. (* TODO really replace this by bool *) *)
(* Definition dual_pol p := if p is Pos then Neg else Pos. *)

(* Definition eq_polarity (p p' : polarity) : bool := *)
(*   match p, p' with *)
(*   | Pos, Pos *)
(*   | Neg, Neg => true *)
(*   | _, _ => false *)
(*   end. *)

(* Lemma polarity_reflect : Equality.axiom eq_polarity. *)
(* Proof. *)
(*     by do !case ; constructor. *)
(* Qed. *)

(* Definition polarity_eqMixin := EqMixin polarity_reflect. *)
(* Canonical polarity_eqType := EqType _ polarity_eqMixin. *)

(* (* polarities have a simple order (e.g. + < -) *) *)

(* Definition ltn_pol (p p' : polarity) : bool := *)
(*   match p, p' with *)
(*   | Pos, Neg => true *)
(*   | _, _ => false *)
(*   end. *)

(* Lemma ltn_pol_irreflexive : irreflexive ltn_pol. (* x : ltn_pol x x = false. *) *)
(* Proof. *)
(*     by case. *)
(* Qed. *)

(* Lemma ltn_pol_transitive : transitive ltn_pol. *)
(* Proof. *)
(*   by do !case. *)
(* Qed. *)

(* Lemma ltn_pol_total (a b : polarity) : [|| ltn_pol a b, a == b | ltn_pol b a]. *)
(* Proof. *)
(*   move: a b. *)
(*   case ; case => //. *)
(* Qed. *)

(* Definition polarity_ordMixin : Ordered.mixin_of polarity_eqType := *)
(*   OrdMixin *)
(*     ltn_pol_irreflexive *)
(*     ltn_pol_transitive *)
(*     ltn_pol_total. *)
(* Canonical Structure polarity_ordType := OrdType _ polarity_ordMixin. *)

Definition channel := CH.var.
(* Definition ch x p : channel := (x, p). *)

Inductive proc : Set :=
| send : channel -> exp -> proc -> proc
| receive : channel -> proc -> proc
| ife : exp -> proc -> proc -> proc
| par : proc -> proc -> proc
| inact : proc
| nu : proc -> proc (* hides the two channel polarities *)
| bang : proc -> proc (* process replication *)
.
Hint Constructors proc.

(**** locally nameless definitions ****)

(* for expressions *)

Inductive lc_exp : exp -> Prop :=
  | lc_tt : lc_exp tt
  | lc_ff : lc_exp ff
  | lc_vare a: lc_exp (V(EV.Free a))
.
Hint Constructors lc_exp.

(* free variables in things *)

Definition fv_ch (k : channel) : seq CH.atom :=
  match k with
  | CH.Free a => [::a]
  | _ => [::]
  end.

Definition fv_exp (e : exp) : seq EV.atom :=
  match e with
    | V (EV.Free a) => [::a]
    | _ => [::]
  end.

Fixpoint fv_e (P : proc) : seq EV.atom :=
  match P with
  | nu P
  | bang P
  | receive _ P => fv_e P
  | send _ e P => fv_exp e ++ fv_e P
  | ife e P Q => fv_exp e ++ fv_e P ++ fv_e Q
  | par P Q => fv_e P ++ fv_e Q
  | inact => [::]
  end.

Fixpoint fv (P : proc) : seq CH.atom :=
  match P with
  | send k e P => fv_ch k ++ fv P
  | receive k P => fv_ch k ++ fv P
  | ife e P Q => fv P ++ fv Q
  | par P Q => fv P ++ fv Q
  | inact => [::]
  | nu P => fv P
  | bang P => fv P
  end.


(* Open a bound variable in an expression *)
Definition ope (n : nat) (e' : exp) (e : exp) : exp :=
  match e with
  | V v => EV.open_var V n e' v
  | _ => e
  end.

Fixpoint open_e (n : nat) (u : exp) (P : proc) : proc :=
  match P with
  | send k e P => send k (ope n u e) (open_e n u P)
  | receive k P => receive k (open_e (S n) u P)
  | ife e P Q => ife (ope n u e) (open_e n u P) (open_e n u Q)
  | par P Q => par (open_e n u P) (open_e n u Q)
  | inact => inact
  | nu P => nu (open_e n u P)
  | bang P => bang (open_e n u P)
  end.
Notation "{ope k ~> u } t" := (open_e k u t) (at level 67) : sr_scope.

Open Scope sr_scope.
Definition open_e0 P u :={ope 0~>u} P.

(* for processes *)

Inductive lc_ch : channel -> Prop :=
| lc_channel a: lc_ch (CH.Free a).
Hint Constructors lc_ch.

Definition opk (n : nat) (u : CH.var) (k : channel) : channel :=
  CH.open_var id n u k.

Fixpoint open_k (n : nat) (ko : CH.var) (P : proc) : proc :=
  match P with
  | send k e P  => send (opk n ko k) e (open_k n ko P)
  | receive k P => receive (opk n ko k) (open_k n ko P)
  | ife e P Q => ife e (open_k n ko P) (open_k n ko Q)
  | par P Q => par (open_k n ko P) (open_k n ko Q)
  | inact => inact
  | nu P => nu (open_k (S n) ko P)
  | bang P => bang (open_k n ko P)
  end.
Notation "{opk k ~> u } t" := (open_k k u t) (at level 67) : sr_scope.

Definition open_k0 P u :={opk 0~>u} P.

(* TODO delete if not used *)
(* Definition body P := forall (L : seq EV.atom) x, x \notin L -> lc (open_c0 P (LC.Free x)). *)

Inductive lc : proc -> Prop :=
| lc_send : forall k e P,
    lc_ch k ->
    lc_exp e ->
    lc P ->
    lc (send k e P)

| lc_receive : forall (L : seq EV.atom) k P,
    lc_ch k ->
    (forall x, x \notin L -> lc (open_e0 P (V (EV.Free x)))) ->
    lc (receive k P)

| lc_ife : forall e P Q,
    lc_exp e -> lc P -> lc Q ->
    lc (ife e P Q)

| lc_par : forall P Q,
    lc P -> lc Q ->
    lc (par P Q)

| lc_inact : lc inact

| lc_nu : forall (L : seq CH.atom) P,
    (forall kp kn, kp \notin L -> kn \notin L -> kp != kn ->  lc (open_k0 (open_k0 P (CH.Free kp)) kn)) ->
    lc (nu P)

| lc_bang P: lc P -> lc (bang P)
.
Hint Constructors lc.

(**** important definitions ****)

(* structural congruence *)

Reserved Notation "P === Q" (at level 70).
Inductive congruent : proc -> proc -> Set :=
| c_refl P: P === P (* replaces alpha because LN has alpha equivalence built in *)
| c_inact P : (par inact P) === P
| c_comm P Q: (par P Q) === (par Q P)
| c_asoc P Q R: (par (par P Q) R) === (par P (par Q R))
| c_nu P Q: lc Q -> (par (nu P) Q) === (nu (par P Q))
| c_nu_inact : nu inact === inact
| c_bang P : bang P === par P (bang P)
where "P === Q" := (congruent P Q).

(* reductions *)

Reserved Notation "P --> Q" (at level 70).
Inductive red : proc -> proc -> Prop :=
| r_com (k : CH.atom) e P Q:
    lc P -> (* body Q -> *)  (* use open_e instead of ope *)
    (par (send k e P) (receive k Q)) --> (par P ({ope 0 ~> e} Q))

| r_cong P P' Q Q' :
    lc P -> lc Q ->
    P === P' ->
    P' --> Q' ->
    Q' === Q ->
    P --> Q

| r_scop P P':
    (forall (L : seq CH.atom) k,
        k \notin L -> (open_k0 P (CH.Free k)) --> (open_k0 P' (CH.Free k))) ->
    nu P --> nu P'

| r_par P P' Q:
    lc Q ->
    P --> P' ->
    par P Q --> par P' Q

| r_if_tt P Q: ife tt P Q --> P
| r_if_ff P Q: ife ff P Q -->  Q
where "P --> Q" := (red P Q).

Reserved Notation "P -->* Q" (at level 70).
Inductive red_st : proc -> proc -> Prop :=
| r_done P : P -->* P
| r_step P Q R: P --> Q -> Q -->* R -> P -->* R
where "P -->* Q" := (red_st P Q).
