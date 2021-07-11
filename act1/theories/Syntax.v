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

(* expressions *)

Inductive exp : Set :=
  | tt
  | ff
  | one
  | V of evar
.

Coercion V : evar >-> exp.

(* A simple extension would be to add simple computation to
expressions. This would require adding reductions to expressions. And
proving these reductions are type preserving etc.

For example, implementing 'not' that takes a boolean and returns its
negation would be a simple computation rule.
*)

Inductive lc_exp : exp -> Prop :=
  | lc_tt : lc_exp tt
  | lc_ff : lc_exp ff
  | lc_one : lc_exp one
  | lc_var a: lc_exp (V(EV.Free a))
.
Hint Constructors lc_exp.

Definition fv_exp (e : exp) : seq EV.atom :=
  match e with
    | V (EV.Free a) => [::a]
    | _ => [::]
  end.

(* Open a bound variable in an expression (original ope) *)
Definition open_exp (n : nat) (e' : exp) (e : exp) : exp :=
  match e with
  | V v => EV.open_var V n e' v
  | _ => e
  end.

(* processes *)

Inductive proc : Set :=
| send : CH.var -> exp -> proc -> proc
| receive : CH.var -> proc -> proc
| ife : exp -> proc -> proc -> proc
| par : proc -> proc -> proc
| inact : proc
| nu : proc -> proc
| bang : proc -> proc (* process replication *)
.
Hint Constructors proc.

(**** locally nameless definitions ****)

(* free variables in things *)

(* original name fv_e *)
(* may not be really needed *)
Fixpoint fev_proc (P : proc) : seq EV.atom :=
  match P with
  | nu P
  | bang P
  | receive _ P => fev_proc P
  | send _ e P => fv_exp e ++ fev_proc P
  | ife e P Q => fv_exp e ++ fev_proc P ++ fev_proc Q
  | par P Q => fev_proc P ++ fev_proc Q
  | inact => [::]
  end.

Fixpoint fv (P : proc) : seq CH.atom :=
  match P with
  | send k e P => CH.fv k ++ fv P
  | receive k P => CH.fv k ++ fv P
  | ife e P Q => fv P ++ fv Q
  | par P Q => fv P ++ fv Q
  | inact => [::]
  | nu P => fv P
  | bang P => fv P
  end.

Fixpoint open_e (n : nat) (u : exp) (P : proc) : proc :=
  match P with
  | send k e P => send k (open_exp n u e) (open_e n u P)
  | receive k P => receive k (open_e (S n) u P)
  | ife e P Q => ife (open_exp n u e) (open_e n u P) (open_e n u Q)
  | par P Q => par (open_e n u P) (open_e n u Q)
  | inact => inact
  | nu P => nu (open_e n u P)
  | bang P => bang (open_e n u P)
  end.
Notation "{ope k ~> u } t" := (open_e k u t) (at level 67) : sr_scope.

Open Scope sr_scope.
Definition open_e0 P u :={ope 0~>u} P.
(* this effectively substitutes variable index 0 with u *)

(* for processes *)

Definition opk (n : nat) (u : CH.var) (k : CH.var) : CH.var :=
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

Inductive lc : proc -> Prop :=
| lc_send : forall k e P,
    CH.lc k ->
    lc_exp e ->
    lc P ->
    lc (send k e P)

| lc_receive : forall (L : seq EV.atom) k P,
    CH.lc k ->
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
    (forall k, k \notin L ->  lc (open_k0 P (CH.Free k))) ->
    lc (nu P)

| lc_bang P: lc P -> lc (bang P)
.
Hint Constructors lc.

(* TODO what about lines 803-1346 SyntaxR.v *)

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


(* substitutions when dealing with open terms (terms with names in them) *)

Definition subst_ch (z : CH.atom) (k' : CH.var) (k : CH.var) : CH.var :=
  if k == CH.Free z then k' else k.

Definition subst_exp (z : EV.atom) (u : exp) (e : exp) : exp :=
  match e with
  | V (EV.Free b) => if z == b then u else e
  | _ => e
  end.

Fixpoint subst_proc (z : CH.atom) (u : CH.var) (P : proc) : proc :=
  match P with
  | send k e P => send (subst_ch z u k) e (subst_proc z u P)
  | receive k P => receive (subst_ch z u k) (subst_proc z u P)
  | ife e P Q => ife e (subst_proc z u P) (subst_proc z u Q)
  | par P Q => par (subst_proc z u P) (subst_proc z u Q)
  | inact => inact
  | nu P => nu (subst_proc z u P)
  | bang P => bang (subst_proc z u P)
  end.

Fixpoint subst_proc_exp (z : EV.atom) (e : exp) (P : proc) : proc :=
  match P with
  | send k e' P => send k (subst_exp z e e') (subst_proc_exp z e P)
  | receive k P => receive k (subst_proc_exp z e P)
  | ife e' P Q => ife (subst_exp z e e') (subst_proc_exp z e P) (subst_proc_exp z e Q)
  | par P Q => par (subst_proc_exp z e P) (subst_proc_exp z e Q)
  | inact => inact
  | nu P => nu (subst_proc_exp z e P)
  | bang P => bang (subst_proc_exp z e P)
  end.

(* Notation "s[ z ~> u ]n a" := (subst_nm z u a) (at level 68) : sr_scope. *)
Notation "s[ z ~> u ]c k" := (subst_ch z u k) (at level 68) : sr_scope.
Notation "s[ z ~> u ]e e" := (subst_exp z u e) (at level 68) : sr_scope.
Notation "s[ z ~> u ]p P" := (subst_proc z u P) (at level 68) : sr_scope.
Notation "s[ z ~> e ]pe P" := (subst_proc_exp z e P) (at level 68) : sr_scope.
