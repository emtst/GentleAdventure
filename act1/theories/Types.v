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


Definition tp_env_entry := prod_ordType CH_atom_ordType polarity_ordType.
Definition tp_env := @env tp_env_entry tp_eqType.

(* channel name entry*)
Definition ke (en : CH.atom * polarity) : tp_env_entry := en.

Definition completed (D : tp_env) : Prop :=
  def D /\ forall a, a \in dom D -> binds a ended D.


Definition chan_of_entry (c : tp_env_entry) : channel :=
  match c with
  | (k, p) => ch k p
  end.


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
        oft G (open_k0 P ki) (add (ke (ki, Pos)) T (add (ke (ki, Neg)) (dual T)  D))) ->
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
