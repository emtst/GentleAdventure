(** printing nat %\ensuremath{\mathbb{N}}% #&#8469;# *)
(** printing -> %\ensuremath{\to}% #&#8594;$ *)


(* begin hide *)
Require Import mathcomp.ssreflect.all_ssreflect.
Require Import Paco.paco.
(* end hide *)

(** * Act II: Smol-Zooid: multiparty with shallower embedding  *)



(** ** Preliminaries

Deep embeddings lead to complex complex binder mechanisations. Can shallow
embeddings of binders help mechanising a small process language?

*)


(** ** Smol Zooid *)

(** This is a small process language *)

(* begin details: we assume a datatype representing payload types, [type], and a
function [interp_type : type -> Type] that interprets such types as Coq
types. *)

Definition participant := nat.
Inductive type := Nat | Bool.
Definition interp_type t :=
  match t with
  | Nat => nat
  | Bool => bool
  end.

Definition eq_type a1 a2 :=
  match a1, a2 with
  | Nat, Nat => true
  | Bool, Bool => true
  | _, _ => false
  end.

Lemma type_eqP : Equality.axiom eq_type.
Proof. by rewrite /Equality.axiom => [[] []/=]; constructor. Qed.

Definition type_eqMixin := EqMixin type_eqP.
Canonical type_eqType := Eval hnf in EqType type type_eqMixin.

Definition eq_val {T} : interp_type T -> interp_type T -> bool :=
  match T with
  | Nat => fun x y => x == y
  | Bool =>  fun x y => x == y
  end.

Lemma payload_eqP T : Equality.axiom (@eq_val T).
Proof. by  case: T; rewrite /Equality.axiom => x y; apply: eqP. Qed.

Definition payload_eqMixin T := EqMixin (payload_eqP T).
Canonical payload_eqType T := Eval hnf in EqType (interp_type T) (payload_eqMixin T).

Definition check_type {T1 : type} (x : interp_type T1) (T2 : type)
  : option (interp_type T2)
  := match T1, T2 with
     | Nat, Nat => fun x => Some x
     | Bool, Bool => fun x => Some x
     | _, _ => fun _ => None
     end x.

Lemma check_type_eq T x T' : @check_type T x T' -> T == T'.
Proof. by case: T x; case: T'. Qed.

Definition eq_payload {T1 : type} (x : interp_type T1) {T2 : type} (y : interp_type T2)
  : bool
  := match check_type x T2 with
     | Some x => x == y
     | None => false
     end.

Lemma eq_payload_eq T x T' y : @eq_payload T x T' y -> T == T'.
Proof. by case: T x; case: T' y. Qed.

(* end details *)

Inductive proc :=
| Inact
| Rec (e : proc)
| Jump (X : nat)
| Send (p : participant) {T : type} (x : interp_type T) (k : proc)
| Recv (p : participant) {T : type} (k : interp_type T -> proc)

| ReadIO {T : type} (k : interp_type T -> proc)
| WriteIO {T : type} (x : interp_type T) (k : proc)
.

(** This defines processes ([proc]), mixing _shallow_ and _deep_ embeddings of
binders. Particularly, this uses DeBruijn indices for recursion variables, and
regular Coq binders and functions for expressions. *)

Example ended_proc := Inact.

(* begin hide *)

Definition Alice := 0.
Definition Bob := 1.
Definition Ping := interp_type Nat.

(* end hide *)

Example ping_Alice := @Send Alice Nat 0 Inact.
Example ping_Bob := Recv Bob (fun x : Ping => Send Bob x Inact).

Example infinite_ping_Alice :=
  Rec (@Send Alice Nat 0 (Jump 0)).
Example infinite_ping_Bob :=
  Rec (Recv Bob (fun x : Ping => Send Bob x (Jump 0))).

(** ** Semantics of Smol Zooid *)

(* begin details : We define a number of functions to unroll recursive processes
[p_shift : nat -> nat -> proc], [p_subst : nat -> proc -> proc] and [p_unroll :
proc -> proc]*)

Fixpoint p_shift n d e :=
  match e with
  | Inact => Inact
  | Jump X => if X >= d then Jump (n + X) else e
  | Rec e => Rec (p_shift n d.+1 e)
  | Recv p T k => Recv p (fun x => p_shift n d (k x))
  | Send p T x k => Send p x (p_shift n d k)

  | ReadIO T k => ReadIO (fun x => p_shift n d (k x))
  | WriteIO T x k => WriteIO x (p_shift n d k)
  end.

Fixpoint p_subst d e' e :=
  match e with
  | Inact => Inact
  | Rec e => Rec (p_subst d.+1 e' e)
  | Jump X => if X == d then p_shift d 0 e' else e
  | Send p T x k => Send p x (p_subst d e' k)
  | Recv p T k => Recv p (fun x => p_subst d e' (k x))
  | ReadIO T k => ReadIO (fun x => p_subst d e' (k x))
  | WriteIO T x k => WriteIO x (p_subst d e' k)
  end.

(* end hide *)

(** *** Actions **)

(** Actions capture the kind of event that happened (send/receive), and the
necessary information about who performed the action, the other party, the
payload type, and (possibly) what was the payload. The record for events is
parameterised by a function [interp_payload : type -> Type], which can be set to
[fun=>unit] if we are not interested in keeping payloads in the trace.**)

Inductive action := a_send | a_recv.
Record event interp_payload :=
  { action_type : action;
    from : participant;
    to : participant;
    payload_type : type;
    payload : interp_payload payload_type
  }.

(* begin hide *)
Arguments action_type {interp_payload} _.
Arguments from {interp_payload} _.
Arguments to {interp_payload} _.
Arguments payload_type {interp_payload} _.
Arguments payload {interp_payload} _.

Definition eq_action a1 a2 :=
  match a1, a2 with
  | a_send, a_send => true
  | a_recv, a_recv => true
  | _, _ => false
  end.

Lemma action_eqP : Equality.axiom eq_action.
Proof. by rewrite /Equality.axiom => [[] []/=]; constructor. Qed.

Definition action_eqMixin := EqMixin action_eqP.
Canonical action_eqType := Eval hnf in EqType action action_eqMixin.
(* end hide *)

Definition rt_event := event interp_type.

(** *** Traces **)
(** Traces are (potentially infinite) streams of events. They are parameterised
 by the type of events. **)

CoInductive trace (act : Type) :=
| tr_end : trace act
| tr_next : act -> trace act -> trace act.

Definition rt_trace := trace rt_event.

(* begin hide *)
Arguments tr_next {act}.
Arguments tr_end {act}.
(* end hide *)

(* begin details: we can map functions on traces [trace_map {A B : Type} (f : A ->
B) (trc : trace A) : trace B] *)
CoFixpoint trace_map {A B : Type} (f : A -> B) (trc : trace A) : trace B :=
  match trc with
  | tr_end => tr_end
  | tr_next a trc => tr_next (f a) (trace_map f trc)
  end
.
(* end details *)

(** *** Labelled State Transition System **)

(** We define the steps as functions that take a process, an action, and
attepmpts to run it, returning the continuation. Since we only care about
communication, we define a function that exposes the firsst communication
action: [p_unroll]. This function requires two parameters, [readIO : forall T :
type, unit -> interp_type T] and [writeIO : forall T, T -> unit]. We will use
these functions later for code extraction. **)

(** begin details: **)
Variable readIO : forall {T}, unit -> interp_type T.
Variable writeIO : forall {T}, interp_type T -> unit.

Fixpoint run_IO_prefix e :=
  match e with
  | ReadIO T k => run_IO_prefix (k (readIO tt))
  | WriteIO T x k => run_IO_prefix k
  | _ => e
  end.

Definition p_unroll e :=
  match run_IO_prefix e with
  | Rec e' => run_IO_prefix (p_subst 0 e e')
  | e' => e'
  end.
(** end details **)

(** Function [step : proc -> rt_event -> option proc] takes a process [e :
proc], an event [E : rt_event], and checks whether [e] can run event [E], and
performs a step if possible. The definition relies on an auxiliary function
[step'] that assumes that the process has been previously unrolled. **)

Definition step' e E :=
  match e with
  | Send p T x k =>
    if (action_type E == a_send) &&
       (to E == p) &&
       (eq_payload (payload E) x)
    then Some k else None
  | Recv p T k =>
    if (action_type E == a_recv) &&
       (to E == p)
    then match check_type (payload E) T with
         | Some pl => Some (k pl)
         | None => None
         end
    else None
  | _ => None
  end.

Definition step e := step' (p_unroll e).

Definition R_trace := rt_trace -> proc -> Prop.
Inductive proc_lts_ p (G : R_trace) : R_trace :=
  | p_end :
      @proc_lts_ p G tr_end Inact
  | p_next E TRC e e' :
      from E == p ->
      step e E = Some e' ->
      G TRC e' ->
      @proc_lts_ p G (tr_next E TRC) e.
Arguments p_end {p G}.
Arguments p_next [p G E TRC e e'].

Lemma proc_lts_monotone p : monotone2 (proc_lts_ p).
(* begin details: [proc_lts_] is monotone *)
Proof. 
  move=> TRC e R R' [|E TRC' e' e'' SUBJ STEP H] F; first by apply: p_end.
  by apply/(p_next SUBJ STEP)/F.
Qed.
(* end details *)

(** [proc_acceots] encodes the property of a process accepting a trace, and it
 is the greatest fixpoint of [proc_lts_]. **)

Definition proc_accepts p TR P := paco2 (proc_lts_ p) bot2 TR P.

(** ** Types **)

(** We introduce a typing discipline for [proc], to constraint the kinds of
 traces that are allowed by the process. This typing discipline uses *local
 types* from Multiparty Session Types to categorise processes according to the
 set of traces that they accept. For this tutorial, we simplified the local
 types so they do not accept choices. **)

Inductive lty :=
  | l_end
  | l_jump (X : nat)
  | l_rec (k : lty)
  | l_send (p : participant) (T : type) (l : lty)
  | l_recv (p : participant) (T : type) (l : lty)
.

(** The typing system relates [proc] with [lty] in a purely syntactic way: **)

Inductive of_lty : proc -> lty -> Prop :=
| lt_Inact             :                               of_lty Inact            l_end
| lt_Jump    X         :                               of_lty (Jump X)         (l_jump X)
| lt_Rec     k L       : of_lty k L                 -> of_lty (Rec k)          (l_rec L)

| lt_Send    p T k L x : of_lty k L                 -> of_lty (@Send p T x k)  (l_send p T L)
| lt_Recv    p T k L   : (forall x, of_lty (k x) L) -> of_lty (@Recv p T k)    (l_recv p T L)

| lt_ReadIO  T k L     : (forall x, of_lty (k x) L) -> of_lty (@ReadIO T k)    L
| lt_WriteIO T k L x   : of_lty k L                 -> of_lty (@WriteIO T x k) L
.

(* begin hide *)
Arguments lt_Rec [k L].
Arguments lt_Send p [T k L] x.
Arguments lt_Recv p [T k L].
Arguments lt_ReadIO [T k L].
Arguments lt_WriteIO [T k L] x.
(* end hide *)


(** With this relation, it is possible to give specifications, and make sure
that communication only happens according to these. For example: **)

Example pingpong_Alice :=
  Rec (@ReadIO Nat (fun x => Send Bob x (Jump 0))).

Example AliceLT : lty :=
  l_rec (l_send Bob Nat (l_jump 0)).

Example Alice_WellTyped : of_lty pingpong_Alice AliceLT.
Proof.
  apply: lt_Rec.
  apply: lt_ReadIO=>/=x.
  apply: lt_Send.
  apply: lt_Jump.
Qed.

(** Writing well-typed processes in this way is tedious, and requires users to
define:
1. A local type specification;
2. A process implementation;
3. A proof that the process indeed behaves according to the specification

Instead, we define a number of _smart constructors_ that build well-typed terms
_by construction.
**)

Definition SZooid L := { p | of_lty p L}.

Definition z_Inact                  : SZooid l_end      := exist _ _ lt_Inact.
Definition z_Jump  X                : SZooid (l_jump X) := exist _ _ (lt_Jump X).
Definition z_Rec   L (k : SZooid L) : SZooid (l_rec L)  := exist _ _ (lt_Rec (proj2_sig k)).

Definition z_Send  p T x L (k : SZooid L) : SZooid (l_send p T L)
  := exist _ _ (lt_Send p x (proj2_sig k)).
Definition z_Recv p T L (k : interp_type T -> SZooid L) :  SZooid (l_recv p T L)
  := exist _ _ (lt_Recv p (fun x => proj2_sig (k x))).

Definition z_ReadIO T L (k : interp_type T -> SZooid L) : SZooid L
  := exist _ _ (lt_ReadIO (fun x => proj2_sig (k x))).
Definition z_WriteIO T L x  (k :  SZooid L) : SZooid L
  := exist _ _ (@lt_WriteIO T _ _ x (proj2_sig k)).

(* begin hide *)
Arguments z_Rec [L].
Arguments z_Send p T x [L] k.
Arguments z_Recv p T [L] k.
Arguments z_ReadIO T [L] k.
Arguments z_WriteIO T [L] x k.
(* end hide *)

(** Note that the local type of the [SZooid] terms is *fully determined* by the
inputs. Therefore, it is not required to write both the local type and the term,
but we can _infer_ it: **)

Definition AZooid := { L & SZooid L }.

Example Alice_by_construction : AZooid :=
  existT _ _ (
           z_Rec (z_ReadIO Nat (fun x => z_Send Bob Nat x (z_Jump 0)))
         ).

Goal projT1 Alice_by_construction = AliceLT.
    by reflexivity.
Qed.

(** ** Preservation **)

(** We want to make sure that types indeed characterise the traces according to
the allowed traces. We build a semantics for local types, and prove that, given
[p : SZooid L], if [p] transitions to [p'] with some event [E], then [L] also
transitions to [L'] with the "same" event. But, since processes contain payloads
and local types do not, we must first rease these payloads from the trace
events. **)

Definition lt_event := event (fun=>unit).

(* begin details: [erase : rt_event -> lt_event] *)
Definition erase (e : rt_event) : lt_event :=
  {| action_type := action_type e;
     from := from e;
     to := to e;
     payload_type := payload_type e;
     payload := tt
  |}.
(* end details *)

(** We want to make sure that types indeed characterise the traces according to
the allowed traces. We build a semantics for local types, and prove that, given
[p : SZooid L], if [p] transitions to [p'] with some event [E], then [L] also
transitions to [L'] with the "same" event. But, since processes contain payloads
and local types do not, we must first rease these payloads from the trace
events. **)


(** ** Extraction **)
