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

Definition p_unroll_rec e :=
  match e with
  | Rec e' => p_subst 0 e e'
  | e' => e'
  end.

Definition p_unroll e :=
  run_IO_prefix (p_unroll_rec (run_IO_prefix e)).
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

(** [proc_accepts] encodes the property of a process accepting a trace, and it
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

Definition z_Inact : SZooid l_end
  := exist _ _ lt_Inact.
Definition z_Jump  X : SZooid (l_jump X)
  := exist _ _ (lt_Jump X).
Definition z_Rec   L (k : SZooid L) : SZooid (l_rec L)
  := exist _ _ (lt_Rec (proj2_sig k)).

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
and local types do not, we must first erase these payloads from the trace
events. **)

Definition lt_event := event (fun=>unit).
Definition lt_trace := trace lt_event.

(* begin details: [ev_erase : rt_event -> lt_event] and [erase : rt_trace ->
lt_trace] *)
Definition ev_erase (e : rt_event) : lt_event :=
  {| action_type := action_type e;
     from := from e;
     to := to e;
     payload_type := payload_type e;
     payload := tt
  |}.
Definition erase := trace_map ev_erase.
(* end details *)

(** Next, we need to define the semantics of local types. We do this in an
analogous way to the semantics of processes. **)

(* begin hide *)
Fixpoint l_shift n d e :=
  match e with
  | l_end => l_end
  | l_jump X => if X >= d then l_jump (n + X) else e
  | l_rec e => l_rec (l_shift n d.+1 e)
  | l_recv p T k => l_recv p T (l_shift n d k)
  | l_send p T k => l_send p T (l_shift n d k)
  end.

Fixpoint l_subst d e' e :=
  match e with
  | l_end => l_end
  | l_rec e => l_rec (l_subst d.+1 e' e)
  | l_jump X => if X == d then l_shift d 0 e' else e
  | l_send p T k => l_send p T (l_subst d e' k)
  | l_recv p T k => l_recv p T (l_subst d e' k)
  end.
(* end hide *)

(* begin details: [lty_accepts : lty -> lt_trace -> Prop] *)
Definition l_unroll L :=
  match L with
  | l_rec L' => l_subst 0 L L'
  | L' => L'
  end.
Definition lstep' e (E : lt_event) :=
  match e with
  | l_send p T k =>
    if (action_type E == a_send) &&
       (to E == p) &&
       (payload_type E == T)
    then Some k else None
  | l_recv p T k =>
    if (action_type E == a_recv) &&
       (to E == p) &&
       (payload_type E == T)
    then Some k else None
  | _ => None
  end.

Definition lstep e := lstep' (l_unroll e).

Definition L_trace := lt_trace -> lty -> Prop.
Inductive lty_lts_ p (G : L_trace) : L_trace :=
  | pl_end :
      @lty_lts_ p G tr_end l_end
  | pl_next E TRC e e' :
      from E == p ->
      lstep e E = Some e' ->
      G TRC e' ->
      @lty_lts_ p G (tr_next E TRC) e.
Arguments pl_end {p G}.
Arguments pl_next [p G E TRC e e'].

Lemma lty_lts_monotone p : monotone2 (lty_lts_ p).
Proof. 
  move=> TRC e R R' [|E TRC' e' e'' SUBJ STEP H] F; first by apply: pl_end.
  by apply/(pl_next SUBJ STEP)/F.
Qed.

Definition lty_accepts p TR P := paco2 (lty_lts_ p) bot2 TR P.
(* end details *)

(** Using these definitions, we can make the final statement:**)

(* begin hide *)

Lemma runIO_preserves_type e L :
    of_lty e L -> of_lty (run_IO_prefix e) L.
Proof.
  elim=>/=.
  - by constructor.
  - by move=>X; constructor.
  - by move=> {}e {}L H _; constructor.
  - by move=> p T k {}L pl H _; constructor.
  - by move=> p T k {}L H _; constructor.
  - by move=> T k {}L _ IH; apply/IH.
  - by move=> T k {}L _ _ IH; apply/IH.
Qed.

Lemma runIO_not_Read e T k : run_IO_prefix e <> @ReadIO T k.
Proof. by elim: e =>/=. Qed.

Lemma runIO_not_Write e T x k : run_IO_prefix e <> @WriteIO T x k.
Proof. by elim: e =>/=. Qed.

Lemma shift_preserves_type n d P L :
  of_lty P L ->
  of_lty (p_shift d n P) (l_shift d n L).
Proof.
  move=> H; elim: H n=>/=; try by constructor.
  move=> X n; case: ifP; by constructor.
Qed.

Lemma subst_preserves_type e e' L L' n :
  of_lty e L -> of_lty e' L' ->
  of_lty (p_subst n e' e) (l_subst n L' L).
Proof.
  move=> H; elim: H n=>/=; try by constructor.
  - move=>X n; case: ifP=>/=; try by constructor.
    by move=> _ /(shift_preserves_type 0 n).
  - move=> k L0 _ IH m H; constructor.
    by apply/IH.
  - move=> p T k L0 pl _ IH n H; constructor.
    by apply: IH.
  - move=> p T k L0 _ IH n H; constructor => pl.
    by apply: IH.
  - move=> T k L0 _ IH n H; constructor => pl.
    by apply: IH.
  - move=> T k L0 pl _ IH n H; constructor.
    by apply: IH.
Qed.

Lemma unroll_preserves_type e L :
    of_lty e L -> of_lty (p_unroll e) (l_unroll L).
Proof.
  elim=>/=; try by constructor.
  - move=> {}e {}L H _.
    rewrite /p_unroll /=.
    apply/runIO_preserves_type/subst_preserves_type=>//.
    by constructor.
  - move=> T k L0 _ IH.
    rewrite /p_unroll/=-/(p_unroll (k _)).
    by apply: IH.
  - move=> T k L0 pl.
    by rewrite /p_unroll/=-/(p_unroll k).
Qed. 
(* end hide *)

Theorem preservation (e : proc) (L : lty)
        (H : of_lty e L) (E : rt_event) :
  forall e', step e E = Some e' ->
             exists L', lstep L (ev_erase E) = Some L' /\
                        of_lty e' L'.
Proof.
  rewrite /step/lstep.
  move: (unroll_preserves_type _ _ H)=>{}H e'.
  move: (p_unroll e) (l_unroll L) H =>{}e {}L; case=>//=.
  { (* Case Send *)
    admit.
  }
  { (* Case Recv *)
    move=> p T k L0 OfLty.
    case: ifP=>// _.
    case EQ: (check_type (payload E) T)=>[x|//] [<-]{e'}.
    exists L0; split=>//.
    by rewrite (check_type_eq (payload_type E) (payload E)) // EQ.
  }
Admitted.

(** A straightforward corollary is trace soundness **)
Corollary trace_soundness e L p :
  forall trace, proc_accepts p trace e -> lty_accepts p (erase trace) L.
Admitted.

(** ** Extraction **)

(** The main goal of defining a simple process language, with a mixture of deep
and shallow embedded binders is to simplify *certified code extraction*. To
extract [proc], we need an interpretation of its constructs. We do this in a way
that closely resembles that of _effect handlers_. **)

(** First, we define an ambient monad to run processes **)
Module Type ProcessMonad.
  Parameter t : Type -> Type.

  Parameter run : forall {A}, t A -> A.
  Parameter bind : forall {T1 T2}, t T1 -> (T1 -> t T2) -> t T2.
  Parameter pure : forall {T1}, T1 -> t T1.

  Parameter send : forall T, participant -> interp_type T -> t unit.
  Parameter recv : forall T, participant -> t (interp_type T).

  Parameter loop : forall {T1}, nat -> (unit -> t T1) -> t T1.
  Parameter set_current: nat -> t unit.
End ProcessMonad.

(** We then define a module that describes the implementation of processes,
 given an input [ProcessMonad]. **)

Module Type PROCESS (MP: ProcessMonad).
  Parameter proc : MP.t unit.
End PROCESS.

(** The process extraction module takes a [MP : ProcessMonad], and defines the
 [extract_proc] function, that recursivey traverses [proc], and produces code in
 the [MP.t] monad. This is the code that will be extracted. **)
Module ProcExtraction (MP : ProcessMonad).
  Fixpoint extract_proc (d : nat) (p : proc) : MP.t unit :=
    match p with
    | Inact         => MP.pure tt
    | Jump v        => MP.set_current (d - v.+1)
    | Rec p         => MP.loop d (fun _ => extract_proc d.+1 p)

    | Send p T x k  => MP.bind (MP.send T p x)
                               (fun=> extract_proc d k)
    | Recv p T   k  => MP.bind (MP.recv T p)
                               (fun x=> extract_proc d (k x))

    | ReadIO T k    => MP.bind (MP.pure (@readIO T tt))
                               (fun x=> extract_proc d (k x))
    | WriteIO T x k => MP.bind (MP.pure (@writeIO T x))
                               (fun=> extract_proc d k)
    end.
End ProcExtraction.

(** *** Example extraction **)
Require Import Extraction.
Require Import ExtrOcamlBasic.
Require Import ExtrOcamlNatInt.

(** We will force the evaluation of [extract_proc], to generate more readable
 OCaml code. Due to this, any function that is used in local computations needs
 to be declared [Opaque], to make sure it is not unfolded. **)
Opaque eqn.
Opaque addn.
Opaque muln.
Opaque maxn.

About Alice_by_construction.

Let alice := projT1 (projT2 (Alice_by_construction)).
Module  ALICE (MP : ProcessMonad) : PROCESS(MP).
  Module PE := ProcExtraction(MP).
  Definition proc := Eval compute in PE.extract_proc 0 alice.
End ALICE.

Extraction ALICE.

(** This will extract the following OCaml code:
[module ALICE =
 functor (MP:ProcessMonad) ->
 struct
  module PM = MP

  (** val proc : unit MP.t **)

  let proc =
    MP.loop 0 (fun _ ->
      MP.bind (MP.pure (readIO Nat ())) (fun x ->
        MP.bind (MP.send Nat (Pervasives.succ 0) x) (fun _ -> MP.set_current 0)))
 end]
**)
