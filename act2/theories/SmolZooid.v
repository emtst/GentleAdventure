(** printing nat %\ensuremath{\mathbb{N}}% #&#8469;# *)
(** printing -> %\ensuremath{\to}% #&#8594;$ *)

(* begin hide *)
Require Import mathcomp.ssreflect.all_ssreflect.
Require Import Paco.paco.
Require Import Int63.


Require Import Zooid2.ZooidTac.

Set Implicit Arguments.
Set Primitive Projections.
(* end hide *)

(** * Act II: Smol-Zooid: multiparty with shallower embedding  *)



(** ** Preliminaries

Deep embeddings lead to complex complex binder mechanisations. Can shallow
embeddings of binders help mechanising a small process language?

*)


(** ** Smol Zooid *)

(** This is a small process language *)

(* begin details: participant identifiers are natural numbers *)

Definition participant := Int63.int.

Lemma int_eqP : Equality.axiom Int63.eqb.
Proof.
  move=>x y; case: (boolP (x =? y)%int63).
  - by move=>/eqb_correct->; constructor.
  - by move=>/negP-H; constructor=>/eqb_complete/H.
Qed.

(* end details *)

(** We introduce a typing discipline for [proc], to constraint the kinds of
 traces that are allowed by the process. This typing discipline uses *local
 types* from Multiparty Session Types to categorise processes according to the
 set of traces that they accept. For this tutorial, we simplified the local
 types so they do not accept choices. **)

(** The typing system relates [proc] with [lty] so [proc] can only take a
communication type, if the specification allows it: **)

Section LocalTypes.
  Inductive ltyF G :=
  | l_end
  | l_bot
  | l_send (p : participant) T (kL : T -> G)
  | l_recv (p : participant) T (kL : T -> G)
  .

  CoInductive lty := mk_lty { run_lty : ltyF lty }.
End LocalTypes.

Arguments l_end {G}.
Arguments l_bot {G}.
Arguments l_send {G}.
Arguments l_recv {G}.
Declare Scope lty_scope.
Delimit Scope lty_scope with lty.
Bind Scope lty_scope with lty.
Notation END := (mk_lty l_end).
Notation IMPOSSIBLE := (mk_lty l_bot).
Notation "X '<-' p '!!' T ';;' k" := (mk_lty (l_send p T (fun X => k)))
        (at level 60, right associativity) : lty_scope.
Notation "X '@@' P '<-' p '!!' T ';;' K" :=
  (mk_lty
      (l_send p T (fun X =>
                     match X with
                     | P => K
                     | _ => mk_lty l_bot
                     end)))
    (at level 60, P pattern, right associativity) : lty_scope.
Notation "X '<-' p '??' T ';;' K" :=
  (mk_lty
     (l_recv p T (fun X => K)))
    (at level 60, right associativity) : lty_scope.
Notation "X '@@' P '<-' p '??' T ';;' K" :=
  (mk_lty
     (l_recv p T (fun X =>
                    match X with
                    | P => K
                    | _ => mk_lty l_bot
                    end)))
    (at level 60, P pattern, right associativity) : lty_scope.

Section Processes.
  Context (E : Type -> Type).

  Definition IS_SEND X (L : ltyF X) :=
    match L with
    | l_send _ _ _ => true
    | _ => false
    end.
  Definition IS_RECV X (L : ltyF X) :=
    match L with
    | l_recv _ _ _ => true
    | _ => false
    end.
  Definition SUBJ X (L : ltyF X) p :=
    match L with
    | l_send p' _ _ | l_recv p' _ _ => (p =? p')%int63
    | _ => false
    end.
  Definition CAN_SEND_ p X (L : ltyF X) := IS_SEND L && SUBJ L p.
  Definition CAN_RECV_ p X (L : ltyF X) := IS_RECV L && SUBJ L p.

  Definition CAN_SEND p L := CAN_SEND_ p (run_lty L).
  Definition CAN_RECV p L := CAN_RECV_ p (run_lty L).

  Definition PL_ X (L : ltyF X) : Type :=
    match L with
    | l_send _ T _ => T
    | l_recv _ T _ => T
    | _ => False
    end.
  Definition PL L := PL_ (run_lty L).

  Inductive msg L : Type -> Type :=
  | Send p (H : CAN_SEND p L) (x : PL L) : @msg L unit
  | Recv p (H : CAN_RECV p L) : @msg L (PL L)
  | Eff {T} (e : E T) : @msg L T
  .

  Definition RUN_SEND_ {p X L} : @CAN_SEND_ p X L -> PL_ L -> X :=
    match L return @CAN_SEND_ p X L -> PL_ L -> X with
    | l_send _ _ kL => fun=>kL
    | _ => fun F => match notF F with end
    end.
  Definition RUN_RECV_ {p X L} : @CAN_RECV_ p X L -> PL_ L -> X :=
    match L return @CAN_RECV_ p X L -> PL_ L -> X with
    | l_recv _ _ kL => fun=>kL
    | _ => fun F => match notF F with end
    end.
  Definition RUN_SEND {p L} : CAN_SEND p L -> PL L -> lty
    := RUN_SEND_ (L:=run_lty L).
  Definition RUN_RECV {p L} : CAN_RECV p L -> PL L -> lty
    := RUN_RECV_ (L:=run_lty L).

  Definition RUN L T (e : msg L T) : T -> lty :=
    match e with
    | Send _ H x => fun=> RUN_SEND H x
    | Recv _ H => RUN_RECV H
    | _ => fun=> L
    end.

  Definition IS_END_ X (L : ltyF X) :=
    match L with
    | l_end => true
    | _ => false
    end.
  Definition IS_END (L : lty) := IS_END_ (run_lty L).

  Inductive procF (X : lty -> Type) (L : lty) :=
  | Inact (_ : IS_END L)
  | Tau (k : X L)
  | Do {T}  (e : @msg L T) (k : forall x, X (RUN e x))
  .
End Processes.


CoInductive proc E L := mk_proc { observe : @procF E (proc E) L }.
Definition iproc E L := procF E (proc E) L.

Arguments mk_proc & [E L] observe.
Arguments Send & {E L} p H x.
Arguments Recv & {E L} p H.
Arguments Eff & {E L T} e.
Arguments Inact & {E X L}.
Arguments Tau & {E X L } k.
Arguments Do & {E X L T} e k.

(** This defines processes ([proc]) with _shallow_ embeddings of binders.
Particularly, this uses regular Coq binders and functions for expressions, and
requires building greatest fixpoints for recursion. *)

Coercion mkProc E L (x : iproc E L) := mk_proc x.

Definition pInact E L (H : IS_END L) : proc E L := mk_proc (Inact H).
Definition pTau E L (k : proc E L) : proc E L := mk_proc (Tau k).
Definition pDo E L T (e : @msg E L T) k : proc E L := mk_proc (Do e k).
Definition pSend E L p (H : CAN_SEND p L) x k : proc E L := pDo (Send p H x) k.
Definition pRecv E L p (H : CAN_RECV p L) k : proc E L := pDo (Recv p H) k.
Arguments pInact & {E L}.
Arguments pTau & {E L} k.
Arguments pDo & {E L T} e k.
Arguments pSend & {E L} p H x k.
Arguments pRecv & {E L} p H k.

Declare Scope proc_scope.
Notation stop := (pInact is_true_true).
Notation "'call' K" := (pTau K) (at level 60, no associativity).
Notation "p '<~' x ';;' k" :=
  (pSend p is_true_true x (fun=> k))
    (at level 60, right associativity) : proc_scope.
Notation "x ':' T '::=' '<~' p ';;' k" :=
  (pRecv p is_true_true (fun (x : T) => k))
    (at level 60, right associativity) : proc_scope.
Notation "x ':' T '::=' 'lift' e ';;' k" :=
  (pDo (Eff e) (fun (x : T) => k))
    (at level 60, right associativity) : proc_scope.

Section ProcExamples.
  Context (E : Type -> Type).
  Notation process := (proc E).
  Example ended_proc : process END := stop.

  (* begin hide *)
  Definition Alice := 0%int63.
  Definition Bob := 1%int63.
  (* end hide *)

  (* begin details: here we define the specifications that ALICE and BOB
  must satisfy *)

  Open Scope lty_scope.
  Example NRAlice : lty :=
    _ <- Bob !! nat ;;
    _ <- Bob ?? nat ;;
    END.

  Example NRBob : lty :=
    _ <- Alice ?? nat ;;
    _ <- Alice !! nat ;;
    END.

  Example AliceSpec : lty :=
    cofix X :=
      _ <- Bob !! nat ;;
      _ <- Bob ?? nat ;;
      X.

  Example BobSpec : lty :=
    cofix X :=
      _ <- Alice ?? nat ;;
      _ <- Alice !! nat ;;
      X.
  Close Scope lty_scope.

  Open Scope proc_scope.
  Example ping_Alice : process NRAlice :=
    Bob <~ 0;;
    _ : nat ::= <~ Bob ;;
    stop.
  Example ping_Bob : process NRBob :=
    n : nat ::= <~ Alice ;;
    Alice <~ n ;;
    stop.

  Example infinite_ping_Alice : nat -> process AliceSpec :=
    cofix pingpong x :=
      Bob <~ x;;
      _ : nat ::= <~ Bob;;
      pingpong x.+1.

  Example infinite_ping_Bob : process BobSpec :=
    cofix pingpong :=
      n : nat ::= <~ Alice;;
      Alice <~ n;;
      pingpong.

  Example infinite_ping_Bob0 : process BobSpec :=
    n : nat ::= <~ Alice;;
    cofix pingpong :=
      Alice <~ n;;
      n : nat ::= <~ Alice;;
      pingpong.
  Close Scope proc_scope.
End ProcExamples.

(** ** Semantics of Smol Zooid *)

<<<<<<< Updated upstream
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

(* Substitutes (Jump d) with e' in e; if e' contains (Jump n), additionnally shifts them by d *)
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

Example ex_p_subst: p_subst 0 (ping_Alice) (Rec (Jump 1)) = Rec ping_Alice.
auto.
Qed.

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

Example ex_p_unroll_rec: p_unroll_rec (Rec (@Send Alice Nat 0 (Jump 0))) = @Send Alice Nat 0 (Rec (@Send Alice Nat 0 (Jump 0))).
unfold p_unroll_rec.
auto.
Qed.

Definition p_unroll e :=
  run_IO_prefix (p_unroll_rec (run_IO_prefix e)).
(** end details **)


(* end hide *)

=======
>>>>>>> Stashed changes
(** *** Actions **)

(** Actions capture the kind of event that happened (send/receive), and the
necessary information about who performed the action, the other party, and the
payload type. **)


Inductive action := a_send | a_recv.
Record event :=
  mk_ev { action_type : action;
          from : participant;
          to : participant;
          payload_type : Type;
        }.
Inductive rt_event :=
  Obs { event_type : event;
        payload : payload_type event_type
      }.
Definition mk_obs a p q T x := Obs (mk_ev a p q T) x.


(* begin hide *)
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


(** *** Traces **)
(** Traces are (potentially infinite) streams of events. They are parameterised
 by the type of events. **)

Inductive traceF act G :=
| tr_end : traceF act G
| tr_next : act -> G -> traceF act G.
(* begin hide *)
Arguments tr_next & {act G}.
Arguments tr_end & {act G}.
(* end hide *)

CoInductive trace act := roll { unroll : traceF act (trace act) }.

Definition ty_trace := trace event.
Definition rt_trace := trace rt_event.

(* begin details:  *)

Definition trace_mapF {A B : Type} (f : A -> B) X Y G (trc : traceF A X)
  : traceF B Y :=
  match trc with
  | tr_end => tr_end
  | tr_next a trc => tr_next (f a) (G trc)
  end.
CoFixpoint trace_map {A B : Type} (f : A -> B) (trc : trace A) : trace B :=
  roll (trace_mapF f (trace_map f) (unroll trc)).

Definition erase := trace_map event_type.
(* end details *)


<<<<<<< Updated upstream
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

Definition event_alice: event interp_type := {| action_type := a_send; from := Bob; to := Alice; payload_type := Nat; payload := 0 |}.
Example ex_step: step infinite_ping_Alice event_alice = Some infinite_ping_Alice.
auto.
Qed.

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
=======

(** *** Labelled State Transition System **)

(** We define the steps as functions that take a process, an action, and
attepmpts to run it, returning the continuation. Since we only care about
communication, we define a function that exposes the firsst communication
action: [p_unroll]. This function requires two parameters, [readIO : forall T :
type, unit -> interp_type T] and [writeIO : forall T, T -> unit]. We will use
these functions later for code extraction. **)

Section ProcLTS.
  (** begin details: **)
  Variable (E : Type -> Type)
           (run_eff : forall T, E T -> T).
  (** end details **)

  Inductive proc_step (p : participant) L :
    iproc E L -> option rt_event -> forall L', proc E L' -> Prop
    :=
    (* Observable actions *)
    | step_send q x WT k :
        proc_step p (Do (Send q WT x) k) (Some (mk_obs a_send p q x)) (k tt)
    | step_recv q x WT k :
        proc_step p (Do (Recv q WT  ) k) (Some (mk_obs a_recv q p x)) (k x )

    (* Silent actions *)
    | step_eff T a k : proc_step p (Do (Eff a) k) None (k (@run_eff T a))
    | step_unroll e0 : proc_step p (Tau e0)       None e0
  .

  Derive Inversion proc_step_inv
    with (forall p L0 e0 ev L1 e1, @proc_step p L0 e0 ev L1 e1)
         Sort Prop.

  Definition R_trace := rt_trace -> forall L, proc E L -> Prop.
  Inductive proc_lts_ (p : participant) (G : R_trace) : R_trace :=
  | p_end TRC e H :
      unroll TRC = tr_end ->
      observe e = Inact H ->
      @proc_lts_ p G TRC END e
  | p_skip TRC L0 e0 L1 e1 :
      @proc_step p L0 (observe e0) None L1 e1 ->
      @proc_lts_ p G TRC L1 e1 ->
      @proc_lts_ p G TRC L0 e0
  | p_next E TRC0 TRC1 L0 e0 L1 e1 :
      unroll TRC0 = tr_next E TRC1 ->
      @proc_step p L0 (observe e0) (Some E) L1 e1 ->
      G TRC1 L1 e1 ->
      @proc_lts_ p G TRC0 L0 e0
  .
  Arguments p_end {p G}.
  Arguments p_skip [p G TRC L0 e0 L1 e1].
  Arguments p_next [p G E TRC0 TRC1 L0 e0 L1 e1].
  Derive Inversion proc_lts_inv
    with (forall p G TRC L e, @proc_lts_ p G TRC L e) Sort Prop.

  Lemma proc_lts_monotone p : monotone3 (proc_lts_ p).
  (* begin details: [proc_lts_] is monotone *)
  Proof.
    move=> TRC L e R R'.
    elim=>
    [ {}TRC {}e EQ H0 H1 _
    | {}TRC L0 e0 L1 e1 STEP H IH F
    | ev TRC0 TRC1 L0 e0 L1 e1 EQ STEP H F].
    - by apply/p_end.
    - by apply/(p_skip STEP)/IH.
    - by apply/(p_next EQ STEP)/F.
  Qed.
  (* end details *)

  (** [proc_accepts] encodes the property of a process accepting a trace, and it
>>>>>>> Stashed changes
 is the greatest fixpoint of [proc_lts_]. **)

  Definition proc_accepts p TR L P := paco3 (proc_lts_ p) bot3 TR L P.

  (** ** Preservation **)

<<<<<<< Updated upstream
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

Example ex_of_lty:
of_lty infinite_ping_Alice (l_rec (l_send Alice Nat (l_jump 0))).
apply lt_Rec.
apply lt_Send.
apply lt_Jump.
Qed.

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

Definition infinite_alice_by_construction :=
  z_Rec (z_Send Alice Nat 0 (z_Jump 0)).
Example ex_construction: projT1 (existT _ _ infinite_alice_by_construction) = (l_rec (l_send Alice Nat (l_jump 0))).
auto.
Qed.

(** ** Preservation **)

(** We want to make sure that types indeed characterise the traces according to
=======
  (** We want to make sure that types indeed characterise the traces according to
>>>>>>> Stashed changes
the allowed traces. We build a semantics for local types, and prove that, given
[p : SZooid L], if [p] transitions to [p'] with some event [E], then [L] also
transitions to [L'] with the "same" event. But, since processes contain payloads
and local types do not, we must first erase these payloads from the trace
events. **)

<<<<<<< Updated upstream
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
    move=> p T k L0 x OfLty.
    case: ifP=>// H.
    intro.
    exists L0.
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
=======
  Inductive lty_step p : ltyF lty -> event -> lty -> Prop :=
  | lt_send q T x kL :
      lty_step p (l_send q T kL) (mk_ev a_send p q T) (kL x)
  | lt_recv q T x kL :
      lty_step p (l_recv q T kL) (mk_ev a_recv q p T) (kL x)
  .
  Derive Inversion lty_step_inv with
      (forall p L0 Ev L1, @lty_step p L0 Ev L1) Sort Prop.

  Inductive lty_lts_ (p : participant) (G : ty_trace -> lty -> Prop)
    : ty_trace -> lty -> Prop :=
  | ty_end TRC L :
      run_lty L = l_end ->
      unroll TRC = tr_end -> @lty_lts_ p G TRC L
  | ty_next E TRC0 TRC1 L0 L1 :
      unroll TRC0 = tr_next E TRC1 ->
      @lty_step p (run_lty L0) E L1 -> G TRC1 L1 -> @lty_lts_ p G TRC0 L0
  .
  Derive Inversion lty_lts_inv with
      (forall p G TRC L, @lty_lts_ p G TRC L) Sort Prop.
  Definition lty_accepts p := paco2 (lty_lts_ p) bot2.

  Lemma lty_lts_monotone p : monotone2 (lty_lts_ p).
  Proof.
    move=>TRC L r r' H0 H1;  case: H0.
    - by move=> TRC0 U0; constructor.
    - by move=> E0 TRC0 TRC1 L0 L1 U0 ST /H1; apply (ty_next _ _ _ U0).
  Qed.

  Lemma subject_reduction p L0 (e0 : iproc E L0) L1 (e1 : proc E L1) ev :
    proc_step p e0 (Some ev) e1 -> lty_step p (run_lty L0) (event_type ev) L1.
  Proof.
    (* By case analysis on the process step *)
    move EQ: (Some ev)=> mev St; case: St EQ=>//= q.
    { (* Case send *)

      (* Unfold the constraints for sending*)
      rewrite /CAN_SEND/CAN_SEND_/RUN_SEND/PL/= => x WT _.

      (* Rewrite the event *)
      move=> [->]{ev}.

      (* Case analysis on the local type, with the constraint required by the
         process to send ([WT]) *)
      case: (run_lty L0) x WT=>//= q' T kL x /int_eqP<-{q'}.

      (* Apply the constructor for local type step*)
      by constructor.
    }
    { (* Case recv *)

      (* Unfold the constraints for receiving *)
      rewrite /CAN_RECV/CAN_RECV_/RUN_RECV/PL/= => x WT _.

      (* Rewrite the event *)
      move=>[->]{ev}.

      (* Case analysis on the local type, constrained by [WT] *)
      case: (run_lty L0) x WT=>//= q' T kL x /int_eqP<-{q'}.

      (* Apply the constructor for local type step*)
      by constructor.
    }
  Qed.

  Lemma step_silent p L0 (e0 : iproc E L0) L1 (e1 : proc E L1) :
    proc_step p e0 None e1 -> L0 = L1.
  Proof. by elim/proc_step_inv. Qed.

  Theorem trace_soundness p RT_TRC L (e : proc E L) :
    proc_accepts p RT_TRC         e ->
    @lty_accepts p (erase RT_TRC) L.
  Proof.
    (* By (parametric) coinduction (i.e. paco2_acc) *)
    coind CH=> L RT_TRC e Acc.

    (* unfold proc_accepts proc_accepts = \mu proc_lts_ ==> proc_lts_ (\mu proc_lts) *)
    move: Acc => /(paco3_unfold (@proc_lts_monotone p))-Acc.

    (* generalize Acc *)
    move EQ: (upaco3 _ _) Acc=> RR.

    (* by induction on Acc *)
    elim=>/=
        [ TRC0 e0 H0 U0 Oe
        | TRC L0 e0 L1 e1 STEP _ IH
        | E0 T0 T1 L0 e0 L1 e1 U0 St Acc {e}
        ].
    { (* Case: process trace is ended *)

      (* apply G f -> f (G f), followed by the empty trace constructor *)
      apply/paco2_fold; constructor=>//.

      (* reduce [unroll (erase TRC0)], and rewrite [unroll TRC0 = tr_end] *)
      Unset Printing Implicit.
      by cbv; rewrite U0.
    }
    { (* Case: the process takes a silent step *)

      (* Straightforward application of the IH, since
         a silent step does not progress the local type *)
      by move: STEP=>/step_silent->.
    }
    { (* Case: process trace contains one element *)

      (* By applying the constructor for the step trace, we
       then need to prove 3 properties: *)
      apply/paco2_fold/ty_next.

      { (* Property 1: the erasure of the runtime trace contains 1 element *)

        (* Straightforward: if the trace contains one element, so does the erasure *)
        by cbv; rewrite U0 -/(trace_map _ _) -/(erase _).
      }
      { (* Property 2: the local type of [e0] steps to some continuation local type *)

        (* Straightforward by subject reduction *)
        by apply: (subject_reduction St).

      }
      { (* Property 3: the continuation of the local type accepts the remainder
           of the erasure of the trace *)

        (* Straightforward by applying the coinduction hypothesis *)

        (* First rewrite [Acc] so it states that the process accepts the remainder of
           the trace*)
        move: EQ Acc=><-[Acc|//] {RR}.

        (* Then apply the coinduction hypothesis to [Acc] *)
        by right; apply/CH/Acc.
      }
    }
    Qed.
End ProcLTS.
>>>>>>> Stashed changes

(** ** Extraction **)

(** The main goal of defining a simple process language, with a mixture of deep
and shallow embedded binders is to simplify *certified code extraction*. To
extract [proc], we need an interpretation of its constructs. We do this in a way
that somewhat resembles that of _effect handlers_, by assigning to each
construct an **interpretation** as an OCaml function. **)

Require Extraction ExtrOCamlInt63.
Extraction Implicit Send [ L ].
Extraction Implicit Recv [ L ].
Extraction Implicit Eff [ L ].
Extraction Implicit Do [ L ].
Extraction Implicit Tau [ L ].
Extraction Implicit Inact [ L ].

Extraction Implicit pSend [ L ].
Extraction Implicit pRecv [ L ].
Extraction Implicit pDo [ L ].
Extraction Implicit pTau [ L ].
Extraction Implicit pInact [ L ].

Module ProcExtraction.
  Extract Inductive proc => "Proc.t" [ "" ].
  Extract Inlined Constant pSend => "(fun p t k -> let* _ = Proc.send p t in (k tt))".
  Extract Inlined Constant pRecv => "(fun p k -> let* x = Proc.recv p in k)".
End ProcExtraction.

Extraction ping_Alice.
Extraction infinite_ping_Alice.
