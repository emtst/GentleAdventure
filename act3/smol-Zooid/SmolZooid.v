From mathcomp.ssreflect Require Import all_ssreflect seq.
From mathcomp Require Import finmap.

From Paco Require Import paco paco2.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Require Import Common.

Section GlobalSyntax.
  Unset Elimination Schemes.
  (**
   * Global Types
   *)
  Inductive g_ty :=
  | g_end
  | g_var (VAR : nat)
  | g_rec (GT : g_ty)
  | g_msg (FROM TO : role) (CONT : (mty * g_ty)).
  Set Elimination Schemes.

  Lemma g_ty_ind :
    forall (P : g_ty -> Prop),
      P g_end ->
      (forall v, P (g_var v)) ->
      (forall G, P G -> P (g_rec G)) ->
      (forall p q K, P K.2 ->
                     P (g_msg p q K)) ->
      forall g : g_ty, P g.
  Proof.
    move=> P P_end P_var P_rec P_msg; fix Ih 1; case.
    + by apply: P_end.
    + by apply: P_var.
    + by move=>G; apply: P_rec.
    + by move=>p q Ks; apply: P_msg.
  Qed.

  Fixpoint depth (a : g_ty) :=
    match a with
    | g_end
    | g_var _ => 0
    | g_rec G => (depth G).+1
    | g_msg _ _ K => (depth K.2).+1
    end.

  Fixpoint participants (G : g_ty) :=
    match G with
    | g_end
    | g_var _ => [::]
    | g_rec G => participants G
    | g_msg p q K => p::q::(participants K.2)
    end.

  Fixpoint eq_g_ty (a b : g_ty) :=
    match a, b with
    | g_end, g_end => true
    | g_var v1, g_var v2 => v1 == v2
    | g_rec G1, g_rec G2 => eq_g_ty G1 G2
    | g_msg p1 q1 K1, g_msg p2 q2 K2 =>
      (p1 == p2) && (q1 == q2)
      && (K1.1 == K2.1) && eq_g_ty K1.2 K2.2
    | _, _ => false
    end.

  Definition eq_cont (l r : (mty * g_ty)) :=
    (l.1 == r.1) && eq_g_ty l.2 r.2.

  Lemma eqgty_msg p1 q1 (K1 : mty * g_ty) p2 q2 K2 :
    eq_g_ty (g_msg p1 q1 K1) (g_msg p2 q2 K2) =
    (p1 == p2) && (q1 == q2) && eq_cont K1 K2.
  Proof.
    rewrite /=; do 2 (case: eqP=>///= _).
  Qed.
  (*Hint Rewrite eqgty_all : mpst.*)

  Lemma g_ty_eqP : Equality.axiom eq_g_ty.
  Proof.
    rewrite /Equality.axiom; fix Ih 1 => x y.
    case x =>[|vl| Gl |pl ql Kl]; case y =>[|vr| Gr |pr qr Kr];
                                             try (by constructor).
    + by rewrite /eq_g_ty; case: eqP=>[->|H];constructor=>//[[]].
    + by rewrite /=; case: Ih=>[->|H];constructor=>//[[]].
    + rewrite eqgty_msg; do 2 (case: eqP=>[<-|H];[|constructor=>[[]]//] =>/=).
      case: Kl=>tl Gl; case: Kr=> tr Gr.
      rewrite /eq_cont//=; case: eqP=>//=[<-|F]; [|by constructor=>[[/F]]].
        by case Ih=>[<-|F]; constructor=>//=[[/F]].
  Qed.

  Definition g_ty_eqMixin := EqMixin g_ty_eqP.
  Canonical g_ty_eqType := Eval hnf in EqType g_ty g_ty_eqMixin.

  Lemma alt_eqP : Equality.axiom eq_cont.
  Proof.
    rewrite /Equality.axiom/eq_cont; move=>[t1 K1] [t2 Ks2]/=.
    (case: eqP=>[<-|H]; last (by apply: ReflectF => [[/H]])).
    case: g_ty_eqP=>[<-|H]; first by apply: ReflectT.
      by apply: ReflectF =>[[/H]].
  Qed.

  Lemma rec_gty G :
    (exists G', G = g_rec G') \/ (forall G', G != g_rec G').
  Proof. by case:G; try (by right); move=> GT; left; exists GT. Qed.

  Lemma matchGrec A G (f : g_ty -> A) g :
    (forall G', G != g_rec G') ->
    match G with
    | g_rec G' => f G'
    | _ => g
    end = g.
  Proof. by case: G=>// GT /(_ GT)/eqP. Qed.

  (**
   * Does not apply any "shift" to G2, and therefore G2 must always be closed
   *)
  Fixpoint g_open (d : nat) (G2 : g_ty) (G1 : g_ty) :=
    match G1 with
    | g_end => G1
    | g_var v => if v == d then G2 else G1
    | g_rec G => g_rec (g_open d.+1 G2 G)
    | g_msg p q K =>
      g_msg p q (K.1, g_open d G2 K.2)
  end.
  Notation "{ k '~>' v } G":= (g_open k v G) (at level 30, right associativity).
  Notation "G '^' v":= (g_open 0 (g_var v) G) (at level 30, right associativity).

  Definition unroll G := g_open 0 (g_rec G) G.

  Lemma g_open_msg_rw d G2 FROM TO CONT:
  g_open d G2 (g_msg FROM TO CONT)
  = g_msg FROM TO (CONT.1, g_open d G2 CONT.2).
  Proof. by []. Qed.

  Lemma notin_part_g_open_strong d r G G':
    r \notin participants G ->
    r \notin participants G'->
    r \notin participants (g_open d G' G).
  Proof.
    move=> h1 rnG'; move: h1; apply: contra; elim: G d.
    + rewrite //=.
    + rewrite //= => v d.
        by case: ifP=>[_ F|//]; rewrite F in rnG'.
    + rewrite //=. by move=> G ih d; apply ih.
    + move=>p q K ih d; rewrite /= !in_cons.
      move=>/orP-[->//|/orP-[->|]]; first by rewrite orbC.
        by move=> H; do ! (apply/orP; right); apply (ih _ H).
  Qed.

  Lemma same_notin_part_g_open d r G G':
    participants G' = participants G ->
    r \notin participants G ->
    r \notin participants (g_open d G' G).
  Proof.
    move=>h1 h2; apply: notin_part_g_open_strong; by [apply h2 | rewrite h1].
  Qed.

  Lemma notin_part_g_open r G:
    r \notin participants G -> r \notin participants (g_open 0 (g_rec G) G).
  Proof.
      by apply same_notin_part_g_open.
  Qed.

  (*Fixpoint g_fidx (d : nat) (G : g_ty) : seq nat :=
    match G with
    | g_var v => if v >= d then [:: v - d] else [::]
    | g_rec G => g_fidx d.+1 G
    | g_msg p q Ks => flatten [seq g_fidx d K.2.2 | K <- Ks]
    | g_end => [::]
    end.*)
  Fixpoint g_fidx (d : nat) (G : g_ty) : bool :=
    match G with
    | g_var v => if v >= d then false else true
    | g_rec G => g_fidx d.+1 G
    | g_msg p q K => g_fidx d K.2
    | g_end => true
    end.

  Definition g_closed (G : g_ty) := g_fidx 0 G.

  Lemma gfbvar_next n G :
    g_fidx n G -> g_fidx n.+1 G.
  Proof.
    elim: G n=>[//|v|G Ih|p q K Ih] n/=; try by apply Ih.
      by case: ifP=>//=; case: ifP=>//= nv; rewrite (ltnW nv).
  Qed.

  Fixpoint guarded d G :=
    match G with
    | g_end => true
    | g_var v => v >= d
    | g_rec G => guarded d.+1 G
    | g_msg _ _ K => guarded 0 K.2
    end.

  Fixpoint g_binds n G :=
    match G with
    | g_var v => v == n
    | g_rec G => g_binds n.+1 G
    | _ => false
    end.

  Fixpoint guarded' G :=
    match G with
    | g_end
    | g_var _ => true
    | g_rec G => ~~ g_binds 0 G && guarded' G
    | g_msg _ _ K => guarded' K.2
    end.

  Lemma guarded_next n G : guarded n.+1 G = ~~ g_binds n G && guarded n G.
  Proof. by elim: G n=>//= v n; rewrite ltn_neqAle eq_sym. Qed.

  Lemma guarded_binds G : guarded 0 G = guarded' G.
  Proof.
      by elim: G=>[||G|_ _ K Ih]//=; move=><-;apply/guarded_next.
  Qed.

  Lemma alt_eq p1 q1 K1 p2 q2 K2 :
    ((g_msg p1 q1 K1) == (g_msg p2 q2 K2)) =
    (p1 == p2) && (q1 == q2) && (K1 == K2).
  Proof.
      by rewrite eqE/=; do 2 case: eqP=>//=.
  Qed.

  Lemma gty_not_var A G (f : nat -> A) (k : A) :
    (forall v : nat, G != g_var v) ->
    match G with | g_var v => f v | _ => k end = k.
  Proof. by case: G =>// v /(_ v)/eqP. Qed.

  Fixpoint rec_depth G :=
    match G with
    | g_rec G => (rec_depth G).+1
    | _ => 0
    end.

  Lemma rd_zero G :
    (forall G' : g_ty, G != g_rec G') ->
    rec_depth G = 0.
  Proof. by case: G=>// GT /(_ GT)/eqP. Qed.


  Fixpoint n_unroll d G :=
    match d with
    | 0 => G
    | d.+1 =>
      match G with
      | g_rec G' => n_unroll d (unroll G')
      | _ => G
      end
    end.

  Lemma r_in_unroll r G n:
    r \in participants (n_unroll n G) -> r \in participants G.
  Proof.
    apply: contraLR.
    elim: n => [rewrite //= | n ih] in G *; case G; rewrite //=.
    move=> G0 notinpart; apply ih.
    unfold unroll; apply notin_part_g_open; by [].
  Qed.

  Lemma r_in_unroll_rec_depth r G:
    r \in participants (n_unroll (rec_depth G) G) -> r \in participants G.
  Proof. by apply r_in_unroll. Qed.

  Lemma notin_nunroll r n G :
    r \notin participants G ->
    r \notin participants (n_unroll n G).
  Proof.
    elim: n G=>//= n Ih G H.
    by case: G H=>//= GT; rewrite /unroll=>/notin_part_g_open/Ih.
  Qed.

  Lemma guarded_match d G :
    match G with
    | g_var v => d < v
    | _ => guarded d.+1 G
    end ->
    (exists v, (G == g_var v) && (d < v)) \/
    (forall v, (G != g_var v)) /\ guarded d.+1 G.
  Proof.
    case: G=>[|[]||]//=; try by right.
      by move=> n d_n; left; exists n.+1; rewrite eq_refl.
  Qed.

  Lemma guarded_recdepth d G m :
    guarded d G ->
    m < d ->
    forall G', rec_depth G = rec_depth ({m ~> G'} G).
  Proof.
    elim: G=>[|n|G Ih|p q Ks Ih]//= in d m *.
    - move=>dn md G; case: ifP=>[/eqP-E|ne//].
        by move: E dn md=>-> /leq_ltn_trans-H /H; rewrite ltnn.
    - by move=> GG md G'; rewrite (Ih _ m.+1 GG _ G').
  Qed.

  Lemma guarded_depth_gt n dG dG' G :
    n <= dG' ->
    guarded dG' G -> g_fidx n G -> guarded dG G.
  Proof.
    elim: G =>[|m|G Ih|p q Ks Ih]// in n dG dG' *.
    - by move=> /leq_trans-H /= /H->.
    - by move=>/= LE; apply/Ih.
  Qed.

  Lemma gopen_closed G :
    g_closed (g_rec G) ->
    g_closed (g_open 0 (g_rec G) G).
  Proof.
    rewrite/g_closed/==>G_fbv; have: g_fidx 0 (g_rec G) by [].
    move: (g_rec G) => G' G'0.
    elim: G 0 G'0 G_fbv=>[//|v|G Ih|p q K Ih] n G'0/=.
    - rewrite ltn_neqAle; case: ifP=>//=; case: ifP=>//=; case: ifP=>//=.
        by move=> nv vnf; rewrite eq_sym vnf.
    - by apply Ih; apply gfbvar_next.
    - by apply Ih.
  Qed.

  Lemma closed_not_var G :
    g_closed G ->
    forall v, G != g_var v.
  Proof. by case: G. Qed.

  Lemma open_not_var d G G' :
  g_closed G ->
  (forall v, G' != g_var v) ->
  forall v, {d ~> G} G' != g_var v.
  Proof. by case: G'=>// n _ /(_ n)/eqP. Qed.

  Lemma guarded_open d1 d2 G G' :
    guarded 0 G' ->
    g_closed G' ->
    guarded d1 G ->
    guarded d1 ({d2 ~> G'} G).
  Proof.
    elim: G=>[|n|G Ih|p q K Ih]//= in d1 d2 *; try by apply Ih.
      by case: ifP=>// _ /(guarded_depth_gt d1 (leq0n 0))-H /H-{H}H.
  Qed.

  Lemma guarded_gt d d' G :
    d >= d' ->
    guarded d G ->
    guarded d' G.
  Proof.
    elim: G=>[|n|G Ih|p q K Ih]//= in d d' *.
    - by move=>/leq_trans-H /H.
    - by move=> H; apply/Ih.
  Qed.

  Lemma unroll_guarded G :
    g_closed G ->
    guarded 0 G ->
    forall G', n_unroll (rec_depth G) G != g_rec G'.
  Proof.
    move: {-2}(rec_depth G) (eq_refl (rec_depth G)) => n.
    elim: n => [|n Ih]/= in G *; case: G=>// G n_rd CG GG; move: n_rd.
    rewrite eqE/=-eqE => n_rd.
    have/=GG': (guarded 0 (g_rec G)) by [].
    move: n_rd; rewrite (guarded_recdepth GG' (ltn0Sn 0) (g_rec G))=>n_rd.
    apply/Ih=>//; first by apply/gopen_closed.
      by apply/guarded_open=>//; apply/guarded_gt; last by apply/GG'.
  Qed.

  Fixpoint is_end g :=
    match g with
    | g_rec g => is_end g
    | g_end => true
    | _ => false
    end.

  Lemma recdepth_unroll g :
    is_end g -> rec_depth g = rec_depth (unroll g).
  Proof.
    move=>END; have: (is_end (g_rec g)) by [].
    rewrite /unroll; move: (g_rec g)=>g' END'.
      by elim: g 0 END=>// g Ih n /=/(Ih n.+1)->.
  Qed.

  Lemma isend_unroll g :
    is_end g -> is_end (unroll g).
  Proof.
    move=>END; have: (is_end (g_rec g)) by [].
    rewrite /unroll; move: (g_rec g)=>g' END'.
      by elim: g 0 END=>// g Ih n /=/(Ih n.+1)->.
  Qed.

(*Fixpoint non_empty_cont G :=
  match G with
  | g_msg _ _ Ks => ~~ nilp Ks && all id [seq non_empty_cont K.2.2 | K <- Ks]
  | g_rec G => non_empty_cont G
  | _ => true
  end.*)

  Definition g_precond G :=
    g_closed G && guarded 0 G. (*&& non_empty_cont G.*)

(*Lemma ne_open n G G' :
  non_empty_cont G -> non_empty_cont G' -> non_empty_cont (g_open n G' G).
Proof.
  move=> NE1 NE2; move: NE1.
  elim: G n=>//.
  - by move=>v n; rewrite /unroll/=; case: ifP=>//.
  - by move=> G Ih n /=; apply/Ih.
  - move=> F T C Ih n /=; case: C Ih=>//= K Ks Ih /andP-[NE_K ALL].
    rewrite (Ih K (or_introl erefl) n NE_K) /= {NE_K}.
    move: Ih=>/(_ _ (or_intror _) n)=> Ih.
    move: ALL=>/forallbP/forall_member/member_map-ALL.
    apply/forallbP/forall_member/member_map/member_map=>/={}K M.
    by apply/(Ih _ M)/ALL.
Qed.*)

(*Lemma ne_unr n G : non_empty_cont G -> non_empty_cont (n_unroll n G).
Proof.
  elim: n G=>[//|n/=] Ih; case=>//= G NE.
  have: non_empty_cont (g_rec G) by [].
  by move=>/(ne_open 0 NE); apply/Ih.
Qed.*)


  Lemma precond_parts g :
    g_precond g -> ~~ nilp (participants g) \/ is_end g.
  Proof.
    move=>/andP-[CG GG]; move: CG GG; rewrite /g_closed.
    elim: g 0.
    - by move=> n _ _; right.
    - by move=>v n /= H E; move: E H=>->.
    - by move=> G Ih n /=; apply/Ih.
    - by move=> p q K _ n  _ _; left.
  Qed.

End GlobalSyntax.


Section LocalSyntax.

  Unset Elimination Schemes.
  Inductive lty :=
  | l_end
  | l_jump (X : nat)
  | l_rec (k : lty)
  | l_send (q : role) (t : mty) (L : lty)
  | l_recv (p : role) (t : mty) (L : lty)
  .
  Set Elimination Schemes.

  Definition ilook (E : seq (role * lty)) p := odflt l_end (find_cont E p).

  Fixpoint partsL (L : lty) :=
    match L with
    | l_end
    | l_jump _ => [::]
    | l_rec G => partsL G
    | l_send q t L => q::partsL L
    | l_recv p t L => p::partsL L
    end.

  Lemma lty_ind :
    forall (P : lty -> Prop),
      P l_end ->
      (forall v, P (l_jump v)) ->
      (forall G, P G -> P (l_rec G)) ->
      (forall q t L, P L -> P (l_send q t L)) ->
      (forall p t L, P L -> P (l_recv p t L)) ->
      forall l : lty, P l.
  Proof.
    move => P P_end P_jump P_rec P_send P_recv.
    fix Ih 1; case=>[|v|L|q t L|p t L].
    + by apply: P_end.
    + by apply: P_jump.
    + by apply: P_rec.
    + by apply: P_send.
    + by apply: P_recv.
  Qed.

  Fixpoint depth_lty L :=
    match L with
    | l_end
    | l_jump _ => 0
    | l_rec L => (depth_lty L).+1
    | l_send _ _ L => (depth_lty L).+1
    | l_recv _ _ L => (depth_lty L).+1
    end.

  Fixpoint eq_lty x y :=
    match x, y with
    | l_end, l_end => true
    | l_jump x, l_jump y => x == y
    | l_rec x, l_rec y => eq_lty x y
    | l_send q1 t1 L1, l_send q2 t2 L2
      => (q1 == q2) && (t1 == t2) && (eq_lty L1 L2)
    | l_recv p1 t1 L1, l_recv p2 t2 L2
      => (p1 == p2) && (t1 == t2) && (eq_lty L1 L2)
    | _, _ => false
    end.

  (*Definition eq_lcont (l r : (mty * l_ty)) :=
    (l.1 == r.1) && eq_lty l.2 r.2.*)

(*Lemma eqlty_msg a1 a2 r1 r2 K1 K2 :
  eq_lty (l_msg a1 r1 K1) (l_msg a2 r2 K2) =
  (a1 == a2) && (r1 == r2) && eq_lcont K1 K2.
Proof.
  rewrite /=; do 2 (case: eqP=>///= _); move: K1 K2 {r1 r2 a1 a2}.
Qed.*)

  Lemma lty_eqP : Equality.axiom eq_lty.
  Proof.
    rewrite /Equality.axiom; fix Ih 1 => x y.
    case: x => [|v|L|r t L|r t L];
                 case: y =>[|v'|L'|r' t' L'|r' t' L']; try (by constructor).
    + by rewrite /eq_lty; case: eqP=>[->|F]; constructor=>//[[/F]].
    + by rewrite /=; case: Ih=>[->|F]; constructor=>//[[/F]].
    + rewrite /=; do 2 (case: eqP=>[<-|H];[|constructor=>[[]]//] =>/=).
      by case: Ih=>[->|F]; constructor=>//=[[/F]].
    + rewrite /=; do 2 (case: eqP=>[<-|H];[|constructor=>[[]]//] =>/=).
      by case: Ih=>[->|F]; constructor=>//=[[/F]].
  Qed.

  Definition lty_eqMixin := EqMixin lty_eqP.
  Canonical lty_eqType := Eval hnf in EqType lty lty_eqMixin.

(*Lemma in_maximum_leq v l: v \in l -> v <= foldr maxn 0 l.
Proof.
  elim: l=>//v' l Ih; rewrite in_cons=>/orP-[/eqP<-|]/=.
  + by apply: leq_maxl.
  + by move=>/Ih{Ih}; move: (foldr _ _ _) => k {l}; rewrite leq_max orbC=>->.
Qed.*)

(*Lemma l_ty_ind :
  forall (P : l_ty -> Prop),
    P l_end ->
    (forall v, P (l_var v)) ->
    (forall L, P L -> P (l_rec L)) ->
    (forall a p K, (forall K, K \in Ks -> P K.2.2) -> P (l_msg a p Ks)) ->
    forall l : l_ty, P l.
Proof.
  move => P P_end P_var P_rec P_msg L.
  move: {-1}(depth_lty L) (leqnn (depth_lty L))=> n; move: n L; elim.
  + by case.
  + move=>n Ih; case=>/=//.
  - by move=>L D; apply:P_rec; apply: Ih.
  - move=> a r Ks D;apply: P_msg=>K /(map_f (fun X => depth_lty X.2.2)).
    move=>/in_maximum_leq-/=dG; move: (leq_trans dG D)=>{dG} {D}.
      by apply: Ih.
Qed.*)

  Fixpoint l_shift n d (L : lty) :=
    match L with
    | l_end => l_end
    | l_jump v => if v >= d then l_jump (n + v) else L
    | l_send r t L => l_send r t (l_shift n d L)
    | l_recv r t L => l_recv r t (l_shift n d L)
    | l_rec L => l_rec (l_shift n d.+1 L)
    end.

  Fixpoint l_open (d : nat) (L2 : lty) (L1 : lty) :=
    match L1 with
    | l_end => L1
    | l_jump v => if v == d then l_shift d 0 L2 else L1
    | l_rec L => l_rec (l_open d.+1 L2 L)
    | l_send r t L => l_send r t (l_open d L2 L)
    | l_recv r t L => l_recv r t (l_open d L2 L)
    end.
  Notation "{ k '~>' v } L":= (l_open k v L) (at level 30, right associativity).
  Notation "L '^' v":= (l_open 0 (l_jump v) L) (at level 30, right associativity).

  Lemma open_notvar n L L' :
    (forall v : nat, L != l_jump v) ->
    (forall v : nat, l_open n L' L != l_jump v).
  Proof. by case: L=>//v /(_ v)/eqP. Qed.

  Lemma l_open_send_rw d L2 q t L:
    l_open d L2 (l_send q t L) = l_send q t (l_open d L2 L).
  Proof. by []. Qed.

  Lemma l_open_recv_rw d L2 p t L:
    l_open d L2 (l_recv p t L) = l_recv p t (l_open d L2 L).
  Proof. by []. Qed.

(*Lemma unzip2_lift A B C (f : B -> C) (K : seq (A * B)) :
  [seq f x | x <- unzip2 K] = unzip2 [seq (x.1, f x.2) | x <- K].
Proof. by rewrite /unzip2 -!map_comp /comp. Qed.

Lemma unzip1_map2 A B C (f : B -> C) (K : seq (A * B)) :
  unzip1 K = unzip1 [seq (x.1, f x.2) | x <- K].
Proof. by rewrite /unzip1 -map_comp /comp. Qed.

Lemma map2_zip A B C (f : B -> C) (K : seq (A * B)) :
  zip (unzip1 K) [seq f x | x <- unzip2 K] = [seq (x.1, f x.2) | x <- K].
Proof. by rewrite unzip2_lift (unzip1_map2 f) zip_unzip. Qed.*)

  Fixpoint l_fidx (d : nat) (L : lty) : bool :=
    match L with
    | l_end => true
    | l_jump v => if v >= d then false else true
    | l_rec L => l_fidx d.+1 L
    | l_send _ _ L => l_fidx d L
    | l_recv _ _ L => l_fidx d L
    end.

  Definition l_closed (L : lty) := l_fidx 0 L.

  Lemma lfbvar_next n L :
    l_fidx n L -> l_fidx n.+1 L.
  Proof.
    elim: L n=>[//|v|L Ih|r t L Ih|r t L Ih] n/=; try by apply Ih.
    case: v=>//= m H; case: ifP=>// n_m; move: H.
      by move: (leq_trans (leqnSn n) n_m)=>->.
  Qed.

  Lemma lfbvar_gt n m L :
    n <= m ->
    l_fidx n L -> l_fidx m L.
  Proof.
    move=> LE H; move: LE; elim: m=>[|m Ih]//; first by case: n H=>///eqP.
    move: H; case: (boolP (n == m.+1))=>[/eqP->/eqP//|NE _ LE].
      by apply /lfbvar_next/Ih; move: (conj NE LE)=>/andP; rewrite -ltn_neqAle.
  Qed.

  Lemma lshift_closed n d L :
    l_fidx d L -> l_shift n d L = L.
  Proof.
    elim: L=> [| v | L Ih | r t L Ih | r t L Ih]//= in d *.
    { (* jump *)
        by case: ifP=>//.
    }
    { (* rec *)
        by move=>H; congr l_rec; apply/Ih.
    }
    { (* send *)
        by move=>H; rewrite Ih//=.
    }
    { (* recv *)
        by move=>H; rewrite Ih//=.
    }
  Qed.

  Lemma lopen_closed L :
    l_closed (l_rec L) ->
    l_closed (l_open 0 (l_rec L) L).
  Proof.
    rewrite/l_closed/==>L_fbv; have: l_fidx 0 (l_rec L) by [].
    move: (l_rec L) => L' L'0.
    elim: L 0 L_fbv=>[//|v|L Ih|r t L Ih|r t L Ih] n /=; try by apply Ih.
    rewrite  lshift_closed//= ltn_neqAle; case: ifP=>//=.
    case: ifP=>//=; [by rewrite (lfbvar_gt _ L'0)|].
      by case: ifP=>//=; move=> nv vnf; rewrite eq_sym vnf.
  Qed.

  Fixpoint lguarded d L :=
    match L with
    | l_end => true
    | l_jump v => v >= d
    | l_rec L => lguarded d.+1 L
    | l_send _ _ L => lguarded 0 L
    | l_recv _ _ L => lguarded 0 L
    end.

  Fixpoint l_binds n L :=
    match L with
    | l_jump v => v == n
    | l_rec L => l_binds n.+1 L
    | _ => false
    end.

  Fixpoint lguarded' L :=
    match L with
    | l_end
    | l_jump _ => true
    | l_rec L => ~~ l_binds 0 L && lguarded' L
    | l_send _ _ L => lguarded' L
    | l_recv _ _ L => lguarded' L
    end.

  Lemma lguarded_next n L : lguarded n.+1 L = ~~ l_binds n L && lguarded n L.
  Proof. by elim: L n=>//= v n; rewrite ltn_neqAle eq_sym. Qed.

  Lemma lguarded_binds L : lguarded 0 L = lguarded' L.
  Proof.
      by elim: L=>[||L|_ _ L Ih|_ _ L Ih]//=<-;apply/lguarded_next.
  Qed.

  Lemma lguarded_rec d L
    : lguarded d (l_rec L) -> forall s, s <= d -> ~~ l_binds s L.
  Proof.
    elim: L=>[|v|L /= Ih|r t L Ih|r t L Ih]// in d *.
    - move=>/= vd s sd; move: (leq_ltn_trans sd vd).
        by rewrite eq_sym ltn_neqAle=>/andP-[].
    - by rewrite /==>/Ih-{Ih}Ih s Lsd; apply/Ih.
  Qed.

  Fixpoint lrec_depth L :=
    match L with
    | l_rec L => (lrec_depth L).+1
    | _ => 0
    end.

  Fixpoint lunroll d L :=
    match d with
    | 0 => L
    | d.+1 =>
      match L with
      | l_rec L' => lunroll d (l_open 0 L L')
      | _ => L
      end
    end.

  Lemma lguarded_match d L :
    match L with
    | l_jump v => d < v
    | _ => lguarded d.+1 L
    end ->
    (exists v, (L == l_jump v) && (d < v)) \/
    (forall v, (L != l_jump v)) /\ lguarded d.+1 L.
  Proof.
    case: L=>[||||]//=; try by right.
      by move=> n Eq; left; exists n; rewrite eq_refl.
  Qed.

  Lemma lguarded_recdepth d L m :
    lguarded d L ->
    m < d ->
    forall L', lrec_depth L = lrec_depth ({m ~> L'} L).
  Proof.
    elim: L=>[|n|L Ih|r t L Ih|r t L Ih]//= in d m *.
    - move=>dn md L; case: ifP=>[/eqP-E|ne//].
        by move: E dn md=>-> /leq_ltn_trans-H /H; rewrite ltnn.
    - by move=> GL md L'; rewrite (Ih _ m.+1 GL _ L').
  Qed.

  Lemma lty_not_var A L (b1 : nat -> A) (b2 : A) :
    (forall v : nat, L != l_jump v) ->
    match L with | l_jump v => b1 v | _ => b2 end = b2.
  Proof. by case: L =>[|n /(_ n)/eqP|||]. Qed.

  Lemma lguarded_depth_gt dL dL' L :
    lguarded dL' L -> l_closed L -> lguarded dL L.
  Proof.
    rewrite /l_closed=> H H'; move: 0 (leq0n dL') H H'.
    elim: L =>[|n|L Ih|r t L Ih|r t L Ih]// in dL dL' *.
    - by move=> m /leq_trans-H /= /H->.
    - by move=> n ndL' /=; apply/Ih.
  Qed.

  Lemma lclosed_not_var L :
    l_closed L ->
    forall v, L != l_jump v.
  Proof. by case: L=>//= v. Qed.

  Lemma lopen_not_var d L L' :
    l_closed L ->
    (forall v, L' != l_jump v) ->
    forall v, {d ~> L} L' != l_jump v.
  Proof. by case: L'=>// n _ /(_ n)/eqP. Qed.

  Lemma lguarded_open d1 d2 L L' :
    lguarded 0 L' ->
    l_closed L' ->
    lguarded d1 L ->
    lguarded d1 ({d2 ~> L'} L).
  Proof.
    elim: L=>[|n|L Ih|r t L Ih|r t L Ih]//= in d1 d2 *.
    - case: ifP=>// _ gL cL; rewrite (lshift_closed _ cL)=>_.
        by apply/(lguarded_depth_gt _ gL).
    - by apply/Ih.
    - by move=> GL' CL' H; apply Ih=>//=.
    - by move=> GL' CL' H; apply Ih=>//=.
  Qed.

  Lemma lguarded_gt d d' L :
    d >= d' ->
    lguarded d L ->
    lguarded d' L.
  Proof.
    elim: L=>[|n|L Ih|r t L Ih|r t L Ih]//= in d d' *.
    - by move=>/leq_trans-H /H.
    - by move=> H; apply/Ih.
  Qed.

  Lemma lunroll_guarded L :
    l_closed L ->
    lguarded 0 L ->
    forall L', lunroll (lrec_depth L) L != l_rec L'.
  Proof.
    move: {-2}(lrec_depth L) (eq_refl (lrec_depth L)) => n.
    elim: n => [|n Ih]/= in L *; case: L=>// L n_rd CL GL; move: n_rd.
    rewrite eqE/=-eqE => n_rd.
    have/=GL': (lguarded 0 (l_rec L)) by [].
    move: n_rd; rewrite (lguarded_recdepth GL' (ltn0Sn 0) (l_rec L))=>n_rd.
    apply/Ih=>//; first by apply/lopen_closed.
      by apply/lguarded_open=>//; apply/lguarded_gt; last by apply/GL'.
  Qed.

  Fixpoint l_isend L {struct L}:=
    match L with
    | l_rec L => l_isend L
    | l_end => true
    | _ => false
    end.

  Lemma isend_open n L' L :
    l_isend L -> l_open n L' L = L.
  Proof.
    elim: L=>[|v|L Ih|r t L Ih|r t L Ih]//= in n *; move=> END.
      by rewrite Ih.
  Qed.

  Lemma keep_unrolling L :
    l_isend L -> exists m, l_end = lunroll m L.
  Proof.
    elim: L=>[||L Ih||]//; [move=>_| move=>/=END; move:(Ih END)=>[n U]].
    - by exists 0.
    - by exists n.+1=>/=; rewrite (isend_open 0 _ END).
  Qed.

  Lemma l_closed_no_binds_aux m n L: m <= n -> l_fidx m L -> l_binds n L = false.
  Proof.
    elim: L m n; rewrite //=.
    + move=> v m n le; case: ifP=>//.
        by move=> lefalse; elim; apply: ltn_eqF;
                    apply: (leq_trans _ le); move: (negbT lefalse); rewrite-ltnNge //=.
    + by move=> L IH m n le; apply: IH; rewrite //=.
  Qed.

  Lemma l_closed_no_binds n L: l_closed L -> l_binds n L = false.
  Proof. by apply: l_closed_no_binds_aux. Qed.

  Lemma l_binds_open m n L L1: n != m -> l_closed L1
                               -> l_binds m (l_open n L1 L) = l_binds m L.
  Proof.
    elim: L m n L1; [| | |by []| by[]].
    + by move=> m n L1 neq closed; rewrite /l_binds //=.
    + move=> v m n L1 neq closed.
      rewrite /l_binds //=; case: ifP => //=; rewrite <-(rwP eqP); move=>->.
      rewrite (lshift_closed _ closed).
      move: (@l_closed_no_binds m _ closed); rewrite /l_binds; move =>->.
        by move: (negbTE neq).
    + by move=> L IH m n L1 neq closed; rewrite //=; apply: IH.
  Qed.

  Fixpoint n_rec d L :=
    match d with
    | 0 => L
    | d.+1 => l_rec (n_rec d L)
    end.

  Fixpoint n_open d n L :=
    match n with
    | 0 => L
    | m.+1 => l_open d (n_rec d.+1 (n_open d.+1 m L)) (n_open d.+1 m L)
    end.

  Fixpoint get_nr L :=
    match L with
    | l_rec L => get_nr L
    | _ => L
    end.

  Lemma nrec_comm d L : n_rec d (l_rec L) = n_rec d.+1 L.
  Proof. by elim: d =>//= n ->. Qed.

  Lemma nopen_rec_comm n L : n_open 0 n (l_rec L) = l_rec (n_open 1 n L).
  Proof.
    elim: n 0 L=>//= n Ih d L.
    rewrite Ih/= -Ih/= -/(n_rec d.+1 _) -/(n_rec d.+2 _).
      by rewrite Ih -/(n_rec d.+2 _) nrec_comm.
  Qed.

  Lemma lunroll_nopen L :
    lunroll (lrec_depth L) L = n_open 0 (lrec_depth L) (get_nr L).
  Proof.
    rewrite -{2}/(n_open 0 0 L) -{2}(@addn0 (lrec_depth L)); move: {2 4}0 => n.
    elim: L n=>//= L Ih n.
    rewrite nopen_rec_comm/= -/(n_open 0 (lrec_depth L + n).+1 _).
      by rewrite -/(n_open 0 n.+1 _); rewrite Ih addnS.
  Qed.

  Lemma nopen_var' m n L v : n_open m n L = l_jump v -> L = l_jump v.
  Proof.
    elim: n m=>//= n Ih m.
    case EQ: n_open=>[|v'|||]//=; case: ifP=>// _ [EV].
      by move: EV EQ=>->{v'}/Ih.
  Qed.

  Lemma getnr_nonrec L : match get_nr L with
                         | l_rec _ => false
                         | _ => true
                         end.
  Proof. by elim: L. Qed.

  (* lbinds m (get_nr L) is the same as get_nr L = l_var m *)
  Lemma nopen_rec d n L L' :
    n_open d n (get_nr L) = l_rec L' ->
    exists m, l_binds m (get_nr L) /\ m < d + n.
  Proof.
    elim: n =>[|n Ih] //= in d L' *;
                first by move=> H; move: H (getnr_nonrec L)=>->.
    case EQ: (n_open d.+1 n (get_nr L)) => [|v|Lr||]//=.
    - case: ifP=>///eqP-EV; rewrite (nopen_var' EQ)/=EV =>{}EQ.
      exists d; rewrite eq_refl; split=>//.
      rewrite addnS; by apply/leq_addr.
    - move: (Ih _ _ EQ)=>[m][BND] LE _.
        by exists m; split=>//; rewrite addnS.
  Qed.

  (* l_open d L (n_rec m L') = n_rec m (l_open (d - m) L L') ? *)
  Lemma lopen_nrec d m L
    : l_open d L (n_rec m (l_jump m)) =
      n_rec m (if d == 0 then l_shift (d + m) 0 L else l_jump m).
  Proof.
    rewrite -{2 5} (add0n m) -{1 3}(add0n d); move: {-3 5}0=>n.
    elim: m=>[|m Ih]/= in n *.
    - case: (ifP (d == 0))=>[/eqP->|]; first by rewrite eq_refl !addn0.
        by case: ifP=>//; rewrite eqn_add2l eq_sym=>->.
    - by rewrite !addnS -!addSn Ih.
  Qed.

  Lemma nrec_lrecdepthI L : L = n_rec (lrec_depth L) (get_nr L).
  Proof. by elim: L=>//= L<-. Qed.

  Lemma nrec_twice n m L : n_rec n (n_rec m L) = n_rec (n + m) L.
  Proof. by elim n=>//= {}n->. Qed.

  Lemma lopen_bound d n m L :
    m < d + n ->
    l_open d L (n_rec n (l_jump m)) = n_rec n (l_jump m).
  Proof.
    elim: n=>[|n Ih]//= in d *; last by rewrite addnS -addSn=>/Ih->.
      by rewrite addn0 ltn_neqAle=>/andP-[/negPf->].
  Qed.

  Lemma lshift_nrec d r m n :
    n < r + m ->
    l_shift d r (n_rec m (l_jump n)) = n_rec m (l_jump n).
  Proof.
    elim: m=> [|m Ih]//= in r *; first by rewrite addn0 ltnNge=>/negPf->.
      by rewrite addnS -addSn/==>/Ih->.
  Qed.

  Lemma lguarded_lbinds_lt s Lr :
    l_binds s Lr = false ->
    lguarded s Lr ->
    lguarded s.+1 Lr.
  Proof.
    move: {-1}(lrec_depth Lr) (erefl (lrec_depth Lr))=> n E.
    elim: n=>[|n Ih] in s Lr E *.
    - by case: Lr E=>//= v _ /(rwP negPf); rewrite ltn_neqAle eq_sym=>->->.
    - case: Lr E=>//= L [/Ih-E]; apply/E.
  Qed.

End LocalSyntax.

Section IProject.

  Fixpoint project (g : g_ty) (r : role) : option lty :=
    match g with
    | g_end => Some l_end
    | g_var v => Some (l_jump v)
    | g_rec G =>
      match project G r with
      | Some L => Some (if l_binds 0 L then l_end else l_rec L)
      | None => None
      end
    | g_msg p q K =>
      match project K.2 r with
      | Some L => if p == q
                  then None
                  else if p == r
                       then Some (l_send q K.1 L)
                       else if q == r
                            then Some (l_recv p K.1 L)
                            else Some L
      | None => None
      end
    end.

  Fixpoint project_all (parts : seq role) (g : g_ty)
    : option (seq (role * lty))
    := match parts with
       | [::] => Some [::]
       | p :: parts =>
         match project g p, project_all parts g with
         | Some l, Some e => Some ((p, l) :: e)
         | _, _ => None
         end
       end%fmap.

  Definition eproject (g : g_ty) : option (seq (role * lty)) :=
    if g_precond g
    then project_all (undup (participants g)) g
    else None.

  Lemma eproject_some g e :
    eproject g = Some e ->
    ~~ nilp (participants g) ->
    exists p l, project g p = Some l.
  Proof.
    rewrite /eproject; case:ifP=>// _; elim: (participants g)=>//= p ps Ih.
    case:ifP=>//.
    - by move=> p_in_ps /Ih-{}Ih _; apply: Ih; case: ps p_in_ps.
    - move=> _ /=.
      by case PRJ: project=>[L|]// _ _; exists p, L.
  Qed.

  Lemma fnd_not_part g e p :
    eproject g = Some e -> p \notin participants g -> find_cont e p = None.
  Proof.
    rewrite /eproject; case:ifP=>// _ PRJ; rewrite -mem_undup=>PARTS.
    elim: (undup (participants g)) PARTS e PRJ =>//=.
    - by move=> _ e [<-].
    - move => q l Ih.
      rewrite in_cons negb_or=>/andP-[pq] /Ih-{}Ih e.
      case PRJ: project=>[L|]//.
      case ALL: project_all=>[E|]//.
      by move=>[<-]; rewrite /=/extend eq_sym (negPf pq); apply/Ih.
  Qed.

  Lemma eproject_part (g : g_ty) (e : seq (role * lty)) :
    eproject g == Some e ->
    forall p,
      p \in participants g -> project g p = Some (odflt l_end (find_cont e p)).
  Proof.
    rewrite /eproject; case: ifP=>//WF; move: (participants g)=>p; elim:p e=>//=.
    move=> p ps Ih E/=; case: ifP.
    - by move=> p_in_ps /Ih-{}Ih p'; rewrite in_cons=>/orP-[/eqP->|]; apply/Ih.
    - move=>p_not_in/=.
      case PRJp: project=>[L|]//;case ALL: project_all=>[E'|]//.
      move=>/eqP-[<-] q; rewrite in_cons/= /extend eq_sym.
      by case:ifP=>[/eqP<-| _]//=; apply/Ih/eqP.
  Qed.

  Lemma prj_isend g
    : is_end g ->
      forall p, exists l, project g p = Some l /\ l_isend l.
  Proof.
    elim: g=>//.
    - by move=> _ p; exists l_end; split.
    - move=> G Ih /Ih-{}Ih p /=.
      move: (Ih p)=>[L][PRJ] END; rewrite PRJ/=.
      case: ifP=>//_; try by exists l_end.
      by exists (l_rec L); split.
  Qed.

  Lemma notin_parts_project Lp p G
       (Ep : project G p = Some Lp)
       (*NIN : p \notin participants G*)
    : p \notin partsL Lp.
  Proof.
  elim: G=>[|v|G Ih|q r K Ih] in Lp (*NIN*) Ep *; move: Ep=>[]//=.
  - by move<-.
  - by move<-.
  - case Ep: project=>[Lp'|//]; case: ifP=>//; first by move=>_[<-].
      by move=> _ [<-]/=; apply/Ih.
  - case Ep:project=>[Lc|]//=; case: ifP=>//= diff; case: ifP.
    + move=> /eqP-qp []<-//=; rewrite in_cons; apply /norP; split; [|by apply Ih].
      by rewrite -qp diff.
    + move=> diff2; case: ifP; [move=>/eqP-rp []<-//=| by move=> diff3 []<-; apply Ih].
        by rewrite in_cons; apply /norP; split; [rewrite eq_sym diff2 | apply Ih].
  Qed.

  Lemma l_binds_notin Lp p G
        (Ep : project G p = Some Lp)
        (BLp : l_binds 0 Lp)
    : p \notin participants G.
  Proof.
    elim: G 0 =>[|v|G Ih|q r K Ih] n//= in Lp BLp Ep *.
    - move: Ep Ih; case Prj: project=>[L|//]; move: Prj=>/eqP-Prj; case: ifP.
      + move=> B [E]; move: E BLp=><- _.
        by move=>/(_ _ _ B erefl).
      + by move=>_ [E]; move: E BLp=><-/= BLp /(_ _ _ BLp erefl).
    - move: Ep; case Prj: project=>[Kc|//]; case: ifP=>// Eqr.
      case: ifP=>Eqp; first by move=> [E]; move: E BLp=><-.
      case: ifP=>Erp; first by move=> [E]; move: E BLp=><-.
      rewrite !in_cons eq_sym Eqp eq_sym Erp /==>[[]]M.
      by apply (Ih _ _ BLp); rewrite -M.
  Qed.

  Lemma project_var_notin p G v L :
    (L == l_end) || (L == l_jump v) ->
    project G p == Some L ->
    p \notin participants G.
  Proof.
    elim: G => [|v'|G Ih|q r K Ih]//= in L v *.
    - move: Ih=>/=; case Prj: project =>[Lp|//] Ih.
      move=>/orP-[/eqP->|/eqP->]; case: ifP=>[Lp_var|]//.
      by move: (l_binds_notin Prj Lp_var).
    - case Prj: project=>[Lc|]//=; case: ifP=>//= d1.
      case: ifP=> [_ /orP[]/eqP-> /eqP[]//=| d2].
      case: ifP=> [_ /orP[]/eqP-> /eqP[]//=| d3].
      move=> h /eqP[]-eqL; move: Prj.
      rewrite !in_cons eqL eq_sym d2 eq_sym d3//==>/eqP.
      by move: h; apply Ih.
  Qed.

  Lemma projectmsg_var n p r s K:
    project (g_msg r s K) p == Some (l_jump n) ->
    r != p /\ s != p /\ r != s /\
    project K.2 p == Some (l_jump n).
  Proof.
    rewrite //=; case Prj: project => [KL|//]; move: Prj=>/eqP.
    by do ! case: ifP=>//.
  Qed.

  Lemma proj_var_eq G p q v v':
    project G p == Some (l_jump v) ->
    project G q == Some (l_jump v') ->
    v == v'.
  Proof.
    elim: G => [|n|G Ih|f t K Ih]//= in v v' *.
    - by move=>/eqP-[<-]/eqP-[<-].
    - by case Pp: project =>[Lp|//] /eqP[]; case: ifP.
    - case Pp: project =>[Lp|//]; move: Pp=>/eqP=>Pp.
      case Pq: project =>[Lq|//]; move: Pq=>/eqP=>Pq.
      do 5 case: ifP=>//=; move=> _ _ _ _ _ /eqP[]Lpeq /eqP[]Lqeq.
      by rewrite Lpeq in Pp; rewrite Lqeq in Pq; apply Ih.
  Qed.

  Lemma project_binds_eq p q G Lp Lq n m :
    project G p = Some Lp ->
    project G q = Some Lq ->
    l_binds n Lp ->
    l_binds m Lq ->
    l_binds n Lq.
  Proof.
    elim: G=>[|v|G Ih|r s K Ih]//= in Lp Lq n m *.
    - by move=>[<-].
    - by move=>[<-] [<-].
    - case Pp: project=>[Lp'|//]; case Pq: project=>[Lq'|//].
      by case: ifP=>_ [<-]//; case: ifP=>_ [<-]//=; apply/Ih.
    - case Pp: project=>[Kp|//]; case Pq: project=>[Kq|//].
      case: ifP=>//= _; do ! (case: ifP=> _; first by move=>[<-]); move=>[]eqp.
      do ! (case: ifP=> _; first by move=>[<-]); move=>eqq.
      rewrite eqp in Pp; rewrite eqq in Pq.
      by apply (Ih _ _ _ _ Pp Pq).
  Qed.

  Lemma gclosed_lclosed d G r L :
    g_fidx d G -> project G r == Some L ->
    l_fidx d L.
  Proof.
    elim: G =>[|v|G Ih|p q K Ih]//= in d L *.
    - by move=> _ /eqP-[<-].
    - by case: ifP=>//=; move=> H _ /eqP-[<-]/=; rewrite H.
    - case Eq: project =>[Lr|//]; case: ifP=> [_ _ /eqP[]<-//=|].
      by move=> gu cl /eqP[]<-//=; apply Ih; [|apply /eqP].
    - move=> cl; case Pr: project=>[Lr|]//=; case: ifP=>//= d1.
      case: ifP=>pr; [by move=>/eqP[]<-//=; apply Ih; [|apply /eqP]|].
      case: ifP=>qr; try by move=>/eqP[]<-//=; apply Ih; [|apply /eqP].
  Qed.

(*  Lemma prjall_open r n g l Ks Ks' :
    (forall p : lbl * (mty * g_ty),
      member p Ks ->
      forall s : lty_eqType,
        project simple_merge p.2.2 r == Some s ->
        project simple_merge (g_open n g p.2.2) r = Some (l_open n l s)) ->
    prj_all simple_merge Ks r = Some Ks' ->
    prj_all simple_merge [seq (K.1, (K.2.1, g_open n g K.2.2)) | K <- Ks] r
    = Some [seq (K.1, (K.2.1, l_open n l K.2.2)) | K <- Ks'].
  Proof.
    elim: Ks Ks' => [|K Ks Ih]; case=>[|K' Ks']//=.
    - by case: project; case: prj_all.
    - move=> H. move: (H K (or_introl erefl)).
      case: project =>// L /(_ L (eq_refl _))->.
      move: H=>/(_ _ (or_intror _))-H; move: Ih => /(_ _ H) {H}.
      by case: prj_all => [Ksr|//] /(_ Ksr erefl)-> [<-<-]/=.
  Qed.*)




  Lemma project_guarded r iG iL :
    project iG r == Some iL -> lguarded 0 iL.
  Proof.
    elim: iG =>[|v|iG Ih|p q K Ih]//= in iL *.
    - by move=>/= /eqP-[<-].
    - by move=>/= /eqP-[<-].
    - case Prj: project=>[Lr|//]; move: Prj=>/eqP/Ih-Prj.
      case: ifP; first by move=> _ /eqP-[<-].
      by move=> B /eqP-[<-]/=; apply/lguarded_lbinds_lt.
    - case Prj: project => [KL|]//; case: ifP=>// pq.
      case: ifP=>pr; [by move=> /eqP[]<-//=; apply Ih; apply /eqP|].
      case: ifP=>qr; try by move=> /eqP[]<-//=; apply Ih; apply /eqP.
  Qed.


  Lemma project_var_parts G v r :
    project G r == Some (l_jump v) -> r \notin participants G.
  Proof. by apply/project_var_notin/orP/or_intror/eq_refl. Qed.


  Lemma prj_open_binds L1 L2 G r :
    project G r = Some L1 ->
    l_binds 0 L1 ->
    project (g_open 0 (g_rec G) G) r = Some L2 ->
    l_isend L2.
  Proof.
    move=>P1 B1; have []: project G r = Some L1 /\ l_binds 0 L1 by split.
    move: {-2}G  {1 2}L1 =>G' L1'.
    elim: G' 0 =>[|v|G' Ih|p q K' Ih] n //= in L1' L2 *.
    - by move=>[<-].
    - by move=>[<-]/=->/=; rewrite P1 B1=> [[<-]].
    - case P: project=>[L''|//].
      case: ifP=>//; first by move=> _ [<-].
      move=> B [<-] {L1'}/= B'.
      case P': project=>[L1'|//].
      case: ifP=> BL1'//; first by move=> [<-].
      by move=>[<-]/=; move: B' P'; apply/Ih.
    - case P: project=>[K|//]; case: ifP=>//=pq.
      do ! case: ifP=>[_ [<-]//|_].
      move=>[]KL1' B1'; case P': project=>[K2|//].
      move=> []K2L2; rewrite -KL1' in B1'; apply (Ih _ _ _ P B1').
      by rewrite -K2L2.
  Qed.

  Lemma project_g_open_comm G1 G2 r L1 L2 k:
    g_closed G1 ->
    project G1 r = Some L1 -> project G2 r = Some L2 ->
    project (g_open k G1 G2) r = Some (l_open k L1 L2).
  Proof.
  elim: G2 G1 k L1 L2.
  + by move=> G1 k L1 L2 gclo eq1 => //=; move=> [eq2]; rewrite -eq2 //=.
  + move=> VAR G1 k L1 L2 gclo eq1 => //=; move=> [eq2]; rewrite -eq2 //=.
    case: ifP=>//; move:eq1=>/eqP-eq1.
    by move: (gclosed_lclosed gclo eq1)=>/lshift_closed-> _; apply/eqP.
  + move=> GT IH G1 k L1 L2 gclo eq1 => //=; case Prj: project=>[LT| //=].
    * case: ifP; move=> lbi [eq2]; rewrite //=.
      move: (IH _ (k.+1) L1 LT gclo eq1 Prj) =>->; rewrite -eq2 //=.
      move: (@l_binds_open 0 (k.+1) LT L1) =>-> //=.
      + by move: lbi; case: ifP => //=.
      + by move: eq1; rewrite (rwP eqP); apply gclosed_lclosed.
    * move: (IH G1 (k.+1) L1 LT gclo eq1 Prj) =>->; move: eq2=><-/=.
      move: (@l_binds_open 0 (k.+1) LT L1) =>-> //=.
      + by move: lbi; case: ifP => //=.
      + by move: eq1; rewrite (rwP eqP); apply gclosed_lclosed.
  + move=> FROM TO CONT IH G1 k L1 L2 gclo eq1 eq2.
    move: eq2=>//=; case prj: project=>[Lc|]//=.
    rewrite (IH _ k _ _ gclo eq1 prj); case: ifP=>//= d1.
    by case: ifP=> Fr; [move=>[]<-| case: ifP=>Tr; try move=>[]<-].
  Qed.

  Lemma project_open L G r
    : l_binds 0 L == false -> g_closed (g_rec G) ->
  project G r = Some L -> project (unroll G) r = Some (l_open 0 (l_rec L) L).
  Proof.
  move=> nlb cl prS.
  have: project (g_rec G) r = Some (l_rec L).
    move: prS; rewrite //=; case Prj: project=>[LT| //=].
    by move=> eq; move: eq Prj nlb=>[<-] Prj; case: ifP=>//=.
  move=> prrecS; apply project_g_open_comm; rewrite //=.
  Qed.

  Lemma project_open_end_strong L G1 G r k:
    project G r = Some L -> project G1 r = Some (l_end)->
    project (g_open k G1 G) r = Some (l_open k l_end L).
  Proof.
  elim: G L G1 k.
  + by rewrite //=; move=> L G1 k [eq] pro; rewrite -eq.
  + rewrite //=; move=> v L G1 k [eq] pro; rewrite -eq.
    case: ifP.
     * by rewrite -(rwP eqP) pro; move=>->//=; case: ifP; rewrite eq_refl.
     * by rewrite //=; case: ifP.
  + move=> G Ih L G1 k; rewrite //=; case prG: project=> [LT|] //.
    case: ifP=> //; move=> lbi' [eq] pro'.
    * rewrite (@Ih LT G1 (k.+1) prG pro') -eq.
      by rewrite (@l_binds_open 0 (k.+1) LT l_end) //=; move: lbi'; case: ifP.
    * rewrite (@Ih LT G1 (k.+1) prG pro') -eq.
      by rewrite (@l_binds_open 0 (k.+1) LT l_end) //=; move: lbi'; case: ifP.
  + move=> FROM TO CONT Ih L G1 k prG pr1; move: prG=>//=.
    case Pr: project=>[Lc| ]//=.
    rewrite (Ih _ _ _ Pr pr1); case: ifP=>//= d1.
    by case: ifP=>Fr; [move=>[]<-| case: ifP=>Tr; try move=>[]<-].
  Qed.

  Lemma project_open_end L G r : l_binds 0 L -> project G r = Some L
    -> project (unroll G) r = Some (l_open 0 l_end L).
  Proof.
  move=> lbi pro; apply project_open_end_strong; move: pro; rewrite //=.
  by case Prj: project=>[LT| //=]; move=> eq; move: eq Prj lbi=>[<-] Prj; case: ifP.
  Qed.

  Lemma lbinds_open_end_strong L k: l_binds k L -> l_isend (l_open k l_end L).
  Proof.
  elim: L k=> //.
  + by move=> v k; rewrite /l_binds -(rwP eqP)=>->/=; case: ifP; rewrite eq_refl.
  + by move=> L ih k //=; apply ih.
  Qed.


  Lemma lbinds_open_end L: l_binds 0 L -> l_isend (l_open 0 l_end L).
  Proof.
  by apply lbinds_open_end_strong.
  Qed.

  Lemma project_unroll_isend n r G L :
    g_closed G ->
    project G r = Some L ->
    l_isend L ->
    exists L', project (n_unroll n G) r = Some L' /\ l_isend L'.
  Proof.
  elim: n=>[|n Ih]//= in G L *.
  - by move=> closed -> H; exists L.
  - case: G=>[|v|G|p q K] closed.
    + by move=> _ _; exists l_end.
    + by move=>[<-].
    + move=>/=.
      case P:project=>[L'|//]; case: ifP.
      * move=> lbi [eq] isend. apply (@Ih _ (l_open 0 l_end L')).
        - by rewrite /unroll; apply gopen_closed.
        - by apply project_open_end.
        - by apply lbinds_open_end.
      * move=> /eqP-lbi; move: (project_open lbi closed P) => P1 [eq] isend.
        apply (Ih _ (l_open 0 (l_rec L') L')); rewrite //=.
        - by rewrite /unroll; apply gopen_closed.
        - move: isend; rewrite -eq => //=; move=> isend; rewrite isend_open //=.
    + by move=>-> H; exists L.
  Qed.

  Lemma project_unroll m G r L :
    g_closed G ->
    project G r = Some L ->
    exists n1 n2 L',
    project (n_unroll m G) r = Some L' /\ lunroll n1 L = lunroll n2 L'.
    Proof.
    move=> closed Prj; elim: m => [|m Ih]//= in G closed L Prj *; first (by exists 0,0,L).
    move: closed Prj;case:(rec_gty G)=>[[G'->]|/(@matchGrec g_ty)->];last (by exists 0,0,L).
    move=>/=; case Prj: project=>[L'|]//= closed.
    case: ifP=>//.
    + move=> lbi; move: (project_open_end lbi Prj) => Prj'.
      move=> [U]; move: (prj_open_binds Prj lbi Prj')=>END.
      move: closed => /gopen_closed-closed.
      move: (project_unroll_isend m closed Prj' END)=>[L0 [-> L0_END]].
      move: (keep_unrolling L0_END)=>[m' U_END].
      by exists m', m', L0; split=>//; rewrite -U -U_END; case: m' {U_END}.
    + rewrite (rwP eqP).
      move=> nlbi [<-]{L}.
      move: (project_open nlbi closed Prj) => Prj'.
      move: closed => /gopen_closed-closed.
      move: (Ih _ closed _ Prj')=>[n1] [n2] [L0] [PRJ] UNR.
      by exists n1.+1,n2,L0.
  Qed.

  Fixpoint l_isvar L :=
    match L with
    | l_jump v => true
    | l_rec L => l_isvar L
    | _ => false
    end.

  (* Depth that guarantees that we find all occurrences of p *)
  Fixpoint depth_part n p G :=
    match n with
    | 0 => false
    | m.+1 =>
      match G with
      | g_msg q r K => if (p == q) || (p == r) then true
                        else (depth_part m p K.2)
      | g_rec G => depth_part m p G
      | _ => false
      end
    end.

  Lemma depth_next n m p G :
    n <= m ->
    depth_part n p G ->
    depth_part m p G.
  Proof.
    elim: G=>[|v|G Ih|F T C Ih]//= in n m *; case: n=>//; case m=>//.
    - by move=>n {}m/= LE; apply/Ih.
    - by move=>n {}m/= LE; case: ifP=>//= pFT; apply Ih.
  Qed.

  Lemma lbinds_isvar n L : l_binds n L -> l_isvar L.
  Proof. by elim: L n =>//= L Ih n /Ih. Qed.

  Lemma project_depth' p G L :
    project G p == Some L ->
    ~~ (l_isend L || l_isvar L) <->
    exists n, depth_part n p G.
  Proof.
    elim: G =>[|v|G Ih|F T C Ih]/= in L *; try move=>/eqP[<-]/=.
    - by split=>// [[[]//]].
    - by split=>// [[[]//]].
    - case PRJ: project=>[L'|]//; move: PRJ=>/eqP-PRJ.
      case: ifP=> B /eqP-[<-]/=.
      + split=>// [][[|n]]//= H; move: (ex_intro (fun n=>_) n H) => {n H}.
        by move=>/(Ih _ PRJ); rewrite negb_or (lbinds_isvar B) andbC.
      + move: (Ih _ PRJ)=>{}Ih; rewrite Ih=> {Ih B PRJ}.
        split=>[][[|n]]//; last by exists n.
        by exists n.+2.
    - case PRJ: project=>[K|]//=; case: ifP=>//= FT.
      case:ifP=>Fp;[by move:Fp=>/eqP->/eqP[]<-;split=>//= _;exists 1;rewrite//= eq_refl|].
      case:ifP=>Tp;[by move:Tp=>/eqP->/eqP[]<-;split=>//= _;exists 1;rewrite//= eq_refl orbT|].
      move=> /eqP[]<-; rewrite Ih; [split; move=> [n hp]|by rewrite PRJ].
      + by exists n.+1=>//=; rewrite eq_sym Fp eq_sym Tp.
      + by move: hp; case: n=>//= n; rewrite eq_sym Fp eq_sym Tp=>hp; exists n.
  Qed.

  Lemma guarded_closed_notvar L :
    l_closed L ->
    lguarded 0 L ->
    l_isvar L = false.
  Proof.
    rewrite /l_closed; elim: L 0=>//=.
    - by move=> v n; case: ifP=>//; rewrite -cardfs_eq0 cardfs1.
    - by move=>L Ih n; apply/Ih.
  Qed.

  Lemma project_depth p G L :
    g_closed G ->
    project G p == Some L ->
    ~~ l_isend L <-> exists n, depth_part n p G.
  Proof.
    move=> cG PRJ; split.
    + move=>pG; move: (gclosed_lclosed cG PRJ) (project_guarded PRJ)=>cL gL.
      move: (guarded_closed_notvar cL gL)=>/(rwP negPf)/(conj pG)/andP.
      by rewrite -negb_or (project_depth' PRJ).
    + by rewrite -(project_depth' PRJ) negb_or=>/andP-[].
  Qed.

  Lemma depthpart_open v n p G G' :
    depth_part n p G ->
    depth_part n p (g_open v G' G).
  Proof.
    elim: G=>[|v'|G Ih|F T C Ih]//= in n v *; case: n=>// n/=.
    - by apply/Ih.
    - by case: ifP=>//= _; apply Ih.
  Qed.

  Lemma lbinds_depth p G L n k :
    project G p == Some L -> l_binds k L -> depth_part n p G = false.
  Proof.
    move=>/project_depth'=>[][_ /(_ (ex_intro _ n _))-H B]; move: H.
    rewrite negb_or andbC (lbinds_isvar B)=>/=; case: depth_part=>//.
    by move=>/(_ is_true_true).
  Qed.

(*  Lemma prj_all_find C p Ks l Ty G :
    prj_all simple_merge C p = Some Ks -> find_cont C l = Some (Ty, G) ->
    exists L, member (l, (Ty, L)) Ks /\ project simple_merge G p = Some L.
  Proof.
    elim: C Ks=>// [][l'][Ty']G' Ks Ih Ks' /=; rewrite /extend.
    case PRJ: project=>[L|]//; case PRJA: prj_all=>[KsL|]//= [<-]/=.
    case: ifP=>[/eqP->|].
    - by move=>[-><-]; exists L; split=>//; left.
    - by move=> ll' /(Ih _ PRJA)-[L' [M PRJ']]; exists L'; split=>//; right.
  Qed.*)

  Lemma project_parts' p G L :
    project G p == Some L ->
    p \notin participants G ->
    l_isend L || l_isvar L.
  Proof.
    elim: G L=>//=.
    - by move=> L /eqP-[<-].
    - by move=> v L /eqP-[<-].
    - move=> G Ih L; case PRJ: project=>[L'|]//.
      move: PRJ=>/eqP-PRJ EQ Part; move: (Ih _ PRJ Part)=>L'end.
      move: EQ; case: ifP=>//=; [move=> _ /eqP-[<-]//| ].
      by move=> _ /eqP-[<-]/=.
    - move=> q r K Ih L; case PRJ: project=>[KL|]//=.
      case: ifP=>//= qr; rewrite !in_cons.
      case: ifP; [by move=>/eqP-> Leq /norP[]; rewrite eq_refl|].
      case: ifP; [by move=>/eqP-> qp Leq /norP[pq] /norP[]; rewrite eq_refl|].
      by move=> rp qp /eqP[]<- /norP[pq] /norP[pr]; apply Ih; rewrite PRJ.
  Qed.

  Lemma project_parts_end p G L :
    project G p == Some L ->
    l_isend L || l_isvar L ->
    p \notin participants G.
  Proof.
    elim: G L=>//.
    - move=> G Ih L /=; case PRJ: project=>[L'|//]; move: PRJ =>/eqP-PRJ.
      case: ifP=>//.
      + move=> /lbinds_isvar-L'var _ _; apply/(Ih L')=>//.
        by rewrite L'var orbT.
      + by move=> _ /eqP-[<-]/=; apply/Ih.
    - move=>q r K Ih L/=; case PRJ: project=>[KL|//=]; case: ifP=>qr //=.
      case: ifP=> qp; [by move=>/eqP[]<-| case: ifP=> rp; [by move=>/eqP[]<-|]].
      move=>/eqP[]<- eorv; rewrite !in_cons; apply /norP; split; [by rewrite eq_sym qp|].
      by apply /norP; split; [rewrite eq_sym rp| move: eorv; apply Ih; rewrite PRJ].
  Qed.

  Lemma project_parts p G L :
    g_closed G ->
    project G p == Some L ->
    p \notin participants G <->
    l_isend L.
  Proof.
    move=> cG PRJ; split.
    + move=>pG; move: (gclosed_lclosed cG PRJ)=>cL.
      move: (project_guarded PRJ) (project_parts' PRJ pG)=> gL.
      by rewrite (guarded_closed_notvar cL gL) orbC.
    + by move=>H; apply/(project_parts_end PRJ); rewrite H.
  Qed.

  Lemma project_parts_in p G L :
    g_closed G ->
    project G p == Some L ->
    ~~ l_isend L <->
    p \in participants G.
  Proof.
    move=> cG pG; split.
    - by move=> /negPf; apply/contraFT=>/(project_parts cG pG).
    - by move=>P; apply/negPf; move:P; apply/contraTF=>/(project_parts cG pG).
  Qed.

  (*Lemma prjall_dom cG cL p :
    prj_all simple_merge cG p = Some cL -> same_dom (find_cont cG) (find_cont cL).
  Proof.
    elim: cG cL=>//=.
    - by move=>cL [<-]/= l Ty; split=>[][G].
    - move=> [l P] Ks Ih cL; case: project=>[L|]//.
      case ALL: prj_all=>[CL|]//[<-] l' Ty'/=; move: ALL=>/Ih-{}Ih.
      split=>[][G]; rewrite /extend; case: ifP=>_.
      + by move=> [->]/=; exists L.
      + by move=>/(dom Ih).
      + by move=>[<-] _; exists P.2; case: P.
      + by move=>/(dom' Ih).
  Qed.*)

  (*Lemma prjall_fnd cG cL p G Ty L l :
    prj_all simple_merge cG p = Some cL ->
    find_cont cG l = Some (Ty, G) -> find_cont cL l = Some (Ty, L) ->
    project simple_merge G p = Some L.
  Proof.
    elim: cG cL=>//=.
    - move=> [l' [Ty' G']] Ks Ih cL; case PRJ: project=>[L'|]//.
      case ALL: prj_all=>[cL'|]// [<-] {cL}.
      rewrite /extend; case: ifP.
      + by move=>/eqP-> [<-<-]/=; rewrite /extend eq_refl=>[][<-].
      + by move=>NEQ FND1 /=; rewrite /extend NEQ; apply/Ih.
  Qed.*)

  (*Lemma simple_merge_equal L Ks :
    simple_merge L [seq K.2.2 | K <- Ks] = Some L ->
    forall (K : (lbl * (mty  * l_ty))), member K Ks -> K.2.2 = L.
  Proof.
    elim: Ks=>//= K Ks Ih; case: ifP=>//.
    by move=>/eqP-Kl /Ih-{}Ih K0 [<-|/Ih].
  Qed.*)

  Lemma proj_lclosed G p L : g_closed G -> project G p == Some L -> l_closed L.
  Proof.
    rewrite /g_closed/l_closed; move: 0.
    elim: G => [| v | {}G Ih | F T C Ih]/= in L *.
    - by move=>n _ /eqP-[<-].
    - by move=>n H /eqP-[<-]/=.
    - move=>n /Ih-{}Ih; case PRJ: project=>[L'|//].
      case: ifP;[move=>_/eqP-[<-]//|move=>_ /eqP-[<-]/=].
      by apply/Ih/eqP.
    - move=>n; case PRJ: project=>[CL|//]; case: ifP=>//= FT.
      case: ifP=>Fp; [by move=> cl /eqP[]<-//=; apply (Ih _ _ cl); rewrite PRJ|].
      case: ifP=>Tp;  [by move=> cl /eqP[]<-//=; apply (Ih _ _ cl); rewrite PRJ|].
      by move=> cl /eqP[]<-; apply (Ih _ _ cl); rewrite PRJ.
  Qed.

(*  Lemma proj_lne G p L :
    non_empty_cont G -> project simple_merge G p == Some L -> l_non_empty_cont L.
  Proof.
    rewrite /g_closed/l_closed.
    elim: G => [| v | {}G Ih | F T C Ih]/= in L *; rewrite -/prj_all.
    - by move=>_ /eqP-[<-].
    - by move=>H /eqP-[<-]/=.
    - move=>/Ih-{}Ih; case PRJ: project=>[L'|//].
      case: ifP;[move=>_/eqP-[<-]//|move=>_ /eqP-[<-]/=].
      by apply/Ih/eqP.
    - move=>/andP-[NE]; rewrite -/(prj_all _ _).
      case ALL: prj_all=>[CL|//]; move: (prjall_dom ALL).
      move=>/samedom_nilp/contra/(_ NE)=>nilCL; move: ALL=>/eqP-ALL.
      move=>/forallbP/forall_member/member_map=>{}NE.
      do ! case: ifP=>// _.
      + move=>/eqP-[<-]/=; rewrite nilCL/=.
        apply/forallbP/forall_member/member_map=> K M.
        move: (prjall_some2 ALL M)=>[G][MG]/eqP-PRJ.
        by apply (Ih _ MG _ (NE _ MG) PRJ).
      + move=>/eqP-[<-]/=; rewrite nilCL/=.
        apply/forallbP/forall_member/member_map=> K M.
        move: (prjall_some2 ALL M)=>[G][MG]/eqP-PRJ.
        by apply (Ih _ MG _ (NE _ MG) PRJ).
      + move=>MRG; move: (prjall_merge ALL MRG)=>PRJ.
        move: ALL MRG=>/eqP-ALL /eqP-MRG; move: (prjall_merge_cons ALL MRG).
        by move=>[K]M; apply/(Ih _ M _ (NE _ M) (PRJ _ M)).
  Qed.*)

End IProject.

Section GTree.

  CoInductive rg_ty :=
  | rg_end
  | rg_msg (FROM TO : role)
           (CONT : mty * rg_ty).

  Unset Elimination Schemes.
  Inductive ig_ty :=
  | ig_end (CONT : rg_ty)
  | ig_msg (ST : bool)
           (FROM TO : role)
           (CONT : mty * ig_ty).
  Set Elimination Schemes.

  (*Definition P_option A (P : A -> Type) (C : option A) : Type :=
    match C with
    | Some X => P X
    | None => True
    end.*)

  (*Definition P_prod A B (P : B -> Type) (C : A * B) : Type :=
    match C with
    | (X, Y)=> P Y
    end.*)

  Lemma ig_ty_ind
        (P : ig_ty -> Prop)
        (P_end : forall CONT, P (ig_end CONT))
        (P_msg : (forall ST FROM TO CONT,
                     P CONT.2 -> P (ig_msg ST FROM TO CONT)))
    : forall G, P G.
  Proof.
    fix Ih 1; case.
    - by apply: P_end.
    - move=> ST F T C; apply: P_msg.
        by apply Ih.
  Qed.

  Lemma ig_ty_rect
      (P : ig_ty -> Type)
      (P_end : forall CONT, P (ig_end CONT))
      (P_msg : (forall ST FROM TO CONT,
                   P CONT.2 -> P (ig_msg ST FROM TO CONT)))
  : forall G, P G.
  Proof.
    fix Ih 1; case.
    - by apply: P_end.
    - move=> ST F T C; apply: P_msg.
      by apply Ih.
  Qed.

  Inductive part_of: role -> rg_ty -> Prop :=
  | pof_from F T C: part_of F (rg_msg F T C)
  | pof_to F T C: part_of T (rg_msg F T C)
  | pof_cont p F T C: part_of p C.2 -> part_of p (rg_msg F T C).

(*Inductive part_of_all: role -> rg_ty -> Prop :=
  | pall_from F T C: part_of_all F (rg_msg F T C)
  | pall_to F T C: part_of_all T (rg_msg F T C)
  | pall_cont p F T C :
      P_all (part_of_all p) C -> part_of_all p (rg_msg F T C).

(* Needed to build the next global type in a step  *)
Inductive part_of_allT: role -> rg_ty -> Type :=
  | pallT_from F T C: part_of_allT F (rg_msg F T C)
  | pallT_to F T C: part_of_allT T (rg_msg F T C)
  | pallT_cont p F T C :
      (forall l Ty G, C l = Some (Ty, G) -> part_of_allT p G) ->
      part_of_allT p (rg_msg F T C).*)

  Inductive iPart_of: role -> ig_ty -> Prop :=
  | ipof_end p cG: part_of p cG -> iPart_of p (ig_end cG)
  | ipof_from F T C: iPart_of F (ig_msg false F T C)
  | ipof_to o F T C: iPart_of T (ig_msg o F T C)
  | ipof_cont p o F T C: iPart_of p C.2 -> iPart_of p (ig_msg o F T C).

  Lemma rgend_part p G : part_of p G -> G = rg_end -> False.
  Proof. by move=>[]. Qed.

  (*Lemma pall_inv F T C G p :
    part_of_all p G -> G = rg_msg F T C -> F <> p -> T <> p ->
    (forall l Ty G, C l = Some (Ty, G) -> part_of_all p G).
  Proof.
    by move=>[ F' T' C' [->]//
             | F' T' C' [_ ->]//
             |{}p F' T' C' ALL [_ _ <-] _ _ l Ty {}G /ALL
             ].
Defined.*)

(*Fixpoint find_partsc p G (H : part_of_all p G) {struct H}
  : part_of_allT p G
  :=
  match G as G0 return G = G0 -> part_of_allT p G0 with
  | rg_msg F T C => fun EQ =>
                      match @eqP _ F p with
                      | ReflectT pF => match EQ, pF with
                                       | erefl, erefl => pallT_from F T C
                                       end
                      | ReflectF pF =>
                        match @eqP _ T p with
                        | ReflectT pT => match EQ, pT with
                                         | erefl, erefl => pallT_to F T C
                                         end
                        | ReflectF pT =>
                          pallT_cont F T
                                     (fun l Ty G Cl =>
                                        find_partsc (pall_inv H EQ pF pT Cl))
                        end
                      end
  | rg_end => fun E => match rgend_part H E with end
  end erefl.*)

  Definition rg_unr (G : rg_ty) : ig_ty :=
    match G with
    | rg_msg F T C => ig_msg false F T (C.1, ig_end C.2)
    | rg_end => ig_end rg_end
    end.

  Definition grel := g_ty -> rg_ty -> Prop.
  Inductive g_unroll (r : grel) : grel :=
  | gu_end :
      g_unroll r g_end rg_end
  | gu_rec IG CG :
      r (g_open 0 (g_rec IG) IG) CG ->
      g_unroll r (g_rec IG) CG
  | gu_msg FROM TO t IG' CG':
      r IG' CG' ->
      g_unroll r (g_msg FROM TO (t,IG')) (rg_msg FROM TO (t,CG')).
  Definition GUnroll IG CG : Prop := paco2 g_unroll bot2 IG CG.

  Derive Inversion gunr_inv with (forall r G cG, g_unroll r G cG) Sort Prop.
  Hint Constructors g_unroll.

  Lemma gunroll_monotone : monotone2 g_unroll.
  Proof.
    move=> IG CG r r' U H; move: IG CG U.
    elim=>[|V|G IH|F T C IH] CG;
            case E:_ _/ =>[|G' CG' R|F' T' C' CC DOM U]//.
    - by move: E R=>[<-]{G'} /H; constructor.
    - by constructor=>//; apply H.
  Qed.
  Hint Resolve gunroll_monotone.

  Lemma gunroll_unfold r iG cG
    : paco2 g_unroll r iG cG -> @g_unroll (upaco2 g_unroll r) iG cG.
  Proof. by move/(paco2_unfold gunroll_monotone). Qed.

  Lemma g_unroll_rec (r : grel) n iG cG :
    (forall n IG CG, r IG CG -> paco2 g_unroll r (n_unroll n IG) CG) ->
    paco2 g_unroll r iG cG <-> paco2 g_unroll r (n_unroll n iG) cG.
  Proof.
    move=> H; split.
    - elim: n =>// n Ih in iG cG *.
      move=> /gunroll_unfold-[]//=.
      + by apply/paco2_fold.
      + by move=>IG CG  [/Ih//|/H].
      + by move=>F T IC CC DOM UA; apply/paco2_fold; constructor.
    - elim: n =>// n Ih in iG cG *.
        by case: iG=>//= G H1; apply/paco2_fold; constructor; left; apply/Ih.
  Qed.

  Lemma GUnroll_ind n iG cG :
    GUnroll iG cG <-> GUnroll (n_unroll n iG) cG.
  Proof. by apply/g_unroll_rec. Qed.

  Lemma gen2 A B (x' : A) (y' : B) Q P :
    (forall x y, Q x y -> x = x' -> y = y' -> P) ->
    Q x' y' -> P.
  Proof. by move=>H /H/( _ erefl erefl).  Qed.

  Lemma r_in_unroll_msg r G p q K :
    GUnroll G (rg_msg p q K) ->
    guarded 0 G ->
    g_closed G ->
    (r == p) || (r == q) ->
    r \in participants G.
  Proof.
    move=> GU GG CG r_pq; apply/(r_in_unroll_rec_depth).
    move: (unroll_guarded CG GG) r_pq => H.
    move: GU=>/(GUnroll_ind (rec_depth G)); move: H.
    move: (n_unroll _ G) => [|v|G'|p' q' Ks'].
    - by move=>_; apply: gen2=>iG cG /gunroll_unfold-[].
    - by move=>_; apply: gen2=>iG cG /gunroll_unfold-[].
    - by move=>/(_ G')/eqP.
    - move=>_; apply: gen2=>iG cG /gunroll_unfold-[]//.
      move=>F T t IG' CG' []//= GU [<-<-<-] [<-<- _]; rewrite !in_cons.
      by case: eqP=>//= _ ->.
  Qed.

  Lemma g_closed_unroll n iG : g_closed iG -> g_closed (n_unroll n iG).
  Proof. by elim: n iG=>[|n Ih]//=; case=>//= iG /gopen_closed/Ih. Qed.

  Lemma g_guarded_unroll iG :
    g_closed (g_rec iG) -> guarded 0 (g_rec iG) -> guarded 0 (unroll iG).
  Proof.
    move=> C GG; have GG': (guarded 1 iG) by move:GG C=>/=; case: iG.
    move: (guarded_open 0 GG C GG')=>/guarded_depth_gt.
      by move=>/(_ _ _ (leq0n 1) (gopen_closed C)).
  Qed.

  Lemma g_guarded_nunroll n iG
    : g_closed iG -> guarded 0 iG -> guarded 0 (n_unroll n iG).
  Proof.
    elim: n iG=>[|n Ih]//;case=>// iG CG /(g_guarded_unroll CG)/Ih-H/=.
      by apply/H/gopen_closed.
  Qed.

  CoFixpoint g_expand (g : g_ty) : rg_ty :=
    match n_unroll (rec_depth g) g with
    | g_msg F T K => rg_msg F T (K.1, g_expand K.2)
    | _ => rg_end
    end.

  Lemma rgtyU G : G = match G with
                      | rg_msg F T C => rg_msg F T C
                      | rg_end => rg_end
                      end.
  Proof. by case: G. Qed.

  Definition g_expand' G :=
    match G with
    | g_msg F T K => rg_msg F T (K.1, g_expand K.2)
    | _ => rg_end
    end.

  Lemma g_expand_once G : g_expand G = g_expand' (n_unroll (rec_depth G) G).
  Proof.
      by rewrite (rgtyU (g_expand _))/g_expand /g_expand'-rgtyU-/g_expand.
  Qed.

  Lemma g_expand_unr G :
    guarded 0 G ->
    g_closed G ->
    GUnroll G (g_expand G).
  Proof.
    move=>gG cG; rewrite g_expand_once.
    move: {-1}(g_expand' _) (erefl (g_expand' (n_unroll (rec_depth G) G))).
    move=>CG ECG; move: G CG {ECG gG cG}(conj ECG (conj gG cG)).
    apply/paco2_acc=>r _ /(_ _ _ (conj erefl (conj _ _)))-CIH.
    move=> G CG [<-]{CG} [gG cG]; case: G cG gG.
    - by move=>_ _ /=; apply/paco2_fold; constructor.
    - by move=>V /closed_not_var/(_ V)/eqP/(_ erefl).
    - move=>G cG gG /=;apply/paco2_fold.
      constructor; right; have gG': guarded 1 G by move: gG.
      rewrite (guarded_recdepth (m:=0) gG' _ (g_rec G)) //.
      apply/CIH; [by apply/g_guarded_unroll|by apply/gopen_closed].
    - move=>F T C//= cG gG; apply/paco2_fold.
      rewrite (surjective_pairing C); constructor; right.
      by rewrite g_expand_once; apply CIH.
  Qed.

  Lemma expand_g_end g
    : is_end g -> g_expand g = rg_end.
  Proof.
    rewrite (rgtyU (g_expand _))/=.
    suff: is_end g -> n_unroll (rec_depth g) g = g_end by move=>E /E->.
    move: {-1}(rec_depth g) (erefl (rec_depth g))=> n.
    elim: n g; first by case=>//.
    move=>n Ih; case=>//= g [] RD END; move: (recdepth_unroll END) RD=>->{}RD.
      by move: END=>/isend_unroll; apply/Ih.
  Qed.

End GTree.

Section LTree.

  CoInductive rl_ty :=
  | rl_end
  | rl_msg (a : l_act) (R : role) (C : (mty * rl_ty))
  .

  Definition rlty_rel := rl_ty -> rl_ty -> Prop.
  Inductive EqL_ (r : rlty_rel) : rlty_rel :=
  | el_end : @EqL_ r rl_end rl_end
  | el_msg a p t C1 C2 : r C1 C2 ->
                       @EqL_ r (rl_msg a p (t,C1)) (rl_msg a p (t,C2)).
  Hint Constructors EqL_.
  Definition EqL L1 L2 := paco2 EqL_ bot2 L1 L2.
  Derive Inversion EqL__inv with (forall r L0 L1, EqL_ r L0 L1) Sort Prop.

  Lemma EqL_monotone : monotone2 EqL_.
  Proof.
    move=>L1 L2 r r' E H; elim: E =>[|a p C1 C2 ]//; constructor=>//.
      by apply H.
  Qed.
  Hint Resolve EqL_monotone.

  Lemma EqL_refl CL : EqL CL CL.
  Proof.
    move: CL {-1 3}CL (erefl CL).
    apply/paco2_acc=> r0 _ CIH CL CL'<- {CL'}.
    apply/paco2_fold.
    case: CL=>//a R C; rewrite (surjective_pairing C); constructor; right.
    by apply CIH.
  Qed.

  Lemma EqL_sym CL1 CL2 : EqL CL1 CL2 -> EqL CL2 CL1.
  Proof.
    move: CL2 CL1; apply/paco2_acc=>r0 _ CIh L0 L1.
    move=>/(paco2_unfold EqL_monotone); elim/EqL__inv=>// _.
    + by move=> _ _; apply/paco2_fold; constructor.
    + move=> a p t C1 C2 []hp _ _ //=; apply/paco2_fold; constructor.
      by right; apply CIh.
  Qed.

  Lemma EqL_r_end_inv_aux lT lT':
    EqL lT lT' -> lT' = rl_end -> lT = rl_end.
  Proof.
      by move=> hp; punfold hp; move: hp => [] //=.
  Qed.

  Lemma EqL_r_end_inv lT:
    EqL lT rl_end -> lT = rl_end.
  Proof.
      by move=> hp; apply (EqL_r_end_inv_aux hp).
  Qed.

  Lemma EqL_r_msg_inv_aux lT lT' a p C':
    EqL lT lT' -> lT' = rl_msg a p C' ->
    exists C, C.1 = C'.1 /\ EqL C.2 C'.2 /\ lT = rl_msg a p C.
  Proof.
    move=> hp; punfold hp; move: hp=>[] //=.
    move=> a0 p0 t C1 C2 []//= eql [eq1 eq2 eq3].
    by exists (t,C1); rewrite eq1 eq2 -eq3.
  Qed.

  Lemma EqL_r_msg_inv a p C' lT:
    EqL lT (rl_msg a p C') ->
    exists C, C.1 = C'.1 /\ EqL C.2 C'.2 /\ lT = rl_msg a p C.
  Proof.
      by move=> hp; apply: (EqL_r_msg_inv_aux hp).
  Qed.

  Lemma EqL_l_msg_inv_aux lT lT' a p C:
    EqL lT lT' -> lT = rl_msg a p C ->
    exists C',  C.1 = C'.1 /\ EqL C.2 C'.2 /\ lT' = rl_msg a p C'.
  Proof.
    move=> hp; punfold hp; move: hp => [] //=.
    move=> a0 p0 t C1 C2 []//= eql [eq1 eq2 eq3].
    by exists (t,C2); rewrite eq1 eq2 -eq3.
  Qed.

  Lemma EqL_l_msg_inv a p C lT':
    EqL (rl_msg a p C) lT' ->
  exists C',  C.1 = C'.1 /\ EqL C.2 C'.2 /\ lT' = rl_msg a p C'.
  Proof.
      by move=> hp; apply: (EqL_l_msg_inv_aux hp).
  Qed.

  Lemma EqL_trans lT1 lT2 lT3:
    EqL lT1 lT2 -> EqL lT2 lT3 -> EqL lT1 lT3.
  Proof.
    move=> hp1 hp2; move: (conj hp1 hp2) => {hp1 hp2}.
    move=> /(ex_intro (fun lT=> _) lT2) {lT2}; move: lT1 lT3.
    apply /paco2_acc; move=> r0 _ CIH lT1 lT3; elim=> lT2 [].
    case: lT3 =>//=.
    + move=> eql12 eql23; move: (EqL_r_end_inv eql23) eql12 =>->.
      move=> eql12; move: (EqL_r_end_inv eql12) =>->.
        by apply /paco2_fold; apply el_end.
    + move=> a r C3 eql12 eql23; move: (EqL_r_msg_inv eql23)=>[C2 [eqC23 [eqlC23 lT2eq]]].
      move: eql12; rewrite lT2eq=> eql12.
      move: (EqL_r_msg_inv eql12)=>[C1 [eqC12 [eqlC12 lT1eq]]]; rewrite lT1eq.
      apply /paco2_fold; rewrite (surjective_pairing C1) (surjective_pairing C3) eqC12 eqC23.
      by apply el_msg; right; apply CIH; exists C2.2.
  Qed.


  Definition lty_rel := rel2 lty (fun=>rl_ty). Print l_act.
  Inductive l_unroll (r : lty_rel) : lty -> rl_ty -> Prop :=
  | lu_end :
      @l_unroll r l_end rl_end
  | lu_rec L L' :
      r (l_open 0 (l_rec L) L) L' ->
      @l_unroll r (l_rec L) L'
  | lu_send p t K C :
      r K C ->
      @l_unroll r (l_send p t K) (rl_msg a_send p (t,C))
  | lu_recv p t K C :
      r K C ->
      @l_unroll r (l_recv p t K) (rl_msg a_recv p (t,C))
  .
  Hint Constructors l_unroll.

  Scheme lunroll_ind := Induction for l_unroll Sort Prop.

  Lemma l_unroll_monotone : monotone2 l_unroll.
  Proof.
    move=>IL CL r r' U H; move: IL CL U.
    elim=>[|V|L IH|q t Lc IH|p t Lc IH] CL//=;
                              case E:_ _/ =>[|G G' R|q' t' Lc' D U|p' t' Lc' D U]//.
  - by move: E R => [<-] /H; constructor.
  - by constructor=>//; apply H.
  - by constructor=>//; apply H.
  Qed.
  Hint Resolve l_unroll_monotone.

  Definition LUnroll IL CL := paco2 l_unroll bot2 IL CL.

  Definition lu_unfold := paco2_unfold l_unroll_monotone.

  Lemma LUnroll_ind n iG cG :
    LUnroll iG cG <-> LUnroll (lunroll n iG) cG.
  Proof.
    split.
    - elim: n =>[//|n Ih] in iG cG *; case: iG=>//= iL /lu_unfold.
        by case E: _ _/ => [|L L' [|]||]//; move: E=>[->]; apply/Ih.
    - elim: n =>// n Ih in iG cG *; case: iG=>//= G /Ih-H1.
        by apply/paco2_fold; constructor; left.
  Qed.

  Lemma lunroll_end cL :
    LUnroll l_end cL -> cL = rl_end.
  Proof. by move=> /lu_unfold-LU; case Eq: _ _ / LU. Qed.

  Lemma l_guarded_unroll iG :
    l_closed (l_rec iG) -> lguarded 0 (l_rec iG) ->
    lguarded 0 (l_open 0 (l_rec iG) iG).
  Proof.
    move=> C GG; have GG': (lguarded 1 iG) by move:GG C=>/=; case: iG.
      by move: (lguarded_open 0 GG C GG')=>/lguarded_depth_gt/(_ (lopen_closed C)).
  Qed.

  Lemma l_guarded_nunroll n iL :
    l_closed iL -> lguarded 0 iL -> lguarded 0 (lunroll n iL).
  Proof.
    elim: n iL=>[|n Ih]//;case=>// iG CG /(l_guarded_unroll CG)/Ih-H/=.
      by apply/H/lopen_closed.
  Qed.

  Lemma l_closed_unroll n iL :
    l_closed iL -> l_closed (lunroll n iL).
  Proof. by elim: n iL=>[|n Ih]//=; case=>//= iG /lopen_closed/Ih. Qed.

  Lemma v_lty L : (exists v, L = l_jump v) \/ (forall v, L != l_jump v).
  Proof. by case: L; try (by right); move=>v;left;exists v. Qed.

  CoFixpoint l_expand (l : lty) : rl_ty :=
    match lunroll (lrec_depth l) l with
    | l_send q t L => rl_msg a_send q (t, l_expand L)
    | l_recv p t L => rl_msg a_recv p (t, l_expand L)
    | _ => rl_end
    end.

  Lemma rltyU L : L = match L with
                      | rl_msg a T C => rl_msg a T C
                      | rl_end => rl_end
                      end.
  Proof. by case: L. Qed.

  (*Fixpoint l_non_empty_cont G :=
    match G with
    | l_msg _ _ Ks => ~~ nilp Ks && all id [seq l_non_empty_cont K.2.2 | K <- Ks]
    | l_rec G => l_non_empty_cont G
    | _ => true
    end.*)

  Definition l_precond L :=
    l_closed L && lguarded 0 L. (*&& l_non_empty_cont L.*)

(*  Lemma lne_shift d n G :
    l_non_empty_cont G ->
    l_non_empty_cont (l_shift d n G).
  Proof.
    elim: G=>[|v|L Ih|a p Ks Ih]//= in n *.
    - by case: ifP.
    - by apply/Ih.
    - move=>/andP-[NIL NE]; apply/andP;split;first by move: Ks NIL {Ih NE}=>[].
      rewrite -map_comp /comp/=; move: NE=>/forallbP/forall_member/member_map.
      move=>/(_ _ ((rwP (memberP _ _)).2 _))=> H.
      apply/forallbP/forall_member/member_map=>b /(rwP (memberP _ _))-IN.
        by apply: (Ih _ IN _ (H _ IN)).
  Qed.

  Lemma lne_open n G G' :
    l_non_empty_cont G -> l_non_empty_cont G' -> l_non_empty_cont (l_open n G' G).
  Proof.
    move=> NE1 NE2; move: NE1.
    elim: G n=>//.
    - by move=> v n; rewrite /=; case: ifP=>// _ _; apply/lne_shift.
    - by move=> G Ih n /=; apply/Ih.
    - move=> a T C Ih n /=; case: C Ih=>//= K Ks Ih /andP-[NE_K ALL].
      have K_in: K \in K :: Ks by rewrite in_cons !eq_refl.
      rewrite (Ih K K_in n NE_K) /= {NE_K}.
      move: ALL=>/forallbP/forall_member/member_map-ALL.
      apply/forallbP/forall_member/member_map/member_map=>/=K' M.
      move: M (ALL _ M)=>/memberP-M {}ALL.
      have K'_in : K' \in K :: Ks by rewrite in_cons M orbT.
        by apply/(Ih _ K'_in n)/ALL.
  Qed.

  Lemma lne_unr n G : l_non_empty_cont G -> l_non_empty_cont (lunroll n G).
  Proof.
    elim: n G=>[//|n/=] Ih; case=>//= G NE.
    have: l_non_empty_cont (l_rec G) by [].
      by move=>/(lne_open 0 NE); apply/Ih.
  Qed.*)

  Definition l_expand' L :=
    match L with
    | l_send r t L => rl_msg a_send r (t, l_expand L)
    | l_recv r t L => rl_msg a_recv r (t, l_expand L)
    | _ => rl_end
    end.

  Lemma l_expand_once L : l_expand L = l_expand' (lunroll (lrec_depth L) L).
  Proof.
      by rewrite (rltyU (l_expand _)) /l_expand /l_expand'-rltyU-/l_expand.
  Qed.

  Lemma l_expand_unr L :
    lguarded 0 L ->
    l_closed L ->
    LUnroll L (l_expand L).
  Proof.
    move=>gG cG; rewrite l_expand_once.
    move: {-1}(l_expand' _) (erefl (l_expand' (lunroll (lrec_depth L) L))).
    move=>CG ECG; move: L CG {ECG gG cG}(conj ECG (conj gG cG)).
    apply/paco2_acc=>r _ /(_ _ _ (conj erefl (conj _ _)))-CIH.
    move=> G CG [<-]{CG} [gG cG]; case: G cG gG.
    - by move=>_ _ /=; apply/paco2_fold; constructor.
    - by move=>V /lclosed_not_var/(_ V)/eqP/(_ erefl).
    - move=>G cG gG /=;apply/paco2_fold.
      constructor; right; have gG': lguarded 1 G by move: gG.
      rewrite (lguarded_recdepth (m:=0) gG' _ (l_rec G)) //.
      apply/CIH; [by apply/l_guarded_unroll| by apply/lopen_closed].
    - move=>F T C//= cG gG; apply/paco2_fold.
      constructor; right.
        by rewrite l_expand_once; apply CIH.
    - move=>F T C//= cG gG; apply/paco2_fold.
      constructor; right.
      by rewrite l_expand_once; apply CIH.
  Qed.

  Lemma LUnroll_EqL L CL CL' : LUnroll L CL -> EqL CL CL' -> LUnroll L CL'.
  Proof.
    move=> H1 H2; move: L CL' {H1 H2 CL} (ex_intro (fun=>_) CL (conj H1 H2)).
    apply/paco2_acc=>r _ /(_ _ _ (ex_intro _ _ (conj _ _)))-CIH.
    move=> L CL [CL'][LU]EQ.
    move: LU EQ=>/(paco2_unfold l_unroll_monotone); case.
    - move=>/(paco2_unfold EqL_monotone); case E: _ _ / =>//.
        by apply/paco2_fold; constructor.
    - move=> G G' [/CIH-GU|//] /GU-H.
        by apply/paco2_fold; constructor; right.
    - move=> p t K C []//= LU /EqL_l_msg_inv[CC//= [-> [eql ->]]].
      apply /paco2_fold; rewrite (surjective_pairing CC)//=; constructor; right.
        by apply (CIH _ _ _ LU).
    - move=> p t K C []//= LU /EqL_l_msg_inv[CC//= [-> [eql ->]]].
      apply /paco2_fold; rewrite (surjective_pairing CC)//=; constructor; right.
      by apply (CIH _ _ _ LU).
  Qed.

  Lemma lunroll_inf Li Lr Li' :
    lunroll (lrec_depth Li) Li = l_rec Li' ->
    LUnroll Li Lr.
  Proof.
    rewrite lunroll_nopen=>/nopen_rec-[m]; rewrite add0n=>[][BND].
    rewrite {2}(nrec_lrecdepthI Li).
    move: (getnr_nonrec Li) BND; case: (get_nr Li)=>//= v _ /eqP->.
    move: (lrec_depth Li)=>d {v Li Li'}.
    move EQ: (n_rec d (l_jump m))=>Li LT; move: {EQ LT}(conj EQ LT)=>H.
    move: (ex_intro (fun=>_) m (ex_intro (fun=>_) d H))=>{m d}H.
    move: Li Lr H; apply/paco2_acc=> r _.
    move=>/(_ _ _ (ex_intro _ _ (ex_intro _ _ (conj erefl _ ))))-CIH Li Lr.
    move=>[m][n][<-]{Li}; case: n=>//= n LE.
    apply/paco2_fold; constructor; move: LE; case: (boolP (n == m)).
    - move=>/eqP-> _; rewrite lopen_nrec add0n eq_refl.
      rewrite -/(n_rec m.+1 _) lshift_nrec // nrec_twice addnS.
        by right; apply/CIH; apply: leq_addr.
    - move=> H0 H1; move: {H0 H1} (conj H0 H1)=>/andP.
      rewrite eq_sym -ltn_neqAle => LE; rewrite lopen_bound //.
        by right; apply/CIH.
  Qed.

  Fixpoint expand_env (e : seq (role * lty)) : {fmap role -> rl_ty} :=
    match e with
    | [::] => [fmap]
    | (k, v) :: t => (expand_env t).[k <- l_expand v]
    end%fmap.

  Lemma in_expanded_env (e : seq (role * lty)) p :
    (omap l_expand (find_cont e p) = (expand_env e).[? p])%fmap.
  Proof.
    elim: e=>//=; first by rewrite fnd_fmap0.
    move=>[k v] t; rewrite fnd_set /extend; case: ifP=>[/eqP->|neq].
    + by rewrite eq_refl.
    + by rewrite eq_sym neq.
  Qed.

  Lemma lunroll_isend L CL : LUnroll L CL -> l_isend L -> CL = rl_end.
  Proof.
    move=> LU /keep_unrolling-[k END]; move: LU=>/(LUnroll_ind k).
      by move: END=><-; apply/lunroll_end.
  Qed.

End LTree.


Section CProject_defs.

  Inductive WF_ (r : rg_ty -> Prop) : rg_ty -> Prop :=
  | WF_end : WF_ r rg_end
  | WF_msg F T C :
      F != T -> r C.2 -> WF_ r (rg_msg F T C).
  Definition WF := paco1 WF_ bot1.

  Lemma WF_mon : monotone1 WF_.
  Proof.
    move=> G r r' [].
    - by move=> _; apply/WF_end.
    - by move=> F T C FT H LE; apply/WF_msg=>//=; apply LE.
  Qed.

  (*Projection: Coinductive Definition*)


  Definition proj_rel := rg_ty -> rl_ty -> Prop.
  Inductive Proj_ (p : role) (r : proj_rel) : proj_rel :=
  | prj_end G : ~ part_of p G -> WF G -> Proj_ p r G rl_end
  | prj_send q CG CL : p != q -> CG.1 = CL.1 -> r CG.2 CL.2 ->
      Proj_ p r (rg_msg p q CG) (rl_msg a_send q CL)
  | prj_recv q CG CL : p != q -> CG.1 = CL.1 -> r CG.2 CL.2 ->
      Proj_ p r (rg_msg q p CG) (rl_msg a_recv q CL)
  | prj_cnt q s CG L:
      q != s -> p != q -> p != s ->
      part_of p CG.2 -> r CG.2 L ->
      Proj_ p r (rg_msg q s CG) L
  .
  Hint Constructors Proj_.
  Derive Inversion Proj__inv  with (forall p r G L, Proj_ p r G L) Sort Prop.

  Lemma Proj_monotone p : monotone2 (Proj_ p).
  Proof.
    rewrite /monotone2; move=> x0 x1 r r' it LE; move: it.
    case=>//; try by move=> q CG CL neq eqt HP; constructor =>//=; apply LE.
      by move=>G part; constructor.
  Qed.
  Hint Resolve Proj_monotone.

  Definition Project p CG CL := paco2 (Proj_ p) bot2 CG CL.

  Lemma Project_inv (p : role) (G : rg_ty) (L : rl_ty)
        (P : role -> rg_ty -> rl_ty -> Prop) :
    (forall G0, G0 = G -> rl_end = L -> ~ part_of p G0 -> WF G0 -> P p G0 rl_end) ->
    (forall q CG CL,
       rg_msg p q CG = G -> rl_msg a_send q CL = L ->
       p != q -> CG.1 = CL.1 -> Project p CG.2 CL.2 ->
       P p (rg_msg p q CG) (rl_msg a_send q CL)) ->
    (forall q CG CL,
       rg_msg q p CG = G -> rl_msg a_recv q CL = L ->
       p != q -> CG.1 = CL.1 -> Project p CG.2 CL.2 ->
       P p (rg_msg q p CG) (rl_msg a_recv q CL)) ->
    (forall (q s : role) CG L0,
        q != s -> p != q -> p != s ->
        rg_msg q s CG = G -> L0 = L ->
        part_of p CG.2 -> Project p CG.2 L0 ->
        P p (rg_msg q s CG) L) ->
    Project p G L -> P p G L.
  Proof.
    move=> Hend Hsnd Hrcv Hcnt /(paco2_unfold (Proj_monotone (p:=p))).
    elim/Proj__inv =>/(paco2_fold _ _ _ _); rewrite -/(Project p G L) => PRJ.
    + by move=> G0 PART WF EQ1 EQ2; apply/Hend.
    + by move=> q CG CL pq eqt []//= IH EQ1 EQ2; apply/Hsnd.
    + by move=> q CG CL pq eqt []//= IH EQ1 EQ2; apply/Hrcv.
    + by move=> q s CG L0 qs pq ps pof []//= IH EQ1 EQ2; apply/Hcnt.
  Qed.

  Inductive IProj (p : role) : ig_ty -> rl_ty -> Prop :=
  | iprj_end CG CL :
      Project p CG CL ->
      IProj p (ig_end CG) CL
  | iprj_send1 q CG CL :
      p != q ->
      CG.1 = CL.1 ->
      IProj p CG.2 CL.2 ->
      IProj p (ig_msg false p q CG) (rl_msg a_send q CL)
  | iprj_send2 q r CG L :
      p != r ->
      q != r ->
      IProj p CG.2 L ->
      IProj p (ig_msg true q r CG) L
  | iprj_recv b q CG CL :
      p != q ->
      CG.1 = CL.1 ->
      IProj p CG.2 CL.2 ->
      IProj p (ig_msg b q p CG) (rl_msg a_recv q CL)
  | iprj_cnt q s CG L :
      q != s ->
      p != q ->
      p != s ->
      IProj p CG.2 L ->
      IProj p (ig_msg false q s CG) L
  .


  Lemma IProj_end_inv_aux p GG CG CL:
    IProj p GG CL -> GG = ig_end CG ->
    Project p CG CL.
  Proof.
  by case=>//; move=> CG0 CL0 ipro [CGeq]; rewrite -CGeq.
  Qed.

  Lemma IProj_end_inv p CG CL:
    IProj p (ig_end CG) CL -> Project p CG CL.
  Proof.
  by move=> hp; apply (IProj_end_inv_aux hp).
  Qed.

  Lemma IProj_send1_inv_aux F T C G L:
    IProj F G L -> G = (ig_msg false F T C) ->
    F != T /\ (exists lC, L = rl_msg a_send T lC /\
    C.1 = lC.1 /\ IProj F C.2 lC.2).
  Proof.
  case=>//=.
  + move=> q gC lC neq eqt hp [eq1 eq2].
    by rewrite -eq1 -eq2; split; [| exists lC;  split; [ |]].
  + move=> o q gC lC neq eqt hp [eq1 eq2 eq3 eq4].
    by move: neq; rewrite eq2 -(rwP negP).
  + move=> q s gC {}L neq1 neq2 neq3 hp [eq1 eq2 eq3].
    by move: neq2; rewrite eq1 eq_refl.
  Qed.

  Lemma IProj_send1_inv F T C L:
    IProj F (ig_msg false F T C) L ->
    F != T /\ (exists lC, L = rl_msg a_send T lC /\
    C.1 = lC.1 /\ IProj F C.2 lC.2).
  Proof.
  by move=> hp; apply: (IProj_send1_inv_aux hp).
  Qed.


  Lemma IProj_send2_inv_aux p F T C G L:
    IProj p G L -> G = (ig_msg true F T C) -> p != T ->
    F != T /\ IProj p C.2 L.
  Proof.
  case=>//.
  + by move=> q r gC {}L neq1 neq2 hp [<-<-<-] neq3; split.
  + by move=> o- q gC lC neq eqt hp [_<-<-<-]; rewrite eq_refl.
  Qed.

  Lemma IProj_send2_inv p F T C L:
    IProj p (ig_msg true F T C) L -> p != T ->
    F != T /\ IProj p C.2 L.
  Proof.
  by move=> hp; apply: (IProj_send2_inv_aux hp).
  Qed.

 Lemma IProj_recv_inv_aux b F T C G L:
    IProj T G L -> G = (ig_msg b F T C) ->
    F != T /\ (exists lC, L = rl_msg a_recv F lC /\
    C.1 = lC.1 /\ IProj T C.2 lC.2).
  Proof.
  case =>//.
  + move=> q gC lC neq eqt hp [eq1 eq2 eq3 eq4].
    by move: neq; rewrite eq3 eq_refl.
  + move=> q r gC lC neq1 neq2 hp [eq1 eq2 eq3].
    by rewrite eq3 eq_refl in neq1.
  + move=> b0 q gC lC neq eqt hp [eq1 <- <-].
    by rewrite eq_sym; split=>//=; exists lC; split=>//=; split.
  + move=> q s gC lC neq1 neq2 neq3 hp [eq1 eq2 eq3 eq4].
    by rewrite eq3 eq_refl in neq3.
  Qed.

  Lemma IProj_recv_inv b F T C L:
    IProj T (ig_msg b F T C) L ->
    F != T /\ (exists lC, L = rl_msg a_recv F lC /\
    C.1 = lC.1 /\ IProj T C.2 lC.2).
  Proof.
  by move=> hp; apply: (IProj_recv_inv_aux hp).
  Qed.

  Lemma IProj_cnt_inv_aux p F T C G L:
    IProj p G L ->
    p != F -> p != T -> G = ig_msg false F T C ->
    F != T /\ IProj p C.2 L.
  Proof.
  case =>//.
  + move=> q gC lC neq eqt hp neqF neqT [eq1 eq2 eq3].
    by rewrite eq1 eq_refl in neqF.
  + move=> b q gC gL neq eqt hp neqF neqT [eq1 eq2 eq3 eq4].
    by rewrite eq3 eq_refl in neqT.
  + move=> q s gC {}L neq1 neq2 neq3 hp neqF neqT [eq1 eq2 <-].
    by rewrite eq1 eq2 in neq1; split.
  Qed.

  Lemma IProj_cnt_inv p F T C L:
    IProj p (ig_msg false F T C) L ->
    p != F -> p != T ->
    F != T /\ IProj p C.2 L.
  Proof.
  by move=> hp neq1 neq2; apply: (IProj_cnt_inv_aux hp neq1 neq2).
  Qed.

  Definition look (E : {fmap role -> rl_ty}) p := odflt rl_end E.[? p]%fmap.

  Definition eProject (G: ig_ty) (E : {fmap role -> rl_ty}) : Prop :=
    forall p, IProj p G (look E p).

  Lemma EqL_Project p G lT lT':
    EqL lT lT' -> Project p G lT -> Project p G lT'.
  Proof.
  move=> eql prj; move: (conj eql prj) => {eql prj}.
  move=> /(ex_intro (fun lT=> _) lT) {lT}.
  move: G lT'; apply /paco2_acc; move=> r0 _ CIH G lT'.
  move: CIH=>/(_ _ _ (ex_intro _ _ (conj _ _)))-CIH.
  move=> [lT []]; case lT'.
  + move=> eql; move: (EqL_r_end_inv eql); move=>->.
    rewrite /Project; move=> pro; move: paco2_mon; rewrite /monotone2.
    by move=> pamo; apply (pamo _ _ _ _ _ _ _ pro).
  + move=> a q C eql; move: (EqL_r_msg_inv eql)=> [C0 [eqt [eqlC lTeq]]].
    rewrite lTeq; elim/Project_inv=>//=.
    * move=> q0 CG CL eqG [asnd q0q ->] pq0 eqt0 prj; rewrite -q0q -asnd.
      apply/paco2_fold; constructor=>//=; [by rewrite eqt0| right].
      by apply (CIH _ _ _ eqlC).
    * move=> q0 CG CL eqG [arcv q0q ->] pq0 eqt0 prj; rewrite -q0q -arcv.
      apply/paco2_fold; constructor=>//=; [by rewrite eqt0| right].
      by apply (CIH _ _ _ eqlC).
    * move=> r s CG L0 neq1 neq2 neq3 eqG eqL part prj.
      apply/paco2_fold; constructor=>//=; right.
      by move: prj; apply CIH; move: eql; rewrite lTeq eqL.
  Qed.

  Lemma EqL_IProj p G lT lT':
    IProj p G lT -> EqL lT lT' -> IProj p G lT'.
  Proof.
  move=> hp; move: hp lT'; elim.
  + move=> CG {}lT Pro lT' eqL; apply: iprj_end.
    by apply: (EqL_Project eqL Pro).
  + move=> q C lC neq eqt proj Ih lT' eqL.
    move: (EqL_l_msg_inv eqL)=>[lC'] [eqt' [eqL' ->]].
    by constructor=>//=; [rewrite eqt|apply Ih].
  + move=> q r C {}lT neq1 neq2 proj Ih lT' eqL.
    by constructor=>//=; apply Ih.
  + move=> b q C lC neq eqt proj Ih lT' eqL.
    move: (EqL_l_msg_inv eqL)=>[lC'] [eqt' [eqL' ->]].
    by constructor=>//=; [rewrite eqt| apply Ih].
  + move=> q s C {}lT qs pq ps prj Ih lT' eqL.
    by constructor=>//=; apply Ih.
  Qed.

End CProject_defs.

Section ProjectionsCommute.

  Lemma partof_cont_unroll G CG p L n :
    g_closed G ->
    GUnroll G CG -> project G p == Some L ->
    depth_part n p G -> part_of p CG.
  Proof.
    elim: n G CG L=>// n Ih [||G|F T C] //= CG L cG.
    - case PRJ: project=>[L0|]//; move: PRJ=>/eqP-PRJ.
      case: ifP; first by move=>/(lbinds_depth _ PRJ)->.
      move=> NB /gunroll_unfold; elim/gunr_inv=>// _ IG CG0 GU [EQ1] EQ2 _ DP.
      move: EQ1 EQ2 GU DP=>//-> _ []//GU /(depthpart_open 0 (g_rec G))-DP.
      move: NB PRJ=>/eqP-NB /eqP-PRJ; move: (project_open NB cG PRJ)=>{}/eqP-P.
        by move: cG=>/gopen_closed/Ih/(_ GU P DP).
    - move=>/gunroll_unfold; elim/gunr_inv=>// _ F' T' C' CC CG' []//= UA [->->eq3] _ {CG}.
      case PRJ: project=>[K|]//; case: ifP=>// FT.
      case: ifP=>[/eqP<- _|pF]; first by constructor.
      case: ifP=>[/eqP<- _|pT]; first by constructor.
      move=> /eqP[]-KL; rewrite eq_sym pF eq_sym pT/= => DP.
      constructor=>//=; move: PRJ DP=>/eqP; move: cG UA; rewrite /g_closed -eq3//=.
      by apply Ih.
  Qed.

  Lemma depth_part_unroll G CG p n :
    GUnroll G CG -> depth_part n p G -> part_of p CG.
  Proof.
    elim: n G CG =>// n Ih [||G|F T C] //= CG.
    - move=>  /gunroll_unfold; elim/gunr_inv=>// _ IG CG0 GU [EQ1] EQ2 DP.
      move: EQ1 EQ2 GU DP=>//-> _ []//GU /(depthpart_open 0 (g_rec G))-DP.
      by move: GU DP; apply Ih.
    - move=>/gunroll_unfold; elim/gunr_inv=>// _ F' T' C' IG' CG' []//= UA [->->eq3] eq4.
      case pF: (p == F)=>//=; [by move: pF=>/eqP<- _; constructor|].
      case: ifP; [by move=>/eqP<- _; constructor|move=> pT DP; constructor=>//=].
      by move: UA DP; rewrite -eq3 //=; apply Ih.
  Qed.

  Lemma depth_part_participants p G:
    (exists n, depth_part n p G) <-> p \in participants G.
  Proof.
    split; [move=> []n|].
    + move: G; elim n=> //= {}n Ih {}G; case: G=>//=.
      move=> F T C; rewrite !in_cons; case pF: (p == F)=>//=.
      by case: ifP=>//= pT; apply Ih.
    + elim G=>//=; [by move=> {}G Ih parts; move: (Ih parts)=> [n {}Ih]; exists n.+1|].
      move=> F T C Ih /orP[]; [by move=> /eqP->; exists 1=>//=; rewrite eq_refl|].
      move=> /orP[]; [by move=> /eqP[]->; exists 1=>//=; rewrite eq_refl orbT|].
      by move=> parts; move: (Ih parts)=>[n {}Ih]; exists n.+1=>//=; case: ifP.
  Qed.

  Lemma participants_unroll G CG p:
    GUnroll G CG ->
    p \in participants G ->
          part_of p CG.
  Proof.
    move=> gu; rewrite -depth_part_participants=>[[n]].
    by apply depth_part_unroll.
  Qed.

  Lemma partof_unroll G CG p :
    g_closed G ->
    guarded 0 G ->
    GUnroll G CG ->
    part_of p CG ->
    p \in participants G.
  Proof.
    move=> cG gG GU PART.
    elim: PART=>[F T C| F T C|{}p F T C pof Ih] in G cG gG GU *.
    - apply: r_in_unroll_rec_depth; move: GU=>/(GUnroll_ind (rec_depth G)).
      move: (n_unroll (rec_depth G) G) (unroll_guarded cG gG)=>{cG gG}G NR GU.
      move: GU NR=>/gunroll_unfold; elim/gunr_inv =>// _;
        first by move=> IG _ _ _ _ /(_ IG); rewrite eq_refl.
        by move=> F' T' C' CG' _ _ _ [->] _ _ _; rewrite in_cons eq_refl.
    - apply: r_in_unroll_rec_depth; move: GU=>/(GUnroll_ind (rec_depth G)).
      move: (n_unroll (rec_depth G) G) (unroll_guarded cG gG)=>{cG gG}G NR GU.
      move: GU NR=>/gunroll_unfold; elim/gunr_inv =>// _;
        first by move=> IG _ _ _ _ /(_ IG); rewrite eq_refl.
        by move=> F' T' C' CG' _ _ _ [] _ <- _ _; rewrite in_cons orbC in_cons eq_refl.
    - apply: r_in_unroll_rec_depth; move: GU=>/(GUnroll_ind (rec_depth G)).
      move: (g_guarded_nunroll (rec_depth G) cG gG) (unroll_guarded cG gG).
      move: (n_unroll (rec_depth G) G) (g_closed_unroll (rec_depth G) cG).
      move=>{cG gG}G cG gG NR GU.
      move: GU NR cG gG =>/gunroll_unfold; elim/gunr_inv =>// _;
        first by move=> IG _ _ _ _ /(_ IG); rewrite eq_refl.
      move=> F' T' t {}CG CG' UA E1 [e1 e2 E2] _; rewrite /g_closed//= => cl gu.
      rewrite !in_cons; apply /orP; right; apply /orP; right.
      by apply (Ih _ cl gu); rewrite -E2//=; move: UA=>[].
  Qed.

  Notation CIH4 X Y H1 H2 H3 H4
    := (ex_intro (fun=>_) X
                 (ex_intro (fun=>_) Y
                           (conj H1 (conj H2 (conj H3 H4))))).
  Lemma project_wf G p L CG :
    g_closed G ->
    guarded 0 G ->
    project G p == Some L ->
    GUnroll G CG -> WF CG.
  Proof.
    move=>H1 H2 H3 H4; move: (CIH4 L G H1 H2 H3 H4)=> {H1 H2 H3 H4 G L}.
    move: CG; apply/paco1_acc=>r _ /(_ _ (CIH4 _ _ _ _ _ _ ))-CIH.
    move=> CG [L] [G] [cG [gG [PRJ GU]]]; apply/paco1_fold.
    move: (unroll_guarded cG gG); move: PRJ=>/eqP-PRJ.
    move: (project_unroll (rec_depth G) cG PRJ)=>[n1][n2][L'][{}PRJ] _.
    move: GU=>/(GUnroll_ind (rec_depth G)); move: PRJ.
    move: gG=>/(g_guarded_nunroll (rec_depth G) cG).
    move: cG=>/(g_closed_unroll (rec_depth G)).
    move: (n_unroll (rec_depth G) G) => {}G; move: L'=>{}L {n1 n2}.
    case: G =>/=.
    - by move=>_ _ _ /gunroll_unfold; elim/gunr_inv=>//; constructor.
    - by move=>v /=; rewrite /g_closed/=.
    - by move=>G _ _ _ _ /(_ G); rewrite eq_refl.
    - rewrite /g_closed//=; move=> F T C cl gu.
      case PRJ: project =>[L'|//]; move: PRJ=>/eqP-PRJ.
      case: ifP=>// FT _; move=>/gunroll_unfold.
      elim/gunr_inv => //=  gun F' T' t C' CC UA [->->eqpair] eqcg _.
      constructor; rewrite ?FT//=; right; apply (CIH _ _ _ cl gu PRJ).
        by rewrite -eqpair; move: UA=>[].
  Qed.

  (*Lemma lunroll_merge r L CL CONT Ks
        (LU : LUnroll L CL)
        (PRJ : prj_all simple_merge CONT r = Some Ks)
        (MRG : simple_merge L [seq K.2.2 | K <- Ks] = Some L)
    : exists CCL,
      same_dom (find_cont Ks) CCL /\ simple_co_merge CCL CL.
  Proof.
    set CCL := fun l =>
                 match find_cont Ks l with
                 | Some (Ty, _) => Some (Ty, CL)
                 | None => None
                 end.
    exists CCL; split.
    - move=> l Ty; split=>[][G]; rewrite /CCL/=.
      + by move=>->; exists CL.
      + by case: find_cont=>// [][Ty' G'][<-_]; exists G'.
    - rewrite /CCL=>l Ty L'; case: find_cont=>//[][Ty' G'][_]->.
      by apply/EqL_refl.
  Qed.*)

(*Unrolling Preserves Projection*)

  Lemma project_nonrec (r0 : proj_rel ) r CL CG L G

        (CIH : forall cG cL iG iL,
            g_closed iG ->
            guarded 0 iG ->
            project iG r == Some iL ->
            GUnroll iG cG ->
            LUnroll iL cL ->
            r0 cG cL)

        (cG : g_closed G)
        (gG : guarded 0 G)
        (nrG : forall G' : g_ty, G != g_rec G')
        (iPrj : project G r = Some L)
        (GU : GUnroll G CG)
        (LU : LUnroll L CL)

    : paco2 (Proj_ r) r0 CG CL.
  Proof.
    move: (closed_not_var cG).
    case: (boolP (r \notin participants G)); [| rewrite negbK].
    - move=> PARTS nvG; move: iPrj=>/eqP-iPrj.
      move: (proj1 (project_parts cG iPrj) PARTS)=> endL.
      move: (lunroll_isend LU endL)=>->; apply/paco2_fold.
      constructor; first by move=>/(partof_unroll cG gG GU)-P'; move: P' PARTS=>->.
        by apply/(project_wf cG gG iPrj).
    - case: G cG gG nrG iPrj GU=>//; first by move=> GT _ _ /(_ GT); rewrite eq_refl.
      move=>FROM TO CONT; rewrite /g_closed //= => cl gu _.
      case prj: project=>[Lpr|]//=; case: ifP=>//= FT; rewrite !in_cons.
      case: ifP =>//=.
      + move=> /eqP-Fr [eqL] /gunroll_unfold.
        case Egmsg: _ _/ =>[ | |F T t IG CG' gun]//=.
        move: gun=>[]//= gun _ _; move: Egmsg=> [<-<- eq3].
        move: (lu_unfold LU); rewrite -eqL eq3=>{}LU.
        case Elmsg: _ _/LU=>[||rr tt LL LL' UL|]//= .
        move: Elmsg UL=>[<-<-<-] UL; rewrite -Fr//=.
        apply /paco2_fold; constructor; [by rewrite FT| by[]|right].
        by move: UL=> []//=; move: prj gun=>/eqP; move: cl gu; rewrite eq3//=; apply CIH.
      + case: ifP=> Tr Fr [eqL] /gunroll_unfold.
        * move: Tr=>/eqP-Tr; case Egmsg: _ _/ =>[ | |F T t IG CG' gun]//= _ _.
          move: gun=>[]//= gun; move: Egmsg=>[<-<- eq3].
          move: (lu_unfold LU); rewrite -eqL eq3=>{}LU.
          case Elmsg: _ _/LU=>[|||rr tt LL LL' UL]//= .
          move: Elmsg UL=>[<-<-<-] UL; rewrite -Tr//=.
          apply /paco2_fold; constructor; [by rewrite eq_sym; rewrite FT| by []|right].
          by move: UL=> []//=; move: prj gun=>/eqP; move: cl gu; rewrite eq3//=; apply CIH.
        * case Egmsg: _ _/ =>[ | |F T t IG CG' gun]//=.
          rewrite eq_sym Fr eq_sym Tr//==>partC _.
          move: gun=>[]//= gun; move: Egmsg=>[<-<- eq3]; apply /paco2_fold.
          constructor; [by rewrite FT| by rewrite eq_sym Fr| by rewrite eq_sym Tr| |right].
          - by apply: (participants_unroll gun); rewrite eq3 in partC.
          - by move: prj gun LU=>/eqP; move: cl gu; rewrite eq3 eqL; apply CIH.
  Qed.

  Theorem ic_proj r :
    forall iG iL cG cL,
      g_closed iG ->
      guarded 0 iG ->
      project iG r == Some iL ->
      GUnroll iG cG ->
      LUnroll iL cL ->
      Project r cG cL.
  Proof.
    move=> iG iL cG cL CG GG Prj GU LU.
    move: (conj CG (conj GG (conj Prj (conj GU LU))))
    => {CG GG Prj GU LU}.
    move => /(ex_intro (fun iL=> _) iL) {iL}.
    move => /(ex_intro (fun iG=> _) iG) {iG}.
    move: cG cL; apply/paco2_acc=> r0 _ CIH.
    move: CIH =>/(_ _ _
                  (ex_intro _ _
                     (ex_intro _ _
                        (conj _ (conj _ (conj _ (conj _ _)))))))-CIH.
    move=> cG cL [iG] [cG'] [ciG] [giG] [iGiL] [GU LU].

    move: iGiL  => /eqP-iGiL.
    move: (project_unroll (rec_depth iG) ciG iGiL) => [U1] [U2] [L] [proj] U12.
    move: LU =>/(LUnroll_ind U1); move: U12=>->; rewrite -LUnroll_ind=>UL.
    move : GU (unroll_guarded ciG giG)=>/(GUnroll_ind (rec_depth iG))=>GU nrG.
    move: (g_guarded_nunroll (rec_depth iG) ciG giG)=>guiG.
    move: (g_closed_unroll (rec_depth iG) ciG)=>cuiG {ciG giG iGiL}.

      by apply/(project_nonrec CIH cuiG guiG nrG proj).
  Qed.

  Theorem coind_proj r G L :
    g_precond G ->
    project G r == Some L ->
    Project r (g_expand G) (l_expand L).
  Proof.
    rewrite/g_precond=>/andP-[cG gG] P.
    move: (proj_lclosed cG P) (project_guarded P) =>cL gL.
    move: (g_expand_unr gG cG) (l_expand_unr gL cL)=>{cL gL}.
      by apply/ic_proj.
  Qed.

  Theorem expand_eProject (g : g_ty) (e : seq (role * lty))
    : eproject g = Some e ->
      eProject (ig_end (g_expand g)) (expand_env e).
  Proof.
    move=>EPRJ p; constructor.
    have PRE: g_precond g by move: EPRJ;rewrite/eproject;case:ifP.
    move: (precond_parts PRE); case: (boolP (nilp (participants g))).
    + move=> NOPARTS [//|END]; move: EPRJ; rewrite /eproject PRE.
      move: (participants g) NOPARTS=>[]//= _ [<-].
      rewrite /look -in_expanded_env/= (expand_g_end END).
      apply/paco2_fold/prj_end; first by case E: _ / =>//.
        by apply/paco1_fold; constructor.
    + move=> NE _ //=.
      have cG: g_closed g by move: PRE=>/andP-[cG gG].
      have gG: guarded 0 g by move: PRE=>/andP-[_ gG].
      have GU: GUnroll g (g_expand g) by apply/(g_expand_unr gG cG).
      move: (eproject_some EPRJ NE)=>[q [L] /eqP-PRJ'].
      have gWF: WF (g_expand g) by apply/(project_wf cG gG PRJ' GU).
      move=>{PRJ' L q}.
      case: (boolP (p \in participants g)).
      - move=>PS; move: EPRJ=>/eqP/eproject_part/(_ _ PS)-PRJ.
        rewrite /look -in_expanded_env.
        have ->: (odflt rl_end (omap l_expand (find_cont e p)))
        = l_expand (odflt l_end (find_cont e p))
          by case: find_cont=>//=;rewrite (rltyU (l_expand _)).
          by apply/coind_proj=>//; apply/eqP.
      - move=>PARTS; have NP: ~ part_of p (g_expand g)
                by move=> P_of; move: PARTS; rewrite (partof_unroll cG gG GU).
        rewrite /look -in_expanded_env (fnd_not_part EPRJ PARTS)/=.
          by apply/paco2_fold/prj_end.
  Qed.

End ProjectionsCommute.

Section GSemantics.

  (*Definition R_only (R : ig_ty -> ig_ty -> Prop)
           L0 (C C' : lbl -> option (mty * ig_ty)) :=
  (forall L1 K, L0 != L1 -> C L1 = Some K <-> C' L1 = Some K)
  /\ exists Ty G0 G1,
    C L0 = Some (Ty, G0)
    /\ C' L0 = Some (Ty, G1)
    /\ R G0 G1.*)

  Unset Elimination Schemes.
  Inductive step : act -> ig_ty -> ig_ty -> Prop :=
  (* Basic rules *)
  | st_send F T Ty G :
      step (mk_act a_send F T Ty) (ig_msg false F T (Ty,G)) (ig_msg true F T (Ty,G))
  | st_recv F T Ty G :
      step (mk_act a_recv T F Ty) (ig_msg true F T (Ty,G)) G
  (* Struct *)
  | st_amsg1 a F T Ty G0 G1:
      subject a != F ->
      subject a != T ->
      step a G0 G1 ->
      step a (ig_msg false F T (Ty,G0)) (ig_msg false F T (Ty,G1))
  | st_amsg2 a F T Ty G0 G1 :
      subject a != T ->
      step a G0 G1 ->
      step a (ig_msg true F T (Ty,G0)) (ig_msg true F T (Ty,G1))
  | st_unr a CG G :
      step a (rg_unr CG) G ->
      step a (ig_end CG) G
  .
  Set Elimination Schemes.

  Derive Inversion step_inv with (forall a G G', step a G G') Sort Prop.

  Scheme step_ind1 := Induction for step Sort Prop.

  Lemma step_ind
        (P : forall (a : act) (i i0 : ig_ty), step a i i0 -> Prop):
    (forall F T Ty G,
        P (mk_act a_send F T Ty) (ig_msg false F T (Ty,G)) (ig_msg true F T (Ty,G))
          (st_send F T Ty G) )
    ->
    (forall F T Ty G,
        P (mk_act a_recv T F Ty) (ig_msg true F T (Ty,G)) G (st_recv F T Ty G))
    ->
    (forall a F T Ty G0 G1 (i : subject a != F) (i0 : subject a != T)
            (s : step a G0 G1),
        P a G0 G1 s ->
        P a (ig_msg false F T (Ty,G0)) (ig_msg false F T (Ty,G1)) (st_amsg1 Ty i i0 s))
    ->
    (forall (a : act) (F T : role) (Ty:mty)
            (G0 G1: ig_ty) (i : subject a != T)
            (s :step a G0 G1), P a G0 G1 s
                               ->  P a (ig_msg true F T (Ty,G0)) (ig_msg true F T (Ty,G1))
                                     (st_amsg2 F Ty i s))
    ->
    (forall (a : act) (CG : rg_ty) (G : ig_ty) (s : step a (rg_unr CG) G),
        P a (rg_unr CG) G s -> P a (ig_end CG) G (st_unr s))
    -> forall (a : act) (i i0 : ig_ty) (s : step a i i0), P a i i0 s.
  Proof.
    move=> P_send P_recv P_amsg1 P_amsg2 P_unr; fix Ih 4.
    move=> a G G'; case; [by[]|by[]| | | ].
    + by move=> a0 F T Ty G0 G1 nF nT s; apply: P_amsg1.
    + by move=> a0 F T Ty G0 G1 nT s; apply: P_amsg2.
    + by move=> a0 CG G0 s; apply: P_unr.
  Qed.

  Definition gtrc_rel := trace act -> ig_ty -> Prop.
  Inductive g_lts_ (r : gtrc_rel) : gtrc_rel :=
  | eg_end : @g_lts_ r (tr_end act) (ig_end rg_end)
  | eg_trans a t G G' :
      step a G G' ->
      r t G' ->
      g_lts_ r (tr_next a t) G.
  Hint Constructors g_lts_.
  Definition g_lts t g := paco2 g_lts_ bot2 t g.

  Lemma g_lts_monotone : monotone2 g_lts_.
  Proof. pmonauto. Qed.
  Hint Resolve g_lts_monotone : paco.

End GSemantics.

Section LSemantics.

  Notation renv := {fmap role -> rl_ty}.
  Notation qenv := {fmap role * role -> seq mty}.

  Definition enq (qs : {fmap (role * role) -> (seq mty)}) k v :=
    match qs.[? k] with
    | Some vs => qs.[ k <- app vs [:: v] ]
    | None => qs.[ k <- [:: v]]
    end%fmap.

  Definition deq (qs : {fmap (role * role) -> (seq mty)}) k :=
    match qs.[? k] with
    | Some vs =>
      match vs with
      | v :: vs => if vs == [::] then Some (v, qs.[~ k])
                   else Some (v, qs.[k <- vs])
      | [::] => None
      end
    | None => None
    end%fmap.

  Definition do_act_lt (L : rl_ty) A :=
    let: (mk_act a p q t) := A in
    match L with
    | rl_msg a' q' (t',Lp) =>
      if (a == a') && (q == q') && (t == t')
      then Some Lp
      else None
    | _ => None
    end%fmap.

  Definition run_act_lt (L : rl_ty) A := odflt L (do_act_lt L A).

  Definition do_act (P : renv) A :=
    let: (mk_act a p q t) := A in
    match do_act_lt (look P p) A with
    | Some Lp => Some (P.[p <- Lp]%fmap)
    | None => None
    end.

  Lemma doact_send (E : renv) p q t Lp :
    (look E p = rl_msg a_send q (t,Lp)) ->
    exists E', (do_act E (mk_act a_send p q t) = Some E').
  Proof.
    move=>H; rewrite /do_act/do_act_lt H !eq_refl/=.
      by exists E.[ p <- Lp]%fmap.
  Qed.

  Definition do_act_l_ty (L: lty) (A : act) : option lty :=
    let: (mk_act a p q t) := A in
    match lunroll (lrec_depth L) L with
    | l_send q' t' Lp =>
      if (a == a_send) && (q == q') && (t == t')
      then Some Lp
      else None
    | l_recv q' t' Lp =>
      if (a == a_recv) && (q == q') && (t == t')
      then Some Lp
      else None
    | _ => None
    end.

  Definition run_act_l_ty (L: lty) (A : act) : lty := odflt L (do_act_l_ty L A).

  Lemma do_act_works Li Lr A :
    LUnroll Li Lr -> LUnroll (run_act_l_ty Li A) (run_act_lt Lr A).
  Proof.
    rewrite /run_act_l_ty/run_act_lt/do_act_l_ty/do_act_lt/==>LU.
    case: A=> a _ q t; move: ((LUnroll_ind (lrec_depth Li) Li Lr).1 LU)=>LU'.
    move: LU' LU.
    case EQ: (lunroll (lrec_depth Li) Li)=> [| v | Li' | r t' Li' | r t' Li' ].
    - by move=> /lunroll_end->.
    - by move=>/(paco2_unfold l_unroll_monotone); case F: _ _ /.
    - by move=>/= _ _; apply/(lunroll_inf _ EQ).
    - move=>/(paco2_unfold l_unroll_monotone).
      case F: _ _ / =>[|| p0 K0 C0 DOM UNR|p0 K0 C0 DOM UNR]//.
      move: F DOM UNR=>[<-<-<-] DOM UNR{p0 K0 EQ}.
      case: (boolP ((a == a_send) && (q == r) && (t == t')))=>//= _ _.
        by move:UNR=>[].
    - move=>/(paco2_unfold l_unroll_monotone).
      case F: _ _ / =>[|| p0 K0 C0 DOM UNR|p0 K0 C0 DOM UNR]//.
      move: F DOM UNR=>[<-<-<-] DOM UNR{p0 K0 EQ}.
      case: (boolP ((a == a_recv) && (q == r) && (t == t')))=>//= _ _.
        by move:UNR=>[].
  Qed.

  Open Scope fmap_scope.
  (** lstep a Q P Q' P' is the 'step' relation <P, Q> ->^a <P', Q'> in Coq*)
  Inductive lstep : act -> renv * qenv -> renv * qenv -> Prop :=
  | ls_send t p q (P P' : renv) (Q Q' : qenv) :
      Q' == enq Q (p, q) t ->
      do_act P (mk_act a_send p q t) = Some P' ->
      lstep (mk_act a_send p q t) (P, Q) (P', Q')
  | ls_recv t p q (P P' : renv) (Q Q' : qenv) :
      deq Q (p, q) == Some (t, Q') ->
      do_act P (mk_act a_recv q p t) = Some P' ->
      lstep (mk_act a_recv q p t) (P, Q) (P', Q')
  .
  Derive Inversion lstep_inv with (forall A P P', lstep A P P') Sort Prop.

  Definition runnable (A : act) (P : renv * qenv) : bool :=
    match do_act P.1 A with
    | Some _ =>
      let: mk_act a p q t := A in
      match a with
      | a_send => true
      | a_recv =>
        match deq P.2 (q, p) with
        | Some (t', Q) => (t == t')
        | None => false
        end
      end
    | None => false
    end.

  Lemma lstep_runnable A P P' : lstep A P P' -> runnable A P.
  Proof.
    by case=> Ty F T {P P'}E E' Q Q' /eqP-QFT/=;
       case LOOK: look=>[|a r [t L]]//; case: ifP=>//EQ _;
       rewrite /runnable/= LOOK EQ // QFT !eq_refl.
  Qed.

  Lemma lstep_eq A P P0 P1 : lstep A P P0 -> lstep A P P1 -> P0 = P1.
  Proof.
    case=>Ty0 F0 T0 {P P0}E E0 Q Q0 /eqP-QFT/=; case LOOK: look=>[|a p [t L]]//;
      case: ifP=>//EQ [<-]; elim/lstep_inv =>//_
           Ty1 F1 T1 E' E1 Q' Q1 /eqP-QFT'/= ACT EQ1 EQ2 EQ3;
      move: EQ1 EQ2 EQ3 ACT QFT QFT'=>[->->->] [->->] _ {F1 T1 Ty1 E' Q' P1};
      rewrite LOOK EQ=>[][<-]->.
    - by move=>->.
    - by move=>[->].
  Qed.

  Definition do_queue (Q : qenv) (A : act) : qenv :=
    match A with
    | mk_act a_send F T Ty => enq Q (F, T) Ty
    | mk_act a_recv F T Ty =>
      match deq Q (T, F) with
      | Some (_, Q') => Q'
      | None => Q
      end
    end.

  (* Attempts to run a step, does nothing if it cannot run *)
  Definition run_step (A : act) (P : renv * qenv) : renv * qenv :=
    match do_act P.1 A with
    | Some E' => (E', do_queue P.2 A)
    | _ => P
    end.

  (* Lemma run_step 'makes sense' *)
  Lemma run_step_sound A P : runnable A P -> lstep A P (run_step A P).
  Proof.
    case: P => E Q.
    rewrite /runnable /=; case E_doact: (do_act _ _)=>[E'|//].
    case: A E_doact=> [[|] p q t E_doact]/=.
    - by move=> _; rewrite /run_step E_doact; constructor=>//.
    - case E_deq: (deq _ _) =>[[t' Q']|//] [/eqP-tt'].
      rewrite /run_step E_doact/= E_deq; constructor=>//=.
        by rewrite tt' E_deq.
  Qed.

  Lemma run_step_compl A P P' : lstep A P P' -> P' = run_step A P.
  Proof.
      by move=> ST; move: (lstep_runnable ST)=>/run_step_sound/(lstep_eq ST).
  Qed.

  Definition rel_trc := trace act -> renv*qenv -> Prop.
  Inductive l_lts_ (r : rel_trc) : rel_trc :=
  | lt_end E :
      (forall p, look E p = rl_end) ->
      @l_lts_ r (tr_end _) (E, [fmap])
  | lt_next a t P P' :
      lstep a P P' ->
      r t P' ->
      @l_lts_ r (tr_next a t) P.
  Hint Constructors l_lts_.
  Lemma l_lts_monotone : monotone2 l_lts_.
  Proof. pmonauto. Qed.
  Hint Resolve l_lts_monotone : paco.

  Definition l_lts t L := paco2 l_lts_ bot2 t L.
  Derive Inversion llts_inv with (forall tr G, l_lts tr G) Sort Prop.

  Definition rty_trc := trace act -> rl_ty -> Prop.
  Inductive l_trc_ (p : role) (r : rty_trc) : rty_trc :=
  | l_trc_end : l_trc_ p r (tr_end _) rl_end
  | l_trc_msg A TR L L' :
      subject A == p -> do_act_lt L A = Some L' ->
      r TR L' ->
      l_trc_ p r (tr_next A TR) L
  .
  Lemma l_trc_monotone p : monotone2 (l_trc_ p).
  Proof.
    move=>TR cL r r' Htrc MON; move: Htrc; case.
    - by constructor.
    - move=>A TR0 L L' Hsubj Hact /MON.
        by move: Hsubj Hact; apply l_trc_msg.
  Qed.

  Definition l_trc p t L := paco2 (l_trc_ p) bot2 t L.

  Definition trc_rel := trace act -> trace act -> Prop.
  Inductive subtrace_ (p : role) (r : trc_rel) : trc_rel :=
  | subtrace_end : subtrace_ p r (tr_end _) (tr_end _)
  | subtrace_skip A TRp TR :
      subject A != p ->
      r TRp TR ->
      subtrace_ p r TRp (tr_next A TR)
  | subtrace_msg A TRp TR :
      subject A == p ->
      r TRp TR ->
      subtrace_ p r (tr_next A TRp) (tr_next A TR)
  .
  Lemma subtrace_monotone p : monotone2 (subtrace_ p).
  Proof.
  move=>TR cL r r' Htrc MON; move: Htrc; case.
  - by constructor.
  - move=> A TRp TR0 Hsubj /MON; move: Hsubj.
      by apply: subtrace_skip.
  - move=> A TRp TR0 Hsubj /MON; move: Hsubj.
      by apply: subtrace_msg.
  Qed.
  Definition subtrace p T0 T1 := paco2 (subtrace_ p) bot2 T0 T1.
  Hint Constructors EqL_.
  Hint Resolve EqL_monotone.
  Hint Resolve EqL_refl.

  Notation cfg := (renv * qenv)%type.

End LSemantics.

Section QProject.

  Open Scope fmap.

  Definition qproj_rel := ig_ty -> {fmap role * role -> seq mty } -> Prop.
  Inductive qProject : qproj_rel :=
  | qprj_end G : qProject (ig_end G) [fmap]%fmap

  | qprj_none p p' t G Q :
      qProject G Q ->
      Q.[? (p,p')] = None ->
      qProject (ig_msg false p p' (t,G)) Q

  | qprj_some p p' t G Q Q':
      deq Q' (p, p') == Some (t, Q) ->
      qProject G Q ->
      qProject (ig_msg true p p' (t,G)) Q'
  .
  Hint Constructors qProject.

  Lemma qProject_end_inv_aux Q iG G:
    qProject iG Q ->  iG = (ig_end G) ->
    Q = ([fmap]%fmap).
  Proof.
    case =>//=.
  Qed.

  Lemma qProject_end_inv Q G:
    qProject (ig_end G) Q ->
    Q = ([fmap]%fmap).
  Proof.
      by move=> hp; apply: (@qProject_end_inv_aux Q _ G hp).
  Qed.

  Lemma qProject_false_inv_aux F T t G Q GG:
    qProject GG Q ->
    GG = (ig_msg false F T (t,G)) ->
    Q.[? (F,T)] = None /\ qProject G Q.
  Proof.
    case =>//=.
    move=> p p' t0 G0 Q0 qpro qno [eq1 eq2 eq3 eq4].
    split; [by rewrite -eq1 -eq2| rewrite -eq4].
      by apply qpro.
  Qed.

  Lemma qProject_false_inv F T t G Q :
    qProject (ig_msg false F T (t,G)) Q ->
    Q.[? (F,T)] = None /\ qProject G Q.
  Proof.
      by move=> hp; move: (@qProject_false_inv_aux F T t G _ _ hp)=>H; apply/H.
  Qed.

  Lemma qProject_true_inv_aux F T t G Q GG:
    qProject GG Q ->
    GG = (ig_msg true F T (t, G)) ->
    (exists Q', deq Q (F, T) == Some (t, Q') /\
        qProject G Q').
  Proof.
    case =>//.
    move=> p p' t0 G0 Q0 Q' deqQ' qpro [eq1 eq2 eq3 eq4].
    rewrite -eq1 -eq2 -eq3 -eq4;  exists Q0.
      by split.
  Qed.

  Lemma qProject_true_inv F T t G Q:
    qProject (ig_msg true F T (t,G)) Q ->
    exists Q', deq Q (F, T) == Some (t, Q') /\
                    qProject G Q'.
  Proof.
    move=> hp; move: (@qProject_true_inv_aux F T t G Q _ hp).
      by move=> triv; apply triv.
  Qed.

  Lemma deq_elsewhere Q Q' k0 k Ty:
    deq Q' k0 == Some (Ty, Q) -> k != k0 ->
    Q'.[?k]=Q.[?k].
  Proof.
    rewrite /deq; case E: (Q'.[? k0]) =>[qs|] //=; case qs => [|q qs0] //=.
    case: ifP; move=> _; rewrite -(rwP eqP); move=> [_ <-].
    + by rewrite fnd_rem1; case: ifP.
    + by rewrite fnd_set; case: ifP.
  Qed.

  Lemma deq_singleton (Q:{fmap role * role -> seq mty}) p q t:
    Q.[?(p,q)] == None ->
    deq Q.[(p, q) <- [:: t]] (p, q) = Some (t, Q).
  Proof.
    move=> Qnone; rewrite /deq fnd_set; case: ifP; rewrite eq_refl //=; elim.
    apply: f_equal; apply: injective_projections =>//=.
    rewrite -fmapP; move=> pq; rewrite fnd_rem1; case: ifP.
    + move=> neq; rewrite fnd_set; case: ifP =>//=.
        by rewrite (negbTE neq) //=.
    + move=> eq; move: (negbNE (negbT eq)).
        by rewrite -(rwP eqP) =>->; rewrite (rwP eqP) eq_sym.
  Qed.

End QProject.


Section TraceEquiv.

  Open Scope fset.
  Open Scope fmap.

  Definition Projection G P := eProject G P.1 /\ qProject G P.2.

  Lemma doact_other p E A L :
    subject A != p -> match do_act E A with
                      | Some E' => Some E'.[p <- L]
                      | None => None
                      end = do_act E.[p <- L] A.
  Proof.
    case: A=>[a F T Ty]; rewrite /do_act/look fnd_set => /=SUBJ.
    rewrite (negPf SUBJ).
    case: (E.[? F])=> [[//|a0 q [t L']] |//]/=.
    case: ifP=>// _.
    by rewrite setfC eq_sym (negPf SUBJ).
  Qed.

  Lemma runnable_upd A E Q L p :
    subject A != p -> runnable A (E, Q) <-> runnable A (E.[p <- L], Q).
  Proof.
    move=> SUBJ; rewrite /runnable/= -doact_other//.
    by case: (do_act E A)=>[_|//].
  Qed.

  Lemma Proj_true_next F T t G P :
    Projection (ig_msg true F T (t, G)) P ->
      Projection G (run_step (mk_act a_recv T F t) P).
  Proof.
    move=>[H qPRJ]; move: (H T)=>PRJ.
    move: PRJ=>/IProj_recv_inv=>[[FT [[t' L'] [ll []//=-teq PRJ]]]].
    move: qPRJ=>/qProject_true_inv[Q'[/eqP-DEQ qPRJ]].
    rewrite /run_step/= ll teq !eq_refl/= DEQ; split=>//=.
    (*rewrite /eProject.*)
    move=>p; case: (boolP (p == T)) =>[/eqP->|pT].
    - by rewrite /look fnd_set eq_refl.
    - rewrite /look fnd_set (negPf pT).
      by move: (H p )=>/IProj_send2_inv /(_ pT) [_].
  Qed.

  Lemma look_comm E F L T (NEQ : F != T) :
    look E.[F <- L] T = look E T.
  Proof. by rewrite/look fnd_set eq_sym (negPf NEQ). Qed.


  Lemma Proj_false_next F T t G P :
    Projection (ig_msg false F T (t,G)) P ->
      Projection G (run_step (mk_act a_recv T F t)
                             (run_step (mk_act a_send F T t) P)).
  Proof.
    move=>[H qPRJ]; move: (H F)=>PRJF.
    move: PRJF=>/IProj_send1_inv-[FT [[t' G'] [llF []//=-teq' PRJF]]].
    move: (H T)=>/IProj_recv_inv-[_ [[t'' G''] [llT []//=-teq'' PRJT]]].
    move: qPRJ=>/qProject_false_inv-[PFT] qPRJ; split.
    - move=> p;
      case: (boolP (p == F)) =>[/eqP-> {p}|pF];
      [|case: (boolP (p == T)) =>[/eqP-> {pF p}|pT]].
      + (* p = F *)
        rewrite /look/run_step/= llF teq' !eq_refl/= look_comm //= llT.
        by rewrite -teq' -teq'' !eq_refl/= fnd_set (negPf FT) fnd_set eq_refl.
      + (* p = T *)
        rewrite /look/run_step/= llF teq' !eq_refl /= look_comm //= llT.
        by rewrite -teq' -teq'' !eq_refl/= fnd_set eq_refl.
      + (* T != p != F *)
        move: (H p)=>/IProj_cnt_inv/(_ pF)/(_ pT)-[_]//=.
        rewrite /run_step/= llF teq' !eq_refl/= look_comm//= llT -teq' -teq'' !eq_refl//=.
        by rewrite look_comm; [rewrite look_comm;[|rewrite eq_sym]|rewrite eq_sym].
    - rewrite /run_step/= llF teq' !eq_refl/= look_comm //= llT -teq' -teq'' !eq_refl//=.
      rewrite /enq PFT /deq fnd_set eq_refl /= remf1_set eq_refl.
      by rewrite remf1_id; [|rewrite -fndSome PFT].
  Qed.

  Lemma doact_diff A E E' :
    do_act E A = Some E' -> exists L, E' = E.[subject A <- L].
  Proof.
    rewrite /do_act/do_act_lt/look/=; case: A=>[a p q t].
    case Ep: E.[? p] =>[[|ap r [tt L]]|]//=.
    by case: ifP=>//= _ [/esym-H]; exists L.
  Qed.

  Definition fst_eq (A B : eqType) (x y : option (A * B)) :=
    match x, y with
    | Some (a, _), Some (b, _) => a == b
    | None, None => true
    | _, _ => false
    end.

  Lemma runnable_next_queue A E (Q Q' : {fmap role * role -> seq mty}) :
    (forall p, fst_eq (deq Q (p, subject A)) (deq Q' (p, subject A)))  ->
    runnable A (E, Q) <-> runnable A (E, Q').
  Proof.
    move=> H; rewrite /runnable; case: do_act=>// _.
    case: A H=>[[//|] p q t]/= /(_ q).
    by case: deq=>[[TyQ WQ]|]; case: deq=>[[TyQ' WQ']|]//==>/eqP->.
  Qed.

  Lemma runnable_next A A' P :
    subject A != subject A' ->
    (subject A != object A') || (act_ty A' == a_recv) ->
    runnable A P <-> runnable A (run_step A' P).
  Proof.
    case A => [a p q Ty]; case A'=>[a' p' q' Ty']/= NEQ COND.
    rewrite /run_step/=; case: look =>[|a0 r0 [Ty0 L0]]//.
    case: ifP=>//=; move=>/andP-[/andP[_ _] _]{a0 r0 Ty0}.
    move: COND; rewrite orbC; case: a'=>//= NEQ'.
    - rewrite -runnable_upd //; case: P=>[E Q]/=.
      apply/runnable_next_queue => r/=.
      rewrite /enq/=; case: Q.[? _] =>[W|].
      + rewrite /deq fnd_set xpair_eqE andbC (negPf NEQ') /andb.
        by case: Q.[? _] =>[[|V [|V' W']]|]/=.
      + rewrite /deq fnd_set xpair_eqE andbC (negPf NEQ') /andb.
        by case: Q.[? _] =>[[|V [|V' W']]|]/=.
    - case DEQ: deq=>[[Ty0 Q']|]//=; last by rewrite -runnable_upd//.
      rewrite -runnable_upd//.
      apply: runnable_next_queue=> r.
      move: DEQ; rewrite /deq/=.
      case EQ: P.2.[? _] => [[|V [|V' W]]|]//= [_ <-] {Q'}.
      * rewrite fnd_rem1 xpair_eqE negb_and orbC (negPf NEQ) /orb/negb.
        by case: P.2.[? _] =>[[|V0 [|V1 W0]]|]/=.
      * rewrite fnd_set xpair_eqE andbC (negPf NEQ) /andb.
        by case: P.2.[? _] =>[[|V0 [|V1 W0]]|]/=.
  Qed.

  Lemma part_of_unr p CG : part_of p CG <-> iPart_of p (rg_unr CG).
  Proof.
    split.
    - case=>//.
      + by move=> F T C; constructor.
      + by move=> F T C; constructor.
      + by move=> {}p F T C pof; apply /(ipof_cont false)/ipof_end.
    - case: CG=>//=.
      + case E: _ / =>[q cG PART|||] //=.
        by move: E PART=>/=[<-].
      + move=> F T [t G] //=.
        case E: _ / =>//= [F' T' [t' G']|b F' T' [t' g']|{}p b F' T' [t' G']//= ipof].
        * by move: E=> [-> _ _ _]; constructor.
        * by move: E=>[_ _ -> _ _]; constructor.
        * move: E ipof=> [_ _ _ _ <-]; case E': _ / =>[{}p GG pof|||]//=.
          by move: E' =>[->]; constructor.
  Qed.

  Lemma iproj_end p cG : ~ part_of p cG -> WF cG -> IProj p (rg_unr cG) rl_end.
  Proof.
    move=>POF /(paco1_unfold WF_mon)-H; move: H POF; case=>/=.
    - move=> P; constructor; apply/paco2_fold; constructor=>//.
      by apply/paco1_fold; constructor.
    - move=> F T C FT wf.
      case: (boolP (p == F))=>[/eqP->|pF]; first by move=>/(_ (pof_from _ _ _)).
      case: (boolP (p == T))=>[/eqP->|pT]; first by move=>/(_ (pof_to _ _ _)).
      (*move=>/(_ (pof_cont _ _ _ )).*)
      move=> nPOF.
      apply (iprj_cnt FT pF pT)=>//=; constructor.
      apply /paco2_fold/prj_end; [|by move: wf=>[]].
      by move: nPOF=>/(_ (pof_cont _ _ _)).
  Qed.

(*  Lemma samedom_unr A
        (CG0 : lbl -> option (mty * rg_ty)) (CL : lbl -> option (mty * A)) :
    same_dom CG0 CL ->
    same_dom (fun lbl : lbl => match CG0 lbl with
                               | Some (t, G) => Some (t, ig_end G)
                               | None => None
                               end) CL.
  Proof.
    move=>DOM l Ty; split=>[][a].
    - case E: (CG0 l)=>[[Ty' a']|]// EQ.
      by move: EQ E=>[<-_] /(dom DOM).
    - by move=>/(dom' DOM)-[b]->; exists (ig_end b).
  Qed.*)

  Lemma IProj_unr p CG L:
    IProj p (ig_end CG) L -> IProj p (rg_unr CG) L.
  Proof.
    move=>/IProj_end_inv; elim/Project_inv=>/=.
    - by move=> G0 -> _ {G0 L}; apply/iproj_end.
    - move=> q CG0 CL _ _ {CG L} pq.
      by constructor=>//=; apply /iprj_end.
    - move=> q CG0 CL _ _ {CG L} pq.
      by constructor=>//=; apply /iprj_end.
    - move=>q r {}CG L0 qr pq pr _ -> PART PRJ {L0}.
      by apply/(iprj_cnt qr pq pr)=>//=; apply /iprj_end.
  Qed.

  Lemma QProj_unr CG Q :
    qProject (ig_end CG) Q -> qProject (rg_unr CG) Q.
  Proof.
    move=>/qProject_end_inv=>->.
    case: CG=>//=; [constructor|].
    move=> F T C; constructor; last by apply/not_fnd.
    by apply: qprj_end.
  Qed.

  Lemma local_runnable G P A G' :
    step A G G' -> Projection G P -> runnable A P.
  Proof.
  move=> ST PRJ.
  move: P PRJ; elim: ST =>
    [ F T t {}G P pro
    | F T t {}G P pro
    | s F T t G0 G1 subF subT st IH P pro
    | s F T t G0 G1 subT st IH P pro
    | a CG G0 st IH P pro
    ] /=.
  - rewrite /runnable/=.
    move: (pro.1 F) => IProj_F.
    move: (IProj_send1_inv IProj_F)=>[FT [[t' L] [ll//= [tt' IProjC]]]].
    by rewrite ll tt' !eq_refl.
  - rewrite /runnable/=.
    move: (pro.1 T) => IProj_T.
    move: (IProj_recv_inv IProj_T)=>[FT [[t' L] [ll//= [tt' IProjC]]]].
    move: (qProject_true_inv pro.2)=>[Q [/eqP-dq _]].
    by rewrite ll dq tt' !eq_refl.
  - move: pro=>/Proj_false_next-pro.
    rewrite (runnable_next (A' := mk_act a_send F T t)) ?subF ?subT//=.
    rewrite (runnable_next (A' := mk_act a_recv T F t)) ?subF ?subT//=.
    by apply IH.
  - move: pro.2=>/qProject_true_inv-[Q' [/eqP-dq qpro]].
    move: pro=>/Proj_true_next-pro.
    rewrite (runnable_next (A':=mk_act a_recv T F t)) ?subT ?orbT //=.
    by apply IH.
  - apply: IH.
    move: pro=>[epro qpro]; split.
    + move: epro; rewrite /eProject=>[pro].
      move=>p; move: (pro p).
      by apply/IProj_unr.
    + by apply/QProj_unr.
  Qed.

  Lemma look_same E F L : look E.[F <- L] F = L.
  Proof. by rewrite /look fnd_set eq_refl. Qed.

  Lemma Projection_send F T t G P :
    Projection (ig_msg false F T (t,G)) P ->
    Projection (ig_msg true F T (t,G)) (run_step (mk_act a_send F T t) P).
  Proof.

    (*we obtain the local and queue environments*)
    move: P=>[E Q]; move=>[/=PRJ QPRJ].

    (*we apply inversion rules of coinductive projection for F and T*)
    move: (IProj_send1_inv (PRJ F))=>[FT [[tF LF] [llF //=[ttF IPRJF]] ]].
    move: (IProj_recv_inv (PRJ T))=>[_ [[tT LT] [llT //=[ttT IPRJT]] ]].

    (*we rewrite the auxiliary function and simplify*)
    rewrite /run_step/= llF ttF !eq_refl//=.
    split=>/=.

    (*we do case analysis on participants for E and we solve each one,
      by applying constructors*)
    - move=>p; case: (boolP (p == F))=>[/eqP->{p}|];
      [|case: (boolP (p == T))=>[/eqP->{p} _|pT pF]].
      + by apply: (iprj_send2 FT FT); rewrite look_same.
      + rewrite look_comm //= llT.
        by apply: (iprj_recv); [rewrite eq_sym|rewrite -ttF|].
      + rewrite look_comm //=; [|by rewrite eq_sym].
        move: (IProj_cnt_inv (PRJ p) pF pT)=>[_ /=] .
          by apply /(@iprj_send2 _ _ _ (tF,G)).

    (*we solve the goal for queue projection: inversion and constructor application*)
    - move: (qProject_false_inv QPRJ)=>[PFT {}QPRJ].
      apply: (qprj_some _ QPRJ)=>//=.
      rewrite /deq/enq PFT fnd_set eq_refl/= remf1_set eq_refl remf1_id //.
      by rewrite -fndSome PFT.
  Qed.

  Lemma Projection_recv F T t G P:
    Projection (ig_msg true F T (t,G)) P ->
    Projection G (run_step (mk_act a_recv T F t) P).
  Proof.
    move=>PRJ.
    move: (qProject_true_inv PRJ.2)=>[Q [/eqP-dq qpro]].
    move: (IProj_recv_inv (PRJ.1 T))=>[FT  [[tT LT] [llT /=[ttT IPRJT]]]].
    move: (IProj_send2_inv (PRJ.1 F) FT)=>[_ /=IPRJF].
    rewrite /run_step/= llT ttT !eq_refl dq/=.
    split=>//=.
    move=>p; case: (boolP (p == F))=>[/eqP->{p}|];
             [|case: (boolP (p == T))=>[/eqP->{p} _|pT pF]].
    - by rewrite look_comm; [|rewrite eq_sym].
    - by rewrite look_same.
    - move: (IProj_send2_inv (PRJ.1 p) pT)=>[_].
      by rewrite look_comm //= eq_sym.
  Qed.

  Lemma do_actC E0 E1 E2 A1 A2 :
    subject A1 != subject A2 ->
    do_act E0 A1 = Some E1 ->
    do_act E0 A2 = Some E2 ->
    exists E3, do_act E1 A2 = Some E3 /\ do_act E2 A1 = Some E3.
  Proof.
    case: A1=>[a1 F1 T1 t1]; case: A2=>[a2 F2 T2 t2]/= FF.
    case E0F1: (look E0 F1) =>[|a3 q3 [t3 L3]]//;
    case E0F2: (look E0 F2) =>[|a4 q4 [t4 L4]]//.
    case: ifP=>// EQ [<-]; case: ifP=>// EQ' [<-].
    rewrite /look !fnd_set eq_sym (negPf FF).
    move: E0F1; rewrite /look; case: E0.[? _] =>// L0->.
    move: E0F2; rewrite /look; case: E0.[? _] =>// {}L0->.
    rewrite EQ' EQ setfC eq_sym (negPf FF).
    by exists (E0.[F2 <- L4]).[F1 <- L3].
  Qed.

  Lemma do_act_none E0 E1 A1 A2 :
    subject A1 != subject A2 ->
    do_act E0 A1 = Some E1 ->
    do_act E0 A2 = None ->
    do_act E1 A2 = None.
  Proof.
    case: A1=>[a1 F1 T1 t1]; case: A2=>[a2 F2 T2 t2]/= FF.
    case E0F1: (look E0 F1)=>[|a3 q3 [t3 L3]]//.
    case: ifP=>// EQ [<-].
    case E0F2: (look E0 F2)=>[|a4 q4 [t4 L4]]//.
    - rewrite /look fnd_set eq_sym (negPf FF).
      by move: E0F2; rewrite /look; case: (E0.[? F2])=>// L->.
    - case: ifP=>// EQ0; move: E0F2.
      by rewrite /look fnd_set eq_sym (negPf FF)=>->; rewrite EQ0.
  Qed.

  Lemma enqC k k' (NEQ : k != k') Q v v' :
    enq (enq Q k v) k' v' = enq (enq Q k' v') k v.
  Proof.
    by rewrite /enq; case Qk: Q.[? k] => [W|];
       rewrite fnd_set eq_sym (negPf NEQ); case: Q.[? k'] =>[W'|];
       rewrite fnd_set (negPf NEQ) Qk //= setfC eq_sym (negPf NEQ).
  Qed.

  Lemma runnable_recv_deq F T t P :
    runnable (mk_act a_recv F T t) P ->
    exists Q W, deq P.2 (T, F) = Some (t, Q) /\
              P.2.[? (T, F)] = Some (t :: W) /\
              forall k, k != (T, F) -> Q.[? k] = P.2.[? k].
  Proof.
    rewrite /runnable/=.
    case PF: (look P.1 F) =>[|a r [t' L']]//.
    case: ifP=>//= COND; case DEQ: deq=>[[t'' Q]|]// E1.
    move:E1 DEQ=>/eqP<-.
    rewrite /deq; case PTF: (P.2.[? (T, F)])=>[[|V' W]|]//=.
    case: ifP=> we [[te Qe]].
    - exists Q, [::]; move: we=>/eqP->; rewrite te; do !split=>//=.
      by move=> k NEQ; rewrite -Qe fnd_rem1 NEQ.
    - exists Q, W;  rewrite te; do !split=>//=.
      by move=> k NEQ; rewrite -Qe fnd_set (negPf NEQ).
  Qed.

  Lemma deq_enq_neqC k k' (NEQ : k != k') v Q :
    deq (enq Q k v) k' =
    match deq Q k' with
    | Some (v', Q') => Some (v', enq Q' k v)
    | None => None
    end.
  Proof.
    by rewrite /deq/enq; (have NEQ': (k' != k) by (move: NEQ; rewrite eq_sym));
       case Qk': Q.[? k'] =>[[|v0 [|v1 w0] ]|]//=; case Qk: Q.[? k] =>[W|];
       rewrite fnd_set eq_sym (negPf NEQ) Qk' //= ?fnd_rem1 ?fnd_set (negPf NEQ)
               //= Qk ?remf1_set //= ?(negPf NEQ') //= setfC (negPf NEQ').
  Qed.

  Lemma deq_enq_sameC Q k' v' Q' :
    deq Q k' = Some (v', Q') ->
    forall k v, deq (enq Q k v) k' = Some (v', enq Q' k v).
  Proof.
    rewrite /deq; case Qk': Q.[? k'] => [[|V0 [|V0' W0]]|]//= [<-<-] {v' Q'} k v.
    - rewrite /enq; case Qk: Q.[? k] => [W|]//=; rewrite fnd_set;
      move: Qk' Qk; case: ifP=>[/eqP->|neq] Qk'; rewrite Qk'//=.
      + move=> [<-]/=; rewrite fnd_rem1 eq_refl /=.
        by rewrite setfC eq_refl setf_rem1.
      + by move=> Qk; rewrite fnd_rem1 eq_sym neq /= Qk remf1_set neq.
      + by move=> Qk; rewrite fnd_rem1 eq_sym neq /= Qk remf1_set neq.
    - rewrite /enq; case Qk: Q.[? k] => [W|]//=; rewrite fnd_set;
      move: Qk' Qk; case: ifP=>[/eqP->|neq] Qk'; rewrite Qk'//=.
      + move=> [<-]/=; rewrite fnd_set eq_refl /=.
        by rewrite setfC eq_refl setfC eq_refl.
      + by move=> Qk; rewrite fnd_set eq_sym neq /= Qk setfC neq.
      + by move=> Qk; rewrite fnd_set eq_sym neq /= Qk setfC neq.
  Qed.

  Lemma  deq_someC k0 k1 (NEQ : k0 != k1) Q v0 v1 Q0 Q1 :
    deq Q k0 = Some (v0, Q0) ->
    deq Q k1 = Some (v1, Q1) ->
    exists Q2, deq Q0 k1 = Some (v1, Q2) /\ deq Q1 k0 = Some (v0, Q2).
  Proof.
    rewrite /deq.
    case Qk0: Q.[? k0] => [[|V0 [|V0' W0]]|]//=;
    case Qk1: Q.[? k1] => [[|V1 [|V1' W1]]|]//= [<-<-] [<-<-] {v0 v1}.
    - exists Q.[~ k0].[~ k1].
      rewrite fnd_rem1 eq_sym NEQ Qk1 /= fnd_rem1 NEQ Qk0 /=; split=>//.
      by rewrite !remf_comp fsetUC.
    - exists Q.[~ k0].[k1 <- V1' :: W1].
      rewrite fnd_rem1 eq_sym NEQ Qk1 /=; split=>//.
      by rewrite fnd_set (negPf NEQ) Qk0 /= remf1_set (negPf NEQ).
    - exists (Q.[k0 <- V0' :: W0]).[~ k1].
      rewrite fnd_set eq_sym (negPf NEQ) Qk1; split=>//.
      by rewrite fnd_rem1 NEQ Qk0 /= remf1_set eq_sym (negPf NEQ).
    - exists (Q.[k0 <- V0' :: W0]).[k1 <- V1' :: W1].
      rewrite !fnd_set eq_sym (negPf NEQ) Qk0 Qk1 /=; split=>//.
      by rewrite setfC (negPf NEQ).
  Qed.

  Lemma  deq_noneC k0 k1 (NEQ : k0 != k1) Q v0 Q0 :
    deq Q k0 = Some (v0, Q0) ->
    deq Q k1 = None ->
    deq Q0 k1 = None.
  Proof.
    rewrite [in deq Q k0]/deq.
    by case Qk0: Q.[? k0] =>[[|V [|V' W]]|]//= [_ <-];
       rewrite /deq; case Qk1: Q.[? k1] =>[[|V1 [|V2 W1]]|]//=_;
       rewrite ?fnd_rem1 ?fnd_set eq_sym (negPf NEQ)/= Qk1.
  Qed.


  Lemma deq_neqC k k' (NEQ : k != k') Q :
    match deq match deq Q k' with | Some (_, Q') => Q' | None => Q end k with
    | Some (_, Q') => Q'
    | None => match deq Q k' with | Some (_, Q') => Q' | None => Q end
    end =
    match deq match deq Q k with | Some (_, Q') => Q' | None => Q end k' with
    | Some (_, Q') => Q'
    | None => match deq Q k with | Some (_, Q') => Q' | None => Q end
    end.
  Proof.
    case Qk': (deq Q k')=>[[v' Q']|];
      case Qk: (deq Q k)=>[[v Q'']|]; rewrite ?Qk' //.
    - by move: (deq_someC NEQ Qk Qk')=>[Q2] [->->].
    - by rewrite (deq_noneC _ Qk' Qk) // eq_sym.
    - by rewrite (deq_noneC NEQ Qk Qk').
  Qed.

  Lemma do_queueC A A' P :
    subject A != subject A' ->
    (subject A != object A') || (act_ty A' == a_recv) && runnable A' P ->
    do_queue (do_queue P.2 A') A = do_queue (do_queue P.2 A) A'.
  Proof.
    case: A=>[[] F T Ty]; case: A'=>[[] F' T' Ty']//=.
    - by rewrite orbC/==> FF FT; rewrite enqC // xpair_eqE eq_sym negb_and FF.
    - move=> FF /orP-[FT|/runnable_recv_deq-[Q] [W] [DEQ] [LOOK] Q_EQ].
      + by rewrite deq_enq_neqC ?xpair_eqE ?negb_and ?FT //; case: deq=>[[]|].
      + by rewrite DEQ (deq_enq_sameC DEQ).
    - move=> FF; rewrite orbC eq_sym=>/= FT.
      by rewrite deq_enq_neqC ?xpair_eqE ?negb_and ?FT ?orbT//;case: deq=>[[]|].
    - by move=> FF _; apply: deq_neqC; rewrite xpair_eqE negb_and orbC FF.
  Qed.

  Lemma run_stepC A A' P :
    subject A != subject A' ->
    (subject A != object A') || ((act_ty A' == a_recv) && runnable A' P) ->
    run_step A (run_step A' P) = run_step A' (run_step A P).
  Proof.
    rewrite /run_step;
    case PA': (do_act P.1 A')=>[E'|]/=; case PA: (do_act P.1 A)=>[E|]//=;
    rewrite ?PA' ?PA // => SUBJ.
    - move: (do_actC SUBJ PA PA')=> [E3] [->->] COND.
      by rewrite do_queueC.
    - by move: SUBJ; rewrite eq_sym=>SUBJ; rewrite (do_act_none SUBJ PA' PA).
    - by rewrite (do_act_none SUBJ PA PA').
  Qed.

  Lemma Projection_runnable F T t G P :
    Projection (ig_msg true F T (t,G)) P ->
    runnable (mk_act a_recv T F t) P.
  Proof.
    move=> [EPROJ QPROJ].
    move: EPROJ; rewrite /eProject=>/(_ T)-PRJ.
    move: PRJ=>/IProj_recv_inv=>[[FT [[t' L] [ll //=[tt' PRJ]]]]].
    move: QPROJ=>/qProject_true_inv=>[[Q' [/eqP-DEQ QPRJ]]].
    by rewrite /runnable/= ll -tt' !eq_refl /= DEQ.
  Qed.

  Lemma Projection_unr G P :
    Projection (ig_end G) P -> Projection (rg_unr G) P.
  Proof.
    move=>[EPRJ QPRJ]; split.
    - move=>p; move: (EPRJ p)=>{}EPRJ.
      by apply: IProj_unr.
    - by apply: QProj_unr.
  Qed.

(*  Definition PAll co_merge (C : lbl -> option (mty * ig_ty)) P
    := forall l Ty G, C l = Some (Ty, G) -> Projection co_merge G (P l Ty).*)

  Definition send_recv F T t P :=
    run_step (mk_act a_recv T F t) (run_step (mk_act a_send F T t) P).

  Lemma look_act A P F :
    subject A != F -> look (run_step A P).1 F = look P.1 F.
  Proof.
    case A=>[a p q t]; rewrite /run_step/do_act/=.
    case: (look P.1 p) =>// a' r' [t' L]//=.
    by case: ifP=>// _ pF; rewrite look_comm.
  Qed.

  Lemma queue_act A F T P :
    (subject A != F) ->
    (subject A != T) ->
    ((run_step A P).2).[? (F, T)] = P.2.[? (F, T)].
  Proof.
    case A=>[a p q t]; rewrite /run_step/do_act/=.
    case: (look P.1 p) =>// a' r' [t' L]//=.
    case: ifP=>//_ pF pT; case: a=>//; rewrite /enq/deq.
    - by case: P.2.[? _] =>[a|]; rewrite fnd_set xpair_eqE eq_sym (negPf pF).
    - case: P.2.[? _] =>[[|V0 [|V1 W]]|]//.
      + by rewrite fnd_rem1 xpair_eqE negb_and orbC eq_sym  (negPf pT).
      + by rewrite fnd_set xpair_eqE andbC eq_sym (negPf pT).
  Qed.

(*  Definition buildC (C : lbl -> option (mty * ig_ty)) E p :=
    fun l => match C l with
             | Some (Ty, _) => Some (Ty, look E p)
             | None => None
             end.*)

(*  Lemma dom_buildC C E p : same_dom C (buildC C E p).
  Proof.
    move=>l Ty; rewrite/buildC;case EQ: (C l)=>[[Ty' G]|]; split=>[][G']//[->_].
    - by exists (look E p).
    - by exists G.
  Qed.*)

(*  Lemma mrg_buildC C E p : simple_co_merge (buildC C E p) (look E p).
  Proof.
    move=> l Ty L'; rewrite /buildC; case: (C l)=>[[Ty' G]|]// [_->].
    by apply: EqL_refl.
  Qed.
  Arguments mrg_buildC C E p : clear implicits.*)

(*  Lemma proj_all P C Cl :
    same_dom C Cl ->
    PAll simple_co_merge C P ->
    forall p,
      (forall l Ty L, Cl l = Some (Ty, L) -> look (P l Ty).1 p = L) ->
      R_all (IProj simple_co_merge p) C Cl.
  Proof.
    move=> DOM All p H l Ty G L /All-[ePRJ qPRJ] Cll.
    by move: (H l Ty L Cll) (ePRJ p) =>->.
  Qed.*)

  Lemma case_part (p F T : role) : p = F \/ p = T \/ (p != F /\ p != T).
  Proof.
    case: (boolP (p == F))=>[/eqP-pF|pF]; [by left|right].
    by case: (boolP (p == T))=>[/eqP-pT|pT]; [by left|right].
  Qed.

  Lemma Proj_send_undo F T t LF LT G P:
    F != T ->
    look P.1 F = rl_msg a_send T (t, LT) ->
    look P.1 T = rl_msg a_recv F (t, LF) ->
    Projection G (send_recv F T t P) ->
    (P.2).[? (F, T)] = None ->
    Projection (ig_msg false F T (t,G)) P.
  Proof.
    move=> FT EF ET PRJ QPRJ.
    split.
    - move=> p; move: (case_part p F T)=>[->|[->|[pF pT]]].
      + rewrite EF; constructor=>//=.
        move: (PRJ.1 F); rewrite /send_recv look_act//=; [|by rewrite eq_sym].
        by rewrite /run_step/= EF !eq_refl/= look_same.
      + rewrite ET; constructor=>//=; [by rewrite eq_sym|].
        move: (PRJ.1 T); rewrite /send_recv /run_step/= EF !eq_refl/=.
        by rewrite look_comm//= ET !eq_refl/= look_same.
      + apply: (iprj_cnt FT pF pT)=>//=.
        move: (PRJ.1 p); rewrite /send_recv look_act//=;[|by rewrite eq_sym].
        by rewrite look_act//= eq_sym.
    - constructor=>//=.
      move: (PRJ.2); rewrite /send_recv/run_step/= EF !eq_refl/=.
      rewrite look_comm// ET !eq_refl/= /deq/enq QPRJ fnd_set eq_refl/=.
      by rewrite remf1_set eq_refl remf1_id// -fndSome QPRJ.
  Qed.

  Lemma deq_act A F T P t Q' :
    subject A != T ->
    deq P.2 (F, T) = Some (t, Q') ->
    deq (run_step A P).2 (F, T) = Some (t, (run_step A (P.1, Q')).2).
  Proof.
    case: A=>[a p q t']; rewrite /run_step/=.
    case: look=>[|a0 r0 [t0 L0]]//.
    case: ifP=>//COND; case: a COND=>//= COND pT.
    - by move=>DEQ; apply: (deq_enq_sameC DEQ).
    - rewrite /deq/=.
      case EQ: (P.2.[? (F, T)])=>[[|V0 W]|]//.
      case EQ': (P.2.[? (q, p)])=>[[|V1 W']|]//.
      + rewrite EQ.
        case: ifP EQ=>[/eqP->|WEQ]; move=>PFT [<-] <-.
        * by rewrite fnd_rem1 xpair_eqE negb_and orbC pT /= EQ'.
        * by rewrite fnd_set xpair_eqE andbC (negPf pT) /= EQ'.
      + case: ifP EQ=>[/eqP-EQW|WEQ]  PFT [<-<-]; case:ifP=>EQ//.
        * rewrite fnd_rem1 xpair_eqE negb_and orbC eq_sym pT PFT /orb EQW.
          rewrite eq_refl fnd_rem1 xpair_eqE negb_and pT orbT EQ' EQ /orb.
          by rewrite !remf_comp fsetUC.
        * rewrite fnd_set xpair_eqE andbC eq_sym (negPf pT) PFT /andb EQW.
          rewrite fnd_rem1 xpair_eqE negb_and pT orbT EQ' EQ remf1_set.
          by rewrite xpair_eqE andbC eq_sym (negPf pT).
        * rewrite fnd_rem1 xpair_eqE negb_and orbC eq_sym pT /orb PFT.
          rewrite fnd_set xpair_eqE (negPf pT) andbC /andb EQ' EQ WEQ.
          by rewrite remf1_set xpair_eqE (negPf pT) andbC.
        * rewrite fnd_set xpair_eqE andbC eq_sym (negPf pT) /andb PFT WEQ.
          rewrite fnd_set xpair_eqE andbC (negPf pT) /andb EQ' EQ.
          by rewrite setfC xpair_eqE andbC eq_sym (negPf pT).
      + case: ifP EQ=>[/eqP->|WEQ] PFT [<-<-]; rewrite PFT.
        * by rewrite fnd_rem1 xpair_eqE negb_and pT orbC /= EQ'.
        * by rewrite WEQ fnd_set xpair_eqE andbC (negPf pT)/= EQ'.
  Qed.



  (*Definition R_all_except (l' : lbl) (R : ig_ty -> rl_ty -> Prop)
             (C : lbl -> option (mty * ig_ty))
             (lC : lbl -> option (mty * rl_ty)) :=
    forall l Ty G L,
      l' != l -> C l = Some (Ty, G) -> lC l = Some (Ty, L) -> R G L.*)

  (*Definition updC A (l : lbl) (Ty : mty) C (a : A) l' :=
    if l == l' then
      Some (Ty, a) (* look E p *)
    else
      C l'.*)

  (*Lemma dom_updC A l Ty C (a : A) L' :
    C l = Some (Ty, L') ->
    same_dom C (updC l Ty C a).
  Proof.
    move=>Cl l1 Ty1;split=>[][G]; rewrite/updC; case: ifP=>EQ.
    + by move: EQ=>/eqP<-; rewrite Cl=>[][<- _]; exists a.
    + by move=>->; exists G.
    + by move: EQ=>/eqP<-; move=>[<-]; exists L'.
    + by move=>->; exists G.
  Qed.*)

  Lemma Proj_recv_undo F T t LT P G Q' :
    F != T ->
    (*C l = Some (Ty, G) ->*)
    look P.1 T = rl_msg a_recv F (t,LT) ->
    (*same_dom C lCT ->*)
    (*R_all_except l (IProj simple_co_merge T) C lCT ->*)
    deq P.2 (F, T) = Some (t, Q') ->
    (*(forall p, exists lC, same_dom C lC /\ R_all_except l (IProj simple_co_merge p) C lC)  ->*)
    Projection G (run_step (mk_act a_recv T F t) P) ->
    Projection (ig_msg true F T (t,G)) P.
  Proof.
    move=> FT llT dq PRJ; split.
    - move=>p; case: (boolP (p == T))=>[/eqP->|pT].
      + move: FT; rewrite eq_sym llT =>TF.
        apply (iprj_recv true TF)=>//=.
        by move: (PRJ.1 T); rewrite /run_step/= llT !eq_refl/= look_same.
      + move: (PRJ.1 p); rewrite /run_step/= llT !eq_refl/=.
        rewrite look_comm; [|by rewrite eq_sym].
        by move=> IPRJ; apply iprj_send2.
    - by move: PRJ.2; apply: qprj_some; rewrite /run_step/= llT !eq_refl/= dq.
  Qed.

  (*here*)

(*  (* Not quite right yet *)
  Lemma  proj_same l C0 C1 F T E :
    same_dom C0 C1 ->
    (forall l' K, l != l' -> C0 l' = Some K <-> C1 l' = Some K) ->
    eProject simple_co_merge (ig_msg (Some l) F T C0) E ->
    forall p, exists lC,
        same_dom C1 lC /\
        forall l' Ty' G' L',
          l != l' ->
          C1 l' = Some (Ty', G') ->
          lC l' = Some (Ty', L') ->
          IProj simple_co_merge p G' L'.
  Proof.
    move=> DOM SAME_C PRJ p.
    move: (IProj_recv_inv (PRJ T))=>[FT] [lC] [ET] [DOMT] ALLC.
    move _: DOM => DOM'; move:DOM'=>/same_dom_sym/same_dom_trans/(_ DOMT)-{}DOMT.
    case: (boolP (p == T))=>[/eqP->|NEQ].
    - exists lC; split=>// l' Ty' G' L' NE C1l lCl.
      by apply/(ALLC _ _ _ _ _ lCl)/SAME_C.
    - move: (IProj_send2_inv (PRJ p) NEQ)=>[_] [lCp] [Typ] [lCpl] [DOMp] ALLp.
      move _: DOM => DOM'; move:DOM'=>/same_dom_sym/same_dom_trans/(_ DOMp)-{}DOMp.
      exists lCp; split=>// l' Ty' G' L' NE C1l lCl.
      by apply/(ALLp _ _ _ _ _ lCl)/SAME_C.
  Qed.*)

  Lemma runstep_proj G P : forall A G',
      step A G G' ->
      Projection G P ->
      Projection G' (run_step A P).
  Proof.
    move=> A G' ST; move: P; elim: ST=>
    [ F T t G0 P
    | F T t G0 P
    | {}A F T t G0 G1 AF AT st IH P PRJ
    | {}A F T t G0 G1 AT st IH P PRJ
    | {}A G0 G0' st IH P
    ]/=.
    - by apply: Projection_send.
    - by apply: Projection_recv.
    - move: (IProj_send1_inv (PRJ.1 F))=>[FT [[t' L'] [llF [/=tt' IPROJF]]]].
      move: (IProj_recv_inv (PRJ.1 T))=>[_ [[t'' L''] [llT [/=tt'' IPROJT]]]].
      move: llF; rewrite -(look_act _ AF)=>{}llF.
      move: llT; rewrite -(look_act _ AT)=>{}llT.
      rewrite -tt' in llF; rewrite -tt'' in llT.
      move: (Proj_false_next PRJ)=>PRJ0.
      apply: (Proj_send_undo FT llF llT);
        [|by move: PRJ.2=>/qProject_false_inv-[QPRJ] _; rewrite queue_act].
      rewrite /send_recv.
      rewrite -(run_stepC (A:=A)) ?AT//= -(run_stepC (A:=A)) ?AF ?AT//=.
        by apply IH.
    - move: (Projection_runnable PRJ)=>RUN.
      move: (IProj_recv_inv (PRJ.1 T))=>[FT [[t' L'] []]].
      rewrite -(look_act _ AT)=> llT [/=tt' IPROJT].
      rewrite -tt' in llT; move: (Proj_true_next PRJ)=>/IH.
      rewrite run_stepC/= ?RUN ?orbT//==>PRJ0.
      Search run_step.
      move: PRJ.2=>/qProject_true_inv[Q' [/eqP/(deq_act AT)-DQ QPRJ]].
      by apply: (Proj_recv_undo FT llT DQ PRJ0).
    - by move=>/Projection_unr; apply IH.
  Qed.
  (*here*)
  (*
  Definition payload A :=
    let: (mk_act _ _ _ l Ty) := A in (l, Ty).

  Definition match_fst (A : eqType) (a : A) B (V : option (A * B)) :=
    match V with
    | None => false
    | Some (t, _) => t == a
    end.

  Lemma step_queue A P P' :
    lstep A P P' ->
    (act_ty A == l_send) || match_fst (payload A) (deq P.2 (object A, subject A)).
  Proof.
      by case=>// Ty F T l {P P'}E E' Q Q' /eqP/=->; rewrite /match_fst eq_refl.
  Qed.

  Lemma step_look_notend P P' A :
    lstep A P P' -> look P.1 (subject A) = rl_end -> False.
  Proof. by elim/lstep_inv=>//= _ Ty F T l E E' Q Q' _; case: look. Qed.

  Lemma step_look_cont P P' A a p C :
    lstep A P P' -> look P.1 (subject A) = rl_msg a p C ->
    match_fst (payload A).2 (C (payload A).1) /\ act_ty A = a /\ object A = p.
  Proof.
    by elim/lstep_inv=>//= _ Ty F T l E E' Q Q' _; case: look=>// a' p' C';
       case C'l: (C' l)=>[[Ty' L']|]//; case: ifP=>//B _ _ _ _ EQ {A P P'};
       rewrite /match_fst; move: EQ B=>[<- <-<-] /andP-[/andP-[]];
       move=>/eqP<-/eqP<- EQ; rewrite C'l eq_sym EQ; do ! split.
  Qed.

  Definition step_find A P P' :
    lstep A P P' ->
    {C & { L |
      look P.1 (subject A) = rl_msg (act_ty A) (object A) C /\
      C (payload A).1 = Some ((payload A).2, L) } }.
  Proof.
    case: A=>[[] F T l Ty]/=; move: {-1}(look P.1 F) (erefl (look P.1 F))=>[].
    - by move=> LF ST; move: (step_look_notend ST LF).
    - move=> a R C L ST; exists C.
      move: (step_look_cont ST L)=>/=; rewrite /match_fst.
      case: (C l)=>[[Ty' L']|]//; last by move=>[][].
      by move=>[/eqP->][<-]<-; exists L'.
    - by move=> LF ST; move: (step_look_notend ST LF).
    - move=> a R C L ST; exists C.
      move: (step_look_cont ST L)=>/=; rewrite /match_fst.
      case: (C l)=>[[Ty' L']|]//; last by move=>[][].
      by move=>[/eqP->][<-]<-; exists L'.
  Qed.

  Lemma Project_gstep_proj G P A P' G' :
    lstep A P P' ->
    step A G G' ->
    Projection simple_co_merge G P ->
    Projection simple_co_merge G' P'.
  Proof.
    move=> ST; move: (run_step_compl ST)=>E; move: E ST=>->_.
    by apply/runstep_proj.
  Qed.

  Lemma project_pall F G L a T C :
    Project simple_co_merge F G L ->
    L = rl_msg a T C ->
    part_of_all F G.
  Proof.
    elim/Project_inv=>//.
    - by move=> q {}C _ _ _ _ _ _ _; constructor.
    - by move=> q {}C _ _ _ _ _ _ _; constructor.
    - move=> F' T' C' CL L' F'T' FF' FT' _ _ _ ALL _ _ _ _ {G L'}.
      by constructor.
  Qed.

  Inductive option_spec A (o : option A) : Type :=
  | oSome x : o = Some x -> option_spec o
  | oNone : o = None -> option_spec o.

  Lemma optionP A (o : option A) : option_spec o.
  Proof.
    case: o=>[x|].
    by apply/oSome/erefl.
    by apply/oNone.
  Qed.

  Lemma CProj_step l Ty L1 F G L0 T C :
    C l = Some (Ty, L1) ->
    Project simple_co_merge F G L0 ->
    L0 = rl_msg l_send T C ->
    { G' | step (mk_act l_send F T l Ty) (ig_end G) G' }.
  Proof.
    move=> Cl PRJ EL; move: (project_pall PRJ EL)=>/find_partsc-PART.
    move: EL PRJ=>->; elim: PART.
    - move=> {}F T' C' PRJ.
      have [<- DOM]: T = T'/\ same_dom C' C.
      { move: PRJ; elim/Project_inv=>//;
                 last by move=> q s CG CL L2 _ /eqP-Fq _ [] /esym/Fq.
        by move=>q CG CL  [->->] [->->] FT DOM _; split.
      }
      exists (ig_msg (Some l) F T (fun l =>
                                     match C' l with
                                     | Some (Ty, G) => Some (Ty, ig_end G)
                                     | None => None
                                     end)).
      by move: (dom' DOM Cl)=>[G'] Cl'; apply/st_unr/st_send; rewrite Cl'.
    - move=> F' T' C' PRJ; exfalso.
      move: PRJ; elim/Project_inv=>// .
      + by move=> q CG CL [->->->]; rewrite eq_refl.
      + by move=> q s CG CL L2 qs T'q /eqP-T's [_ /esym/T's].
    - move=> p {}F T' C' H0 Ih.
      case: (boolP (p == F))=>[/eqP->|].
      + move=> PRJ; have [<- DOM]: T = T'/\ same_dom C' C.
        { move: PRJ; elim/Project_inv=>//;
                         last by move=> q s CG CL L2 _ /eqP-Fq _ [] /esym/Fq.
            by move=>q CG CL  [->->] [->->] FT DOM _; split.
        }
        exists (ig_msg (Some l) F T (fun l =>
                                       match C' l with
                                       | Some (Ty, G) => Some (Ty, ig_end G)
                                       | None => None
                                       end)).
        by move: (dom' DOM Cl)=>[G'] Cl'; apply/st_unr/st_send; rewrite Cl'.
      + move=> pF PRJ.
        have [{}PRJ [NE pT']]: (forall l Ty G, C' l = Some (Ty, G) ->
                                               Project simple_co_merge p G (rl_msg l_send T C))
                               /\ (exists l' Ty' G', C' l' = Some (Ty', G'))
                               /\ p != T'.
        { move: PRJ; elim/Project_inv=>//.
          - by move=>q CG CL [/eqP]; rewrite (negPf pF).
          - move=>q s CG CL L2 qs pq ps E1 E2.
            move: E1 E2 qs pq ps=>[->->->] _ FT PF PT {q s CG L2}.
            move=> NE _ DOM ALL MRG; split=>//.
            move=> l0 Ty0 G0 Cl1.
            move: (dom DOM Cl1)=>[L'] CLl'; move: (MRG _ _ _ CLl')=>EQ.
            by apply/(EqL_Project EQ)/(ALL _ _ _ _ Cl1).
        }
        set C'' :=
          fun l =>
            match optionP (C' l) with
            | oSome (Ty, G) P => Some (Ty, sval (Ih _ _ _ P (PRJ _ _ _ P)))
            | oNone _ => None
            end.
        exists (ig_msg None F T' C''); move: NE=>[l' NE].
        have {}NE: exists Ty' G', (fun lbl : lbl =>
                                     match C' lbl with
                                     | Some (t, G0) => Some (t, ig_end G0)
                                     | None => None
                                     end) l' = Some (Ty', G')
            by move: NE=>[Ty' [G' C'l']]; rewrite C'l'; exists Ty', (ig_end G').
        apply/st_unr/(st_amsg1 _ _ NE)=>//=.
        * rewrite /C'' /==> l0 Ty0; case: optionP=>[[Ty1 G1] E|->]//; rewrite E.
          split=>[][G2][<-] _; last by exists (ig_end G1).
          by exists (sval (Ih l0 Ty1 G1 E (PRJ l0 Ty1 G1 E))).
        * move=> l0 Ty0 G0 G1; rewrite /C''; case: optionP=>//.
          move=> [Ty1 G2] E; rewrite E=>[][<-<-] [<-].
          by move: (Ih l0 Ty1 G2 E (PRJ l0 Ty1 G2 E))=>[IG ST]/=.
  Qed.

  Definition match_lbl A (l : lbl) (o : option (lbl * mty * A)) : Prop :=
    match o with
    | Some (l', _, _) => l == l'
    | None => false
    end.

  Lemma Project_gstep G P A P' :
    lstep A P P' ->
    Projection simple_co_merge G P ->
    {G' | step A G G'}.
  Proof.
    case: A=>a F T l Ty ST PRJ.
    move: PRJ.2 (step_queue ST)=>/=.
    move: (step_find ST) (PRJ.1 F)=>/=[C][L1][]/=-> Cl {ST P'}PRJ QPRJ DEQ.
    elim: G P.2=>[CG|o F' T' C' Ih] {P}Q in PRJ DEQ QPRJ *.
    - move: (qProject_end_inv QPRJ)=>EQ; move: EQ DEQ=>->.
      rewrite /match_fst/deq/= not_fnd//= orbC /==>/eqP-a_snd.
      move: a_snd PRJ=>->PRJ.
      by apply/(CProj_step Cl (IProj_end_inv PRJ)).
    - move: PRJ QPRJ DEQ; case: (boolP (F == T'))=>[|FT'].
      { move=>/eqP<- PRJ; move: (IProj_recv_inv PRJ)=>[FF']PRJ' QPRJ DEQ{Ih}.
        have [a_rcv [TF'][DOM]{}PRJ]:
          a = l_recv /\ T = F' /\ same_dom C' C /\ R_all (IProj simple_co_merge F) C' C
          by move: PRJ'=>[lC][][->->->][DOM] PRJ0; do 2 split=>//.
        move: a_rcv TF' DEQ=>->->/= DEQ {a PRJ' T}.
        have OL: o = Some l.
        { case: o QPRJ=>[l'|].
          * move=>/qProject_Some_inv-[Ty'][G'][Q'][_][DEQ'] _.
            move: DEQ DEQ'; rewrite /match_fst /deq.
            case PTF: Q.[? _] =>[[|V1 W1]|]//.
            rewrite -fun_if -fun_if=>E1; move: E1 PTF=>/eqP->PTF {V1}.
            by move=>/eqP-[->].
          * move=>/qProject_None_inv=>[][PFF'] _.
            move: DEQ PFF'; rewrite /match_fst/deq.
            by case PTF: Q.[? _] =>[[|V1 W1]|]//.
        }
        move: OL QPRJ=>-> QPRJ {DEQ QPRJ}.
        case: (optionP (C' l)); last by move=>/(dom_none DOM); rewrite Cl.
        move=>[Ty' G'] C'l; have: Ty = Ty'
                by move: (dom' DOM Cl)=>[G'']; rewrite C'l=>[][->].
        move=> ETy; move: ETy C'l=><- ETy; exists G'.
        by constructor.
      }
      case: o =>[l'|].
      { move=>PRJ; move: (IProj_send2_inv PRJ FT')=>[F'T']{}PRJ QPRJ.
        move: (qProject_Some_inv QPRJ)=>{}QPRJ DEQ.
        have: match_lbl l' (deq Q (F', T'))
          by move: QPRJ=>[Ty1][G][Q'][_][]/eqP->; rewrite /match_lbl eq_refl.
        case DQ1: deq =>[[[l'' Ty'] Q']|]//= /eqP-ll'.
        move: ll' DQ1=><- DQ1 {l''}.
        have {}DEQ: (a == l_send) || match_fst (l, Ty) (deq Q' (T, F)).
        { move: DEQ=>/orP-[/eqP->//|]; move: DQ1; rewrite /match_fst/deq/=.
          case EQ1: Q.[? _] =>[[|V1 W1]|]//; do 2 rewrite -fun_if.
          move=>[_ <-];case EQ2: Q.[? _] =>[[|V2 W2]|]//; do 2 rewrite -fun_if.
          move=>/eqP<-; apply/orP; right.
          rewrite (fun_if (fun Q => (ffun_of_fmap Q).[? _])).
          rewrite ?fnd_rem1 ?fnd_set xpair_eqE (negPf FT') Bool.andb_false_r.
          by rewrite if_same EQ2; do 2 rewrite -fun_if; rewrite eq_refl.
        }
        have: match_fst Ty' (C' l')
          by move: QPRJ=>[Ty0][G0][Q0][->][]; rewrite DQ1=>/eqP-[<-]; rewrite /match_fst eq_refl.
        case C'l': (C' l')=>[[Ty0 G']|]//; rewrite /match_fst=>/eqP-ETy.
        move: ETy C'l'=>-> C'l' {Ty0}.
        move: Ih=>/(_ _ _ _ C'l' Q' _ DEQ)-Ih.
        have {}PRJ: IProj simple_co_merge F G' (rl_msg a T C).
        { move: PRJ=>[lC][Ty0][lCl'][DOM] PRJ.
          move: (dom DOM C'l')=>[L]; rewrite lCl'=>[][ETy0] _.
          move: ETy0 lCl' =>-> lCl' {Ty0}.
          by apply/(PRJ _ _ _ _ C'l' lCl').
        }
        have {}QPRJ: qProject G' Q'.
        { move: QPRJ=>[Ty0][G0][Q''][C'l'0][]; rewrite DQ1=>/eqP-[_ <-].
          by move: C'l'0; rewrite C'l'=>[][_]<-.
        }
        move: Ih=>/(_ PRJ QPRJ)-Ih.
        set C'' := fun l => if l == l' then Some (Ty', sval Ih) else C' l.
        exists (ig_msg (Some l') F' T' C'').
        apply/st_amsg2=>//=; last split.
        + rewrite /C'' =>l1 Ty1; case: ifP=>[/eqP->|]//; rewrite C'l'.
          by split=>[][IG][<-] _; [exists (sval Ih) | exists G'].
        + by move=> l0 K0 NE; rewrite /C'' eq_sym (negPf NE).
        + exists Ty', G', (sval Ih); do 2 split=>//; first by rewrite /C'' eq_refl.
          by apply/(proj2_sig Ih).
      }
      case: (boolP (F == F'))=>[/eqP<-|].
      {move=>PRJ; move: (IProj_send1_inv PRJ)=>[_] PRJ' QPRJ DEQ{Ih}.
        have [a_snd [TF'][DOM]{}PRJ]:
          a = l_send /\ T = T' /\ same_dom C' C /\ R_all (IProj simple_co_merge F) C' C
          by move: PRJ'=>[lC][][->->->][DOM] PRJ0; do 2 split=>//.
        move: a_snd TF' FT' DEQ QPRJ=>-><- FT _ QPRJ {a PRJ' T'}.
        exists (ig_msg (Some l) F T C').
        move: (dom' DOM Cl)=>[G'] C'l.
        by apply/st_send/C'l.
      }
      { move=> FF' PRJ.
        have [{}PRJ [NE pT']]: (forall l Ty G, C' l = Some (Ty, G) ->
                                               IProj simple_co_merge F G (rl_msg a T C))
                               /\ (exists l Ty' G', C' l = Some (Ty', G'))
                               /\ F' != T'.
        { move: (IProj_mrg_inv PRJ FF' FT')=>[F'T'][NE][lC][DOM][{}PRJ]MRG; split.
          - move=>l0 Ty0 G C'l0; move: (dom DOM C'l0)=>[L'] lCl0.
            move: (MRG _ _ _ lCl0)=>EQ.
            by apply/(EqL_IProj _ EQ)/(PRJ _ _ _ _ C'l0).
          - by split=>//.
        }
        move=> QPRJ DEQ.
        move: (qProject_None_inv QPRJ)=>[EMPTY] {}QPRJ.
        set C'' :=
          fun l =>
            match optionP (C' l) with
            | oSome (Ty, G) P =>
              Some (Ty, sval (Ih _ _ _ P Q (PRJ _ _ _ P) DEQ (QPRJ _ _ _ P)))
            | oNone _ => None
            end.
        exists (ig_msg None F' T' C''); move: NE=>[l'] NE.
        apply/(st_amsg1 _ _ NE)=>//=.
        * rewrite /C'' /==> l0 Ty0; case: optionP=>[[Ty1 G1] E|->]//; rewrite E.
          split=>[][G2][<-] _; last by exists G1.
          set G'' := sval _; by exists G''.
        * move=> l0 Ty0 G0 G1; rewrite /C''; case: optionP=>//.
          move=> [Ty1 G2] E; rewrite E=>[][<-<-] [<-].
          by apply/(proj2_sig (Ih _ _ _ _ _ _ _ _)).
      }
  Qed.

  Theorem Project_step G P : forall A G',
    step A G G' ->
    Projection simple_co_merge G P ->
    exists P', Projection simple_co_merge G' P' /\ lstep A P P'.
  Proof.
  move=> A G' ST Prj; exists (run_step A P); split.
  - apply/(runstep_proj ST Prj).
  - apply/run_step_sound/(local_runnable ST Prj).
  Qed.

  Theorem Project_lstep G P A P' :
    lstep A P P' ->
    Projection simple_co_merge G P ->
    exists G', Projection simple_co_merge G' P' /\ step A G G'.
  Proof.
    move=> ST PRJ; move: (Project_gstep ST PRJ)=>[G' GST].
    exists G'; split=>//.
    by apply: (Project_gstep_proj ST GST).
  Qed.

  Theorem TraceEquivalence G P :
    Projection simple_co_merge G P -> forall TRACE, g_lts TRACE G <-> l_lts TRACE P.
  Proof.
    move=> PRJ TRC; split => STEPS.
    - move: (ex_intro (fun=>_) G (conj PRJ STEPS)) =>{PRJ STEPS G}.
      move: TRC P; apply/paco2_acc=> r _ /(_ _ _ (ex_intro _ _ (conj _ _)))-CIH.
      move=>TRC P [G [PRJ] /(paco2_unfold g_lts_monotone)-GLTS].
      case: GLTS PRJ.
      + move=> PRJ; apply/paco2_fold.
        move: PRJ.1; rewrite /eProject=>EPRJ.
        have: forall p, look P.1 p = rl_end
            by move=>p; move: (EPRJ p)=>/IProj_end_inv; elim/Project_inv=>//.
        move: PRJ.2 => /qProject_end_inv {PRJ EPRJ}; case: P=>[E Q]/=-> H.
        by constructor.
      + move=> A {}TRC {}G G' ST [LTS|//] PRJ; apply/paco2_fold.
        move: (Project_step ST PRJ)=>[P'][PRJ']LST.
        by apply: (lt_next LST); right; apply: (CIH _ _ _ PRJ' LTS).
    - move: (ex_intro (fun=>_) P (conj PRJ STEPS)) =>{PRJ STEPS P}.
      move: TRC G; apply/paco2_acc=> r _ /(_ _ _ (ex_intro _ _ (conj _ _)))-CIH.
      move=>TRC G [P [PRJ] /(paco2_unfold l_lts_monotone)-LLTS].
      case: LLTS PRJ.
      + move=> E EMPTY PRJ; apply/paco2_fold.
        move: PRJ.1; rewrite /eProject/==>EPRJ.
        have GEND: forall p, IProj simple_co_merge p G rl_end
            by move=>p; move: (EPRJ p); rewrite EMPTY.
        suff: G = ig_end rg_end by move=>->; constructor.
        move=>{PRJ EPRJ}; case: G GEND=>[[]|]//.
        * move=> F T C /(_ F) /IProj_end_inv; elim/Project_inv=>//.
          by move=>{}G->_/(_ (pof_from _ _ _)).
          by move=> q s CG CL L0 _ /eqP-FF _ [/esym/FF].
        * by move=> O F T C /(_ T) /IProj_recv_inv-[_][lC][]//.
      + move=> A {}TRC {}P P' STEP [TRACE|//] PROJ.
        move: (Project_lstep STEP PROJ)=>[G'][PRJ']{}STEP.
        apply/paco2_fold; apply/eg_trans; first by apply/STEP.
        by right; apply/(CIH _ _ _ PRJ' TRACE).
  Qed.
*)
End TraceEquiv.

(*Section InductiveTrace.
  Definition gty_accepts TRACE g := g_lts TRACE (ig_end (g_expand g)).
  Definition lty_accepts TRACE e := l_lts TRACE (expand_env e, [fmap]%fmap).

  Definition well_formed g : bool := eproject simple_merge g.

  Definition project_env g : well_formed g -> seq (role * l_ty)
    := match eproject simple_merge g as eg
             return isSome eg -> seq (role * l_ty)
       with
       | Some e => fun=>e
       | None => fun pf => False_rect _ (not_false_is_true pf)
       end.

  Theorem IndTraceEquiv g (WF : well_formed g) :
    forall trace, gty_accepts trace g <-> lty_accepts trace (project_env WF).
  Proof.
    apply/TraceEquivalence; split;[|by constructor].
    apply/expand_eProject; rewrite /project_env.
    by move: WF; rewrite /well_formed; case: eproject.
  Qed.

  Print Assumptions IndTraceEquiv.

End InductiveTrace.*)
