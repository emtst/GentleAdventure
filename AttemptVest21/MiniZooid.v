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

Lemma notin_part_g_open_strong d r G G': r \notin participants G ->
  r \notin participants G'-> r \notin participants (g_open d G' G).
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

Lemma same_notin_part_g_open d r G G': participants G' = participants G ->
  r \notin participants G -> r \notin participants (g_open d G' G).
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
Inductive l_ty :=
| l_end
| l_var (v : nat)
| l_rec (L : l_ty)
| l_msg (a : l_act) (r : role) (K : (mty * l_ty))
.
Set Elimination Schemes.

(*Print find_cont.
Definition ilook (E : seq (role * l_ty)) p := odflt l_end (find_cont E p).*)

Fixpoint partsL (G : l_ty) :=
  match G with
  | l_end
  | l_var _ => [::]
  | l_rec G => partsL G
  | l_msg a p K => p::partsL K.2
  end.

Lemma l_ty_ind :
  forall (P : l_ty -> Prop),
    P l_end ->
    (forall v, P (l_var v)) ->
    (forall G, P G -> P (l_rec G)) ->
    (forall a p K, P K.2 -> P (l_msg a p K)) ->
    forall l : l_ty, P l.
Proof.
  move => P P_end P_var P_rec P_msg.
  fix Ih 1; case=>[|v|L|a r K].
  + by apply: P_end.
  + by apply: P_var.
  + by apply: P_rec.
  + by apply: P_msg; elim: K.
Qed.

Fixpoint depth_lty L :=
  match L with
  | l_end
  | l_var _ => 0
  | l_rec L => (depth_lty L).+1
  | l_msg _ _ K => (depth_lty K.2).+1
  end.

Fixpoint eq_lty x y :=
  match x, y with
  | l_end, l_end => true
  | l_var x, l_var y => x == y
  | l_rec x, l_rec y => eq_lty x y
  | l_msg a1 r1 C1, l_msg a2 r2 C2
    => (a1 == a2) && (r1 == r2)
         && (C1.1 == C2.1) && (eq_lty C1.2 C2.2)
  | _, _ => false
  end.

Definition eq_lcont (l r : (mty * l_ty)) :=
  (l.1 == r.1) && eq_lty l.2 r.2.

Lemma eqlty_msg a1 a2 r1 r2 K1 K2 :
  eq_lty (l_msg a1 r1 K1) (l_msg a2 r2 K2) =
  (a1 == a2) && (r1 == r2) && eq_lcont K1 K2.
Proof.
  rewrite /=; do 2 (case: eqP=>///= _); move: K1 K2 {r1 r2 a1 a2}.
Qed.

Lemma lty_eqP : Equality.axiom eq_lty.
Proof.
  rewrite /Equality.axiom; fix Ih 1 => x y.
  case: x => [|v|L|a r K]; case: y =>[|v'|L'|a' r' K']; try (by constructor).
  + by rewrite /eq_lty; case: eqP=>[->|F]; constructor=>//[[/F]].
  + by rewrite /=; case: Ih=>[->|F]; constructor=>//[[/F]].
  + rewrite eqlty_msg; do 2 (case: eqP=>[<-|H];[|constructor=>[[]]//] =>/=).
    case: K=>t G; case: K'=> t' G'.
    rewrite /eq_lcont//=; case: eqP=>//=[<-|F]; [|by constructor=>[[/F]]].
    by case Ih=>[<-|F]; constructor=>//=[[/F]].
Qed.

Definition lty_eqMixin := EqMixin lty_eqP.
Canonical lty_eqType := Eval hnf in EqType l_ty lty_eqMixin.

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

Fixpoint l_shift n d (L : l_ty) :=
  match L with
  | l_end => l_end
  | l_var v => if v >= d then l_var (n + v) else L
  | l_msg a p K => l_msg a p (K.1, l_shift n d K.2)
  | l_rec L => l_rec (l_shift n d.+1 L)
  end.

Fixpoint l_open (d : nat) (L2 : l_ty) (L1 : l_ty) :=
  match L1 with
  | l_end => L1
  | l_var v => if v == d then l_shift d 0 L2 else L1
  | l_rec L => l_rec (l_open d.+1 L2 L)
  | l_msg a p K => l_msg a p (K.1, l_open d L2 K.2)
  end.
Notation "{ k '~>' v } L":= (l_open k v L) (at level 30, right associativity).
Notation "L '^' v":= (l_open 0 (l_var v) L) (at level 30, right associativity).

Lemma open_notvar n L L' :
  (forall v : nat, L != l_var v) ->
  (forall v : nat, l_open n L' L != l_var v).
Proof. by case: L=>//v /(_ v)/eqP. Qed.

Lemma l_open_msg_rw d L2 a r K:
 l_open d L2 (l_msg a r K) = l_msg a r (K.1, l_open d L2 K.2).
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

Fixpoint l_fidx (d : nat) (L : l_ty) : bool :=
  match L with
  | l_end => true
  | l_var v => if v >= d then false else true
  | l_rec L => l_fidx d.+1 L
  | l_msg _ _ K => l_fidx d K.2
  end.

Definition l_closed (L : l_ty) := l_fidx 0 L.

Lemma lfbvar_next n L :
  l_fidx n L -> l_fidx n.+1 L.
Proof.
  elim: L n=>[//|v|L Ih|a p K Ih] n/=; try by apply Ih.
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
  elim: L=> [| v | L Ih | a p K Ih]//= in d *.
  { (* var *)
    by case: ifP=>//.
  }
  { (* rec *)
    by move=>H; congr l_rec; apply/Ih.
  }
  { (* msg *)
    by move=>H; rewrite Ih//= -!surjective_pairing.
  }
Qed.

Lemma lopen_closed L :
  l_closed (l_rec L) ->
  l_closed (l_open 0 (l_rec L) L).
Proof.
  rewrite/l_closed/==>L_fbv; have: l_fidx 0 (l_rec L) by [].
  move: (l_rec L) => L' L'0.
  elim: L 0 L_fbv=>[//|v|L Ih|a q K Ih] n /=.
  - rewrite  lshift_closed//= ltn_neqAle; case: ifP=>//=.
    case: ifP=>//=; [by rewrite (lfbvar_gt _ L'0)|].
    by case: ifP=>//=; move=> nv vnf; rewrite eq_sym vnf.
  - by apply Ih; apply gfbvar_next.
  - by apply Ih.
 Qed.

Fixpoint lguarded d L :=
  match L with
  | l_end => true
  | l_var v => v >= d
  | l_rec L => lguarded d.+1 L
  | l_msg _ _ K => lguarded 0 K.2
  end.

Fixpoint l_binds n L :=
  match L with
  | l_var v => v == n
  | l_rec L => l_binds n.+1 L
  | _ => false
  end.

Fixpoint lguarded' L :=
  match L with
  | l_end
  | l_var _ => true
  | l_rec L => ~~ l_binds 0 L && lguarded' L
  | l_msg _ _ K => lguarded' K.2
  end.

Lemma lguarded_next n L : lguarded n.+1 L = ~~ l_binds n L && lguarded n L.
Proof. by elim: L n=>//= v n; rewrite ltn_neqAle eq_sym. Qed.

Lemma lguarded_binds L : lguarded 0 L = lguarded' L.
Proof.
  by elim: L=>[||L|_ _ K Ih]//=<-;apply/lguarded_next.
Qed.

Lemma lguarded_rec d L
  : lguarded d (l_rec L) -> forall s, s <= d -> ~~ l_binds s L.
Proof.
elim: L=>[|v|L /= Ih|a p K Ih]// in d *.
- move=>/= vd s sd; move: (leq_ltn_trans sd vd).
  by rewrite eq_sym ltn_neqAle=>/andP-[].
- by rewrite /==>/Ih-{Ih}Ih s Lsd; apply/Ih.
Qed.

Fixpoint lrec_depth L :=
  match L with
  | l_rec G => (lrec_depth G).+1
  | _ => 0
  end.

Fixpoint lunroll d G :=
  match d with
  | 0 => G
  | d.+1 =>
    match G with
    | l_rec G' => lunroll d (l_open 0 G G')
    | _ => G
    end
  end.

Lemma lguarded_match d G :
  match G with
  | l_var v => d < v
  | _ => lguarded d.+1 G
  end ->
  (exists v, (G == l_var v) && (d < v)) \/
  (forall v, (G != l_var v)) /\ lguarded d.+1 G.
Proof.
  case: G=>[|||]//=; try by right.
  by move=> n Eq; left; exists n; rewrite eq_refl.
Qed.

Lemma lguarded_recdepth d L m :
  lguarded d L ->
  m < d ->
  forall L', lrec_depth L = lrec_depth ({m ~> L'} L).
Proof.
  elim: L=>[|n|L Ih|a p K Ih]//= in d m *.
  - move=>dn md L; case: ifP=>[/eqP-E|ne//].
    by move: E dn md=>-> /leq_ltn_trans-H /H; rewrite ltnn.
  - by move=> GL md L'; rewrite (Ih _ m.+1 GL _ L').
Qed.

Lemma lty_not_var A L (b1 : nat -> A) (b2 : A) :
  (forall v : nat, L != l_var v) ->
  match L with | l_var v => b1 v | _ => b2 end = b2.
Proof. by case: L =>[|n /(_ n)/eqP||]. Qed.

Lemma lguarded_depth_gt dL dL' L :
  lguarded dL' L -> l_closed L -> lguarded dL L.
Proof.
  rewrite /l_closed=> H H'; move: 0 (leq0n dL') H H'.
  elim: L =>[|n|L Ih|a p Ks Ih]// in dL dL' *.
  - by move=> m /leq_trans-H /= /H->.
  - by move=> n ndL' /=; apply/Ih.
Qed.

Lemma lclosed_not_var L :
  l_closed L ->
  forall v, L != l_var v.
Proof. by case: L=>//= v. Qed.

Lemma lopen_not_var d L L' :
  l_closed L ->
  (forall v, L' != l_var v) ->
  forall v, {d ~> L} L' != l_var v.
Proof. by case: L'=>// n _ /(_ n)/eqP. Qed.

Lemma lguarded_open d1 d2 L L' :
  lguarded 0 L' ->
  l_closed L' ->
  lguarded d1 L ->
  lguarded d1 ({d2 ~> L'} L).
Proof.
  elim: L=>[|n|L Ih|p q K Ih]//= in d1 d2 *.
  - case: ifP=>// _ gL cL; rewrite (lshift_closed _ cL)=>_.
    by apply/(lguarded_depth_gt _ gL).
  - by apply/Ih.
  - by move=> GL' CL' H; apply Ih=>//=.
Qed.

Lemma lguarded_gt d d' L :
  d >= d' ->
  lguarded d L ->
  lguarded d' L.
Proof.
  elim: L=>[|n|L Ih|p q Ks Ih]//= in d d' *.
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
  elim: L=>[|v|L Ih|a p K Ih]//= in n *; move=> END.
  by rewrite Ih.
Qed.

Lemma keep_unrolling L :
  l_isend L -> exists m, l_end = lunroll m L.
Proof.
  elim: L=>[||L Ih|]//; [move=>_| move=>/=END; move:(Ih END)=>[n U]].
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
elim: L m n L1.
+ by move=> m n L1 neq closed; rewrite /l_binds //=.
+ move=> v m n L1 neq closed.
  rewrite /l_binds //=; case: ifP => //=; rewrite <-(rwP eqP); move=>->.
  rewrite (lshift_closed _ closed).
  move: (@l_closed_no_binds m _ closed); rewrite /l_binds; move =>->.
  by move: (negbTE neq).
+ by move=> L IH m n L1 neq closed; rewrite //=; apply: IH.
+ by [].
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

Lemma nopen_var' m n L v : n_open m n L = l_var v -> L = l_var v.
Proof.
  elim: n m=>//= n Ih m.
  case EQ: n_open=>[|v'||]//=; case: ifP=>// _ [EV].
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
  case EQ: (n_open d.+1 n (get_nr L)) => [|v|Lr|]//=.
  - case: ifP=>///eqP-EV; rewrite (nopen_var' EQ)/=EV =>{}EQ.
    exists d; rewrite eq_refl; split=>//.
    rewrite addnS; by apply/leq_addr.
  - move: (Ih _ _ EQ)=>[m][BND] LE _.
    by exists m; split=>//; rewrite addnS.
Qed.

(* l_open d L (n_rec m L') = n_rec m (l_open (d - m) L L') ? *)
Lemma lopen_nrec d m L
  : l_open d L (n_rec m (l_var m)) =
    n_rec m (if d == 0 then l_shift (d + m) 0 L else l_var m).
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
  l_open d L (n_rec n (l_var m)) = n_rec n (l_var m).
Proof.
  elim: n=>[|n Ih]//= in d *; last by rewrite addnS -addSn=>/Ih->.
  by rewrite addn0 ltn_neqAle=>/andP-[/negPf->].
Qed.

Lemma lshift_nrec d r m n :
  n < r + m ->
  l_shift d r (n_rec m (l_var n)) = n_rec m (l_var n).
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

  Fixpoint project (g : g_ty) (r : role) : option l_ty :=
    match g with
    | g_end => Some l_end
    | g_var v => Some (l_var v)
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
                       then Some (l_msg l_send q (K.1, L))
                       else if q == r
                            then Some (l_msg l_recv p (K.1, L))
                            else Some L
      | None => None
      end
    end.

  Fixpoint project_all (parts : seq role) (g : g_ty)
    : option (seq (role * l_ty))
    := match parts with
       | [::] => Some [::]
       | p :: parts =>
         match project g p, project_all parts g with
         | Some l, Some e => Some ((p, l) :: e)
         | _, _ => None
         end
       end%fmap.

  Definition eproject (g : g_ty) : option (seq (role * l_ty)) :=
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

  Lemma eproject_part (g : g_ty) (e : seq (role * l_ty)) :
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
    (L == l_end) || (L == l_var v) ->
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
    project (g_msg r s K) p == Some (l_var n) ->
    r != p /\ s != p /\ r != s /\
    project K.2 p == Some (l_var n).
  Proof.
    rewrite //=; case Prj: project => [KL|//]; move: Prj=>/eqP.
    by do ! case: ifP=>//.
  Qed.

  Lemma proj_var_eq G p q v v':
    project G p == Some (l_var v) ->
    project G q == Some (l_var v') ->
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
    project G r == Some (l_var v) -> r \notin participants G.
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
    | l_var v => true
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
