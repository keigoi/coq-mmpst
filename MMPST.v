(* Certified extended MPST (WIP) by Keigo Imai *)
(* Namings and several definitions are largely from:
 * Certified MPST: Zooid. https://github.com/emtst/zooid-cmpst.git 
 *)

From mathcomp.ssreflect Require Import all_ssreflect seq.
From mathcomp Require Import finmap.

From Paco Require Import paco paco2 paco3.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Definition role:=nat.
Definition lbl := nat.

Inductive g_ty :=
| g_end
| g_var (VAR : nat)
| g_rec (GT : g_ty)
| g_msg (FROM TO : role) (LBL : lbl) (CONT : g_ty)
| g_choice (AT : role) (CL : g_ty) (CR : g_ty).
Hint Constructors g_ty : mpst.

Notation member := List.In.

Fixpoint g_open (d : nat) (G2 : g_ty) (G1 : g_ty) :=
  match G1 with
  | g_end => G1
  | g_var v => if v == d then G2 else G1
  | g_rec G => g_rec (g_open d.+1 G2 G)
  | g_msg p q l K =>
    g_msg p q l (g_open d G2 K)
  | g_choice p KL KR =>
    g_choice p (g_open d G2 KL) (g_open d G2 KR)
  end.

CoInductive rg_ty :=
| rg_end
| rg_msg (FROM TO : role) (LBL : lbl)
         (CONT : rg_ty)
| rg_choice (AT : role) (CONTL : rg_ty) (CONTR : rg_ty).

Inductive ig_ty :=
| ig_end (CONT : rg_ty)
| ig_msg (bRECV : bool)
         (FROM TO : role) (LBL : lbl)
         (CONT : ig_ty)
| ig_choice (AT : role) (CONTL : ig_ty) (CONTR : ig_ty).


Definition grel := g_ty -> rg_ty -> Prop.

Inductive g_unroll (r : grel) : grel :=
| gu_end :
    g_unroll r g_end rg_end
| gu_rec IG CG :
    r (g_open 0 (g_rec IG) IG) CG ->
    g_unroll r (g_rec IG) CG
| gu_msg FROM TO LBL iCONT cCONT :
    r iCONT cCONT ->
    g_unroll r (g_msg FROM TO LBL iCONT) (rg_msg FROM TO LBL cCONT)
| gu_choice AT iCL iCR cCL cCR :
    r iCL cCL -> r iCR cCR ->
    g_unroll r (g_choice AT iCL iCR) (rg_choice AT cCL cCR).
Definition GUnroll IG CG : Prop := paco2 g_unroll bot2 IG CG.

Derive Inversion gunr_inv with (forall r G cG, g_unroll r G cG) Sort Prop.
Hint Constructors g_unroll.

Lemma gunroll_monotone : monotone2 g_unroll.
Proof.
    (* for exercise on my own, put refine tactic to see the assumption/goal *)
    rewrite/monotone2.
    refine (_ : forall x0 x1 r r' U0 R_mon, g_unroll r' x0 x1).
      move=> IG CG r r' U0 R_mon; move: IG CG U0.
    refine (_ : forall (IG:g_ty) (CG:rg_ty), g_unroll r IG CG -> _).
    Check R_mon: forall x0 x1, r x0 x1 -> r' x0 x1.
      (* induction on IG *)   
      elim=>[|V|IG0 IH|F T L C IH|AT IGL IHL IGR IHR] CG;
      refine (_ : g_unroll r _ CG -> _);
      (* case analysis on g_unroll and keep equality in E -- which proves most things *)
      case E:_ _ / => [|IG' CG' R|F' T' L' G' C' R|AT' KL KR CL CR RL RR]//.
    (* prove the rest *)
    - refine (_ : g_unroll r' (g_rec IG') CG').
        constructor.
      refine (_ : r' (g_open 0 (g_rec IG') IG') CG').
      Check R : r (g_open 0 (g_rec IG') IG') CG'.
        apply/R_mon/R.
    - refine (_ : g_unroll r' (g_msg F' T' L' G') (rg_msg F' T' L' C')).
        constructor; apply/R_mon/R.
    - refine (_ : g_unroll r' (g_choice AT' KL KR) (rg_choice AT' CL CR)).
        constructor. 
        * refine (_ : r' KL CL); apply/R_mon/RL. 
        * refine (_ : r' KR CR); apply/R_mon/RR. 
Qed.

CoInductive trace (act : Type) :=
| tr_nil : trace act
| tr_cons : act -> trace act -> trace act.

Inductive l_act := l_send | l_recv.

Inductive act :=
| mk_act (a : l_act) (p : role) (q : role) (l : lbl).

Inductive tr_finite A : trace A -> Prop :=
  | trfin_nil : tr_finite (tr_nil A)
  | trfin_cons : forall (l : trace A) (a : A), tr_finite l -> tr_finite (tr_cons a l).

CoInductive tr_infinite A : trace A -> Prop :=
    trinf_cons a l : tr_infinite l -> tr_infinite (tr_cons a l).

Lemma finite_not_infinite A : forall l : trace A, tr_finite l -> tr_infinite l -> False.
Proof. (* put refine to see intermediate assumption/goals *)
    move=>l.
    (* induction on tr_finite *)
      elim=> [|{}l a fin IH];
    refine (_:tr_infinite _ -> False);
    (* case analysis on tr_infinite will produce two cases:
       (1) l is nil, which contradicts immediately, or
       (2) l is infinite, contradicts with IH.
       By keeping E, tr_nil the former case will wipe out automatically. *)
      case E: _/ => [a0 l0 inf_l]//.
    refine (_ : False).
    Check IH : tr_infinite l -> False.
    Check inf_l : tr_infinite l0.
    (* somehow the variable name does not fit -- rewrite it *)
      move:E; case=> eqa eql; rewrite <- eql in * |-. 
      apply/IH/inf_l.
Qed.

Definition gtrc_rel := trace act -> ig_ty -> Prop.

CoFixpoint tr_append A (xs ys:trace A) :=
match xs with
| tr_nil => ys
| tr_cons x xs => tr_cons x (tr_append xs ys)
end.

Inductive tr_all_ A (P : A -> Prop) (r : trace A -> Prop): trace A -> Prop :=
| tr_forall_nil : tr_all_ P r (@tr_nil A)
| tr_forall_cons x xs :
  P x -> r xs -> tr_all_ P r (tr_cons x xs).

Definition tr_all A (P : A -> Prop) : trace A -> Prop :=
    paco1 (tr_all_ P) bot1.

Definition tr_all_subj_neq p tr := 
tr_all (fun act => let: (mk_act _ q _ _) := act in p != q) tr.

CoFixpoint send_forever P Q L :=
  tr_cons (mk_act l_send P Q L) (send_forever P Q L).

Definition tr_unf A (xs : trace A) :=
  match xs with 
  | tr_cons n xs => tr_cons n xs 
  | tr_nil => tr_nil A
  end.

Lemma sunf_eq A (s : trace A) : s = @tr_unf A s.
Proof.
  by move:s;case.
Qed.

Proposition subj_not_p p q r l:
  r != p -> tr_all_subj_neq r (send_forever p q l).
Proof.
    move=>H.
    refine (_ : tr_all _ _).
  * pcofix CH.
    Check (CH : r0 (send_forever p q l)).
    refine (_ : paco1 (tr_all_ _) r0 (send_forever p q l)).
  * pfold.
    refine (_ : tr_all_ _ (upaco1 _ _) (send_forever p q l)).
  * rewrite (sunf_eq (send_forever p q l))//; simpl.
    refine (_ : tr_all_ _ (upaco1 _ _) (tr_cons (mk_act l_send p q l) (send_forever p q l))).
  * right=>//.
    refine (_ : upaco1 _ _ _).
  * rewrite/upaco1.
    refine (_ : _ \/ r0 (send_forever p q l)).
  * by right.
Qed.

Notation "x @ y" := (tr_append x y) (at level 40).
Notation "a .: y" := (tr_cons a y) (at level 20).

Definition subject A := let: mk_act _ p q _ := A in p.
Definition object A := let: mk_act _ p q _ := A in q.

Definition Delay_rel := act -> trace act -> trace act -> Prop.

Inductive delay_rules (r : Delay_rel) : Delay_rel :=
| delay_none A TR : delay_rules r A TR (A.:TR)
| delay_outout A B C D M M' TR TR': 
    A != C
    -> r (mk_act l_send A B M) TR TR'
    -> delay_rules r
             (mk_act l_send A B M)
             (mk_act l_send C D M' .: TR)
             (mk_act l_send C D M' .: TR')
| delay_inin A B C D M M' TR TR': 
    B != D
    -> r (mk_act l_send A B M) TR TR'
    -> delay_rules r
             (mk_act l_recv B A M)
             (mk_act l_recv D C M' .: TR)
             (mk_act l_recv D C M' .: TR')
| delay_outin A B C D M M' TR TR':
    A != C && (A != D || B != C)
    -> r (mk_act l_send A B M) TR TR'
    -> delay_rules r
        (mk_act l_send A B M)
        (mk_act l_recv C D M' .: TR)
        (mk_act l_recv C D M' .: TR')
| delay_inout A B C D M M' TR TR':
    A != C
    -> r (mk_act l_recv A B M) TR TR'
    -> delay_rules r
        (mk_act l_recv A B M)
        (mk_act l_send C D M' .: TR)
        (mk_act l_send C D M' .: TR')
.
Definition delay_co ACT TR TR' := paco3 delay_rules bot3 ACT TR TR'.
Inductive delay_ind : Delay_rel :=
  Delay_ind ACT TR TR' : delay_rules delay_ind ACT TR TR' -> delay_ind ACT TR TR'.

Inductive g_lts_rules (r : gtrc_rel) : gtrc_rel :=
| gtr_end : g_lts_rules r (tr_nil act) (ig_end rg_end)
| gtr_send F T L G TR TR':
  r TR G ->
  delay_co (mk_act l_send F T L) TR TR' ->
  g_lts_rules r TR' (ig_msg false F T L G)
| gtr_recv F T L G TR TR':
  r TR G ->
  delay_co (mk_act l_recv T F L) TR TR' ->
  g_lts_rules r TR' (ig_msg true F T L G)
| gtr_chiocefin AT GL GR TR0 ACT TR TR' :
  tr_finite TR0 ->
  tr_all_subj_neq AT TR ->
  subject ACT == AT ->
  (r (TR0 @ ACT.:TR) GL /\ r (TR0 @ TR') GR)
  \/
  (r (TR0 @ TR') GR /\ r (TR0 @ ACT.:TR) GL)
   ->
  g_lts_rules r (TR0 @ ACT.:TR) (ig_choice AT GL GR)
| gtr_choiceinf AT GL GR TR :
  tr_infinite TR ->
  tr_all_subj_neq AT TR ->
  r TR GL -> r TR GR ->
  g_lts_rules r TR (ig_choice AT GL GR)
.

Inductive g_lts_corules (r : gtrc_rel) : gtrc_rel :=
| gtrco_send F T L G TR TR':
    delay_ind (mk_act l_send F T L) TR TR' ->
    g_lts_corules r TR' (ig_msg false F T L G)
| gtrco_recv F T L G TR TR':
    delay_ind (mk_act l_recv T F L) TR TR' ->
    g_lts_corules r TR' (ig_msg true F T L G)
| gtrco_choicefin AT GL GR TR0 ACT TR :
  tr_finite TR0 ->
  tr_all_subj_neq AT TR ->
  subject ACT == AT ->
  (r (TR0 @ ACT.:TR) GL \/ r (TR0 @ ACT.:TR) GR) ->
  g_lts_corules r TR (ig_choice AT GL GR)
| gtrco_choiceinf AT GL GR TR :
  tr_infinite TR ->
  tr_all_subj_neq AT TR ->
  (r TR GL \/ r TR GR) ->
  g_lts_corules r TR (ig_choice AT GL GR)
.
Inductive g_lts_fin : gtrc_rel :=
| g_lts_ind_rule TR G : g_lts_rules g_lts_fin TR G -> g_lts_fin TR G
| g_lts_ind_corule TR G : g_lts_corules g_lts_fin TR G -> g_lts_fin TR G
.
Inductive g_lts_gen r : gtrc_rel :=
| g_lts_gen_make TR G : g_lts_rules r TR G -> g_lts_fin TR G -> g_lts_gen r TR G.

Hint Constructors g_lts_rules.
Definition g_lts t g := paco2 g_lts_gen bot2 t g.

Inductive rg_guarded : rg_ty -> Set :=
| rggd_end : rg_guarded rg_end 
| rggd_msg F T M G : rg_guarded (rg_msg F T M G)
| rggd_choice AT GL GR 
    : rg_guarded GL -> rg_guarded GR -> rg_guarded (rg_choice AT GL GR).
  
Fixpoint rg_unr (G : rg_ty) (H:rg_guarded G) {struct H} : ig_ty :=
    match H with
    | rggd_end => ig_end rg_end
    | rggd_msg F T M G => ig_msg false F T M (ig_end G)
    | rggd_choice AT GL GR HL HR => 
      ig_choice AT (@rg_unr GL HL) (@rg_unr GR HR)
    end.

