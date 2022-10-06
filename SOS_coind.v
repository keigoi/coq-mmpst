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

CoInductive rg_ty : Set :=
| rg_end
| rg_msg (bSEND : bool) (FROM TO : role) (LBL : lbl)
         (CONT : rg_ty)
| rg_choice (AT : role) (CONTL : rg_ty) (CONTR : rg_ty).
Hint Constructors rg_ty.

(* CoInductive rg_bisim : rg_ty -> rg_ty -> Prop :=
| rgbisim_end : rg_bisim rg_end rg_end
| rgbisim_msg B F T L G1 G2 : 
    rg_bisim G1 G2 ->
    rg_bisim (rg_msg B F T L G1) (rg_msg B F T L G2)
| rgbisim_choice AT GL1 GR1 GL2 GR2 :
    rg_bisim GL1 GL2 ->
    rg_bisim GR1 GR2 ->
    rg_bisim (rg_choice AT GL1 GR1) (rg_choice AT GL2 GR2). *)

Definition g_rel := rg_ty -> rg_ty -> Prop.


Inductive rg_bisim_gen (r:g_rel) : g_rel :=
| rgbisim_end : rg_bisim_gen r rg_end rg_end
| rgbisim_msg B F T L G1 G2 : 
    r G1 G2 ->
    rg_bisim_gen r (rg_msg B F T L G1) (rg_msg B F T L G2)
| rgbisim_choice AT GL1 GR1 GL2 GR2 :
    r GL1 GL2 ->
    r GR1 GR2 ->
    rg_bisim_gen r (rg_choice AT GL1 GR1) (rg_choice AT GL2 GR2).

Hint Constructors rg_bisim_gen.

Lemma rg_bisim_gen_monotone : monotone2 rg_bisim_gen.
Proof. pmonauto. Qed.
Hint Resolve rg_bisim_gen_monotone.

Definition rg_bisim g g' := paco2 rg_bisim_gen bot2 g g'.

Lemma rg_bisim_refl G : forall r, paco2 rg_bisim_gen r G G.
Proof.
    move:G; pcofix CH => G.
    pfold.
    case G=> [|bSEND F T L G'|AT GL GR].
    - by apply: rgbisim_end.
    - by apply: rgbisim_msg; right.
    - by apply: rgbisim_choice; right.
Qed.
Hint Resolve rg_bisim_refl : core.

Definition rg_unf g :=
  match g with
  | rg_end => rg_end
  | rg_msg b F T L G => rg_msg b F T L G
  | rg_choice AT GL GR => rg_choice AT GL GR
  end.

Lemma rg_unf_eq g : g = rg_unf g.
Proof.
    destruct g; auto.
Qed.

Inductive l_act := l_send | l_recv.

Inductive act :=
| mk_act (a : l_act) (p : role) (q : role) (l : lbl).

Notation "p , q ! m " := (mk_act l_send p q m) (at level 10).
Notation "p , q ? m " := (mk_act l_recv p q m) (at level 10).

Definition g_step_rel := rg_ty -> act -> rg_ty -> Prop.

Definition subject A := let: mk_act _ p q _ := A in p.
Definition object A := let: mk_act _ p q _ := A in q.

Inductive gop_step_rules (r:g_step_rel) : g_step_rel :=
| gop_send F T L G : 
    gop_step_rules r 
        (rg_msg true F T L G)
        (F, T ! L)
        G
| gop_recv F T L G : 
    gop_step_rules r 
        (rg_msg false F T L G)
        (T, F ? L)
        G
| gop_sendasync F T L G ACT G' :
    r G ACT G' ->
    subject ACT <> F ->
    subject ACT <> T ->
    gop_step_rules r
        (rg_msg true F T L G)
        ACT
        (rg_msg true F T L G')
| gop_recvasync F T L G ACT G' :
    r G ACT G' ->
    subject ACT <> T ->
    gop_step_rules r
        (rg_msg false F T L G)
        ACT
        (rg_msg false F T L G')
| gop_choiceL P GL GR ACT GL' :
    r GL ACT GL' ->
    subject ACT = P ->
    gop_step_rules r 
        (rg_choice P GL GR)
        ACT
        GL'
| gop_choiceR P GL GR ACT GR' :
    r GR ACT GR' ->
    subject ACT = P ->
    gop_step_rules r 
        (rg_choice P GL GR)
        ACT
        GR'
| gop_choice_async P GL GR ACT GL' GR' :
    r GL ACT GL' ->
    r GR ACT GR' ->
    subject ACT <> P ->
    gop_step_rules r
        (rg_choice P GL GR)
        ACT
        (rg_choice P GL' GR')
.
Derive Dependent Inversion gop_step_rules_dep_inv with (forall r G ACT G', gop_step_rules r G ACT G') Sort Prop.
Derive Inversion gop_step_rules_inv with (forall r G ACT G', gop_step_rules r G ACT G') Sort Prop.
Hint Constructors gop_step_rules.

Inductive gop_step_corules (r:g_step_rel) : g_step_rel :=
| gop_corule_choiceL P GL GR ACT GL' GR' :
    r GL ACT GL' ->
    subject ACT <> P ->
    gop_step_corules r
        (rg_choice P GL GR)
        ACT
        (rg_choice P GL' GR')
| gop_corule_choiceR P GL GR ACT GL' GR' :
    r GR ACT GR' ->
    subject ACT <> P ->
    gop_step_corules r
        (rg_choice P GL GR)
        ACT
        (rg_choice P GL' GR')
.
Derive Dependent Inversion gop_step_corules_inv with (forall r G ACT G', gop_step_corules r G ACT G') Sort Prop.
Hint Constructors gop_step_corules.


Unset Elimination Schemes.
Inductive g_step_wit : g_step_rel :=
| g_step_wit_rule G ACT G' : 
    gop_step_rules g_step_wit G ACT G' ->
    g_step_wit G ACT G'
| g_step_wit_corule G ACT G' : 
    gop_step_corules g_step_wit G ACT G' ->
    g_step_wit G ACT G'
.
Set Elimination Schemes.
Derive Inversion g_step_wit_inv with (forall G ACT G', g_step_wit G ACT G').


Lemma g_step_wit_ind
	 : forall (P : rg_ty -> act -> rg_ty -> Prop),
       (forall (F T : role) (L : lbl) (G' : rg_ty),
        P (rg_msg true F T L G') (F, T ! L) G') ->
       (forall (F T : role) (L : lbl) (G : rg_ty),
        P (rg_msg false F T L G) (T, F ? L) G) ->
       (forall (F T : role) (L : lbl) 
          (G : rg_ty) (ACT : act) (G' : rg_ty),
        g_step_wit G ACT G' ->
        P G ACT G' ->
        subject ACT <> F ->
        subject ACT <> T ->
        P (rg_msg true F T L G) ACT (rg_msg true F T L G')) ->
       (forall (F T : role) (L : lbl) 
          (G : rg_ty) (ACT : act) (G' : rg_ty),
        g_step_wit G ACT G' ->
        P G ACT G' ->
        subject ACT <> T ->
        P (rg_msg false F T L G) ACT (rg_msg false F T L G')) ->
       (forall (AT : role) (GL GR : rg_ty) (ACT : act) (GL' : rg_ty),
        g_step_wit GL ACT GL' ->
        P GL ACT GL' -> subject ACT = AT -> P (rg_choice AT GL GR) ACT GL') ->
       (forall (AT : role) (GL GR : rg_ty) (ACT : act) (GR' : rg_ty),
        g_step_wit GR ACT GR' ->
        P GR ACT GR' -> subject ACT = AT -> P (rg_choice AT GL GR) ACT GR') ->
       (forall (AT : role) (GL GR : rg_ty) (ACT : act)
          (GL' GR' : rg_ty),
        g_step_wit GL ACT GL' ->
        P GL ACT GL' ->
        g_step_wit GR ACT GR' ->
        P GR ACT GR' ->
        subject ACT <> AT ->
        P (rg_choice AT GL GR) ACT (rg_choice AT GL' GR')) ->
       (forall (AT : role) (GL GR : rg_ty) (ACT : act)
          (GL' GR' : rg_ty),
        g_step_wit GL ACT GL' ->
        P GL ACT GL' ->
        subject ACT <> AT ->
        P (rg_choice AT GL GR) ACT (rg_choice AT GL' GR')) ->
       (forall (AT : role) (GL GR : rg_ty) (ACT : act)
          (GL' GR' : rg_ty),
        g_step_wit GR ACT GR' ->
        P GR ACT GR' ->
        subject ACT <> AT ->
        P (rg_choice AT GL GR) ACT (rg_choice AT GL' GR')) ->
       forall (r : rg_ty) (a : act) (r0 : rg_ty),
       g_step_wit r a r0 -> P r a r0
.
Proof.
    move=> P 
        P_send P_recv P_sendasync P_recvasync P_choiceL P_choiceR 
        P_choiceasync P_choicecoruleL P_choicecoruleR.
    fix Ih 4 => G ACT G'. 
    elim/g_step_wit_inv. 
      + move => _ _ _ _ H _ _ _; move: H;
        elim/gop_step_rules_inv => _//.
        - by move=>F T L G0 ACT0 G'0 PREM Hsubj1 Hsubj2 eq _ eq';
          apply: P_sendasync=>//;  apply Ih.
        - by move=>F T L G0 ACT0 G'0 PREM Hsubj1 eq _ eq';
          apply: P_recvasync=>//;  apply Ih.
        - by move=>AT GL GR ACT0 GL' PREM subj_eq eq _ eq';
          apply: P_choiceL=>//; apply Ih.
        - by move=>AT GL GR ACT0 GR' PREM subj_eq eq _ eq';
          apply: P_choiceR=>//; apply Ih.
        - by move=>AT GL GR ACT0 GL' GR' PREM1 PREM2 eq _ _ eq';
          apply: P_choiceasync=>//; apply Ih.
      + move => Hwit _ _ _ H _ _ _; move: H.
        elim/gop_step_corules_inv => _ AT GL GR ACT0 GL' GR' PREM subj_neq eq _ eq'//.
        - by apply: P_choicecoruleL=>//; apply Ih.
        - by apply: P_choicecoruleR=>//; apply Ih.
Qed.

(* Inductive g_step_gen r : g_step_rel :=
| g_step_gen_make G ACT G' : 
    gop_step_rules r G ACT G' -> 
    g_step_wit G ACT G' ->
    g_step_gen r G ACT G'. *)

Inductive g_step_gen r G ACT G' : Prop :=
| g_step_gen_make : 
    gop_step_rules r G ACT G' -> 
    g_step_wit G ACT G' ->
    g_step_gen r G ACT G'.

Derive Inversion g_step_gen_inv 
with (forall r G ACT G', g_step_gen r G ACT G') Sort Prop.

Axiom g_step_gen_monotone : monotone3 g_step_gen.
Hint Resolve g_step_gen_monotone.

Hint Constructors g_step_gen.
Definition g_step g act g' := paco3 g_step_gen bot3 g act g'.

Definition g_step_rules := gop_step_rules (upaco3 g_step_gen bot3).

Lemma g_step_inv G ACT G' (P : rg_ty -> act -> rg_ty -> Prop):
       (g_step G ACT G' ->
        g_step_rules G ACT G' ->
        g_step_wit G ACT G' ->
        P G ACT G') ->
       g_step G ACT G' -> P G ACT G'.
Proof.
    by move=> Hinv H;
       apply: Hinv=>//;
       move:H; move=>/(paco3_unfold g_step_gen_monotone)=>//=; elim/g_step_gen_inv=>//=.
Qed.

Proposition simple1 P Q L 
    : g_step (rg_msg false P Q L rg_end) (Q,P ? L) rg_end.
Proof.
pcofix CIH.
pfold.
apply 
    (g_step_gen_make (gop_recv (upaco3 g_step_gen r) P Q L rg_end)).
apply
    (g_step_wit_rule (gop_recv g_step_wit P Q L rg_end)).
Qed.

CoFixpoint repeat_recv P Q L := rg_msg false P Q L (repeat_recv P Q L).

Proposition repeat1 P Q L
    : g_step (repeat_recv P Q L) (Q,P ? L) (repeat_recv P Q L).
Proof.
pcofix CIH.
pfold.
rewrite -> (rg_unf_eq _) at 1.
simpl.
apply 
    (g_step_gen_make 
        (gop_recv (upaco3 g_step_gen r) P Q L (repeat_recv P Q L))).
apply 
    (g_step_wit_rule 
        (gop_recv g_step_wit P Q L (repeat_recv P Q L))).
Qed.

Require Import Coq.Program.Equality.

Locate "!=".

Lemma example n m k : k <= n -> (n <= m) && (m <= k) -> n = k.
Proof.
    move=>lekn/andP.
    Abort.

CoInductive disjoint_choice : rg_ty -> Prop :=
| disjoint_choice_end :
    disjoint_choice rg_end
| disjoint_choice_msg bSEND F T L G' :
    disjoint_choice G' ->
    disjoint_choice (rg_msg bSEND F T L G')
| disjoint_choice_choice AT GL GR :
    (forall ACTL ACTR GL' GR' r r', 
      subject ACTL == AT ->
      subject ACTR == AT ->
      (gop_step_rules r GL ACTL GL' \/ gop_step_corules r GL ACTL GL') ->
      (gop_step_rules r' GR ACTL GR' \/ gop_step_corules r' GR ACTL GR') ->
      ACTL <> ACTR) ->
    disjoint_choice GL ->
    disjoint_choice GR ->
    disjoint_choice (rg_choice AT GL GR).

Hint Constructors disjoint_choice.
Check g_step_inv.

Ltac injection_top0 :=
    match goal with 
    | |- ?x = ?y -> _ => 
      first
        [ by discriminate
        | is_var x; move=>? 
        | is_var y; move=>? 
        | move=>[]
        ]
    end.

Ltac injection_top :=
  repeat injection_top0.
Print Bool.reflect.

Ltac injection_all :=
  repeat
    match goal with 
    | |- _ = _ -> _ => 
      injection_top0
    | |- _ <> _ -> _ =>
      intro
    | |- ?P -> _ =>
      let H := fresh in 
      move=>H; try injection_all; move:H
    end.

Ltac injection_subst :=
    injection_all; subst=>//=.

Ltac inversion_subst P Hinv :=
    let H:= fresh in
    elim/Hinv: P =>H >; try injection_all; try subst=>//=; move:H.

Ltac inversion_using P Hinv :=
    let H:= fresh in
    elim/Hinv: P =>H >; try injection_all; move:H.

Ltac unfold_upaco :=
    case; last done; let H:= fresh in move=>H; punfold H; move:H.

Ltac unfold_upaco_all :=
    repeat
      match goal with
      | |- upaco2 ?gf bot2 _ _ -> _ =>
        case; last done; let H:= fresh in move=>H; punfold H; unfold_upaco_all; move:H
      | |- upaco3 ?gf bot3 _ _ _ -> _ =>
        case; last done; let H:= fresh in move=>H; punfold H; unfold_upaco_all; move:H
      | |- _ -> _ =>
        let H := fresh in move=>H; punfold H; unfold_upaco_all; move:H
      | _ =>
        idtac
      end.

Lemma determinacy G ACT G1
    : disjoint_choice G -> g_step G ACT G1 -> forall G2, g_step G ACT G2 -> rg_bisim G1 G2.
Proof.
    move:G ACT G1; 
    pcofix CIH;
    move=>G ACT G1 Hdisj Hstep;
    punfold Hstep; move:(Hstep);
    case=>Hrule Hwit;
    elim/g_step_wit_ind:Hwit=> (* nested induction for proving choice *)
    [F T L {}G1
    |F T L {}G1
    |F T L G' {}ACT G'' _ IH Hsubj1 Hsubj2
    |F T L G' {}ACT G'' _ IH Hsubj1
    |AT GL GR {}ACT {}G1 Hwit1' IH Hsubj
    |AT GL GR {}ACT {}G1 Hwit1' IH Hsubj
    |AT GL GR {}ACT GL' GR' Hwit1L IH1 Hwit1R IH2 Hsubj
    |AT GL GR {}ACT GL' GR' Hwit1' IH Hsubj
    |AT GL GR {}ACT GL' GR' Hwit1' IH Hsubj]
    in Hdisj Hstep Hrule *;
    move=>G2 Hstep2;
    punfold Hstep2; move:(Hstep2);
    case=>Hrule2 Hwit2;    
    inversion_subst Hrule gop_step_rules_inv=> _;
    inversion_subst Hrule2 gop_step_rules_inv=>_.
        
    (* We have 13 goals here.
       The reason for the use of our inversion_subst is just for 
       hypothesis naming; the standard inversion tactic
       (inversion Hrule as []; inversion Hrule2 as []; subst; try done.)
       will yield the same number of goals; though without control 
       on names for hypotheses. 
      *)

    1,2,3,4,5,6,7,8,9,10:
      move=>Hstep2' Hstep1'; pclearbot.

    11,12,13:
      move=>Hstep2L Hstep2R Hstep1L Hstep1R; pclearbot.

    1,2:
      (* asynchronous send/recv *)
      pfold; constructor; right; 
      apply:CIH; first (inversion_clear Hdisj; apply:H); pfold;
      punfold Hstep1'; punfold Hstep2';
      by first [apply:Hstep1' | apply:Hstep2'].
    
    1,8:
      (* choice. we need induction hypothesis! *)
      apply:IH=>//; punfold Hstep1'; punfold Hstep2'=>//=;
      by first [
        inversion_clear Hdisj as [ | |? ? ? _ HdisjL HdisjR]; 
        first [by apply:HdisjL | by apply:HdisjR]
      |
        by first [by case:Hstep1'=>Hrule1' | by case:Hstep2'=>Hrule2' ] ].

    1,2,3,4,5,6:
      (* contradiction *)
      inversion_clear Hdisj;
      (have: ACT<>ACT; last (by elim));
      apply:H=>//;
      by first [
        by left; punfold Hstep1'; inversion Hstep1'; apply H |
        by left; punfold Hstep2'; inversion Hstep2'; apply H |
        by inversion Hwit1'; 
        first [by left; apply H | by right; apply H]].

    1,2,3:
      (* asynchronous choice *)
      pfold; constructor; right;
      apply:CIH.
      - all: 
        try first[
              by apply:Hstep1L
            | by apply:Hstep1R
            | by apply:Hstep2L
            | by apply:Hstep2R
        ].
      - all:
          by inversion_clear Hdisj as [ | | ? ? ? ? HdisjL HdisjR]; 
             first [by apply:HdisjL|by apply:HdisjR].
Qed.
