From iris.algebra Require Import gmap auth agree gset coPset excl csum.
From Perennial.base_logic.lib Require Export fancy_updates.
From stdpp Require Export namespaces.
From Perennial.base_logic.lib Require Import wsat invariants ae_invariants saved_prop.
From Perennial.Helpers Require Import Qextra.
From iris.algebra Require Import gmap.
From iris.proofmode Require Import tactics.
From Perennial.program_logic Require Export step_fupd_extra crash_weakestpre ae_invariants_mutable later_res private_invariants.
Set Default Proof Using "Type".
Import uPred.

Inductive staged_inv_status :=
| inuse : Qp → Qp → staged_inv_status
| idle.

Global Instance staged_inv_status_inhabited : Inhabited staged_inv_status.
Proof. econstructor. apply idle. Qed.

Canonical Structure staged_inv_statusO := leibnizO staged_inv_status.

Class stagedG (Σ : gFunctors) : Set := WsatG {
  staging_saved_inG :> savedPropG Σ;
  staging_auth_inG :> inG Σ (authR (optionUR (exclR (prodO gnameO gnameO))));
  staging_status_inG :> inG Σ (authR (optionUR (exclR staged_inv_statusO)));
  staging_shot_inG :> inG Σ (csumR (fracR) (agreeR unitO));
}.

Definition stagedΣ : gFunctors :=
  #[GFunctor (csumR fracR (agreeR unitO));
   GFunctor (authR (optionUR (exclR (prodO gnameO gnameO))));
   GFunctor (authR (optionUR (exclR staged_inv_statusO)));
   savedPropΣ].

Instance subG_stagedG {Σ} : subG stagedΣ Σ → stagedG Σ.
Proof. solve_inG. Qed.

Definition staged_pending `{stagedG Σ} (q: Qp) (γ: gname) : iProp Σ :=
  own γ (Cinl q).
Definition staged_done `{stagedG Σ} (γ: gname) : iProp Σ :=
  own γ (Cinr (to_agree ())).

(* This is the modality guarding the crash condition in a wpc *)
Definition wpc_crash_modality `{!irisGS Λ Σ, !crashG Σ} E1 mj Φc :=
  ((∀ g1 ns D κs,
       let E2 :=  ⊤ ∖ D in
       global_state_interp g1 ns mj D κs -∗ C -∗
     ||={E1|E2,∅|∅}=> ||▷=>^(num_laters_per_step ns) ||={∅|∅,E1|E2}=> global_state_interp g1 ns mj D κs ∗ Φc))%I.

Section def.
Context `{IRISG: !irisGS Λ Σ}.
Context `{!pri_invG IRISG}.
Context `{!later_tokG IRISG}.
Context `{!stagedG Σ}.

Definition staged_inv_inner E1 E2 mj (γsaved γfinished γstatus: gname) (P: iProp Σ) : iProp Σ :=
  ((∃ γprop_stored γprop_remainder (stat: staged_inv_status) Ps Pr,
             own γsaved (● Excl' (γprop_stored, γprop_remainder)) ∗
             saved_prop_own γprop_stored Ps ∗
             saved_prop_own γprop_remainder Pr ∗
             own γstatus (● Excl' stat) ∗
             ((match stat with
              | inuse mj1' mj2' => (⌜ (/2) ≤ mj1' ∧ (/2 + mj2')%Qp = mj1' ∧ mj1' ≤ mj ⌝%Qp ∗ Ps ∗ pri_inv_tok mj2' E2 ∗ □ (Ps -∗ wpc_crash_modality E1 mj1' (Pr ∗ P)))
              | idle => (Ps ∗ □ (Ps -∗ C ==∗ P ∗ Pr))
              end)
              ∨
             (Pr ∗ C ∗ staged_done γfinished))))%I.


Definition staged_inv E1 E2 (γsaved γfinished γstatus: gname) (P: iProp Σ) : iProp Σ :=
  (∃ mj, pri_inv E2 (staged_inv_inner E1 E2 mj γsaved γfinished γstatus P)).

Definition staged_value' E1 (Ps Pr: iProp Σ) P stat : iProp Σ :=
  (∃ E2 γsaved γfinished γstatus γprop γprop',
      own γsaved (◯ Excl' (γprop, γprop')) ∗
      own γstatus (◯ Excl' stat) ∗
          saved_prop_own γprop Ps ∗
          saved_prop_own γprop' Pr ∗
          later_tok ∗
          match stat with
          | idle => pri_inv_tok (/2)%Qp E2
          | inuse mj1 mj2 => True%I
          end ∗
          staged_inv E1 E2 γsaved γfinished γstatus P)%I.

Definition staged_value E Ps P : iProp Σ := staged_value' E Ps True%I P idle.

End def.

Section inv.
Context `{IRISG: !irisGS Λ Σ}.
Context `{!pri_invG IRISG}.
Context `{!later_tokG IRISG}.
Context `{!stagedG Σ}.
Implicit Types i : positive.
Implicit Types N : namespace.
Implicit Types P Q R : iProp Σ.

(* TODO: this is annoying but true *)
(*
Global Instance staged_contractive  E γ γ' : Contractive (staged_inv E γ γ').
Proof.
  rewrite /staged_inv=> n ?? ?.
  rewrite pri_inv_full_eq /pri_inv_full_def.
  f_equiv => ?.
  rewrite pri_inv_eq /pri_inv_def.
  do 4 f_equiv.
Qed.

Global Instance staged_ne N k E E' γ γ': NonExpansive (staged_inv N k E E' γ γ').
Proof.
  rewrite /staged_inv=> n ?? ?.
  repeat (apply step_fupdN_ne || f_contractive || f_equiv); eauto using dist_le.
Qed.

Global Instance staged_proper N k E E' γ γ' : Proper ((⊣⊢) ==> (⊣⊢)) (staged_inv N k E E' γ γ').
Proof. apply ne_proper, _. Qed.
*)

Global Instance staged_persistent E1 E2 γ1 γ2 γ3 P : Persistent (staged_inv E1 E2 γ1 γ2 γ3 P).
Proof. rewrite /staged_inv. apply _. Qed.

Lemma pending_done q γ: staged_pending q γ -∗ staged_done γ -∗ False.
Proof.
  rewrite /staged_pending/staged_done.
  iIntros "H H'".
  { by iDestruct (own_valid_2 with "H H'") as %?. }
Qed.

Lemma pending_upd_done γ: staged_pending 1%Qp γ ==∗ staged_done γ.
Proof.
  rewrite /staged_pending/staged_done.
  iIntros "H". iMod (own_update with "H") as "$".
  { by apply cmra_update_exclusive. }
  done.
Qed.

Lemma pending_alloc:
  ⊢ |==> ∃ γ, staged_pending 1 γ.
Proof.
  iApply (own_alloc (Cinl 1%Qp)).
  { rewrite //=. }
Qed.

Lemma pending_split γ:
  staged_pending 1 γ ⊢ staged_pending (1/2)%Qp γ ∗ staged_pending (1/2)%Qp γ.
Proof. by rewrite /staged_pending -own_op -Cinl_op frac_op Qp_div_2. Qed.

Lemma pending_split34 γ:
  staged_pending 1 γ ⊢ staged_pending (3/4)%Qp γ ∗ staged_pending (1/4)%Qp γ.
Proof. by rewrite /staged_pending -own_op -Cinl_op frac_op Qp_three_quarter_quarter. Qed.

Lemma pending_join γ:
 staged_pending (1/2)%Qp γ ∗ staged_pending (1/2)%Qp γ ⊢  staged_pending 1 γ.
Proof. by rewrite /staged_pending -own_op -Cinl_op frac_op Qp_div_2. Qed.

Lemma pending_join34 γ:
 staged_pending (3/4)%Qp γ ∗ staged_pending (1/4)%Qp γ ⊢  staged_pending 1 γ.
Proof. by rewrite /staged_pending -own_op -Cinl_op frac_op Qp_three_quarter_quarter. Qed.

Lemma pending34_pending34 γ:
 staged_pending (3/4)%Qp γ -∗ staged_pending (3/4)%Qp γ -∗ False.
Proof.
  rewrite /staged_pending.
  iIntros "H H'".
  { by iDestruct (own_valid_2 with "H H'") as %?. }
Qed.

Lemma pending_pending γ:
 staged_pending 1%Qp γ -∗ staged_pending 1%Qp γ -∗ False.
Proof.
  rewrite /staged_pending.
  iIntros "H H'".
  { by iDestruct (own_valid_2 with "H H'") as %?. }
Qed.

(* TODO : *)
(*
Lemma staged_inv_iff E i γ γ' P Q :
  ▷ □ (P ↔ Q) -∗
  staged_inv E i γ γ' P -∗
  staged_inv E i γ γ' Q.
Proof.
  iIntros "#HPQ". iApply inv_iff. iNext. iAlways. iSplit.
  - iIntros "H". iDestruct "H" as (?? P0 P0') "(?&?&?&#HP0&Hcase)". iExists _, _, P0, P0'. iFrame.
    iAlways. iIntros. iSpecialize ("HP0" with "[$] [$]").
    iApply (step_fupdN_inner_wand' with "HP0"); eauto.
    iIntros "(?&$)". by iApply "HPQ".
  - iIntros "H". iDestruct "H" as (?? P0 P0') "(?&?&?&#HP0&Hcase)". iExists _, _, P0, P0'. iFrame.
    iAlways. iIntros. iSpecialize ("HP0" with "[$] [$]").
    iApply (step_fupdN_inner_wand' with "HP0"); eauto.
    iIntros "(?&$)". by iApply "HPQ".
Qed.
*)

Lemma wpc0_pri_inv_tok_res s k mj E1 e Φ Φc :
  (∀ D E', pri_inv_tok 1%Qp E' ∗ ⌜ E' ## D ⌝ -∗ ||={E1|⊤∖D, E1|⊤∖D}=> wpc0 s k mj E1 e Φ Φc) -∗
  wpc0 s k mj E1 e Φ Φc.
Proof.
  iIntros "H".
  iEval (rewrite wpc0_unfold).
  rewrite /wpc_pre.
  iSplit.
  {
    destruct (to_val e) eqn:Heq_val.
    - iIntros (q g1 ns D κs) "Hg HNC".
      iMod (pri_inv_tok_alloc with "[$]") as (Einv Hdisj) "(Hitok&Hg)".
      iSpecialize ("H" with "[$Hitok //]").
      rewrite wpc0_unfold/ wpc_pre. rewrite Heq_val.
      iMod "H" as "(H&_)". by iMod ("H" with "[$] [$]") as "$".
    - iIntros.
      iMod (pri_inv_tok_alloc with "[$]") as (Einv Hdisj) "(Hitok&Hg)".
      iSpecialize ("H" with "[$Hitok //]").
      rewrite wpc0_unfold/ wpc_pre. rewrite Heq_val.
      iMod "H" as "(H&_)". by iMod ("H" with "[$] [$] [$]") as "$".
  }
  iIntros.
  iMod (pri_inv_tok_alloc with "[$]") as (Einv Hdisj) "(Hitok&Hg)".
  iSpecialize ("H" with "[$Hitok //]").
  rewrite wpc0_unfold/ wpc_pre.
  iMod "H" as "(_&H)". by iMod ("H" with "[$] [$]") as "$".
Qed.

(*
Lemma wpc0_pri_inv_tok_disj s k mj E1 E e Φ Φc :
  pri_inv_tok q E -∗
  (⌜ E ## D ⌝ -∗ pri_inv_tok E -∗ wpc0 s k D E1 e Φ Φc) -∗
  wpc0 s k D E1 e Φ Φc.
Proof.
  iIntros "Hitok H".
  iEval (rewrite wpc0_unfold).
  rewrite /wpc_pre.
  iSplit.
  {
    destruct (to_val e) eqn:Heq_val.
    - iIntros (q g1 ns κs) "Hg HNC".
      iDestruct (pri_inv_tok_disj with "[$]") as %Hdisj.
      iSpecialize ("H" with "[//] [$Hitok]").
      rewrite wpc0_unfold/ wpc_pre. rewrite Heq_val.
      iDestruct "H" as "(H&_)". by iMod ("H" with "[$] [$]") as "$".
    - iIntros.
      iDestruct (pri_inv_tok_disj with "[$]") as %Hdisj.
      iSpecialize ("H" with "[//] [$Hitok]").
      rewrite wpc0_unfold/ wpc_pre. rewrite Heq_val.
      iDestruct "H" as "(H&_)". by iMod ("H" with "[$] [$] [$]") as "$".
  }
  iIntros.
  iDestruct (pri_inv_tok_disj with "[$]") as %Hdisj.
  iSpecialize ("H" with "[//] [$Hitok]").
  rewrite wpc0_unfold/ wpc_pre.
  iDestruct "H" as "(_&H)". by iMod ("H" with "[$] [$]") as "$".
Qed.
*)

Existing Instances pri_inv_tok_timeless later_tok_timeless.

Lemma wpc_staged_inv_init s k E e Φ Φc P Pc:
  later_tok ∗
  later_tok ∗
  P ∗
  □ (P -∗ Pc) ∗
  (staged_value E P Pc -∗ WPC e @ s; k; E {{ Φ }} {{ Φc }})
  ⊢ WPC e @ s; k; E {{ Φ }} {{ Φc ∗ Pc }}.
Proof.
  iIntros "(Htok1&Htok2&HP&#Hwand&Hwp)".
  rewrite wpc_eq /wpc_def. iIntros (mj).
  iApply wpc0_pri_inv_tok_res.
  iIntros (D Einv) "(Hitok&%Hdisj)".

  (* Create the invariant *)

  iMod (saved_prop_alloc P) as (γprop) "#Hsaved".
  iMod (saved_prop_alloc True%I) as (γprop') "#Hsaved'".
  iMod (own_alloc (● (Excl' (γprop, γprop')) ⋅ ◯ (Excl' (γprop, γprop')))) as (γ) "[H1 H2]".
  { apply auth_both_valid_2; [econstructor | reflexivity]. }
  iMod (pending_alloc) as (γ') "H".
  iMod (own_alloc (● (Excl' idle) ⋅ ◯ (Excl' idle))) as (γstatus) "[Hstat1 Hstat2]".
  { apply auth_both_valid_2; [econstructor | reflexivity]. }

  iDestruct (pri_inv_tok_infinite with "Hitok") as %Hinf.
  iMod (pri_inv_alloc Einv _ _ (staged_inv_inner E Einv mj γ γ' γstatus Pc) with "[HP H1 Hstat1]") as
      "#Hpri_inv"; auto.
  { iNext. rewrite /staged_inv_inner. iExists _, _, idle, P, True%I. iFrame "∗ #".
    iLeft. iFrame. iModIntro. iIntros "HP HC". iModIntro. iDestruct ("Hwand" with "[$]") as "$"; eauto.
  }

  iEval (rewrite -Qp_inv_half_half) in "Hitok".
  iDestruct (pri_inv_tok_split with "Hitok") as "(Hitok1&Hitok2)".

  (* The inductive proof *)
  iSpecialize ("Hwp" with "[Htok1 Hitok1 H2 Hstat2]").
  { iExists _, _, _, _, _, _. iFrame "∗". iFrame "Hsaved Hsaved'".
    iExists _. iFrame "Hpri_inv". }
  iSpecialize ("Hwp" $! mj).

  iModIntro.
  clear D Hdisj.
  iLöb as "IH" forall (e).
  rewrite ?wpc0_unfold. rewrite /wpc_pre.
  iSplit; last first.
  {
    iDestruct "Hwp" as "(_&Hwp)".
    iIntros (g ns D κs) "Hg #HC".
    iDestruct (pri_inv_tok_disj_inv_half with "[$]") as %Hdisj.
    iMod (pri_inv_acc with "Hpri_inv") as "(Hinner&Hclo)".
    { set_solver. }
    iDestruct "Hinner" as (?????) "(Hown1&#Hsaved1&#Hsaved2&Hstat&Hinner)".
    iDestruct "Hinner" as "[Hs|Hbad]"; last first.
    {
      (* This case is impossible since we have the staged_pending token *)
      iDestruct "Hbad" as "(_&_&>Hdone)".
      iDestruct (pending_done with "[$] [$]") as %[].
    }
    iMod (later_tok_decr with "[$]") as (ns' Hle) "Hg".
    iApply (step_fupd2N_inner_le).
    { apply (num_laters_per_step_exp ns'). lia. }
    iEval (simpl).
    iMod (fupd2_mask_subseteq ∅ ∅) as "Hclo'"; try set_solver+.
    do 2 (iModIntro; iModIntro; iNext).
    iMod "Hclo'".
    destruct stat as [q1 q2|].
    {
      iDestruct "Hs" as (Hle') "(HPs&Hitok&#Hwand')".
      iDestruct ("Hwand'" with "[$]") as "HPcr".
      rewrite /wpc_crash_modality.
      iApply step_fupd2N_inner_plus.
      iDestruct (pri_inv_tok_global_le_acc _ _ _ q1 with "[] Hg") as "(Hg&Hg_clo)".
      { iPureIntro. naive_solver. }
      iDestruct (pri_inv_tok_join with "[$] [$]") as "Hitok".
      iMod (pri_inv_tok_disable with "[$Hg Hitok]") as "Hg".
      { destruct Hle' as (?&<-&_). rewrite Qp_add_comm. iFrame. }
      replace (⊤ ∖ D ∖ Einv) with (⊤ ∖ (Einv ∪ D)) by set_solver.
      iSpecialize ("HPcr" with "[$] [$]").
      iApply (step_fupd2N_inner_wand with "HPcr"); auto.
      iIntros "(Hg&HPr&HPc)".
      replace (⊤ ∖ (Einv ∪ D)) with (⊤ ∖ D ∖ Einv) by set_solver.
      iMod (pri_inv_tok_enable with "[$Hg //]") as "(Hitok&Hg)".
      iMod (pending_upd_done with "H") as "H".
      destruct Hle' as (?&<-&_).
      iDestruct (pri_inv_tok_split with "[$]") as "(Hitok1&Hitok2)".
      iDestruct ("Hg_clo" with "[$]") as "Hg".
      iMod ("Hclo" with "[HPr Hitok2 Hown1 H Hstat]").
      { iNext. iExists _, _, (inuse _ _), _, _. iFrame "∗ #". iRight. iFrame. }
      iSpecialize ("Hwp" with "[$] [$]").
      iApply step_fupd2N_inner_fupd.
      iApply (step_fupd2N_inner_wand with "Hwp"); auto. iIntros "(Hg&$)". iFrame.
      iApply (global_state_interp_le with "[$]"); eauto.
      lia.
    }
    {
      iDestruct "Hs" as "(HPs&#Hwand')".
      iMod ("Hwand'" with "[$] [$]") as "(HPc&HPr)".
      iMod (pending_upd_done with "H") as "H".
      iMod ("Hclo" with "[HPr Hown1 H Hstat]").
      { iNext. iExists _, _, idle, _, _. iFrame "∗ #". iRight. iFrame. }
      iApply step_fupd2N_inner_plus.
      iApply step_fupd2N_inner_later; auto. iNext.
      iSpecialize ("Hwp" with "[$] [$]").
      iApply step_fupd2N_inner_fupd.
      iApply (step_fupd2N_inner_wand with "Hwp"); auto. iIntros "(Hg&$)". iFrame.
      iApply (global_state_interp_le with "[$]"); eauto.
      lia.
    }
  }
  iDestruct "Hwp" as "(Hwp&_)".
  destruct (to_val e).
  { iIntros. iMod ("Hwp" with "[$] [$]"). eauto. }
  iIntros.
  iMod ("Hwp" with "[$] [$] [$]") as "Hwp".
  iModIntro. simpl. iMod "Hwp". iModIntro.
  iNext. iMod "Hwp". iModIntro. iApply (step_fupd2N_wand with "Hwp").
  iIntros "($&Hwp)".
  iIntros. iMod ("Hwp" with "[//]") as "($&$&Hwpc&$&$)". iModIntro. iApply ("IH" with "[$] [$] [$]").
  eauto.
Qed.


Lemma wpc_staged_inv s k E1 E1' e Φ Φc Qs P :
  to_val e = None →
  E1 ⊆ E1' →
  staged_value E1' Qs P ∗
  (Φc ∧ (Qs -∗ WPC e @ NotStuck; k; E1 {{λ v, ∃ Qnew, Qnew ∗ □ (Qnew -∗ C ==∗ P) ∗
                                       (staged_value E1' Qnew P -∗ Φc ∧ Φ v)}}
                                 {{ Φc ∗ P }}))
  ⊢ WPC e @ s; (S k); E1 {{ Φ }} {{ Φc }}.
Proof.
  iIntros (Hnval Hsub) "(Hstaged&Hwp)".
  iDestruct "Hstaged" as (??????) "(Hown&Hownstat&#Hsaved1&#Hsaved2&Hltok&Hitok&Hinv)".
  iDestruct "Hinv" as (mj_init) "Hinv".
  rewrite /staged_inv.
  rewrite wpc_eq /wpc_def. iIntros (mj).

  iLöb as "IH" forall (γprop γprop' Qs) "Hsaved1 Hsaved2".

  (* Base case *)
  iEval (rewrite wpc0_unfold).
  rewrite /wpc_pre. iSplit; last first.
  {
    iDestruct "Hwp" as "(Hwp&_)".
    iIntros (g1 ns D' κs) "Hg #HC".
    iApply step_fupd2N_inner_later'.
    iNext; iModIntro; iFrame.
  }
  rewrite Hnval.
  iIntros (q σ1 g1 ns D κ κs nt) "Hσ Hg HNC".
  iDestruct (pri_inv_tok_disj_inv_half with "[$]") as %Hdisj.
  iMod (pri_inv_acc with "[$]") as "(Hinner&Hclo)".
  { set_solver. }
  iDestruct "Hinner" as (?????) "(>Hown'&#Hsaved1'&#Hsaved2'&>Hstatus'&Hinner)".
  iDestruct (own_valid_2 with "Hown' Hown") as "#H".
  iDestruct "H" as %[Heq%Excl_included%leibniz_equiv _]%auth_both_valid_discrete.
  iDestruct (own_valid_2 with "Hstatus' Hownstat") as "#Heq_status".
  iDestruct "Heq_status" as %[Heq_status%Excl_included%leibniz_equiv _]%auth_both_valid_discrete.
  inversion Heq; subst.
  iMod (later_tok_decr with "[$]") as (ns' Hlt) "Hg".
  iMod (fupd2_mask_subseteq ∅ ∅) as "Hclo'"; try set_solver+.
  iModIntro. simpl. iModIntro. iNext. iModIntro. iApply (step_fupd2N_le (S (S (num_laters_per_step ns')))).
  { etransitivity; last eapply (num_laters_per_step_exp ns'); lia. }
  simpl.
  iDestruct (saved_prop_agree with "Hsaved1 Hsaved1'") as "Hequiv1".
  iDestruct (saved_prop_agree with "Hsaved2 Hsaved2'") as "Hequiv2".
  iModIntro. iModIntro. iModIntro.
  iDestruct "Hinner" as "[(HPs&Hs)|Hfin]"; last first.
  { (* Impossible, since we have NC token. *)
    iDestruct "Hfin" as "(_&HC&_)". iDestruct (NC_C with "[$] [$]") as %[]. }
  iRewrite -"Hequiv1" in "HPs".
  iDestruct "Hwp" as "(_&Hwp)".
  iSpecialize ("Hwp" with "[$]").

  iDestruct (pri_inv_tok_global_valid with "Hg") as %(Hmin&Hvalid).
  destruct (Qp_plus_inv_2_gt_1_split mj) as (mj_keep&mj_inv&Heq_mj&Hinvalid); first auto.

  iMod (pri_inv_tok_disable with "[$]") as "Hg".
  iSpecialize ("Hwp" $! _).
  iEval (rewrite wpc0_unfold) in "Hwp".
  iDestruct "Hwp" as "(Hwp&_)".
  iMod ("Hclo'").
  rewrite Hnval.
  replace (⊤ ∖ (E2 ∪ D)) with (⊤ ∖ D ∖ E2) by set_solver.
  iMod ("Hwp" with "[$] [$] [$]") as "Hwp".
  simpl. iMod "Hwp". iModIntro. iNext. iMod "Hwp". iModIntro.
  iApply (step_fupd2N_wand with "Hwp"). iIntros "(%Hred&Hwp)".
  iSplit. { destruct s; eauto. }
  iIntros (e2 σ2 g2 efs Hstep). iMod ("Hwp" with "[//]") as "($&Hg&H&Hefs&$)".
  iMod (later_tok_incr with "[$]") as "(Hg&Hltok)".

  iMod (saved_prop_alloc
          (wpc0 NotStuck k (E2 ∪ D) E1 e2
            (λ v : val Λ, ∃ Qnew : iPropI Σ, Qnew ∗ □ (Qnew -∗ C ==∗ P) ∗ (staged_value E1' Qnew P -∗ Φc ∧ Φ v))
            (Φc ∗ P))%I) as (γprop_stored') "#Hsaved1''".
  iMod (saved_prop_alloc Φc) as (γprop_remainder') "#Hsaved2''".
  iMod (own_update_2 _ _ _ (● Excl' (γprop_stored', γprop_remainder') ⋅
                            ◯ Excl' (γprop_stored', γprop_remainder'))
          with "Hown' Hown") as "[Hown' Hown]".
  { by apply auth_update, option_local_update, exclusive_local_update. }
  iMod (own_update_2 _ _ _ (● Excl' inuse ⋅ ◯ Excl' inuse)
          with "Hstatus' Hownstat") as "[Hstatus' Hownstat]".
  { by apply auth_update, option_local_update, exclusive_local_update. }
  iMod (pri_inv_tok_enable with "[$Hg //]") as "(Hitok&Hg)".
  iMod ("Hclo" with "[Hown' Hstatus' H Hitok]").
  { iNext.
    iExists _, _, _, _, _. iFrame "∗ #".
    iLeft. iFrame "H Hitok". iModIntro. iIntros "Hwpc".
    iEval (rewrite wpc0_unfold) in "Hwpc". iDestruct "Hwpc" as "(_&Hwpc)".
    rewrite /wpc_crash_modality.
    iIntros (????) "Hg HC".

    (* TODO: ******** maybe we don't want to use the whole wpc/wpc0 mechanism of fixing an mj that doens't change? 
       Can just reserve name space token, split in 1/2, staged_val owns 1/2 and the staged inv init owns other half. When in use staged val user puts 1/2 in the invariant, thus initer can "disable" for the wpc that's in there.

      But then how does the staged val user open on next step?

       Maybe the mj is the fraction needed above 1/2 to disable?


      User --> has 1/2 of pri_inv_tok, starts with some mj1
      Initer --> hs 1/2 of pri_inv_tok, starts with some mj2

      User's "sub" wpc, we set to have min(mj1, mj2) (or so).


      Basically user must keep at least mj1 of pri_inv_tok so it can argue it is still enabled on the next step *)
Abort.

(*
    iSpecialize ("Hwpc" with "[$] [$]").
    iDestru
 }
  iMod (global_state_interp_le _ ns with "[$]"); eauto.
  { lia. }
  iApply step_fupd2N_inner_later; auto. iNext. iFrame.
  }
  iMod ("Hs" with "[$] [$]") as "(HP&HPr)".
  iDestruct "Hs" as "[Hs1|Hs2]".
  {
  iMod (later_tok_decr with "[$]") as (ns' Hle) "Hg".
  iApply (step_fupd2N_inner_le).
  { apply (num_laters_per_step_exp ns'). lia. }
  simpl.
  iMod (fupd2_mask_subseteq ∅ ∅) as "Hclo'"; try set_solver+.
  iModIntro. iModIntro. iNext.
  iMod "Hclo'".
  iDestruct "Hs" as "[Hinuse|Hunused]".
  {
    iDestruct "Hinuse" as "(HPs&Hitok&#Hwand')".
    iDestruct ("Hwand'" with "[$]") as "HPcr".
    rewrite /wpc_crash_modality.
    iApply step_fupd2N_inner_plus.
    iMod (pri_inv_tok_disable with "[$]") as "Hg".
    replace (⊤ ∖ D ∖ Einv) with (⊤ ∖ (Einv ∪ D)) by set_solver.
    iSpecialize ("HPcr" with "[$] [$]").
    iApply (step_fupd2N_inner_wand with "HPcr"); auto.
    iIntros "(Hg&HPc&HPr)".
    replace (⊤ ∖ (Einv ∪ D)) with (⊤ ∖ D ∖ Einv) by set_solver.
    iMod (pri_inv_tok_enable with "[$Hg //]") as "(Hitok&Hg)".
    iMod (pending_upd_done with "H") as "H".
    iMod ("Hclo" with "[HPr Hitok Hown1 H]").
    { iNext. iExists _, _, _, _. iFrame "∗ #". iRight. iFrame. }
    iSpecialize ("Hwp" with "[$] [$]").
    iApply step_fupd2N_inner_fupd.
    iApply (step_fupd2N_inner_wand with "Hwp"); auto. iIntros "(Hg&$)". iFrame.
    iApply (global_state_interp_le with "[$]"); eauto.
    lia.
  }
  {
      iDestruct "Hunused" as "(HPs&#Hwand')".
      iMod ("Hwand'" with "[$] [$]") as "(HPc&HPr)".
      iMod (pending_upd_done with "H") as "H".
      iMod ("Hclo" with "[HPr Hown1 H]").
      { iNext. iExists _, _, _, _. iFrame "∗ #". iRight. iFrame. }
      iApply step_fupd2N_inner_plus.
      iApply step_fupd2N_inner_later; auto. iNext.
      iSpecialize ("Hwp" with "[$] [$]").
      iApply step_fupd2N_inner_fupd.
      iApply (step_fupd2N_inner_wand with "Hwp"); auto. iIntros "(Hg&$)". iFrame.
      iApply (global_state_interp_le with "[$]"); eauto.
      lia.
    }

  iMod (pri_inv_acc with "[$]").
  iDestruct "Hinv" as (?) "H".

End inv.
*)

(*
Lemma wpc_staged_inv s k E1 E1' e Φ Φc Qs Qr P :
  E1 ⊆ E1' →
  staged_value E1' Qs Qr P ∗
  ((Qr -∗ Φc) ∧ (Qs -∗ WPC e @ NotStuck; k; E1 {{λ v, ∃ Qnew, Qnew ∗ □ (Qnew -∗ C ==∗ P) ∗
                                       (staged_value E1' Qnew True P -∗ Φc ∧ Φ v)}}
                                 {{ Φc ∗ P }}))
  ⊢ WPC e @ s; (S k); E1 {{ Φ }} {{ Φc }}.
Proof.
  iIntros (Hsub) "(Hstaged&Hwp)".
  iDestruct "Hstaged" as (?????) "(Hown&#Hsaved1&#Hsaved2&Hltok&Hitok&#Hinv)".
  rewrite /staged_inv.
  rewrite wpc_eq /wpc_def. iIntros (D).
  iLöb as "IH" forall (γprop γprop' Qs Qr) "Hsaved1 Hsaved2".

  (* Base case *)
  iEval (rewrite wpc0_unfold).
  rewrite /wpc_pre. iSplit; last first.
  {
    (* Crash case *)
    iIntros (g1 ns κs) "Hg #HC".
    iDestruct (pri_inv_tok_disj with "[$]") as %Hdisj.
    iMod (pri_inv_acc with "[$]") as "(Hinner&Hclo)".
    { set_solver. }
    iDestruct "Hinner" as (????) "(>Hown'&#Hsaved1'&#Hsaved2'&Hinner)".
    iDestruct (own_valid_2 with "Hown' Hown") as "#H".
    iDestruct "H" as %[Heq%Excl_included%leibniz_equiv _]%auth_both_valid_discrete.
    inversion Heq; subst.
    iMod (later_tok_decr with "[$]") as (ns' Hlt) "Hg".
    iApply (step_fupd2N_inner_le).
    { apply (num_laters_per_step_exp ns'). lia. }
    simpl.
    iMod (fupd2_mask_subseteq ∅ ∅) as "Hclo'"; try set_solver+.
    iModIntro. iModIntro. iNext.
    iDestruct (saved_prop_agree with "Hsaved1 Hsaved1'") as "Hequiv1".
    iDestruct (saved_prop_agree with "Hsaved2 Hsaved2'") as "Hequiv2".
    iModIntro. iModIntro. iNext.
    iDestruct "Hinner" as "[(Hltok&Hs)|Hfin]"; last first.
    {
      (* The staged_inv allocator already "triggered" the crash view shift and collected
         its part *)

      (* TODO: need to generalize for induction whether we have pri_inv_tok or if it's in
         the invariant *)

      iDestruct "Hfin" as "(HPr&_&#Hdone)".
      iRewrite -"Hequiv2" in "HPr".
      iDestruct "Hwp" as "(Hcrash&_)".
      iSpecialize ("Hcrash" with "[$]").
      iMod "Hclo'".
      iMod (saved_prop_alloc True%I) as (γprop_remainder_new) "#Hsaved2_new".
      iMod (own_update_2 _ _ _ (● Excl' (γprop_stored, γprop_remainder_new) ⋅
                                ◯ Excl' (γprop_stored, γprop_remainder_new))
              with "Hown' Hown") as "[Hown' Hown]".
      { by apply auth_update, option_local_update, exclusive_local_update. }
      iMod ("Hclo" with "[Hown']").
      { iNext. iExists _, _, _, _. iFrame "∗ #". }
      iMod (global_state_interp_le _ ns with "[$]"); eauto.
      { lia. }
      iApply step_fupd2N_inner_later; auto. iNext. iFrame.
    }
    (*
    iDestruct "Hs" as "[Hs1|Hs2]".
    {
    iMod (later_tok_decr with "[$]") as (ns' Hle) "Hg".
    iApply (step_fupd2N_inner_le).
    { apply (num_laters_per_step_exp ns'). lia. }
    simpl.
    iMod (fupd2_mask_subseteq ∅ ∅) as "Hclo'"; try set_solver+.
    iModIntro. iModIntro. iNext.
    iMod "Hclo'".
    iDestruct "Hs" as "[Hinuse|Hunused]".
    {
      iDestruct "Hinuse" as "(HPs&Hitok&#Hwand')".
      iDestruct ("Hwand'" with "[$]") as "HPcr".
      rewrite /wpc_crash_modality.
      iApply step_fupd2N_inner_plus.
      iMod (pri_inv_tok_disable with "[$]") as "Hg".
      replace (⊤ ∖ D ∖ Einv) with (⊤ ∖ (Einv ∪ D)) by set_solver.
      iSpecialize ("HPcr" with "[$] [$]").
      iApply (step_fupd2N_inner_wand with "HPcr"); auto.
      iIntros "(Hg&HPc&HPr)".
      replace (⊤ ∖ (Einv ∪ D)) with (⊤ ∖ D ∖ Einv) by set_solver.
      iMod (pri_inv_tok_enable with "[$Hg //]") as "(Hitok&Hg)".
      iMod (pending_upd_done with "H") as "H".
      iMod ("Hclo" with "[HPr Hitok Hown1 H]").
      { iNext. iExists _, _, _, _. iFrame "∗ #". iRight. iFrame. }
      iSpecialize ("Hwp" with "[$] [$]").
      iApply step_fupd2N_inner_fupd.
      iApply (step_fupd2N_inner_wand with "Hwp"); auto. iIntros "(Hg&$)". iFrame.
      iApply (global_state_interp_le with "[$]"); eauto.
      lia.
    }
    {
      iDestruct "Hunused" as "(HPs&#Hwand')".
      iMod ("Hwand'" with "[$] [$]") as "(HPc&HPr)".
      iMod (pending_upd_done with "H") as "H".
      iMod ("Hclo" with "[HPr Hown1 H]").
      { iNext. iExists _, _, _, _. iFrame "∗ #". iRight. iFrame. }
      iApply step_fupd2N_inner_plus.
      iApply step_fupd2N_inner_later; auto. iNext.
      iSpecialize ("Hwp" with "[$] [$]").
      iApply step_fupd2N_inner_fupd.
      iApply (step_fupd2N_inner_wand with "Hwp"); auto. iIntros "(Hg&$)". iFrame.
      iApply (global_state_interp_le with "[$]"); eauto.
      lia.
    }

  iMod (pri_inv_acc with "[$]").
  iDestruct "Hinv" as (?) "H".
*)
*)

End inv.
