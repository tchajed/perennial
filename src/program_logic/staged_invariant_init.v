From iris.algebra Require Import gmap auth agree gset coPset excl csum.
From Perennial.base_logic.lib Require Export fancy_updates.
From stdpp Require Export namespaces.
From Perennial.base_logic.lib Require Import wsat invariants ae_invariants saved_prop.
From Perennial.Helpers Require Import Qextra.
From iris.algebra Require Import gmap.
From iris.proofmode Require Import tactics.
From Perennial.program_logic Require Export step_fupd_extra crash_weakestpre ae_invariants_mutable later_res private_invariants staged_invariant_alt.

Existing Instances pri_inv_tok_timeless later_tok_timeless.

Section inv.
Context `{IRISG: !irisGS Λ Σ}.
Context `{PRI: !pri_invG IRISG}.
Context `{!later_tokG IRISG}.
Context `{!stagedG Σ}.
Implicit Types i : positive.
Implicit Types N : namespace.
Implicit Types P Q R : iProp Σ.
Existing Instances pri_inv_tok_timeless later_tok_timeless.

Lemma wpc0_mj_valid s k mj E e Φ Φc :
  (⌜ (/2 < mj)%Qp ⌝ → wpc0 s k mj E e Φ Φc) -∗
  wpc0 s k mj E e Φ Φc.
Proof using PRI.
  iIntros "H".
  iApply wpc0_pri_inv_tok_res. iIntros (??) "(H'&%)".
  iModIntro. iApply "H"; iPureIntro; naive_solver.
Qed.

Lemma wpc0_staged_inv_create s k mj' mj E e Φ Φc P Pc :
  (/ 2 < mj')%Qp →
  later_tok ∗
  later_tok ∗
  P ∗
  □ (P -∗ Pc) ∗
  (staged_value E P Pc ∗ staged_inv_cancel E mj' Pc -∗ wpc0 s k mj E e Φ (Φc ∗ Pc))
  ⊢ wpc0 s k mj E e Φ (Φc ∗ Pc).
Proof.
  iIntros (Hlt) "(Htok1&Htok2&HP&#Hwand&Hwp)".
  iApply wpc0_pri_inv_tok_res.
  iIntros (D Einv) "(Hitok&%Hgt&%Hdisj)".

  (* Create the invariant *)

  iMod (saved_prop_alloc P) as (γprop) "#Hsaved".
  iMod (saved_prop_alloc True%I) as (γprop') "#Hsaved'".
  iMod (own_alloc (● (Excl' (γprop, γprop')) ⋅ ◯ (Excl' (γprop, γprop')))) as (γ) "[H1 H2]".
  { apply auth_both_valid_2; [econstructor | reflexivity]. }
  iMod (pending_alloc) as (γ') "H".
  iMod (own_alloc (● (Excl' idle) ⋅ ◯ (Excl' idle))) as (γstatus) "[Hstat1 Hstat2]".
  { apply auth_both_valid_2; [econstructor | reflexivity]. }

  iDestruct (pri_inv_tok_infinite with "Hitok") as %Hinf.
  destruct (Qp_plus_inv_2_gt_1_split mj') as (mj_ikeep&mj_ishare&Heq_mj&Hinvalid); first auto.
  iEval (rewrite -Qp_inv_half_half) in "Hitok".
  iDestruct (pri_inv_tok_split with "Hitok") as "(Hitok_u&Hitok_i)".
  iEval (rewrite -Heq_mj) in "Hitok_i".
  iDestruct (pri_inv_tok_split with "Hitok_i") as "(Hitok_ikeep&Hitok_ishare)".
  iMod (pri_inv_alloc Einv _ _ (staged_inv_inner E Einv mj' mj_ishare γ γ' γstatus Pc) with "[HP H1 Hitok_ishare Hstat1]") as
      "#Hpri_inv"; auto.
  { iNext. rewrite staged_inv_inner_unfold. iExists _, _, idle, P, True%I. iFrame "∗ #".
    iLeft. iFrame. iModIntro. iIntros "HP HC". iModIntro. iDestruct ("Hwand" with "[$]") as "$"; eauto.
  }
  iModIntro.
  iApply "Hwp".
  iSplitL "Htok1 H2 Hstat2 Hitok_u".
  {
    iExists _, _, _, _, _, _. iFrame "∗". iFrame "Hsaved Hsaved'".
    iExists _, _. iFrame "Hpri_inv". eauto.
  }
  {
    iExists _, _, _, _, _, _. iFrame "%". iFrame. eauto.
  }
Qed.

Lemma wpc0_staged_inv_cancel s k mj' mj E1 E2 e Φ Φc Pc:
  E1 ⊆ E2 →
  (mj' ≤ mj)%Qp →
  staged_inv_cancel E1 mj' Pc -∗
  wpc0 s k mj E2 e (λ v, staged_inv_cancel E1 mj' Pc -∗ Φ v) Φc -∗
  wpc0 s k mj E2 e Φ (Φc ∗ Pc).
Proof.
  iIntros (Hsub Hle_mj) "Hsc Hwp".
  iDestruct "Hsc" as (mj0 Einv mj_ishare mj_ikeep γ γ' ?) "Hsc".
  iDestruct "Hsc" as (Hlt Hinf Hinvalid Heq_mj) "(Htok2&H&Hitok_ikeep&#Hpri_inv)".
  iLöb as "IH" forall (e E2 Hsub).
  rewrite ?wpc0_unfold. rewrite /wpc_pre.
  iSplit; last first.
  {
    iDestruct "Hwp" as "(_&Hwp)".
    iClear "IH".
    iAssert (∃ E', ⌜ E' ⊆ E1 ⌝ ∧ pri_inv Einv (staged_inv_inner E' Einv mj0 mj_ishare γ γ' γstatus Pc))%I as "Hpri_inv'".
    { iExists E1. iSplit; eauto. }
    iClear "Hpri_inv". iDestruct "Hpri_inv'" as (E' Hsub') "#Hpri_inv".
    iLöb as "IH" forall (E' Einv mj0 mj_ikeep mj_ishare γ γ' γstatus Hsub' Heq_mj Hle_mj Hinvalid Hinf Hlt) "Hpri_inv".
    iIntros (g ns D κs) "Hg #HC".
    iDestruct (pri_inv_tok_disj with "[$]") as %[Hdisj|Hval]; last first.
    { exfalso. apply Qp_lt_nge in Hinvalid. revert Hval. rewrite frac_valid.
      intros Hle'. apply Hinvalid. etransitivity; last eassumption.
      apply Qp_add_le_mono_r. destruct Hlt; etransitivity; eassumption. }
    iMod (pri_inv_acc with "Hpri_inv") as "(Hinner&Hclo)".
    { set_solver. }
    iEval (rewrite staged_inv_inner_unfold) in "Hinner".
    iDestruct "Hinner" as (?????) "(Hown1&#Hsaved1&#Hsaved2&Hstat&>Hitok_ishare&Hinner)".
    iDestruct "Hinner" as "[Hs|Hfired]"; last first.
    {
      iDestruct "Hfired" as "(HPr&_&[HPc|>Hbad])"; last first.
      { (* This case is impossible since we have the staged_pending token *)
        iDestruct (pending_done with "[$] [$]") as %[]. }
      iMod (later_tok_decr with "[$]") as (ns' Hle) "Hg".
      iApply (step_fupd2N_inner_le).
      { apply (num_laters_per_step_exp ns'). lia. }
      iMod (fupd2_mask_subseteq ∅ ∅) as "Hclo'"; try set_solver+.
      iEval (simpl).
      do 2 (iModIntro; iModIntro; iNext).
      iMod (pending_upd_done with "H") as "H".
      iMod ("Hclo'").
      iMod ("Hclo" with "[-Hg HPc Hwp]").
      { iNext. iEval (rewrite staged_inv_inner_unfold). iExists _, _, _, _, _. iFrame "∗ #". iRight. iFrame. }
      iSpecialize ("Hwp" with "[$] [$]").
      iApply step_fupd2N_inner_fupd.
      iApply (step_fupd2N_inner_wand with "Hwp"); auto.
      { lia. }
      iIntros "(Hg&$)". iFrame.
      iApply (global_state_interp_le with "[$]"); eauto.
      lia.
    }
    iMod (later_tok_decr with "[$]") as (ns' Hle) "Hg".
    iApply (step_fupd2N_inner_le).
    { apply (num_laters_per_step_exp ns'). lia. }
    iEval (simpl).
    iMod (fupd2_mask_subseteq ∅ ∅) as "Hclo'"; try set_solver+.
    do 2 (iModIntro; iModIntro; iNext).
    iMod "Hclo'".
    destruct stat as [q1 q2|q|].
    {
      iDestruct "Hs" as (Hle') "(HPs&Hitok&#Hwand')".
      iDestruct ("Hwand'" with "[$]") as "HPcr".
      rewrite /wpc_crash_modality.
      iApply step_fupd2N_inner_plus.
      iDestruct (pri_inv_tok_global_le_acc _ _ _ q1 with "[] Hg") as "(Hg&Hg_clo)".
      { iPureIntro. split; first naive_solver.
        transitivity mj0; first naive_solver.
        destruct Hlt; etransitivity; eassumption. }
      iDestruct (pri_inv_tok_join with "Hitok_ikeep Hitok_ishare") as "Hitok'".
      rewrite Heq_mj.
      iDestruct (pri_inv_tok_join with "[$] [$]") as "Hitok".
      iDestruct (pri_inv_tok_le_acc q1 with "[$]") as "(Hitok&Hitok_clo)".
      { naive_solver. }
      iMod (pri_inv_tok_disable with "[$Hg $Hitok]") as "Hg".
      replace (⊤ ∖ D ∖ Einv) with (⊤ ∖ (Einv ∪ D)) by set_solver.
      iSpecialize ("HPcr" with "[$] [$]").
      iApply (step_fupd2N_inner_wand with "HPcr"); auto.
      { set_solver. }
      iIntros "(Hg&HPr&HPc)".
      replace (⊤ ∖ (Einv ∪ D)) with (⊤ ∖ D ∖ Einv) by set_solver.
      iMod (pri_inv_tok_enable with "[$Hg //]") as "(Hitok&Hg)".
      iMod (pending_upd_done with "H") as "H".
      iDestruct ("Hitok_clo" with "[$]") as "Hitok".
      iDestruct (pri_inv_tok_split with "[$]") as "(Hitok1&Hitok2)".
      iEval (rewrite -Heq_mj) in "Hitok1".
      iDestruct (pri_inv_tok_split with "[$]") as "(Hitok1_keep&Hitok1_share)".
      iDestruct ("Hg_clo" with "[$]") as "Hg".
      iMod ("Hclo" with "[HPr Hitok2 Hitok1_share Hown1 H Hstat]").
      { iNext. iEval (rewrite staged_inv_inner_unfold).
        iExists _, _, (inuse _ _), _, _. iFrame "∗ #". iRight. iFrame. }
      iSpecialize ("Hwp" with "[$] [$]").
      iApply step_fupd2N_inner_fupd.
      iApply (step_fupd2N_inner_wand with "Hwp"); auto. iIntros "(Hg&$)". iFrame.
      iApply (global_state_interp_le with "[$]"); eauto.
      lia.
    }
    {
      iDestruct "Hs" as "[Hs|Hbad]"; last first.
      { iDestruct (pending_done with "[$] [$]") as %[]. }
      iDestruct "Hs" as (? E1' Einv' mj_ishare' mj_ikeep' γs' γfinish' γstatus') "Hs".
      iDestruct "Hs" as (????) "(Hltok&H'&Hitok'&#Hinv')".
      iMod (pending_upd_done with "H") as "Hdone".
      iMod ("Hclo" with "[Hown1 Hstat Hitok_ishare Hdone]").
      { iNext. iEval (rewrite staged_inv_inner_unfold).
        iExists _, _, _, _, _. iFrame "∗ #". iLeft. iRight. iFrame. }
      iSpecialize ("IH" $! E1' _ q _ mj_ishare' with "[] [] [] [] [] [] [$] [$] [$] Hwp [] [$] [$]"); eauto.
      { iPureIntro; etransitivity; try eassumption. }
      { iPureIntro.
        split.
        - naive_solver.
        - transitivity (mj0); naive_solver. }
      iApply step_fupd2N_inner_fupd.
      iApply (step_fupd2N_inner_wand with "IH"); auto.
      { lia. }
      iIntros "(?&$&$)". iMod (global_state_interp_le with "[$]") as "$"; eauto. lia.
    }
    {
      iDestruct "Hs" as "(HPs&#Hwand')".
      iMod ("Hwand'" with "[$] [$]") as "(HPc&HPr)".
      iMod (pending_upd_done with "H") as "H".
      iMod ("Hclo" with "[HPr Hown1 Hitok_ishare H Hstat]").
      { iNext. iEval (rewrite staged_inv_inner_unfold).
        iExists _, _, idle, _, _. iFrame "∗ #". iRight. iFrame. }
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
  { iIntros. iMod ("Hwp" with "[$] [$]") as "(Hv&$&$)".
    iModIntro. iApply "Hv". iExists _, _, _, _, _, _, _. iFrame "∗ #". eauto.
  }
  iIntros.
  iMod ("Hwp" with "[$] [$] [$]") as "Hwp".
  iModIntro. simpl. iMod "Hwp". iModIntro.
  iNext. iMod "Hwp". iModIntro. iApply (step_fupd2N_wand with "Hwp").
  iIntros "($&Hwp)".
  iIntros. iMod ("Hwp" with "[//]") as "($&$&Hwpc&$&$)". iModIntro.
  iApply ("IH" with "[] [$] [$] [$]").
  { iPureIntro. destruct (to_val); set_solver. }
  eauto.
Qed.

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
  iApply (wpc0_mj_valid). iIntros (Hlt).
  iApply (wpc0_staged_inv_create _ _ _ _ _ _ _ _ P); try eassumption.
  iFrame "∗ #". iIntros "(Hval&Hcancel)".
  iApply (wpc0_staged_inv_cancel with "Hcancel"); auto.
  iSpecialize ("Hwp" with "[$]").
  iSpecialize ("Hwp" $! _).
  iApply (wpc0_strong_mono with "Hwp"); eauto.
  iSplit.
  - iIntros (?) "$". eauto.
  - eauto.
Qed.

End inv.
