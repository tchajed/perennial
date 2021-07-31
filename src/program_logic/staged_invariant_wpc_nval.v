From iris.algebra Require Import gmap auth agree gset coPset excl csum.
From Perennial.base_logic.lib Require Export fancy_updates.
From stdpp Require Export namespaces.
From Perennial.base_logic.lib Require Import wsat invariants ae_invariants saved_prop.
From Perennial.Helpers Require Import Qextra.
From iris.algebra Require Import gmap.
From iris.proofmode Require Import tactics.
From Perennial.program_logic Require Export step_fupd_extra crash_weakestpre ae_invariants_mutable later_res private_invariants staged_invariant_alt wpc_nval.

Existing Instances pri_inv_tok_timeless later_tok_timeless.

Section def.
Context `{IRISG: !irisGS Λ Σ}.
Context `{!pri_invG IRISG}.
Context `{!later_tokG IRISG}.
Context `{!stagedG Σ}.

Lemma wpc_staged_inv_use_post' s k E1 e Φl Φr Φc Qs P :
  to_val e = None →
  staged_value ⊤ Qs P ∗
  WPC e @ s; k; E1 {{λ v, (Qs ∗ Φl v) -∗
                           |NC={E1,E1}=> ∃ Qnew, Qnew ∗ (Qnew -∗ C ==∗ P) ∗ (staged_value ⊤ Qnew P -∗ Φr v)}}
                   {{ Φc }}
  ⊢ WPC e @ s; k; E1 {{ λ v, Φl v -∗ Φr v }} {{ Φc }}.
Proof.
  iIntros (Hnval) "(Hstaged&Hwp)".
  iDestruct "Hstaged" as (??????) "(Hown&Hownstat&#Hsaved1&#Hsaved2&Hltok&Hitok&Hinv)".
  iDestruct "Hinv" as (mj_wp_init mj_ishare Hlt) "#Hinv".
  rewrite /staged_inv.
  rewrite wpc_eq /wpc_def. iIntros (mj).

  iLöb as "IH" forall (γprop γprop' Qs) "Hsaved1 Hsaved2".

  (* Base case *)
  iEval (rewrite wpc0_unfold).
  rewrite /wpc_pre. iSplit; last first.
  {
    iSpecialize ("Hwp" $! _).
    iEval (rewrite wpc0_unfold /wpc_pre) in "Hwp".
    iDestruct ("Hwp") as "(_&Hwp)".
    eauto.
  }
  rewrite Hnval.
  iIntros (q σ1 g1 ns D κ κs nt) "Hσ Hg HNC".
  iDestruct (pri_inv_tok_disj_inv_half with "[$]") as %Hdisj.
  iMod (pri_inv_acc with "[$]") as "(Hinner&Hclo)".
  { set_solver. }
  iEval (rewrite staged_inv_inner_unfold) in "Hinner".
  iDestruct "Hinner" as (?????) "(>Hown'&#Hsaved1'&#Hsaved2'&>Hstatus'&>Hitok_ishare&Hinner)".
  iDestruct (own_valid_2 with "Hown' Hown") as "#H".
  iDestruct "H" as %[Heq%Excl_included%leibniz_equiv _]%auth_both_valid_discrete.
  iDestruct (own_valid_2 with "Hstatus' Hownstat") as "#Heq_status".
  iDestruct "Heq_status" as %[Heq_status%Excl_included%leibniz_equiv _]%auth_both_valid_discrete.
  inversion Heq; subst.
  iMod (later_tok_decr with "[$]") as (ns' Hlt') "Hg".
  iMod (fupd2_mask_subseteq ∅ ∅) as "Hclo'"; try set_solver+.
  iModIntro. simpl. iModIntro. iNext. iModIntro. iApply (step_fupd2N_le (S (S (num_laters_per_step ns')))).
  { etransitivity; last eapply (num_laters_per_step_exp ns'); lia. }
  simpl.
  iDestruct (saved_prop_agree with "Hsaved1 Hsaved1'") as "Hequiv1".
  iDestruct (saved_prop_agree with "Hsaved2 Hsaved2'") as "Hequiv2".
  iModIntro. iModIntro. iModIntro.
  iDestruct "Hinner" as "[HPs|Hfin]"; last first.
  { (* Impossible, since we have NC token. *)
    iDestruct "Hfin" as "(_&HC&_)". iDestruct (NC_C with "[$] [$]") as %[]. }
  iRewrite -"Hequiv1" in "HPs".
  iDestruct "HPs" as "(HPs&_)".

  iDestruct (pri_inv_tok_global_valid with "Hg") as %(Hmin&Hvalid).
  destruct (Qp_plus_inv_2_gt_1_split mj) as (mj_ukeep&mj_ushare&Heq_mj&Hinvalid); first auto.
  set (mj_wp := (mj_wp_init `min` mj `min` (/2 + mj_ishare) `min` (/2 + mj_ushare))%Qp).
  assert (/ 2 < mj_wp)%Qp.
  {
    - rewrite /mj_wp. apply Qp_min_glb1_lt; auto.
      * apply Qp_min_glb1_lt; auto.
        ** apply Qp_min_glb1_lt; auto.
        ** apply Qp_lt_add_l.
      * apply Qp_lt_add_l.
  }
  iDestruct (pri_inv_tok_global_le_acc _ _ _ mj_wp with "[] Hg") as "(Hg_inv&Hg_inv_clo)".
  { iPureIntro; split; auto.
    rewrite /mj_wp.
    etransitivity; first eapply Qp_le_min_l.
    etransitivity; first eapply Qp_le_min_l.
    apply Qp_le_min_r.
  }

  iDestruct (pri_inv_tok_join with "[$Hitok] [$]") as "Hitok".
  iDestruct (pri_inv_tok_le_acc mj_wp with "Hitok") as "(Hitok_wp&Hitok_inv_clo)".
  { rewrite /mj_wp.
    etransitivity; first eapply Qp_le_min_l.
    apply Qp_le_min_r. }


  iMod (pri_inv_tok_disable_reenable with "[$]") as "(Hg&Hreenable)".
  iSpecialize ("Hwp" $! mj_wp).
  iEval (rewrite wpc0_unfold) in "Hwp".
  iDestruct "Hwp" as "(Hwp&_)".
  iMod ("Hclo'").
  rewrite Hnval.
  replace (⊤ ∖ D ∖ E2) with (⊤ ∖ (E2 ∪ D)) by set_solver.
  iMod ("Hwp" with "[$] [$] [$]") as "Hwp".
  simpl. iMod "Hwp". iModIntro. iNext. iMod "Hwp". iModIntro.
  iApply (step_fupd2N_wand with "Hwp"). iIntros "(%Hred&Hwp)".
  iSplit. { eauto. }
  iIntros (e2 σ2 g2 efs Hstep). iMod ("Hwp" with "[//]") as "($&Hg&H&Hefs&HNC)".
  iMod (later_tok_incr with "[$]") as "(Hg&Hltok)".

  destruct (to_val e2) eqn:Heq_val.
  {
    iEval (rewrite wpc0_unfold /wpc_pre) in "H".
    iDestruct "H" as "(H&_)".
    rewrite Heq_val.
    iMod ("H" with "[$] [$]") as "H".
    iDestruct "H" as "(Hv&Hg&HNC)".
    iMod ("Hv" with "[$]
    iDestruct "Hv" as (Qnew) "(HQnew&Hwand_new&Hpost)".
    iMod (saved_prop_alloc Qnew) as (γprop_stored') "#Hsaved1''".
    iMod (saved_prop_alloc True%I) as (γprop_remainder') "#Hsaved2''".
    iMod (own_update_2 _ _ _ (● Excl' (γprop_stored', γprop_remainder') ⋅
                              ◯ Excl' (γprop_stored', γprop_remainder'))
            with "Hown' Hown") as "[Hown' Hown]".
    { by apply auth_update, option_local_update, exclusive_local_update. }
    iMod (own_update_2 _ _ _ (● Excl' idle ⋅ ◯ Excl' idle)
            with "Hstatus' Hownstat") as "[Hstatus' Hownstat]".
    { by apply auth_update, option_local_update, exclusive_local_update. }
    iMod ("Hreenable" with "[$Hg //]") as "(Hitok&Hg)".
    iDestruct ("Hitok_inv_clo" with "[$]") as "Hitok".
    iDestruct (pri_inv_tok_split with "[$Hitok]") as "(Hitok_u&Hitok_ishare)".
    iMod ("Hclo" with "[Hown' Hstatus' HQnew Hwand_new Hitok_ishare]").
    { iNext.
      iEval (rewrite staged_inv_inner_unfold).
      iExists _, _, _, _, _. iFrame "∗ #".
      iLeft. iSplit; first by iFrame "∗".
      iIntros. iMod ("Hwand_new" with "[$] [$]") as "$"; eauto.
    }
    iDestruct ("Hg_inv_clo" with "Hg") as "Hg".
    iMod (global_state_interp_le with "Hg") as "$".
    { apply lt_le_S, step_count_next_mono. lia. }
    iModIntro. iFrame.
    iSplitR "Hefs".
    - iEval (rewrite wpc0_unfold /wpc_pre).
      rewrite Heq_val.
      iSpecialize ("Hpost" with "[-]").
      {
        iExists _, _, _, _, _, _. iFrame "∗".
        iFrame "Hsaved1''".
        iFrame "Hsaved2''".
        iExists _, _. iFrame "#". iPureIntro. auto.
      }
      iSplit.
      * iIntros. iModIntro. iFrame. iDestruct "Hpost" as "(_&$)".
      * iIntros. iApply step_fupd2N_inner_later; auto. iModIntro. iFrame. iDestruct "Hpost" as "($&_)".
    - iApply (big_sepL_mono with "Hefs").
      iIntros. iApply (wpc0_mj_le); last by iFrame.
      split; auto.
      etransitivity; first eapply Qp_le_min_l.
      etransitivity; first eapply Qp_le_min_l.
      eapply Qp_le_min_r.
  }

  iFrame "HNC".
  iMod (saved_prop_alloc
          (wpc0 NotStuck k mj_wp ⊤ e2
            (λ v : val Λ, ∃ Qnew : iPropI Σ, Qnew ∗ (Qnew -∗ C ==∗ P) ∗ (staged_value ⊤ Qnew P -∗ Φc ∧ Φ v))
            (Φc ∗ P))%I) as (γprop_stored') "#Hsaved1''".
  iMod (saved_prop_alloc Φc) as (γprop_remainder') "#Hsaved2''".
  iMod (own_update_2 _ _ _ (● Excl' (γprop_stored', γprop_remainder') ⋅
                            ◯ Excl' (γprop_stored', γprop_remainder'))
          with "Hown' Hown") as "[Hown' Hown]".
  { by apply auth_update, option_local_update, exclusive_local_update. }
  iMod (own_update_2 _ _ _ (● Excl' (inuse mj_wp mj_ushare) ⋅ ◯ Excl' (inuse mj_wp mj_ushare))
          with "Hstatus' Hownstat") as "[Hstatus' Hownstat]".
  { by apply auth_update, option_local_update, exclusive_local_update. }
  iMod ("Hreenable" with "[$Hg //]") as "(Hitok&Hg)".
  iDestruct ("Hitok_inv_clo" with "[$]") as "Hitok".
  iDestruct (pri_inv_tok_split with "[$Hitok]") as "(Hitok&Hitok_ishare)".
  iEval (rewrite -Heq_mj) in "Hitok".
  iDestruct (pri_inv_tok_split with "[$Hitok]") as "(Hitok_ukeep&Hitok_ushare)".
  iMod ("Hclo" with "[Hown' Hstatus' H Hitok_ishare Hitok_ushare]").
  { iNext.
    iEval (rewrite staged_inv_inner_unfold).
    iExists _, _, _, _, _. iFrame "∗ #".
    iLeft.
    iSplit.
    { iPureIntro. split_and!; auto.
      - rewrite /mj_wp. apply Qp_le_min_r.
      - rewrite /mj_wp.
        etransitivity; first eapply Qp_le_min_l.
        etransitivity; first eapply Qp_le_min_l.
        eapply Qp_le_min_l.
    }
    iFrame.
    iModIntro.
    iIntros "Hwpc".
    iEval (rewrite wpc0_unfold) in "Hwpc". iDestruct "Hwpc" as "(_&Hwpc)".
    rewrite /wpc_crash_modality.
    iIntros (????) "Hg HC".
    iSpecialize ("Hwpc" with "[$] [$]").
    iApply (step_fupd2N_inner_wand with "Hwpc"); auto.
  }
  iDestruct ("Hg_inv_clo" with "Hg") as "Hg".
  iMod (global_state_interp_le with "Hg") as "$".
  { apply lt_le_S, step_count_next_mono; lia. }
  iModIntro. iSplitR "Hefs"; last first.
  { iApply (big_sepL_mono with "Hefs").
    iIntros. iApply (wpc0_mj_le); last by iFrame.
    split; auto.
      - rewrite /mj_wp.
        etransitivity; first eapply Qp_le_min_l.
        etransitivity; first eapply Qp_le_min_l.
        eapply Qp_le_min_r.
  }
  iAssert (staged_value_inuse k e2 ⊤ ⊤ mj mj_wp mj_ukeep Φ Φc P) with "[-]" as "Hsv".
  {
    iExists _, _, mj_ishare, _, _, _, _, _. iExists _. iFrame "∗".
    iSplit; first eauto.
    iFrame "Hsaved1'' Hsaved2''".
    iSplit; first eauto.
    iSplit; first eauto.
    iSplit; first eauto.
    iSplit.
    { iPureIntro. rewrite /mj_wp.
      etransitivity; first eapply Qp_le_min_l.
      etransitivity; first eapply Qp_le_min_l.
      eapply Qp_le_min_r. }
    iSplit.
    { iPureIntro. rewrite /mj_wp.
      etransitivity; first eapply Qp_le_min_l.
      eapply Qp_le_min_r. }
    iSplit; first eauto.
    iExact "Hinv".
  }
  iApply (wpc_staged_inv_aux with "[$]").

Lemma wpc_staged_inv_use_post s k E1 e Φ Φc Qs P :
  to_val e = None →
  staged_value ⊤ Qs P ∗
  WPC e @ s; k; E1 {{λ v, Qs -∗ |NC={E1,E1}=> ∃ Qnew, Qnew ∗ (Qnew -∗ C ==∗ P) ∗ (staged_value ⊤ Qnew P -∗ Φ v)}}
                                 {{ Φc }}
  ⊢ WPC e @ s; k; E1 {{ Φ }} {{ Φc }}.
Proof.
  iIntros (Hnv) "(Hval&Hs)".
  iDestruct (wpc_staged_inv_use_post' s k E1 e (λ _, True%I) Φ Φc Qs P with "[$Hval Hs]") as "H"; auto.
  { iApply (wpc_strong_mono with "Hs"); auto. iSplit; last eauto.
    iIntros (v) "H". iModIntro. 
    iIntros "(HQs&_)". iApply "H". eauto. }
  iApply (wpc_mono with "H"); eauto.
  iIntros (?) "H". iApply "H"; eauto.
Qed.
Qed.





Lemma staged_inv_wpc_nval_helper E P Qs R :
  staged_value E Qs P -∗
  wpc_nval E (Qs -∗ (∃ Qs', □ (Qs' -∗ P) ∗ Qs' ∗ (staged_value ⊤ Qs' P -∗ R))) -∗
  wpc_nval E R.
Proof.
  iIntros "Hstaged Hwand".
  rewrite /wpc_nval.
  iIntros (E' e s k Φ Φc Hnval Hsub) "Hwp".
  iDestruct "Hstaged" as (??????) "(Hown&Hownstat&#Hsaved1&#Hsaved2&Hltok&Hitok&Hinv)".
  iDestruct "Hinv" as (mj_wp_init mj_ishare Hlt) "#Hinv".
  rewrite /staged_inv.
  rewrite wpc_eq /wpc_def. iIntros (mj).

  iEval (rewrite wpc0_unfold).
  rewrite /wpc_pre. iSplit; last first.
  {
    iSpecialize ("Hwp" $! mj). rewrite wpc0_unfold /wpc_pre.
    iDestruct "Hwp" as "(_&Hwp)".
    iIntros (g1 ns D' κs) "Hg #HC".
    iSpecialize ("Hwp" with "[$] [$]").
    iApply (step_fupd2N_inner_wand with "Hwp"); auto.
  }
  rewrite Hnval.
  iIntros (q σ1 g1 ns D κ κs nt) "Hσ Hg HNC".
  iDestruct (pri_inv_tok_disj_inv_half with "[$]") as %Hdisj.
  iMod (pri_inv_acc with "[$]") as "(Hinner&Hclo)".
  { set_solver. }
  iEval (rewrite staged_inv_inner_unfold) in "Hinner".
  iDestruct "Hinner" as (?????) "(>Hown'&#Hsaved1'&#Hsaved2'&>Hstatus'&>Hitok_ishare&Hinner)".
  iDestruct (own_valid_2 with "Hown' Hown") as "#H".
  iDestruct "H" as %[Heq%Excl_included%leibniz_equiv _]%auth_both_valid_discrete.
  iDestruct (own_valid_2 with "Hstatus' Hownstat") as "#Heq_status".
  iDestruct "Heq_status" as %[Heq_status%Excl_included%leibniz_equiv _]%auth_both_valid_discrete.
  inversion Heq; subst.
  iMod (later_tok_decr with "[$]") as (ns' Hlt') "Hg".
  iMod (fupd2_mask_subseteq ∅ ∅) as "Hclo'"; try set_solver+.
  iModIntro. simpl. iModIntro. iNext. iModIntro. iApply (step_fupd2N_le (S (S (num_laters_per_step ns')))).
  { etransitivity; last eapply (num_laters_per_step_exp ns'); lia. }
  simpl.
  iDestruct (saved_prop_agree with "Hsaved1 Hsaved1'") as "Hequiv1".
  iDestruct (saved_prop_agree with "Hsaved2 Hsaved2'") as "Hequiv2".
  iModIntro. iModIntro. iModIntro.
  iDestruct "Hinner" as "[(HPs&_)|Hfin]"; last first.
  { (* Impossible, since we have NC token. *)
    iDestruct "Hfin" as "(_&HC&_)". iDestruct (NC_C with "[$] [$]") as %[]. }
  iRewrite -"Hequiv1" in "HPs".
  iMod "Hclo'".
  iSpecialize ("Hwand" with "[$]").
  rewrite ncfupd_eq /ncfupd_def. iSpecialize ("Hwand" with "[$]").
  iPoseProof (fupd_fupd2 with "Hwand") as "Hwand".
  iMod (fupd2_mask_mono with "Hwand") as "((#Hwand&HQs'&HR)&HNC)"; eauto.
 
  iSpecialize ("Hwp" $! mj). rewrite wpc0_unfold /wpc_pre.
  rewrite Hnval. iDestruct "Hwp" as "(Hwp&_)".
  iMod (saved_prop_alloc Qs') as (γprop_stored') "#Hsaved1''".
  iMod (saved_prop_alloc True%I) as (γprop_remainder') "#Hsaved2''".
  iMod (own_update_2 _ _ _ (● Excl' (γprop_stored', γprop_remainder') ⋅
                              ◯ Excl' (γprop_stored', γprop_remainder'))
              with "Hown' Hown") as "[Hown' Hown]".
  { by apply auth_update, option_local_update, exclusive_local_update. }
  iMod ("Hclo" with "[Hown' Hstatus' HQs' Hitok_ishare]").
  { iNext.
    iEval (rewrite staged_inv_inner_unfold).
    iExists _, _, _, _, _. iFrame "∗ #".
    iLeft.
    iSplit; eauto.
    { iIntros. iDestruct ("Hwand" with "[$]") as "$". eauto. }
  }
  iMod ("Hwp" with "[$] [$] [$]") as "H".
  iApply (step_fupd2N_wand with "H").
  iIntros "($&H)". 
  iIntros.
  iMod ("H" with "[//]") as "($&Hg&Hwpc0&$)".
  iMod (later_tok_incr with "[$]") as "(Hg&Hltok)".
  iMod (global_state_interp_le with "Hg") as "$".
  { apply lt_le_S, step_count_next_mono; lia. }
  iModIntro.
  iApply (wpc0_strong_mono with "Hwpc0"); auto.
  iSplit.
  { iIntros (?) "H". iDestruct ("H" with "[-]") as "H".
    { iFrame. iExists _, _, _, _, _, _. iFrame "# ∗".
      iExists _, _. iFrame "#". eauto. }
    iFrame. eauto. }
  eauto.
Qed.





Lemma staged_inv_wpc_nval E P Qs R :
  staged_value E Qs P -∗
  wpc_nval E (Qs -∗ (∃ Qs', □ (Qs' -∗ P) ∗ Qs' ∗ (staged_value ⊤ Qs' P -∗ R))) -∗
  wpc_nval E R.
Proof.
  iIntros "Hstaged Hwand".
  rewrite /wpc_nval.
  iIntros (E' e s k Φ Φc Hnval Hsub) "Hwp".
  iDestruct "Hstaged" as (??????) "(Hown&Hownstat&#Hsaved1&#Hsaved2&Hltok&Hitok&Hinv)".
  iDestruct "Hinv" as (mj_wp_init mj_ishare Hlt) "#Hinv".
  rewrite /staged_inv.
  rewrite wpc_eq /wpc_def. iIntros (mj).

  iEval (rewrite wpc0_unfold).
  rewrite /wpc_pre. iSplit; last first.
  {
    iSpecialize ("Hwp" $! mj). rewrite wpc0_unfold /wpc_pre.
    iDestruct "Hwp" as "(_&Hwp)".
    iIntros (g1 ns D' κs) "Hg #HC".
    iSpecialize ("Hwp" with "[$] [$]").
    iApply (step_fupd2N_inner_wand with "Hwp"); auto.
  }
  rewrite Hnval.
  iIntros (q σ1 g1 ns D κ κs nt) "Hσ Hg HNC".
  iDestruct (pri_inv_tok_disj_inv_half with "[$]") as %Hdisj.
  iMod (pri_inv_acc with "[$]") as "(Hinner&Hclo)".
  { set_solver. }
  iEval (rewrite staged_inv_inner_unfold) in "Hinner".
  iDestruct "Hinner" as (?????) "(>Hown'&#Hsaved1'&#Hsaved2'&>Hstatus'&>Hitok_ishare&Hinner)".
  iDestruct (own_valid_2 with "Hown' Hown") as "#H".
  iDestruct "H" as %[Heq%Excl_included%leibniz_equiv _]%auth_both_valid_discrete.
  iDestruct (own_valid_2 with "Hstatus' Hownstat") as "#Heq_status".
  iDestruct "Heq_status" as %[Heq_status%Excl_included%leibniz_equiv _]%auth_both_valid_discrete.
  inversion Heq; subst.
  iMod (later_tok_decr with "[$]") as (ns' Hlt') "Hg".
  iMod (fupd2_mask_subseteq ∅ ∅) as "Hclo'"; try set_solver+.
  iModIntro. simpl. iModIntro. iNext. iModIntro. iApply (step_fupd2N_le (S (S (num_laters_per_step ns')))).
  { etransitivity; last eapply (num_laters_per_step_exp ns'); lia. }
  simpl.
  iDestruct (saved_prop_agree with "Hsaved1 Hsaved1'") as "Hequiv1".
  iDestruct (saved_prop_agree with "Hsaved2 Hsaved2'") as "Hequiv2".
  iModIntro. iModIntro. iModIntro.
  iDestruct "Hinner" as "[(HPs&_)|Hfin]"; last first.
  { (* Impossible, since we have NC token. *)
    iDestruct "Hfin" as "(_&HC&_)". iDestruct (NC_C with "[$] [$]") as %[]. }
  iRewrite -"Hequiv1" in "HPs".
  iMod "Hclo'".
  iSpecialize ("Hwand" with "[$]").
  rewrite ncfupd_eq /ncfupd_def. iSpecialize ("Hwand" with "[$]").
  iPoseProof (fupd_fupd2 with "Hwand") as "Hwand".
  iMod (fupd2_mask_mono with "Hwand") as "((#Hwand&HQs'&HR)&HNC)"; eauto.
 
  iSpecialize ("Hwp" $! mj). rewrite wpc0_unfold /wpc_pre.
  rewrite Hnval. iDestruct "Hwp" as "(Hwp&_)".
  iMod (saved_prop_alloc Qs') as (γprop_stored') "#Hsaved1''".
  iMod (saved_prop_alloc True%I) as (γprop_remainder') "#Hsaved2''".
  iMod (own_update_2 _ _ _ (● Excl' (γprop_stored', γprop_remainder') ⋅
                              ◯ Excl' (γprop_stored', γprop_remainder'))
              with "Hown' Hown") as "[Hown' Hown]".
  { by apply auth_update, option_local_update, exclusive_local_update. }
  iMod ("Hclo" with "[Hown' Hstatus' HQs' Hitok_ishare]").
  { iNext.
    iEval (rewrite staged_inv_inner_unfold).
    iExists _, _, _, _, _. iFrame "∗ #".
    iLeft.
    iSplit; eauto.
    { iIntros. iDestruct ("Hwand" with "[$]") as "$". eauto. }
  }
  iMod ("Hwp" with "[$] [$] [$]") as "H".
  iApply (step_fupd2N_wand with "H").
  iIntros "($&H)". 
  iIntros.
  iMod ("H" with "[//]") as "($&Hg&Hwpc0&$)".
  iMod (later_tok_incr with "[$]") as "(Hg&Hltok)".
  iMod (global_state_interp_le with "Hg") as "$".
  { apply lt_le_S, step_count_next_mono; lia. }
  iModIntro.
  iApply (wpc0_strong_mono with "Hwpc0"); auto.
  iSplit.
  { iIntros (?) "H". iDestruct ("H" with "[-]") as "H".
    { iFrame. iExists _, _, _, _, _, _. iFrame "# ∗".
      iExists _, _. iFrame "#". eauto. }
    iFrame. eauto. }
  eauto.
Qed.
*)

Lemma staged_inv_wpc_nval E P Qs Qs' R :
  staged_value ⊤ Qs P -∗
  ▷ (Qs -∗ |NC={E}=> □ (Qs' -∗ P) ∗ Qs' ∗ R) -∗
  wpc_nval E (R ∗ staged_value ⊤ Qs' P).
Proof.
  iIntros "Hval Hwand".
  rewrite /wpc_nval.
  iIntros (E' e s k Φ Φc Hnval Hsub) "Hwp".
  iApply (wpc_staged_inv_use_post); auto.
  iFrame "Hval".
  iApply (wpc_step_strong_mono with "[$]"); auto.
  iSplit; last eauto.
  iNext. iIntros (v) "HΦ".
  iModIntro. iIntros "HQs". iExists Qs'.
  iApply (ncfupd_mask_mono E); auto.
  iMod ("Hwand" with "[$]") as "(#H1&H2&H3)".
  iModIntro. iFrame. iSplitL "".
  { iIntros. iApply "H1". eauto. }
  { iIntros. iApply "HΦ". iFrame. }
Qed.

Lemma wpc_staged_inv_use_post_sepM `{Countable A} {B} s k E1 e Φ Φc Qs Qs' (P : A → B → iProp Σ) R m:
  to_val e = None →
  ([∗ map] i ↦ x ∈ m, staged_value ⊤ (Qs i x) (P i x)) ∗
  WPC e @ s; k; E1 {{λ v, ([∗ map] i ↦ x ∈ m, Qs i x) -∗ |NC={E1,E1}=>
                         (* Must reprove Qs but to re-establish staged value *)
                         (□ ([∗ map] i ↦ x ∈ m, ((Qs' i x) -∗ (P i x))) ∗
                         ([∗ map] i ↦ x ∈ m, Qs' i x) ∗ R ∗
                         (([∗ map] i ↦ x ∈ m, staged_value ⊤ (Qs' i x) (P i x)) -∗ R -∗ Φ v))}}
                      {{ Φc }}
  ⊢ WPC e @ s; k; E1 {{ Φ }} {{ Φc }}.
Proof.
  revert R.
  induction m as [|i x m] using map_ind.
  {
    iIntros (?) "_ Hrestore".
    iDestruct "Hrestore" as "(_&H)".
    iApply (wpc_strong_mono with "H"); auto. iSplit; last eauto.
    iIntros (v) "H".
    iDestruct ("H" with "[]") as "> (_&_&HR)";
      first by (iApply big_sepM_empty; trivial).
    iModIntro. rewrite big_sepM_empty; trivial. iDestruct "HR" as "(HR&H)". iApply "H"; by iFrame.
  }
  iIntros (R Hnval) "(Hcrash_invs&Hrestores)".
  iDestruct (big_sepM_insert with "Hcrash_invs")
    as "[Hcrash_inv Hcrash_invs]";
    first by assumption.
  iApply (IHm (staged_value ⊤ (Qs' i x) (P i x) ∗ R)%I with "[$Hcrash_invs Hrestores Hcrash_inv]"); first auto.
  iApply (wpc_staged_inv_use_post' _ _ _ _ (λ v, ([∗ map] i↦ x∈ m, Qs i x))%I with "[-]"); auto.
  iFrame "Hcrash_inv".
  iApply (wpc_strong_mono with "Hrestores"); eauto.
  iSplit; last eauto.
  iIntros (v) "H". iModIntro.
  iIntros "(HQs&Hrest)".
  iMod ("H" with "[Hrest HQs]") as "(#Hstatuses&HQ's&HR)".
  {
    iApply big_sepM_insert; first by assumption.
    iFrame.
  }
  iModIntro.
  iExists (Qs' i x).
  iDestruct (big_sepM_insert with "HQ's")
    as "[HQ' HQ's]";
    first by assumption.
  iDestruct (big_sepM_insert with "Hstatuses")
    as "[Hstatus Hstatuses']";
    first by assumption.
  iFrame "∗".
  iSplitL "".
  { iIntros. iApply "Hstatus"; eauto. }
  iIntros "Hval1".
  iModIntro.
  iDestruct "HR" as "(HR&HΦ)".
  iFrame "Hval1 Hstatuses' HR".
  iIntros "H1 (H2&HR)". iApply ("HΦ" with "[H1 H2] [$]").
  iApply big_sepM_insert; first by assumption.
  iFrame.
Qed.

Lemma staged_inv_wpc_nval_sepM `{Countable A} {B} E (P: A → B → iProp Σ) Q Q' R m:
  ([∗ map] i ↦ x ∈ m, staged_value ⊤ (Q i x) (P i x)) -∗
  (([∗ map] i ↦ x ∈ m, Q i x) -∗
   |NC={E}=> □ ([∗ map] i ↦ x ∈ m, ((Q' i x) -∗ (P i x))) ∗
              ([∗ map] i ↦ x ∈ m, (Q' i x)) ∗ R) -∗
  wpc_nval E (R ∗ ([∗ map] i ↦ x ∈ m, staged_value ⊤ (Q' i x) (P i x))).
Proof.
  iIntros "Hval Hwand".
  rewrite /wpc_nval.
  iIntros (E' e s k Φ Φc Hnval Hsub) "Hwp".
  iApply (wpc_staged_inv_use_post_sepM _ _ _ _ _  _ _ Q' P R); auto.
  iFrame "Hval".
  iApply (wpc_step_strong_mono with "[$]"); auto.
  iSplit; last eauto.
  iNext. iIntros (v) "HΦ".
  iModIntro. iIntros "HQs".
  iApply (ncfupd_mask_mono E); auto.
  iMod ("Hwand" with "[$]") as "(#H1&H2&H3)".
  iModIntro. iFrame. iSplitL "".
  { iIntros. iApply "H1". }
  { iIntros. iApply "HΦ". iFrame. }
Qed.


(*
Lemma staged_inv_wpc_nval E P Qs Qs' R :
  staged_value ⊤ Qs P -∗
  ▷ (Qs -∗ |NC={E}=> □ (Qs' -∗ P) ∗ Qs' ∗ R) -∗
  wpc_nval E (R ∗ staged_value ⊤ Qs' P).
Proof.
  iIntros "Hstaged Hwand".
  rewrite /wpc_nval.
  iIntros (E' e s k Φ Φc Hnval Hsub) "Hwp".
  iDestruct "Hstaged" as (??????) "(Hown&Hownstat&#Hsaved1&#Hsaved2&Hltok&Hitok&Hinv)".
  iDestruct "Hinv" as (mj_wp_init mj_ishare Hlt) "#Hinv".
  rewrite /staged_inv.
  rewrite wpc_eq /wpc_def. iIntros (mj).

  iEval (rewrite wpc0_unfold).
  rewrite /wpc_pre. iSplit; last first.
  {
    iSpecialize ("Hwp" $! mj). rewrite wpc0_unfold /wpc_pre.
    iDestruct "Hwp" as "(_&Hwp)".
    iIntros (g1 ns D' κs) "Hg #HC".
    iSpecialize ("Hwp" with "[$] [$]").
    iApply (step_fupd2N_inner_wand with "Hwp"); auto.
  }
  rewrite Hnval.
  iIntros (q σ1 g1 ns D κ κs nt) "Hσ Hg HNC".
  iDestruct (pri_inv_tok_disj_inv_half with "[$]") as %Hdisj.
  iMod (pri_inv_acc with "[$]") as "(Hinner&Hclo)".
  { set_solver. }
  iEval (rewrite staged_inv_inner_unfold) in "Hinner".
  iDestruct "Hinner" as (?????) "(>Hown'&#Hsaved1'&#Hsaved2'&>Hstatus'&>Hitok_ishare&Hinner)".
  iDestruct (own_valid_2 with "Hown' Hown") as "#H".
  iDestruct "H" as %[Heq%Excl_included%leibniz_equiv _]%auth_both_valid_discrete.
  iDestruct (own_valid_2 with "Hstatus' Hownstat") as "#Heq_status".
  iDestruct "Heq_status" as %[Heq_status%Excl_included%leibniz_equiv _]%auth_both_valid_discrete.
  inversion Heq; subst.
  iMod (later_tok_decr with "[$]") as (ns' Hlt') "Hg".
  iMod (fupd2_mask_subseteq ∅ ∅) as "Hclo'"; try set_solver+.
  iModIntro. simpl. iModIntro. iNext. iModIntro. iApply (step_fupd2N_le (S (S (num_laters_per_step ns')))).
  { etransitivity; last eapply (num_laters_per_step_exp ns'); lia. }
  simpl.
  iDestruct (saved_prop_agree with "Hsaved1 Hsaved1'") as "Hequiv1".
  iDestruct (saved_prop_agree with "Hsaved2 Hsaved2'") as "Hequiv2".
  iModIntro. iModIntro. iModIntro.
  iDestruct "Hinner" as "[(HPs&_)|Hfin]"; last first.
  { (* Impossible, since we have NC token. *)
    iDestruct "Hfin" as "(_&HC&_)". iDestruct (NC_C with "[$] [$]") as %[]. }
  iRewrite -"Hequiv1" in "HPs".
  iMod "Hclo'".
  iSpecialize ("Hwand" with "[$]").
  rewrite ncfupd_eq /ncfupd_def. iSpecialize ("Hwand" with "[$]").
  iPoseProof (fupd_fupd2 with "Hwand") as "Hwand".
  iMod (fupd2_mask_mono with "Hwand") as "((#Hwand&HQs'&HR)&HNC)"; eauto.
 
  iSpecialize ("Hwp" $! mj). rewrite wpc0_unfold /wpc_pre.
  rewrite Hnval. iDestruct "Hwp" as "(Hwp&_)".
  iMod (saved_prop_alloc Qs') as (γprop_stored') "#Hsaved1''".
  iMod (saved_prop_alloc True%I) as (γprop_remainder') "#Hsaved2''".
  iMod (own_update_2 _ _ _ (● Excl' (γprop_stored', γprop_remainder') ⋅
                              ◯ Excl' (γprop_stored', γprop_remainder'))
              with "Hown' Hown") as "[Hown' Hown]".
  { by apply auth_update, option_local_update, exclusive_local_update. }
  iMod ("Hclo" with "[Hown' Hstatus' HQs' Hitok_ishare]").
  { iNext.
    iEval (rewrite staged_inv_inner_unfold).
    iExists _, _, _, _, _. iFrame "∗ #".
    iLeft.
    iSplit; eauto.
    { iIntros. iDestruct ("Hwand" with "[$]") as "$". eauto. }
  }
  iMod ("Hwp" with "[$] [$] [$]") as "H".
  iApply (step_fupd2N_wand with "H").
  iIntros "($&H)". 
  iIntros.
  iMod ("H" with "[//]") as "($&Hg&Hwpc0&$)".
  iMod (later_tok_incr with "[$]") as "(Hg&Hltok)".
  iMod (global_state_interp_le with "Hg") as "$".
  { apply lt_le_S, step_count_next_mono; lia. }
  iModIntro.
  iApply (wpc0_strong_mono with "Hwpc0"); auto.
  iSplit.
  { iIntros (?) "H". iDestruct ("H" with "[-]") as "H".
    { iFrame. iExists _, _, _, _, _, _. iFrame "# ∗".
      iExists _, _. iFrame "#". eauto. }
    iFrame. eauto. }
  eauto.
Qed.
*)

End def.
