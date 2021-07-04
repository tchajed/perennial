From iris.algebra Require Import gmap auth agree gset coPset excl csum.
From Perennial.program_logic Require Import staged_invariant.
From Perennial.goose_lang Require Import crash_modality lifting wpr_lifting.
From Perennial.goose_lang Require Import wpc_proofmode.
From Perennial.base_logic.lib Require Import saved_prop.
From Perennial.Helpers Require Import Qextra.


Section crash_borrow_def.
Context `{ext:ffi_syntax}.
Context `{ffi_sem: ffi_semantics}.
Context `{!ffi_interp ffi}.

Context `{!heapGS Σ}.
Context `{!stagedG Σ}.

Global Instance later_tokG_heap : later_tokG (heapG_irisG).
Proof.
  refine {| later_tok := cred_frag 1 |}.
  - iIntros (g ns mj D κ) "(Hg&Hfrag)".
    iDestruct "Hg" as "(Hffi&Hinv&Hcred&Htok)".
    iMod (cred_interp_decr with "[$]") as (ns' ->) "(Hauth&Hfrag)".
    iExists ns'. iModIntro; iSplit; first done.
    iFrame. iDestruct "Hauth" as "($&_)".
  - iIntros (g ns mj D κ) "Hg".
    iDestruct "Hg" as "(Hffi&Hinv&(Hcred&H0)&Htok)".
    iMod (cred_interp_incr with "[$]") as "(Hauth&Hfrag)".
    iFrame. eauto.
  - intros n1 n2 Hlt => /=.
    transitivity (3 ^ (1 + (n1 + 1)))%nat; last first.
    { apply Nat.pow_le_mono_r; lia. }
    rewrite [a in _ _ a]Nat.pow_add_r.
    rewrite [a in _ _ a]/=.
    transitivity (2 + 3^(n1 + 1) + 3^(n1 + 1))%nat; first by lia.
    rewrite plus_0_r -plus_assoc.
    apply plus_le_compat_r.
    clear.
    transitivity (2 ^ 1)%nat; first by auto.
    etransitivity; last eapply (Nat.pow_le_mono_r _ 1); try (simpl; lia).
  - intros n1 n2 Hlt => /=. lia.
  - intros n1 n2 Hlt => /=. lia.
Defined.

Lemma ownfCP_inf_le1 γ (q : Qp) (E : coPset) :
  ownfCP_inf γ q E -∗ ⌜ q ≤ 1 ⌝%Qp.
Proof.
  iDestruct 1 as "(%Hinf&Hown)".
  iDestruct (own_valid with "Hown") as %Hval.
  iPureIntro.
  destruct Hval as (Hval&Hdom).
  specialize (Hval (coPpick E)).
  rewrite /= decide_True in Hval => //=.
  apply coPpick_elem_of.
  intros ?. apply set_not_infinite_finite in Hinf; eauto.
Qed.

Lemma ownfCP_disj1 γ q1 D E :
  ownfCP γ q1 D ∗ ownfCP_inf γ 1 E -∗ ⌜ E ## D ⌝.
Proof.
  iIntros. iDestruct (ownfCP_disj with "[$]") as %Hcases. iPureIntro.
  destruct Hcases as [Hdisj|Hbad]; auto. exfalso.
  move: Hbad. rewrite frac_valid Qp_le_ngt => Hnlt. apply Hnlt.
  apply Qp_lt_add_r.
Qed.

Lemma ownfCP_disj_gt2 γ q D E :
  (/2 < q)%Qp →
  ownfCP γ q D ∗ ownfCP_inf γ q E -∗ ⌜ E ## D ⌝.
Proof.
  iIntros. iDestruct (ownfCP_disj with "[$]") as %Hcases. iPureIntro.
  destruct Hcases as [Hdisj|Hbad]; auto. exfalso.
  move: Hbad. rewrite frac_valid Qp_le_ngt => Hnlt. apply Hnlt.
  rewrite -Qp_inv_half_half.
  apply Qp_add_lt_mono; auto.
Qed.

Global Instance pri_invG_heap : pri_invG (heapG_irisG).
Proof.
  refine {| pri_inv_tok := λ q E, pinv_tok_inf q E |}; rewrite /pinv_tok_inf.
  - iIntros (??) "($&?)".
  - iIntros (???) "H". by rewrite ownfCP_inf_op_plus.
  - iIntros (???). rewrite ownfCP_inf_op_plus. by iIntros "$ $".
  - iIntros (q E) "H". by iApply (ownfCP_inf_le1).
  - iIntros (?????) "Hg". iDestruct "Hg" as "(?&?&?&?&?)". eauto.
  - iIntros (??????) "%Hlt Hg". iDestruct "Hg" as "(?&?&?&%Hle2&Hp)".
    iDestruct (ownfCP_op_plus with "Hp") as "(Hp1&$)".
    iFrame. iSplit.
    { iPureIntro. split; auto. transitivity (q1 + q2)%Qp; last by naive_solver.
      apply Qp_le_add_r. }
    iIntros (???) "Hg". iDestruct "Hg" as "(?&?&?&%Hle2'&Hp)".
    iFrame. iSplit; first auto.
    iApply ownfCP_op_plus. iFrame.
  - iIntros (?????) "%Hlt (Hg&Hp')". iDestruct "Hg" as "(?&?&?&%Hle2&Hp)".
    iFrame. iDestruct "Hp'" as "(%Hinf&Hp')".
    iDestruct (ownfCP_op_plus with "[$Hp' $Hp]") as "Hp".
    iDestruct (ownfCP_inf_le1 with "[$Hp //]") as %Hle3.
    iFrame. iPureIntro.
    split; auto. transitivity q2; first naive_solver.
    apply Qp_lt_add_r.
  - iIntros (g ns q D κ) "Hg".
    iMod (ownfCP_inf_init (coPset_name credit_cr_names)) as (E) "H".
    iDestruct "Hg" as "($&$&$&$&Hp)".
    iDestruct "H" as "(%Hinf&H)".
    iExists E.
    iDestruct (ownfCP_disj1 with "[$Hp H]") as %Hdisj.
    { iFrame; eauto. }
    iFrame. eauto.
  - iIntros (E g ns q D κ) "(Hp&Hg)".
    iDestruct "Hg" as "($&$&$&%Hle&Hp')".
    iFrame "%".
    iDestruct (ownfCP_disj_gt2 with "[$Hp $Hp']") as %Hdisj; first naive_solver.
    iDestruct "Hp" as "(Hinf&Hp)".
    iModIntro. iApply ownfCP_op_union; auto.
    iFrame.
  - iIntros (E g ns q D κ) "((%Hdisj&%Hinf)&Hg)".
    iDestruct "Hg" as "($&$&$&$&Hp)".
    iDestruct (ownfCP_op_union with "Hp") as "($&$)"; auto.
  - iIntros (g ns q1 q2 D κ E) "(Hg&Hp')".
    iDestruct "Hg" as "(?&?&?&%Hle&Hp)".
    iApply (ownfCP_disj with "[$]").
Qed.

Definition crash_borrow Ps Pc : iProp Σ :=
  (□ (Ps -∗ Pc) ∗ staged_value_idle ⊤ Ps True%I Pc ∗ later_tok).

Lemma wpc_crash_borrow_init s k e Φ Φc P Pc :
  language.to_val e = None →
  P -∗
  □ (P -∗ Pc) -∗
  Φc ∧ (crash_borrow P Pc -∗ WPC e @ s; k; (⊤ ∖ (↑borrowN : coPset)) {{ Φ }} {{ Φc }}) -∗
  WPC e @ s; k; ⊤ {{ Φ }} {{ Φc ∗ Pc }}.
Proof.
  iIntros (Hnv) "HP #Hwand Hwpc".
  iApply wpc_borrow_inv.
  iIntros "#Hinv".
  rewrite wpc_unfold /wpc_pre. iIntros (mj).
  rewrite Hnv.
  iSplit; last first.
  { iIntros. iApply step_fupd2N_inner_later; eauto. iNext. iFrame.
    iDestruct "Hwpc" as "($&_)". by iApply "Hwand". }
  iIntros (q σ g1 ns D κ κs nt) "Hσ Hg HNC".
  iInv "Hinv" as ">H" "Hclo".
  rewrite /crash_borrow_ginv_number.
  iDestruct (cred_frag_split 1 _ with "H") as "(Hlt1&H)".
  iDestruct (cred_frag_split 1 _ with "H") as "(Hlt2&H)".
  iDestruct (cred_frag_split 1 _ with "H") as "(Hlt3&H)".
  iDestruct (cred_frag_split 1 _ with "H") as "(Hlt4&_)".
  iDestruct "Hwpc" as "(_&Hwpc)".

  iMod (pri_inv_tok_alloc with "[$]") as (Einv Hdisj) "(Hitok&Hg)".
  iDestruct (pri_inv_tok_global_valid with "[$]") as %(Hgt&Hle).

  (* Create the invariant *)

  iMod (saved_prop_alloc P) as (γprop) "#Hsaved".
  iMod (saved_prop_alloc True%I) as (γprop') "#Hsaved'".
  iMod (own_alloc (● (Excl' (γprop, γprop')) ⋅ ◯ (Excl' (γprop, γprop')))) as (γ) "[H1 H2]".
  { apply auth_both_valid_2; [econstructor | reflexivity]. }
  iMod (pending_alloc) as (γ') "Hpending".
  iMod (own_alloc (● (Excl' idle) ⋅ ◯ (Excl' idle))) as (γstatus) "[Hstat1 Hstat2]".
  { apply auth_both_valid_2; [econstructor | reflexivity]. }

  iDestruct (pri_inv_tok_infinite with "Hitok") as %Hinf.
  destruct (Qp_plus_inv_2_gt_1_split mj) as (mj_ikeep&mj_ishare&Heq_mj&Hinvalid); first auto.
  iEval (rewrite -Qp_inv_half_half) in "Hitok".
  iDestruct (pri_inv_tok_split with "Hitok") as "(Hitok_u&Hitok_i)".
  iEval (rewrite -Heq_mj) in "Hitok_i".
  iDestruct (pri_inv_tok_split with "Hitok_i") as "(Hitok_ikeep&Hitok_ishare)".
  iMod (pri_inv_alloc Einv _ _ (staged_inv_inner ⊤ Einv mj mj_ishare γ γ' γstatus Pc) with "[HP H1 Hitok_ishare Hstat1]") as
      "#Hpri_inv"; auto.
  { iNext. rewrite staged_inv_inner_unfold. iExists _, _, idle, P, True%I. iFrame "∗ #".
    iLeft. iFrame. iModIntro. iIntros "HP HC". iModIntro. iDestruct ("Hwand" with "[$]") as "$"; eauto.
  }

  iAssert (crash_borrow P Pc)%I with "[Hlt1 Hlt2 H2 Hstat2 Hitok_u]"  as "Hborrow".
  {
    iFrame "# ∗".
    iExists _, _, _, _, _, _. iFrame "∗". iFrame "Hsaved Hsaved'".
    iExists _, _. iFrame "Hpri_inv". eauto.
  }

  iAssert (staged_inv_cancel ⊤ mj Pc)%I with "[Hitok_ikeep Hpending Hlt3]" as "Hcancel".
  {
    iExists _, _, _, _, _, _, _. iFrame "%". iFrame. eauto.
  }
  iSpecialize ("Hwpc" with "[$]").
  rewrite wpc_unfold /wpc_pre.
  iSpecialize ("Hwpc" $! mj). iDestruct ("Hwpc") as "(Hwpc&_)".
  rewrite Hnv.
  iMod (later_tok_decr with "[$]") as (ns' Heq) "Hg".
  iMod ("Hwpc" with "[$] [$] [$]") as "Hwpc".
  iModIntro.
  iApply (step_fupd_extra.step_fupd2N_le (S (num_laters_per_step ns')) (num_laters_per_step ns) with "[-]").
  { assert (Hlt: ns' < ns) by lia.
    apply num_laters_per_step_lt in Hlt. lia.
  }
  iApply (step_fupd2N_wand with "Hwpc").
  iIntros "($&H)".
  iIntros. iMod ("H" with "[//]") as "(Hσ&Hg&Hwp&$)".
  iFrame.
  iMod (later_tok_incrN 10 with "[$]") as "(Hg&Htoks)".
  iMod (global_state_interp_le _ ((step_count_next ns)) _ _ with "Hg") as "Hg".
  { by apply step_count_next_add. }
  iFrame.
  iMod ("Hclo" with "[Htoks]").
  { iNext.
    repeat (iDestruct "Htoks" as "(?&Htoks)").
    repeat (rewrite -(cred_frag_join (S 0)); iFrame). }
  iModIntro.
  iApply (wpc0_staged_inv_cancel with "[$]").
  { destruct (to_val e2); eauto. }
  { auto. }
  iApply (wpc0_strong_mono with "Hwp"); auto.
  { destruct (to_val e2); eauto. }
Qed.

Lemma wpc_crash_borrow_split k E e Φ Φc P Pc P1 P2 Pc1 Pc2 :
  language.to_val e = None →
  crash_borrow P Pc -∗
  (P -∗ P1 ∗ P2) -∗
  □ (P1 -∗ Pc1) -∗
  □ (P2 -∗ Pc2) -∗
  (Pc1 ∗ Pc2 -∗ Pc) -∗
  WPC e @ NotStuck; k; E {{ λ v, (crash_borrow P1 Pc1 ∗ crash_borrow P2 Pc2) -∗  (Φc ∧ Φ v) }} {{ Φc }} -∗
  WPC e @ NotStuck; k; E {{ Φ }} {{ Φc }}.
Proof.
  iIntros (Hnval) "Hborrow Hshift #Hwand1 #Hwand2 Hwandc Hwpc".
  iDestruct "Hborrow" as "(#Hwand&Hinv&Htok)".
  iApply (wpc_staged_inv_inuse); first done.
  iFrame "Hinv".
  iSplit.
  { iIntros. rewrite wpc_unfold. iDestruct ("Hwpc" $! _) as "(_&Hwpc)".
    iApply "Hwpc". }
  iIntros "HP".
  iDestruct ("Hshift" with "[$]") as "(HP1&HP2)".
  iIntros (mj Hlt).
  iApply wpc_fupd2.
  iApply (wpc_pri_inv_tok_res).
  iIntros (E1') "Hitok1".
  iApply (wpc_pri_inv_tok_res).
  iIntros (E2') "Hitok2".
  iApply (wpc_later_tok_invest with "[$]"); first done.
  rewrite wpc_eq. iIntros (mj').
  iApply (wpc0_strong_mono with "Hwpc"); auto.
  iSplit; last first.
  { iIntros "$ !>". iApply "Hwandc". iSplitL "HP1".
    - iApply "Hwand1". eauto.
    - iApply "Hwand2". eauto.
  }
  iIntros (v) "Hc !> Htok".

  (* create staged inv for first crash borrow *)
  iDestruct ("Htok") as "(Htok1&Htok)".
  iDestruct ("Htok") as "(Htok2&Htok)".
  iMod (staged_inv_create _ _ P1 Pc1 ⊤ _ mj with "[$] [$] Hitok1 [$] [$]") as "(Hval1&Hcancel1)".
  { auto. }

  (* create staged inv for second crash borrow *)
  iDestruct ("Htok") as "(Htok1&Htok)".
  iDestruct ("Htok") as "(Htok2&Htok)".
  iMod (staged_inv_create _ _ P2 Pc2 ⊤ _ mj with "[$] [$] Hitok2 [$] [$]") as "(Hval2&Hcancel2)".
  { auto. }

  iDestruct ("Htok") as "(Htok1&Htok)".
  iDestruct ("Htok") as "(Htok2&Htok)".
  iSpecialize ("Hc" with "[Htok1 Htok2 Hval1 Hval2]").
  { iFrame "# ∗". }
  iDestruct (staged_inv_cancel_wpc_crash_modality with "Hcancel1") as "Hcancel1".
  iDestruct (staged_inv_cancel_wpc_crash_modality with "Hcancel2") as "Hcancel2".

  iDestruct ("Htok") as "(Htok1&Htok)".
  iDestruct (wpc_crash_modality_combine with "[$] [$] [$]") as "Hcombined".
  iModIntro. iSplitR "Hc".
  {
    iApply (wpc_crash_modality_wand with "Hcombined").
    iIntros "(?&?) !>". iApply "Hwandc"; by iFrame.
  }
  iSplit.
  - iDestruct "Hc" as "(Hc&_)".
    iApply (wpc_crash_modality_intro). auto.
  - iDestruct "Hc" as "(_&$)".
Qed.

Lemma wpc_crash_borrow_combine k E e Φ Φc P P1 P2 Pc1 Pc2 :
  language.to_val e = None →
  crash_borrow P1 Pc1 -∗
  crash_borrow P2 Pc2 -∗
  □ (P -∗ (Pc1 ∗ Pc2)) -∗
  (P1 ∗ P2 ==∗ P) -∗
  WPC e @ NotStuck; k; E {{ λ v, (crash_borrow P (Pc1 ∗ Pc2)) -∗ (Φc ∧ Φ v) }} {{ Φc }} -∗
  WPC e @ NotStuck; k; E {{ Φ }} {{ Φc }}.
Proof.
  iIntros (Hnval) "Hborrow1 Hborrow2 #Hc Hwand Hwpc".

  iDestruct "Hborrow1" as "(#Hwand1&Hinv1&Htok1)".
  iApply (wpc_staged_inv_inuse); first done.
  iFrame "Hinv1".
  iSplit.
  { iIntros. rewrite wpc_unfold. iDestruct ("Hwpc" $! _) as "(_&Hwpc)".
    iApply "Hwpc". }
  iIntros "HP1". iIntros (mj_wp1 Hlt1).

  iDestruct "Hborrow2" as "(#Hwand2&Hinv2&Htok2)".
  iApply (wpc_staged_inv_inuse); first done.
  iFrame "Hinv2".
  iSplit.
  { iIntros. rewrite wpc_unfold. iDestruct ("Hwpc" $! _) as "(_&Hwpc)".
    iApply (wpc_crash_modality_wand with "Hwpc").
    iIntros "HΦc".
    iModIntro. iFrame. iApply "Hwand1". iFrame. }

  iIntros "HP2". iIntros (mj_wp2 Hlt2).
  iApply wpc_fupd2.
  iApply (wpc_later_tok_invest with "[$]"); first done.
  iApply (wpc_pri_inv_tok_res).
  iIntros (Enew) "Hitok_new".
  iApply (wpc_pri_inv_tok_res).
  iIntros (Esplit) "Hitok_split".
  rewrite wpc_eq. iIntros (mj').

  iApply (wpc0_strong_mono with "Hwpc"); auto.
  iSplit; last first.
  { iIntros "$ !>". iSplitL "HP1".
    - iApply "Hwand1". eauto.
    - iApply "Hwand2". eauto.
  }
  iIntros (v) "Hc' !> Htok".

  iDestruct ("Htok") as "(Htok2&Htok)".
  iMod ("Hwand" with "[$]") as "HP".
  assert (∃ mj0, /2 < mj0 ∧ mj0 < mj_wp1 `min` mj_wp2)%Qp as (mj0&Hmj0).
  { admit. }

  iMod (staged_inv_create _ _ P (Pc1 ∗ Pc2) ⊤ _ mj0 with "[$] [$] Hitok_new [$] [$]") as "(Hval&Hcancel)".
  { naive_solver. }

  iDestruct (staged_inv_cancel_wpc_crash_modality with "Hcancel") as "Hcancel".
  iDestruct ("Htok") as "(Htok1&Htok)".
  iDestruct ("Htok") as "(Htok2&Htok)".
  iDestruct (wpc_crash_modality_split _ _ _ (mj_wp1 `min` mj_wp2) with "[$] [$] [$] [$]") as "Hcancel".
  { auto. }

  iMod (fupd2_mask_subseteq ∅ ∅) as "Hclo"; try set_solver+.
  iMod "Hcancel" as "(Hcancel1&Hcancel2)".
  iMod "Hclo" as "_". iModIntro.

  iSplitL "Hcancel2".
  { iApply (wpc_crash_modality_strong_wand with "Hcancel2"); auto.
    split.
    - apply Qp_min_glb1_lt; auto.
    - apply Qp_le_min_r.
  }

  iDestruct ("Htok") as "(Htok1&Htok)".
  iSpecialize ("Hc'" with "[Hval Htok1]").
  { iFrame "Hval Htok1". eauto. }

  iSplit.
  { iApply (wpc_crash_modality_strong_wand with "Hcancel1"); auto.
    { admit. }
    { split.
      - apply Qp_min_glb1_lt; auto.
      - apply Qp_le_min_r.
    }
    iIntros "$". by iDestruct "Hc'" as "($&_)".
  }

  iSplitL "Hcancel1".
  { iApply (wpc_crash_modality_strong_wand with "Hcancel1"); auto.
    { split.
      - apply Qp_min_glb1_lt; auto.
      - apply Qp_le_min_l.
    }
  }

 iSplit.
 - iDestruct "Hc'" as "(Hc'&_)". iApply wpc_crash_modality_intro. auto.
 - iDestruct "Hc'" as "(_&$)".
Abort.

End crash_borrow_def.
