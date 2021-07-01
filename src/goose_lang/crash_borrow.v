From Perennial.program_logic Require Import staged_invariant.
From Perennial.goose_lang Require Import crash_modality lifting wpr_lifting.


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
Qed.

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
  (staged_value_idle ⊤ Ps True%I Pc ∗ later_tok ∗ later_tok ∗ later_tok).

End crash_borrow_def.
