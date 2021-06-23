From iris.proofmode Require Import base tactics classes.
From Perennial.Helpers Require Import ipm.
From Perennial.base_logic Require Export invariants.
From Perennial.program_logic Require Import crash_weakestpre.
Set Default Proof Using "Type".


(* This class holds for IrisG instances with certain properties needed to show
   the existence of a token that can be spent to strip a later around a `wpc` *)
Class later_tokG {Λ Σ} (IRISG : irisGS Λ Σ) := {
  later_tok : iProp Σ;
  later_tok_timeless : Timeless later_tok;
  later_tok_decr :
    ⊢ (∀ g ns D κ, global_state_interp g ns D κ ∗ later_tok ==∗
                                   ∃ ns', ⌜ S ns' ≤ ns ⌝%nat ∗ global_state_interp g ns' D κ)%I;
  later_tok_incr :
    ⊢ (∀ g ns D κ, global_state_interp g ns D κ ==∗ global_state_interp g (S ns) D κ ∗ later_tok)%I;
  num_laters_per_step_exp:
              ∀ n1 n2, n1 < n2 → 2 + num_laters_per_step n1 + num_laters_per_step n1 ≤ num_laters_per_step n2
}.


Arguments later_tok {_ _ _ _}.

Section res.

Context `{IRISG: !irisGS Λ Σ}.
Context `{LT: !later_tokG IRISG}.
Implicit Types s : stuckness.
Implicit Types P : iProp Σ.
Implicit Types Φ : val Λ → iProp Σ.
Implicit Types Φc : iProp Σ.
Implicit Types v : val Λ.
Implicit Types e : expr Λ.

Lemma num_laters_per_step_lt : ∀ n1 n2, n1 < n2 → num_laters_per_step n1 < num_laters_per_step n2.
Proof using LT.
  intros ?? ?%num_laters_per_step_exp. lia.
Qed.

(*
Definition later_tok : iProp Σ :=
  (∀ g ns κ, global_state_interp g ns κ ==∗
             ∃ ns', ⌜ S ns' ≤ ns ⌝%nat ∗ global_state_interp g ns' κ).

Definition is_later_tok Q : iProp Σ :=
  □ (∀ g ns κ, global_state_interp g ns κ ∗ Q ==∗
             ∃ ns', ⌜ S ns' ≤ ns ⌝%nat ∗ global_state_interp g ns' κ) ∗
  □ (∀ g ns κ, global_state_interp g ns κ ==∗ global_state_interp g (S ns) κ ∗ Q).

Definition later_tok : iProp Σ :=
  ∃ Q, Q ∗ is_later_tok Q.
*)

Lemma wpc_later_tok_use s E e k Φ Φc :
  language.to_val e = None →
  later_tok -∗
  ▷ WPC e @ s; k; E {{ v, later_tok -∗ Φ v }} {{ later_tok -∗ Φc }} -∗
  WPC e @ s; k; E {{ Φ }} {{ Φc }}.
Proof.
  iIntros (Hnval) "Htok Hwp".
  rewrite ?wpc_unfold /wpc_pre.
  rewrite Hnval.
  iIntros (mj).
  iSplit.
  - iIntros (q σ1 g1 ns κ κs nt) "Hσ Hg HNC".
    iMod (later_tok_decr with "[$]") as (ns' Heq) "Hg".
    iMod (fupd2_mask_subseteq ∅ ∅) as "H"; [ set_solver+ | set_solver+ |].
    iModIntro. simpl. iModIntro. iNext. iMod "H" as "_".
    iDestruct ("Hwp" $! _) as "(Hwp&_)".
    iSpecialize ("Hwp" $! _ _ _ _ _ _ _ with "Hσ Hg HNC").
    iMod "Hwp".
    iApply (step_fupd_extra.step_fupd2N_le (S (num_laters_per_step ns')) (num_laters_per_step ns)
              with "[Hwp]").
    { assert (Hlt: ns' < ns) by lia.
      apply num_laters_per_step_lt in Hlt. lia.
    }
    iApply (step_fupd_extra.step_fupd2N_wand with "Hwp").
    iNext. iIntros "($&H)".
    iIntros. iMod ("H" with "[//]") as "(Hσ&Hg&Hwp&$)".
    iMod (later_tok_incr with "[$]") as "(Hg&Htok')".
    iFrame.
    iMod (global_state_interp_le _ (S ns) _ _ with "Hg") as "Hg".
    { lia. }
    iFrame.
    iApply (wpc0_strong_mono with "Hwp"); try reflexivity.
    iModIntro. iSplit.
    * iIntros (?) "H". iModIntro. iApply "H"; eauto.
    * iIntros "H". iModIntro. iApply "H"; eauto.
  - iIntros (g ns κs) "Hg HC".
    iMod (later_tok_decr with "[$]") as (ns' Heq) "Hg".
    iMod (fupd2_mask_subseteq ∅ ∅) as "H"; [ set_solver+ | set_solver+ |].
    iApply (step_fupd_extra.step_fupd2N_le (S (num_laters_per_step ns')) (num_laters_per_step ns)).
    { assert (Hlt: ns' < ns) by lia.
      apply num_laters_per_step_lt in Hlt. lia.
    }
    rewrite Nat_iter_S. iModIntro. iModIntro. iNext.
    iMod "H". iDestruct ("Hwp" $! _) as "(_&Hwp)".
    iMod ("Hwp" with "[$] [$]") as "Hwp".
    iModIntro.
    iApply (step_fupd_extra.step_fupd2N_wand with "Hwp"). iIntros "Hwp".
    iMod "Hwp" as "(Hg&HΦc)".
    iMod (later_tok_incr with "[$]") as "(Hg&Htok')".
    iMod (global_state_interp_le _ ns _ _ with "Hg") as "Hg".
    { lia. }
    iFrame.
    iModIntro. by iApply "HΦc".
Qed.

End res.
