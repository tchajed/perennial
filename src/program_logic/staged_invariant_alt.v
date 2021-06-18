From iris.algebra Require Import gmap auth agree gset coPset excl csum.
From Perennial.base_logic.lib Require Export fancy_updates.
From stdpp Require Export namespaces.
From Perennial.base_logic.lib Require Import wsat invariants ae_invariants saved_prop.
From iris.algebra Require Import gmap.
From iris.proofmode Require Import tactics.
From Perennial.program_logic Require Export step_fupd_extra crash_weakestpre ae_invariants_mutable later_res private_invariants.
Set Default Proof Using "Type".
Import uPred.

Class stagedG (Σ : gFunctors) : Set := WsatG {
  staging_saved_inG :> savedPropG Σ;
  staging_auth_inG :> inG Σ (authR (optionUR (exclR (prodO gnameO gnameO))));
  staging_shot_inG :> inG Σ (csumR (fracR) (agreeR unitO));
}.

Definition stagedΣ : gFunctors :=
  #[GFunctor (csumR fracR (agreeR unitO)); GFunctor (authR (optionUR (exclR (prodO gnameO gnameO))));
   savedPropΣ].

Instance subG_stagedG {Σ} : subG stagedΣ Σ → stagedG Σ.
Proof. solve_inG. Qed.

Definition staged_pending `{stagedG Σ} (q: Qp) (γ: gname) : iProp Σ :=
  own γ (Cinl q).
Definition staged_done `{stagedG Σ} (γ: gname) : iProp Σ :=
  own γ (Cinr (to_agree ())).

(* This is the modality guarding the crash condition in a wpc *)
Definition wpc_crash_modality `{!irisGS Λ Σ, !crashG Σ} E1 Φc :=
  ((∀ g1 ns D κs,
       let E2 :=  ⊤ ∖ D in
       global_state_interp g1 ns D κs -∗ C -∗
     ||={E1|E2,∅|∅}=> ||▷=>^(num_laters_per_step ns) ||={∅|∅,E1|E2}=> global_state_interp g1 ns D κs ∗ Φc))%I.

Section def.
Context `{IRISG: !irisGS Λ Σ}.
Context `{!pri_invG IRISG}.
Context `{!later_tokG IRISG}.
Context `{!stagedG Σ}.

Definition staged_inv_inner E1 E2 (γ γ': gname) (P: iProp Σ) : iProp Σ :=
  ((∃ γprop_stored γprop_remainder Ps Pr,
             own γ (● Excl' (γprop_stored, γprop_remainder)) ∗
             saved_prop_own γprop_stored Ps ∗
             saved_prop_own γprop_remainder Pr ∗
             (later_tok ∗ ((Ps ∗ pri_inv_tok E2 ∗ □ (Ps -∗ wpc_crash_modality E1 (P ∗ Pr)))
                ∨
              (Ps ∗ □ (Ps -∗ C ==∗ P ∗ Pr)))
              ∨
             (Pr ∗ C ∗ staged_done γ'))))%I.


Definition staged_inv E1 E2 (γ γ': gname) (P: iProp Σ) : iProp Σ :=
  (pri_inv E2 (staged_inv_inner E1 E2 γ γ' P)).

Definition staged_value E1 (Ps Pr: iProp Σ) P : iProp Σ :=
  (∃ E2 γ γ' γprop γprop', own γ (◯ Excl' (γprop, γprop')) ∗ saved_prop_own γprop Ps ∗ saved_prop_own γprop' Pr ∗ later_tok ∗ pri_inv_tok E2 ∗ staged_inv E1 E2 γ γ' P)%I.

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

Global Instance staged_persistent E1 E2 γ γ' P : Persistent (staged_inv E1 E2 γ γ' P).
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

Lemma wpc0_pri_inv_tok_res s k D E1 e Φ Φc :
  (∀ E', (⌜ E' ## D ⌝ ∧ pri_inv_tok E') -∗
          ||={E1|⊤∖D, E1|⊤∖D}=> wpc0 s k D E1 e Φ Φc) -∗
  wpc0 s k D E1 e Φ Φc.
Proof.
  iIntros "H".
  iEval (rewrite wpc0_unfold).
  rewrite /wpc_pre.
  iSplit.
  {
    destruct (to_val e) eqn:Heq_val.
    - iIntros (q g1 ns κs) "Hg HNC".
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

Existing Instances pri_inv_tok_timeless later_tok_timeless.

Lemma wpc_staged_inv_init s k E e Φ Φc P Pc:
  later_tok ∗
  later_tok ∗
  P ∗
  □ (P -∗ Pc) ∗
  (staged_value E P True Pc -∗ WPC e @ s; k; E {{ Φ }} {{ Φc }})
  ⊢ WPC e @ s; k; E {{ Φ }} {{ Φc ∗ Pc }}.
Proof.
  iIntros "(Htok1&Htok2&HP&#Hwand&Hwp)".
  rewrite wpc_eq /wpc_def. iIntros (D).
  iApply wpc0_pri_inv_tok_res.
  iIntros (Einv) "(%Hdisj&Hitok)".

  (* Create the invariant *)

  iMod (saved_prop_alloc P) as (γprop) "#Hsaved".
  iMod (saved_prop_alloc True%I) as (γprop') "#Hsaved'".
  iMod (own_alloc (● (Excl' (γprop, γprop')) ⋅ ◯ (Excl' (γprop, γprop')))) as (γ) "[H1 H2]".
  { apply auth_both_valid_2; [econstructor | reflexivity]. }
  iMod (pending_alloc) as (γ') "H".

  iDestruct (pri_inv_tok_infinite with "Hitok") as %Hinf.
  iMod (pri_inv_alloc Einv _ _ (staged_inv_inner E Einv γ γ' Pc) with "[HP H1 Htok2]") as "#Hpri_inv"; auto.
  { iNext. rewrite /staged_inv_inner. iExists _, _, P, True%I. iFrame "∗ #".
    iLeft. iFrame. iRight.
    iModIntro. iIntros "HP HC". iModIntro. iDestruct ("Hwand" with "[$]") as "$"; eauto.
  }

  (* The inductive proof *)
  iSpecialize ("Hwp" with "[Htok1 Hitok H2]").
  { iExists _, _, _, _, _. iFrame "∗ #". }
  iSpecialize ("Hwp" $! D).

  iModIntro.
  iLöb as "IH" forall (e).
  rewrite ?wpc0_unfold. rewrite /wpc_pre.
  iSplit; last first.
  {
    iDestruct "Hwp" as "(_&Hwp)".
    iIntros (g ns κs) "Hg #HC".
    iMod (pri_inv_acc with "Hpri_inv") as "(Hinner&Hclo)".
    { set_solver. }
    iDestruct "Hinner" as (????) "(Hown1&#Hsaved1&#Hsaved2&Hinner)".
    iDestruct "Hinner" as "[(>Hltok&Hs)|Hbad]"; last first.
    {
      (* This case is impossible since we have the staged_pending token *)
      iDestruct "Hbad" as "(_&_&>Hdone)".
      iDestruct (pending_done with "[$] [$]") as %[].
    }
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
  }
  iDestruct "Hwp" as "(Hwp&_)".
  destruct (to_val e).
  { iIntros. iMod ("Hwp" with "[$] [$]"). eauto. }
  iIntros.
  iMod ("Hwp" with "[$] [$] [$]") as "Hwp".
  iModIntro. simpl. iMod "Hwp". iModIntro.
  iNext. iMod "Hwp". iModIntro. iApply (step_fupd2N_wand with "Hwp").
  iIntros "($&Hwp)".
  iIntros. iMod ("Hwp" with "[//]") as "($&$&Hwpc&$&$)". iModIntro. iApply ("IH" with "[$] [$]").
Qed.

End inv.
