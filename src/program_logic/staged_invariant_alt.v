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
| canceled : Qp → staged_inv_status
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

(*
Definition staged_inv_cancel_pre E mj Pc : iProp Σ :=
  ∃ Einv mj_ishare mj_ikeep γ γfinish γstatus,
    ⌜ set_infinite Einv ⌝ ∗
    ⌜ 1 < mj + mj_ikeep ⌝%Qp ∗
    ⌜ (mj_ikeep + mj_ishare = /2)%Qp ⌝ ∗
    later_tok ∗
    staged_pending 1 γfinish ∗
    pri_inv_tok mj_ikeep Einv ∗
    pri_inv Einv (staged_inv_inner E Einv mj mj_ishare γ γfinish γstatus Pc).
*)

Definition staged_inv_inner_pre
           (staged_inv_inner : coPset -d> coPset -d> Qp -d> Qp -d> gname -d> gname
                              -d> gname -d> iPropO Σ -d> iPropO Σ) :
           coPset -d> coPset -d> Qp -d> Qp -d> gname -d> gname -d> gname -d> iPropO Σ -d> iPropO Σ :=
          λ E1 E2 mj mj_ishare (γsaved γfinished γstatus: gname) (P: iProp Σ) ,
  ((∃ γprop_stored γprop_remainder (stat: staged_inv_status) Ps Pr,
             own γsaved (● Excl' (γprop_stored, γprop_remainder)) ∗
             saved_prop_own γprop_stored Ps ∗
             saved_prop_own γprop_remainder Pr ∗
             own γstatus (● Excl' stat) ∗
             pri_inv_tok mj_ishare E2 ∗
             ((match stat with
              | inuse mj_wp mj_ushare => (⌜ (/2) < mj_wp ∧ mj_wp ≤ /2 + mj_ushare ∧ mj_wp ≤ mj ⌝%Qp ∗ Ps ∗ pri_inv_tok mj_ushare E2 ∗ □ (Ps -∗ wpc_crash_modality E1 mj_wp (Pr ∗ P)))
              | canceled mj' => (⌜ (/2) < mj' ≤ mj  ⌝%Qp ∗
                                ∃ E1' Einv mj_ishare mj_ikeep γ γfinish γstatus,
                                  ⌜ E1' ⊆ E1 ⌝ ∗
                                  ⌜ set_infinite Einv ⌝ ∗
                                  ⌜ 1 < mj' + mj_ikeep ⌝%Qp ∗
                                  ⌜ (mj_ikeep + mj_ishare = /2)%Qp ⌝ ∗
                                  later_tok ∗
                                  staged_pending 1 γfinish ∗
                                  pri_inv_tok mj_ikeep Einv ∗
                                  pri_inv Einv (staged_inv_inner E1' Einv mj' mj_ishare γ γfinish γstatus P)) ∨
                                  staged_done γfinished
              | idle => (Ps ∗ □ (Ps -∗ C ==∗ P ∗ Pr))
              end)
              ∨
             (Pr ∗ C ∗ (P ∨ staged_done γfinished)))))%I.

Local Instance staged_inv_inner_pre_contractive : Contractive (staged_inv_inner_pre).
Proof.
  rewrite /staged_inv_inner_pre => n pre1 pre2 Hequiv ????????.
  do 15 (f_contractive || f_equiv).
  destruct a1.
  - repeat (f_contractive || f_equiv).
  - do 25 (f_contractive || f_equiv).
    eapply Hequiv.
  - repeat (f_contractive || f_equiv).
Qed.

Definition staged_inv_inner := fixpoint (staged_inv_inner_pre).

Lemma staged_inv_inner_unfold  E1 E2 mj1 mj2 γ1 γ2 γ3 P :
      staged_inv_inner E1 E2 mj1 mj2 γ1 γ2 γ3 P ⊣⊢
      staged_inv_inner_pre staged_inv_inner E1 E2 mj1 mj2 γ1 γ2 γ3 P.
Proof. apply (fixpoint_unfold staged_inv_inner_pre). Qed.

Definition staged_inv E1 E2 (γsaved γfinished γstatus: gname) (P: iProp Σ) : iProp Σ :=
  (∃ mj mj_ishare, ⌜ /2 < mj ⌝%Qp ∗ pri_inv E2 (staged_inv_inner E1 E2 mj mj_ishare γsaved γfinished γstatus P)).

Definition staged_inv_cancel E mj0 Pc : iProp Σ :=
  ∃ mj Einv mj_ishare mj_ikeep γ γfinish γstatus,
    ⌜ /2 < mj ≤ mj0 ⌝%Qp ∗
    ⌜ set_infinite Einv ⌝ ∗
    ⌜ 1 < mj + mj_ikeep ⌝%Qp ∗
    ⌜ (mj_ikeep + mj_ishare = /2)%Qp ⌝ ∗
    later_tok ∗
    staged_pending 1 γfinish ∗
    pri_inv_tok mj_ikeep Einv ∗
    pri_inv Einv (staged_inv_inner E Einv mj mj_ishare γ γfinish γstatus Pc).

Definition staged_value_idle E1 (Ps Pr: iProp Σ) P : iProp Σ :=
  (∃ E2 γsaved γfinished γstatus γprop γprop',
      own γsaved (◯ Excl' (γprop, γprop')) ∗
      own γstatus (◯ Excl' idle) ∗
          saved_prop_own γprop Ps ∗
          saved_prop_own γprop' Pr ∗
          later_tok ∗
          pri_inv_tok (/2)%Qp E2 ∗
          staged_inv E1 E2 γsaved γfinished γstatus P)%I.

Definition staged_value E Ps P : iProp Σ := staged_value_idle E Ps True%I P.

End def.

Section inv.
Context `{IRISG: !irisGS Λ Σ}.
Context `{PRI: !pri_invG IRISG}.
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
  (∀ D E', pri_inv_tok 1%Qp E' ∗ ⌜ (/2 < mj)%Qp ∧ E' ## D ⌝ -∗ ||={E1|⊤∖D, E1|⊤∖D}=> wpc0 s k mj E1 e Φ Φc) -∗
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
      iDestruct (pri_inv_tok_global_valid with "[$]") as %(?&?).
      iSpecialize ("H" with "[$Hitok //]").
      rewrite wpc0_unfold/ wpc_pre. rewrite Heq_val.
      iMod "H" as "(H&_)". by iMod ("H" with "[$] [$]") as "$".
    - iIntros.
      iMod (pri_inv_tok_alloc with "[$]") as (Einv Hdisj) "(Hitok&Hg)".
      iDestruct (pri_inv_tok_global_valid with "[$]") as %(?&?).
      iSpecialize ("H" with "[$Hitok //]").
      rewrite wpc0_unfold/ wpc_pre. rewrite Heq_val.
      iMod "H" as "(H&_)". by iMod ("H" with "[$] [$] [$]") as "$".
  }
  iIntros.
  iMod (pri_inv_tok_alloc with "[$]") as (Einv Hdisj) "(Hitok&Hg)".
  iDestruct (pri_inv_tok_global_valid with "[$]") as %(?&?).
  iSpecialize ("H" with "[$Hitok //]").
  rewrite wpc0_unfold/ wpc_pre.
  iMod "H" as "(_&H)". by iMod ("H" with "[$] [$]") as "$".
Qed.


End inv.
