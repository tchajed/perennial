From stdpp Require Export namespaces.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import gmap frac.
From Perennial.base_logic.lib Require Export fancy_updates fupd_level.
From Perennial.base_logic.lib Require Import wsat.
From Perennial.program_logic Require Import crash_weakestpre.
From Perennial.Helpers Require Import Qextra.
Set Default Proof Using "Type".
Unset Implicit Arguments.
Import uPred.

(* I think this can be done using dyn_reservation_map in global_state_interp *)
Class pri_invG {Λ Σ} (IRISG : irisGS Λ Σ) := {
  pri_inv_tok : fracR → coPset → iProp Σ;
  pri_inv_tok_timeless : ∀ q E, Timeless (pri_inv_tok q E);
  pri_inv_tok_infinite : ∀ q E, pri_inv_tok q E -∗ ⌜ set_infinite E ⌝;
  pri_inv_tok_split : ∀ q1 q2 E, pri_inv_tok (q1 + q2)%Qp E -∗ (pri_inv_tok q1 E ∗ pri_inv_tok q2 E);
  pri_inv_tok_join : ∀ q1 q2 E, pri_inv_tok q1 E -∗ pri_inv_tok q2 E -∗ pri_inv_tok (q1 + q2)%Qp E;
  pri_inv_tok_valid : ∀ q E, pri_inv_tok q E -∗ ⌜ q ≤ 1 ⌝%Qp;
  pri_inv_tok_global_valid : ∀ g ns q D κ, global_state_interp g ns q D κ -∗ ⌜ /2 < q ∧ q ≤ 1⌝%Qp;
  pri_inv_tok_global_split :
     ∀ g ns q1 q2 D κ, ⌜ /2 < q2 ⌝%Qp -∗ global_state_interp g ns (q1 + q2)%Qp D κ -∗
                         global_state_interp g ns q2 D κ ∗ pri_inv_tok q1 D;
  pri_inv_tok_global_join :
     ∀ g ns q1 q2 D κ, global_state_interp g ns q2 D κ ∗ pri_inv_tok q1 D -∗
                       global_state_interp g ns (q1 + q2)%Qp D κ;
  pri_inv_tok_alloc :
    ⊢ (∀ g ns q D κ, global_state_interp g ns q D κ ==∗
                   ∃ E, ⌜ E ## D ⌝ ∗ pri_inv_tok 1%Qp E ∗ global_state_interp g ns q D κ)%I;
  pri_inv_tok_disable :
    ⊢ (∀ E g ns q D κ, pri_inv_tok q E ∗ global_state_interp g ns q D κ ==∗
                       global_state_interp g ns q (E ∪ D) κ)%I;
  pri_inv_tok_enable :
    ⊢ (∀ E g ns q D κ, ⌜ E ## D ⌝ ∧ global_state_interp g ns q (E ∪ D) κ ==∗
                     pri_inv_tok q E ∗ global_state_interp g ns q D κ)%I;
  pri_inv_tok_disj :
    ⊢ (∀ g ns q1 q2 D κ E, global_state_interp g ns q1 D κ ∗ pri_inv_tok q2 E -∗ ⌜ E ## D ∨ ✓(q1 + q2)%Qp ⌝)
}.

Section def.
Context `{IRISG: !irisGS Λ Σ}.
Context `{!pri_invG IRISG}.
Definition pri_inv_def E P : iProp Σ :=
  ∃ i, ⌜i ∈ MaybeEn2 E⌝ ∧ ownI O i (bi_sch_var_fixed O) (list_to_vec [P]).
Definition pri_inv_aux : seal (@pri_inv_def). Proof. by eexists. Qed.
Definition pri_inv := pri_inv_aux.(unseal).
Definition pri_inv_eq : @pri_inv = @pri_inv_def := pri_inv_aux.(seal_eq).
Typeclasses Opaque pri_inv.

(*
Definition pri_inv_full_def P : iProp Σ :=
    ∃ E, pri_inv_tok E ∗ pri_inv E P.
Definition pri_inv_full_aux : seal (@pri_inv_full_def). Proof. by eexists. Qed.
Definition pri_inv_full := pri_inv_full_aux.(unseal).
Definition pri_inv_full_eq : @pri_inv_full = @pri_inv_full_def := pri_inv_full_aux.(seal_eq).
Instance: Params (@pri_inv_full) 3 := {}.
Typeclasses Opaque pri_inv_full.
*)
End def.

Local Hint Extern 0 (AlwaysEn ## MaybeEn1 _) => apply coPset_inl_inr_disj : core.
Local Hint Extern 0 (AlwaysEn ## MaybeEn2 _) => apply coPset_inl_inr_disj : core.
Local Hint Extern 0 (MaybeEn1 _ ## MaybeEn2 _) => apply MaybeEn12_disj : core.

Section pri_inv.
Context `{IRISG: !irisGS Λ Σ}.
Context `{PRI: !pri_invG IRISG}.
  Implicit Types i : positive.
  Implicit Types E : coPset.
  Implicit Types P Q R : iProp Σ.
  Implicit Types Ps Qs Rs : list (iProp Σ).

  Lemma pri_inv_tok_global_le_acc :
     ∀ g ns q1 q2 D κ, ⌜ /2 < q2 ∧ q2 ≤ q1 ⌝%Qp -∗ global_state_interp g ns q1 D κ -∗
                         global_state_interp g ns q2 D κ ∗
                         (∀ g' ns' κ', global_state_interp g' ns' q2 D κ' -∗ global_state_interp g' ns' q1 D κ').
  Proof using PRI.
    iIntros (g ns q1 q2 D κ [Hle1 Hle2]) "Hg".
    apply Qp_le_lteq in Hle2.
    destruct Hle2 as [Hlt|Heq]; last first.
    { subst. iFrame. eauto. }
    apply Qp_split_lt in Hlt as (q'&Hplus).
    rewrite Qp_add_comm in Hplus.
    rewrite -Hplus.
    iDestruct (pri_inv_tok_global_split with "[] Hg") as "(Hg&Hitok)"; eauto.
    iFrame. iIntros. iApply pri_inv_tok_global_join. by iFrame.
  Qed.

  Lemma pri_inv_tok_le_acc (q1 q2 : Qp) E :
    (q1 ≤ q2)%Qp →
    pri_inv_tok q2 E -∗ pri_inv_tok q1 E ∗ (pri_inv_tok q1 E -∗ pri_inv_tok q2 E).
  Proof.
    intros [Hlt|Heq]%Qp_le_lteq.
    - iIntros "Hp". apply Qp_split_lt in Hlt as (q'&Hplus).
      rewrite -Hplus. iDestruct (pri_inv_tok_split with "Hp") as "(Hp1&Hp2)".
      iFrame. iIntros. iApply (pri_inv_tok_join with "[$] [$]").
    - subst. iIntros "$". auto.
  Qed.

  Lemma pri_inv_tok_disj_inv_half g ns q D κ E:
    global_state_interp g ns q D κ ∗ pri_inv_tok (/ 2)%Qp E -∗ ⌜ E ## D ⌝.
  Proof.
    iIntros "(Hg&Hitok)".
    iDestruct (pri_inv_tok_disj with "[$]") as %Hcases.
    iDestruct (pri_inv_tok_global_valid with "[$]") as %(Hmin&_).
    iPureIntro. destruct Hcases as [Hdisj|Hval]; auto.
    revert Hval. rewrite frac_valid => Hval.
    assert (1 < q + / 2)%Qp.
    { rewrite -Qp_inv_half_half. apply Qp_add_lt_mono_r; auto. }
    exfalso. apply Qp_le_ngt in Hval; eauto.
  Qed.

  Lemma pri_inv_alloc E E1 E2 P : set_infinite E → ▷ P -∗ ||={E1|E2, E1|E2}=> pri_inv E P.
  Proof.
    rewrite uPred_fupd2_eq /uPred_fupd2_def.
    iIntros (Hinf) "HP [Hw $]".
    iMod (wsat_all_acc 1 with "[$]") as "(Hw&Hclo)".
    iMod (ownI_alloc (.∈ MaybeEn2 E) (bi_sch_var_fixed O) O (list_to_vec [P]) (list_to_vec [])
            with "[$HP $Hw]")
      as (i' ?) "[? [? ?]]"; auto using fresh_inv_name.
    {
      intros E'.
      exists (coPpick (MaybeEn2 E ∖ gset_to_coPset E')).
      rewrite -elem_of_gset_to_coPset (comm and) -elem_of_difference.
      apply coPpick_elem_of=> Hfin.
      apply (difference_finite_inv _ _) in Hfin; auto using gset_to_coPset_finite.
      apply MaybeEn2_infinite in Hfin; auto.
      intros ?. eapply set_not_infinite_finite; eauto.
    }
    iDestruct ("Hclo" with "[$]") as "$".
    iIntros "!> !>". rewrite pri_inv_eq /pri_inv_def. iExists _. iFrame; eauto.
  Qed.

  Lemma pri_inv_acc E1 E2 E P :
    E ⊆ E2 → pri_inv E P -∗ ||={E1|E2,E1|E2∖E}=> ▷ P ∗ (▷ P -∗ ||={E1|E2∖E,E1|E2}=> True).
  Proof.
    rewrite uPred_fupd2_eq /uPred_fupd2_def pri_inv_eq.
    iIntros (Hsub) "HiP".
    iDestruct "HiP" as (i' Hin2%elem_of_subseteq_singleton) "#HiP".
    rewrite (ownE_op (AlwaysEn ∪ _)) //; last first.
    { apply disjoint_union_l; split; auto. }
    rewrite {1 4}(union_difference_L E E2) // ownE_op_MaybeEn2; last set_solver.
    rewrite {1 2}(union_difference_L {[ i' ]} (MaybeEn2 _)) //.
    rewrite ownE_op //.
    rewrite ownE_op //; last by set_solver.
    iIntros "(Hw & (HAE & HE1) & (HE2a&HE2b) & HE2')".
    iMod (wsat_all_acc 1 with "[$]") as "(Hw&Hclo)".
    iIntros "!> !>".
    iDestruct (ownI_open O i' with "[$Hw $HE2a $HiP]") as "(Hw & HI & HD)".
    iDestruct ("Hclo" with "[$]") as "$".
    iDestruct "HI" as (? Ps_mut) "(Hinterp&Hmut)".
    iEval (rewrite ?bi_schema_interp_unfold /=) in "Hinterp". iFrame "Hinterp".
    rewrite ownE_op //; last first.
    { apply disjoint_union_l; split; auto. }
    rewrite ownE_op //; last first.
    iFrame.
    iIntros "HP [Hw [$ $]]".
    iMod (wsat_all_acc 1 with "[$]") as "(Hw&Hclo)".
    iDestruct (ownI_close O _ _ (list_to_vec [P]) with "[$Hmut $Hw $HiP HP $HD]") as "(Hw&?)".
    { rewrite ?bi_schema_interp_unfold /=. iFrame. }
    iDestruct ("Hclo" with "[$]") as "$"; eauto.
  Qed.

  Global Instance pri_inv_persistent E P : Persistent (pri_inv E P).
  Proof. rewrite pri_inv_eq. apply _. Qed.

End pri_inv.
