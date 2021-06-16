From stdpp Require Export namespaces.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import gmap.
From Perennial.base_logic.lib Require Export fancy_updates fupd_level.
From Perennial.base_logic.lib Require Import wsat.
From Perennial.program_logic Require Import crash_weakestpre.
Set Default Proof Using "Type".
Unset Implicit Arguments.
Import uPred.

Class pri_invG {Λ Σ} (IRISG : irisGS Λ Σ) := {
  pri_inv_tok : positive → iProp Σ;
  pri_inv_timeless : ∀ i, Timeless (pri_inv_tok i);
  pri_inv_alloc :
    ⊢ (∀ g ns D κ, global_state_interp g ns D κ ==∗
                                   ∃ i, ⌜ i ∉ D ⌝ ∗ pri_inv_tok i ∗ global_state_interp g ns D κ)%I;
  pri_inv_disj :
    ⊢ (∀ g ns D κ i, global_state_interp g ns D κ ∗ pri_inv_tok i -∗ ⌜ i ∉ D ⌝)
}.

Section def.
Context `{IRISG: !irisGS Λ Σ}.
Context `{!pri_invG IRISG}.
Definition pri_inv_def (i: positive) P : iProp Σ :=
  ∃ i', ⌜i' ∈ MaybeEn2 (gset_to_coPset {[i]})⌝ ∧ ownI O i' (bi_sch_var_fixed O) (list_to_vec [P]).
Definition pri_inv_aux : seal (@pri_inv_def). Proof. by eexists. Qed.
Definition pri_inv := pri_inv_aux.(unseal).
Definition pri_inv_eq : @pri_inv = @pri_inv_def := pri_inv_aux.(seal_eq).
Typeclasses Opaque pri_inv.

Definition pri_inv_full_def P : iProp Σ :=
    ∃ i, pri_inv_tok i ∗ pri_inv i P.
Definition pri_inv_full_aux : seal (@pri_inv_full_def). Proof. by eexists. Qed.
Definition pri_inv_full := pri_inv_full_aux.(unseal).
Definition pri_inv_full_eq : @pri_inv_full = @pri_inv_full_def := pri_inv_full_aux.(seal_eq).
Instance: Params (@pri_inv_full) 3 := {}.
Typeclasses Opaque pri_inv_full.
End def.

Local Hint Extern 0 (AlwaysEn ## MaybeEn1 _) => apply coPset_inl_inr_disj : core.
Local Hint Extern 0 (AlwaysEn ## MaybeEn2 _) => apply coPset_inl_inr_disj : core.
Local Hint Extern 0 (MaybeEn1 _ ## MaybeEn2 _) => apply MaybeEn12_disj : core.

Section pri_inv.
Context `{IRISG: !irisGS Λ Σ}.
Context `{!pri_invG IRISG}.
  Implicit Types i : positive.
  Implicit Types mj: option nat.
  Implicit Types E : coPset.
  Implicit Types P Q R : iProp Σ.
  Implicit Types Ps Qs Rs : list (iProp Σ).

  Lemma pri_inv_acc E1 E2 i P :
    i ∈ E2 → pri_inv i P -∗ ||={E1|E2,E1|E2∖{[i]}}=> ▷ P ∗ (▷ P -∗ ||={E1|E2∖{[i]},E1|E2}=> True).
  Proof.
    rewrite uPred_fupd2_eq /uPred_fupd2_def pri_inv_eq.
    iIntros (Hin%elem_of_subseteq_singleton) "HiP".
    iDestruct "HiP" as (i' Hin2%elem_of_subseteq_singleton) "#HiP".
    rewrite (ownE_op (AlwaysEn ∪ _)) //; last first.
    { apply disjoint_union_l; split; auto. }
    rewrite {1 4}(union_difference_L {[i]} E2) // ownE_op_MaybeEn2; last set_solver.
    rewrite {1 2}(union_difference_L {[ i' ]} (MaybeEn2 _)); last first.
    { 
      assert (gset_to_coPset {[ i ]} = {[ i ]}) as <-; auto.
      { clear. rewrite -leibniz_equiv_iff. specialize (elem_of_gset_to_coPset {[i]}).
        set_unfold. eauto. }
    }
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

  Global Instance pri_inv_persistent i P : Persistent (pri_inv i P).
  Proof. rewrite pri_inv_eq. apply _. Qed.

End pri_inv.
