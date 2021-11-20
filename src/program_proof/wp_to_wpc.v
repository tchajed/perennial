From Perennial.program_logic Require Import invariants_mutable.
From Perennial.program_proof Require Import disk_prelude. (* FIXME: make this disk-independent *)
From Perennial.base_logic.lib Require Import wsat.

(* This file explores ways to promote a HOCAP wp spec that relies on Perennial 1 style
   for crash safety into a Peony/Perennial 2 HOCAP spec.

   In particular, in the former, one usually has a fupd as a precondition to "update" some
   abstract state, which looks like

    (∀ σ, ▷ P σ ={⊤ ∖ ↑N}=∗ ▷ P (transition σ) ∗ Φ #())

   The issue, when it comes to crash safety, is that the resource used to
   *prove* this fupd, might itself be a durable resource. Thus if a wpc calls a
   wp with the above kind of HOCAP spec, it may not be able to prove its crash
   condition.

   The Peony/Perennial 2 style is to instead have something like

    <disc> ▷ Φc ∧ (∀ σ, ▷ P σ ={⊤ ∖ ↑N}=∗ ▷ P (transition σ) ∗ <disc> ▷ Φc ∧ Φ #())

   The idea is that if we crash *before* the fupd, we use the left side of the
   outer conjunct to prove a Φc crash condition, while if we crash after the
   fupd, we use the left side of the inner conjunct.

   This file shows that style 1 can be promoted to style 2 under some conditions.
*)

Section wpc_spec.
Context `{!heapGS Σ}.
Context `{!stagedG Σ}.


Context (N: namespace).
Definition N1 := N.@"1".
Definition N2 := N.@"2".

Definition mysch : bi_schema :=
  (bi_sch_or (bi_sch_and (bi_sch_var_mut 0) (bi_sch_except_0 (bi_sch_fupd ∅ ∅ (bi_sch_var_fixed 0))))
             (bi_sch_or (bi_sch_sep (bi_sch_var_fixed 2) (bi_sch_var_fixed 3))
                        (bi_sch_var_fixed 1))).
Lemma mysch_interp_weak k P Qs_mut γ :
  bi_schema_interp (S k) (bi_later <$> [P; staged_done γ; C; staged_pending (3/4)%Qp γ])
                   (bi_later <$> Qs_mut) mysch ⊣⊢
                   let Qs := default emp%I (bi_later <$> (Qs_mut !! O)) in
                      (((Qs ∧ ◇ |k,Some O={∅}=> ▷ P) ∨ ((▷ C ∗ ▷ staged_pending (3/4)%Qp γ)
                       ∨ (▷ staged_done γ))))%I.
Proof.
  remember (S k) as n eqn:Heq.
  do 2 (rewrite ?bi_schema_interp_unfold /= //=).
  rewrite Heq.
  erewrite (bi_sch_fupd_interp); last first.
  { rewrite ?bi_schema_interp_unfold /= //=. }
  rewrite list_lookup_fmap. by f_equiv.
Qed.

Lemma mysch_interp_strong k P Q γ :
  bi_schema_interp (S k) (bi_later <$> [P; staged_done γ; C; staged_pending (3/4)%Qp γ])
                   (bi_later <$> [Q]) mysch ⊣⊢
                      (((▷ Q ∧ ◇ |k,Some O={∅}=> ▷ P) ∨ ((▷ C ∗ ▷ staged_pending (3/4)%Qp γ)
                       ∨ (▷ staged_done γ))))%I.
Proof.
  remember (S k) as n eqn:Heq.
  do 2 (rewrite ?bi_schema_interp_unfold /= //=).
  rewrite Heq.
  erewrite (bi_sch_fupd_interp); last first.
  { rewrite ?bi_schema_interp_unfold /= //=. }
  do 2 (rewrite ?bi_schema_interp_unfold /= //=).
Qed.

End wpc_spec.

