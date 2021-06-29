From stdpp Require Export sets coPset.
From iris.algebra Require Export cmra functions frac.
From iris.algebra Require Import updates local_updates.
From iris.prelude Require Import options.

Record frac_coPset :=
  { fc_carrier :> @discrete_fun positive (fun _ => optionO fracR) }.

Section ofe.
  Global Instance frac_coPset_equiv : Equiv (frac_coPset) := λ f g, (fc_carrier f) ≡ (fc_carrier g).
  Global Instance frac_coPset_dist : Dist (frac_coPset) := λ n f g, (fc_carrier f) ≡{n}≡ (fc_carrier g).
  Definition frac_coPset_ofe_mixin : OfeMixin (frac_coPset).
  Proof.
    split.
    - intros f g; split; [intros Hfg n k; apply equiv_dist, Hfg|].
      intros Hfg k; apply equiv_dist=> n; apply Hfg.
    - intros n; split.
      + by intros f x.
      + by intros f g ? x.
      + intros [f] [g] [h] ?? x. trans (g x); eauto.
    - by intros n f g ? x; apply dist_S.
  Qed.
  Canonical Structure frac_coPsetO := Ofe (frac_coPset) frac_coPset_ofe_mixin.
  Global Instance frac_coPset_ofe_discrete :
    OfeDiscrete (frac_coPsetO).
  Proof. intros f f' Heq i. apply Heq. Qed.

  Program Definition frac_coPset_chain `(c : chain frac_coPsetO)
   (x : positive) : chain (optionO fracO) := {| chain_car n := (fc_carrier (c n)) x |}.
  Next Obligation. intros c x n i ?. by apply (chain_cauchy c). Qed.

  Global Instance frac_coPset_fun_inhabited : Inhabited frac_coPsetO :=
    populate {| fc_carrier := (λ _, None) |}.
End ofe.

Section frac_coPset_cmra.
  Implicit Types f g : frac_coPset.

  Local Instance frac_coPset_valid_instance : Valid (frac_coPset) := λ f,
    (∀ x, ✓ (fc_carrier f) x) ∧
    (∃ E : coPset, (∀ p : positive, is_Some (fc_carrier f p) → p ∈ E) ∧ set_infinite (⊤ ∖ E)).
  Local Instance frac_coPset_validN_instance : ValidN (frac_coPset) := λ n f,
    (∀ x, ✓ (fc_carrier f) x) ∧
    (∃ E : coPset, (∀ p : positive, is_Some (fc_carrier f p) → p ∈ E) ∧ set_infinite (⊤ ∖ E)).

  Local Instance frac_coPset_op_instance : Op (frac_coPset) :=
    λ f g, {| fc_carrier := λ x, (fc_carrier f) x ⋅ (fc_carrier g) x |}.
  Local Instance frac_coPset_pcore_instance : PCore (frac_coPset) := λ f,
   Some {| fc_carrier := λ x, core (fc_carrier f x) |}.

  Lemma frac_coPset_lookup_op f g x : fc_carrier (f ⋅ g) x = fc_carrier f x ⋅ fc_carrier g x.
  Proof. auto. Qed.

  Lemma frac_coPset_lookup_core f x : fc_carrier (core f) x = core (fc_carrier f x).
  Proof. auto. Qed.

  Lemma frac_coPset_included_spec_1 f g x : f ≼ g → (fc_carrier f) x ≼ (fc_carrier g) x.
  Proof. by intros [h Hh]; exists (fc_carrier h x); rewrite /op /frac_coPset_op_instance (Hh x). Qed.

  Lemma frac_coPset_ra_mixin : RAMixin frac_coPset.
  Proof.
    apply ra_total_mixin; eauto.
    - intros f1 f2 f3 Hf x. by rewrite ?frac_coPset_lookup_op (Hf x).
    - intros f1 f2 Hf x. by rewrite ?frac_coPset_lookup_core (Hf x).
    - intros f1 f2 Hf (Hvalf&Hdomf).
      split.
      * intros x. specialize (Hf x). apply leibniz_equiv in Hf as <-. auto.
      * destruct Hdomf as (E&Hdom&Hcofin). exists E. split; auto.
        intros x Hsome. apply Hdom. specialize (Hf x). apply leibniz_equiv in Hf as ->. auto.
    - intros f1 f2 f3 x. by rewrite ?frac_coPset_lookup_op ?assoc.
    - intros f1 f2 x. rewrite ?frac_coPset_lookup_op. apply comm, _.
    - intros f x. by rewrite frac_coPset_lookup_op frac_coPset_lookup_core cmra_core_l.
    - by intros f x; rewrite frac_coPset_lookup_core cmra_core_idemp.
    - intros f1 f2 Hf12. exists (core f2)=>x. rewrite frac_coPset_lookup_op.
      apply (frac_coPset_included_spec_1 _ _ x), (cmra_core_mono (fc_carrier f1 x)) in Hf12.
      rewrite !frac_coPset_lookup_core. destruct Hf12 as [? ->].
      rewrite assoc -cmra_core_dup //.
    - intros f1 f2 (Hf&Hdom).
      split.
      * intros x. apply cmra_valid_op_l with (fc_carrier f2 x), Hf.
      * destruct Hdom as (E&Hdom&Hcofin). exists E; split; auto.
        intros x Hsome. apply Hdom.
        rewrite frac_coPset_lookup_op.
        destruct (fc_carrier f1 x), (fc_carrier f2 x) => //=.
        { eexists; eauto. }
        { inversion Hsome. congruence. }
  Qed.
  Canonical Structure frac_coPsetR :=
    (Cmra frac_coPset (discrete_cmra_mixin _ frac_coPset_ra_mixin)).

  Global Instance frac_coPsetR_cmra_discrete:
    CmraDiscrete (frac_coPsetR).
  Proof. split; [apply _|]. intros x Hv. apply Hv. Qed.

  Local Instance frac_coPsetR_empty_instance : Unit (frac_coPset) :=
    {| fc_carrier := (fun _ => None) |}.

  Lemma frac_coPset_ucmra_mixin : UcmraMixin frac_coPset.
  Proof.
    split; try apply _ || done.
    - split.
      * intros; econstructor.
      * exists ∅; split.
        ** intros ? => //=. inversion 1. congruence.
        ** replace (⊤ ∖ ∅) with (⊤ : coPset) by set_solver. apply top_infinite.
    - intros f x. rewrite frac_coPset_lookup_op //= left_id //.
  Qed.
  Canonical Structure frac_coPsetUR := Ucmra frac_coPset frac_coPset_ucmra_mixin.
End frac_coPset_cmra.
