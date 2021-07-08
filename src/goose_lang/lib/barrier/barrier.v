From iris.algebra Require Import auth gset.
From Perennial.program_logic Require Export weakestpre crash_weakestpre.
From Perennial.base_logic Require Import invariants lib.saved_prop.
From Perennial.goose_lang Require Export lang.
From Perennial.goose_lang Require Export lang typing.
From Perennial.goose_lang Require Import proofmode wpc_proofmode notation crash_borrow.
From Perennial.goose_lang Require Export notation typing.
From Perennial.goose_lang.lib Require Export barrier.impl.
Set Default Proof Using "Type".



(** The CMRAs/functors we need. *)
Class barrierG Σ := BarrierG {
  barrier_inG :> inG Σ (authR (gset_disjUR gname));
  barrier_savedPropG :> savedPropG Σ;
}.
Definition barrierΣ : gFunctors :=
  #[ GFunctor (authRF (gset_disjUR gname)); savedPropΣ ].

Instance subG_barrierΣ {Σ} : subG barrierΣ Σ → barrierG Σ.
Proof. solve_inG. Qed.

(** Now we come to the Iris part of the proof. *)
Section goose_lang.
Context `{ffi_sem: ffi_semantics}.
Context `{!ffi_interp ffi}.
Context {ext_tys: ext_types ext}.

Local Coercion Var' (s:string): expr := Var s.
Section proof.
  Context `{!heapGS Σ}.
  Context `{!stagedG Σ, !barrierG Σ}.

Definition N := nroot.@"mynamespace".
Search crash_borrow.

Lemma crash_borrow_crash_wand P Pc:
  crash_borrow P Pc -∗ □ (P -∗ Pc).
Proof. iDestruct 1 as (??) "($&_)". Qed.

Definition barrier_inv (l : loc) (γ γc : gname) (P : iProp Σ) (Pc : iProp Σ) : iProp Σ :=
  (∃ (b : bool) (γsps : gset gname) (γcsps : gset gname) (fprop fcprop : gname → iProp Σ),
    l ↦ #b ∗
    own γ (● (GSet γsps)) ∗
    own γc (● (GSet γcsps)) ∗
    ([∗ set] γsp ∈ γsps, saved_prop_own γsp (fprop γsp)) ∗
    ([∗ set] γsp ∈ γcsps, saved_prop_own γsp (fcprop γsp)) ∗
    if b then
      crash_borrow ([∗ set] γsp ∈ γsps, fprop γsp) (([∗ set] γsp ∈ γcsps, fcprop γsp))
    else
      crash_borrow True%I True%I ∗
      □ (P -∗ ([∗ set] γsp ∈ γsps, fprop γsp)) ∗
      □ (([∗ set] γsp ∈ γcsps, fcprop γsp) -∗ Pc) ∗
      □ (([∗ set] γsp ∈ γsps, fprop γsp) -∗ ([∗ set] γsp ∈ γcsps, fcprop γsp))).


Definition recv (l : loc) (R Rc : iProp Σ) : iProp Σ :=
  (∃ γ γc P Pc R' Rc' γsp γspc,
    inv N (barrier_inv l γ γc P Pc) ∗
    ▷ (R' -∗ R) ∗
    ▷ (Rc -∗ Rc') ∗
    own γ (◯ GSet {[ γsp ]}) ∗
    own γc (◯ GSet {[ γspc ]}) ∗
    saved_prop_own γsp R' ∗
    saved_prop_own γspc Rc')%I.

Definition send (l : loc) (P Pc : iProp Σ) : iProp Σ :=
  (∃ γ γc, □ (P -∗ Pc) ∗ inv N (barrier_inv l γ γc P Pc))%I.

(** Setoids *)
Instance barrier_inv_ne l γ γc : NonExpansive2 (barrier_inv l γ γc).
Proof. solve_proper. Qed.
Global Instance send_ne l : NonExpansive2 (send l).
Proof. solve_proper. Qed.
Global Instance recv_ne l : NonExpansive2 (recv l).
Proof. solve_proper. Qed.

(** Actual proofs *)
Lemma newbarrier_spec (P Pc : iProp Σ) :
  {{{ □ (P -∗ Pc) }}} barrier.newbarrier #() {{{ l, RET #l; recv l P Pc ∗ send l P Pc }}}.
Proof.
  iIntros (Φ) "#Hwand HΦ". wp_lam.
  iApply wp_fupd.
  iApply (wpc_wp _ 0 _ _ _ True%I).
  iApply (wpc_crash_borrow_init_ctx _ _ _ _ _ True%I True%I id); auto.
  iSplit; first done.
  iIntros "Hc".
  iApply (wpc_crash_mono _ _ _ _ _ _ True%I); first eauto.
  iApply wp_wpc.
  wp_apply wp_alloc_untyped; auto.
  iIntros (l) "Hl". simpl.
  iApply (wpc_crash_mono _ _ _ _ _ _ True%I); first eauto.
  iApply wp_wpc.
  wp_pures.
  iApply ("HΦ" with "[> -]").
  iMod (saved_prop_alloc P) as (γsp) "#Hsp".
  iMod (saved_prop_alloc Pc) as (γspc) "#Hspc".
  iMod (own_alloc (● GSet {[ γsp ]} ⋅ ◯ GSet {[ γsp ]})) as (γ) "[H● H◯]".
  { by apply auth_both_valid_discrete. }
  iMod (own_alloc (● GSet {[ γspc ]} ⋅ ◯ GSet {[ γspc ]})) as (γc) "[Hc● Hc◯]".
  { by apply auth_both_valid_discrete. }
  iMod (inv_alloc N _ (barrier_inv l γ γc P Pc) with "[Hl H● Hc● Hc]") as "#Hinv".
  { iExists false, {[ γsp ]}, {[ γspc ]},
            (λ x, if decide (x = γsp) then P else True%I),
            (λ x, if decide (x = γspc) then Pc else True%I).
    iFrame "Hl H● Hc● Hc".
    iNext.
    iSplit.
    { rewrite ?big_sepS_singleton; eauto. rewrite decide_True //. }
    iSplit.
    { rewrite ?big_sepS_singleton; eauto. rewrite decide_True //. }
    iSplit.
    { rewrite ?big_sepS_singleton. rewrite decide_True //. eauto. }
    iSplit.
    { rewrite ?big_sepS_singleton. rewrite decide_True //. eauto. }
    { rewrite ?big_sepS_singleton. rewrite ?decide_True //. }
  }
  iModIntro; iSplitL "H◯ Hc◯".
  - iExists γ, γc, P, Pc, P, Pc, γsp, γspc. iFrame "∗ #".
    iSplitL; eauto.
  - iExists γ, γc. eauto.
Qed.

Lemma signal_spec l P Pc Φ Φc k K `{!LanguageCtx K}:
  send l P Pc -∗
  P -∗
  Φc ∧ (∀ (b: bool), WPC K (of_val #b) @ NotStuck; k; ⊤ {{ Φ }} {{ Φc }}) -∗
  WPC K (barrier.signal #l) @ NotStuck ; k ; ⊤ {{ Φ }} {{ Φc ∗ Pc }}.
Proof.
  iIntros "Hs HP HK".
  iAssert (□ (P -∗ Pc))%I with "[Hs]" as "#Hcwand".
  { iDestruct "Hs" as (??) "($&_)". }
  iApply (wpc_crash_borrow_init_ctx' with "HP"); auto.
  iSplit.
  { by iLeft in "HK". }
  iIntros "Hcb".
  iCache with "HK".
  { by iLeft in "HK". }
  wpc_frame.
  iDestruct "Hs" as (γ γc) "(_&#Hinv)". wp_lam.
  wp_bind (CmpXchg _ _ _).
  iInv N as ([] γsps γcsps fprop fcprop) "(>Hl & H● & Hc● & Hfprop & Hfcprop & HRs)".
  { wp_cmpxchg_fail. iModIntro. iSplitR "".
    { iExists true, γsps, γcsps, fprop, fcprop. iFrame. }
    wp_pures. iModIntro. iIntros "(_&HK)". by iApply "HK".
  }
  iDestruct "HRs" as "(Hcb'&#HP&#HPc&#Hcrash)".
  iApply (wpc_wp _ 0 _ _ _ True%I).
  iApply (wpc_crash_borrow_combine _ _ _ _ _
            ([∗ set] γsp ∈ γsps, (fprop γsp))
            ([∗ set] γsp ∈ γcsps, (fcprop γsp))
            with "[$Hcb] [$Hcb'] [] [] []").
  { auto. }
  { eauto. }
  { iNext. iIntros "H"; iSplit; last done.
    by iApply "HPc".
  }
  { iNext. iIntros "(HP'&HQ')".
    iApply "HP". eauto. }
  iApply wp_wpc.
  wp_cmpxchg_suc.
  iModIntro. iIntros "Hcb". iSplit; first eauto.
  iModIntro.
  iSplitR "".
  { iNext. iExists _, γsps, γcsps, _, _. iFrame. eauto. }
  wp_pures. iModIntro. iIntros "(_&HK)". iApply "HK".
Qed.

Lemma wait_spec l P Pc:
  {{{ recv l P Pc }}} barrier.wait #l {{{ RET #(); crash_borrow P Pc }}}.
Proof.
  rename P into R.
  rename Pc into Rc.
  iIntros (Φ) "HR HΦ".
  iDestruct "HR" as (γ γc P Pc R' Rc' γsp γspc) "(#Hinv & HR & HRc & H◯ & Hc◯ & #Hsp & #Hspc)".
  iLöb as "IH". wp_rec. wp_bind (! _)%E.
  iInv N as ([] γsps γcsps fprop fcprop) "(>Hl & >H● & HRs)"; last first.
  {
    iApply (wp_load with "[$]").
    iNext. iIntros "Hl".
    iModIntro. iSplitL "Hl H● HRs".
    { iExists false, γsps, γcsps, fprop, fcprop. iFrame. }
    wp_pures. by wp_apply ("IH" with "[$] [$] [$] [$]"). }
  iDestruct "HRs" as "(>Hc●&#Hsaved&#Hsavedc&Hcb)".
  (*
  iSpecialize ("HRs" with "[//]").
  iApply (wp_load with "[$]").
   *)
  iDestruct (own_valid_2 with "H● H◯")
    as %[Hvalid%gset_disj_included%elem_of_subseteq_singleton _]%auth_both_valid_discrete.
  iDestruct (own_valid_2 with "Hc● Hc◯")
    as %[Hvalidc%gset_disj_included%elem_of_subseteq_singleton _]%auth_both_valid_discrete.
  iMod (own_update_2 with "H● H◯") as "H●".
  { apply (auth_update_dealloc _ _ (GSet (γsps ∖ {[ γsp ]}))).
    apply gset_disj_dealloc_local_update. }
  iAssert (▷▷ (fcprop γspc ≡ Rc'))%I as "Hcequiv".
  { iNext.
    iDestruct (big_sepS_delete with "Hsavedc") as "[Hthis _]"; first done.
    iDestruct (saved_prop_agree with "Hthis Hspc") as "Hequiv". eauto. }
  iAssert (▷▷ (fprop γsp ≡ R'))%I as "Hequiv".
  { iNext.
    iDestruct (big_sepS_delete with "Hsaved") as "[Hthis _]"; first done.
    iDestruct (saved_prop_agree with "Hthis Hsp") as "Hequiv". eauto. }


  iDestruct (big_sepS_delete with "HRs") as "[HR'' HRs]"; first done.
  iDestruct "HR''" as (R'') "[#Hsp' HR'']".
  iDestruct (saved_prop_agree with "Hsp Hsp'") as "#Heq".
  iNext. iIntros "Hl".
  iIntros "!>". iSplitL "Hl H● HRs".
  { iDestruct (bi.later_intro with "HRs") as "HRs".
    iModIntro. iExists true, (γsps ∖ {[ γsp ]}). iFrame; eauto. }
  wp_if. iApply "HΦ". iApply "HR". by iRewrite "Heq".
Qed.

Lemma recv_split E l P1 P2 :
  ↑N ⊆ E → recv l (P1 ∗ P2) ={E}=∗ recv l P1 ∗ recv l P2.
Proof.
  rename P1 into R1; rename P2 into R2.
  iIntros (?). iDestruct 1 as (γ P R' γsp) "(#Hinv & HR & H◯ & #Hsp)".
  iInv N as (b γsps) "(>Hl & >H● & HRs)".
  iDestruct (own_valid_2 with "H● H◯")
    as %[Hvalid%gset_disj_included%elem_of_subseteq_singleton _]%auth_both_valid_discrete.
  iMod (own_update_2 with "H● H◯") as "H●".
  { apply (auth_update_dealloc _ _ (GSet (γsps ∖ {[ γsp ]}))).
    apply gset_disj_dealloc_local_update. }
  set (γsps' := γsps ∖ {[γsp]}).
  iMod (saved_prop_alloc_cofinite γsps' R1) as (γsp1 Hγsp1) "#Hsp1".
  iMod (saved_prop_alloc_cofinite (γsps' ∪ {[ γsp1 ]}) R2)
    as (γsp2 [? ?%not_elem_of_singleton_1]%not_elem_of_union) "#Hsp2".
  iMod (own_update _ _ (● _ ⋅ (◯ GSet {[ γsp1 ]} ⋅ ◯ (GSet {[ γsp2 ]})))
    with "H●") as "(H● & H◯1 & H◯2)".
  { rewrite -auth_frag_op gset_disj_union; last set_solver.
    apply auth_update_alloc, (gset_disj_alloc_empty_local_update _ {[ γsp1; γsp2 ]}).
    set_solver. }
  iModIntro. iSplitL "HR Hl HRs H●".
  { iModIntro. iExists b, ({[γsp1; γsp2]} ∪ γsps').
    iIntros "{$Hl $H●} HP". iSpecialize ("HRs" with "HP").
    iDestruct (big_sepS_delete with "HRs") as "[HR'' HRs]"; first done.
    iDestruct "HR''" as (R'') "[#Hsp' HR'']".
    iDestruct (saved_prop_agree with "Hsp Hsp'") as "#Heq".
    iAssert (▷ R')%I with "[HR'']" as "HR'"; [iNext; by iRewrite "Heq"|].
    iDestruct ("HR" with "HR'") as "[HR1 HR2]".
    iApply big_sepS_union; first set_solver. iFrame "HRs".
    iApply big_sepS_union; first set_solver.
    iSplitL "HR1"; rewrite big_sepS_singleton; eauto. }
  iModIntro; iSplitL "H◯1".
  - iExists γ, P, R1, γsp1. iFrame; auto.
  - iExists γ, P, R2, γsp2. iFrame; auto.
Qed.

Lemma recv_weaken l P1 P2 : (P1 -∗ P2) -∗ recv l P1 -∗ recv l P2.
Proof.
  iIntros "HP". iDestruct 1 as (γ P R' i) "(#Hinv & HR & H◯)".
  iExists γ, P, R', i. iIntros "{$Hinv $H◯} !> HQ". iApply "HP". by iApply "HR".
Qed.

End proof.

End goose_lang.

Typeclasses Opaque send recv.
