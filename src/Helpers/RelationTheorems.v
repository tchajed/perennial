Require Import Helpers.RelationAlgebra.
Require Import Helpers.RelationRewriting.

Import RelationNotations.

(*
Theorem seq_star_invariant A (r: relation A A unit) P :
  (test P;; r) ---> (test P;; r;; test P) ->
  (test P;; seq_star r) ---> (test P;; seq_star r;; test P).
Proof.
  intros.
  rewrite <- bind_assoc in H.
  apply simulation_seq in H.
  rewrite H.
  rewrite star_expand; norm.
  apply rel_or_elim_rx; norm.
  - setoid_rewrite <- seq_star_none; norm.
    rewrite test_idem; norm.
  - setoid_rewrite <- seq_star1 at 2; norm.
    setoid_rewrite test_to_id at 2; norm.
Qed.
*)

Fixpoint seq_rep_n {A T} (n: nat) (p: relation A A T) : relation A A T :=
  match n with
  | O => identity
  | S n' => p ;; seq_rep_n n' p
  end.

Fixpoint bind_rep_n {A T} (n: nat) (p: T -> relation A A T) (o: T) : relation A A T :=
  match n with
  | O => pure o
  | S n' => x <- p o; bind_rep_n n' p x
  end.

Fixpoint bind_rep_r_n {A T} (n: nat) (p: T -> relation A A T) (o: T) : relation A A T :=
  match n with
  | O => pure o
  | S n' => x <- bind_rep_r_n n' p o; p x
  end.

Lemma seq_star_inv_rep_n A T (p: relation A A T) a1 a2:
  seq_star p a1 a2 ->
  exists n, seq_rep_n n p a1 a2.
Proof.
  induction 1.
  - exists O. do 2 econstructor.
  - destruct IHseq_star as (n&?). exists (S n). destruct_return.
    * simpl. econstructor. do 2 eexists; intuition eauto.
    * simpl. right. do 2 eexists; intuition eauto.
  - exists 1. econstructor; eauto.
Qed.

Lemma bind_star_inv_rep_n A T (p: T -> relation A A T) (o: T) a1 a2:
  bind_star p o a1 a2 ->
  exists n, bind_rep_n n p o a1 a2.
Proof.
  induction 1.
  - exists O; firstorder.
  - destruct IHbind_star as (n&?). exists (S n). destruct_return.
    * simpl. do 2 eexists; intuition eauto.
    * simpl. right. do 2 eexists; intuition eauto.
  - exists 1. econstructor; eauto.
Qed.

Lemma bind_star_rep_n_to_bind_star A T (p: T -> relation A A T) (o: T) a1 a2 n:
  bind_rep_n n p o a1 a2 ->
  bind_star p o a1 a2.
Proof.
  revert o a1 a2. induction n; intros o a1 a2.
  - simpl. inversion 1; subst. apply bind_star_pure.
  - simpl. destruct_return.
    * intros (v&a'&?&?). econstructor; eauto.
    * intros [?|(?&?&?&?)].
      ** eapply bind_star_one_more_err; eauto.
      ** eapply bind_star_one_more_valid; eauto 10.
Qed.

Lemma seq_star_rep_n_ind {A1 A2 T1 T2} (p: relation A1 A2 T1) q (r: relation A1 A2 T2):
  (forall n, (p ;; seq_rep_n n q) ---> r) ->
  (p ;; seq_star q) ---> r.
Proof.
  intros.
  intros a1 a2 Hl.
  destruct_return.
  * destruct Hl as (t1&a2'&Hp&Hstar).
    eapply seq_star_inv_rep_n in Hstar as (n&?).
    eapply H; do 2 eexists; intuition eauto.
  * destruct Hl as [Hhd|(?&?&Hp&Hstar)].
    ** eapply (H O). left; eauto.
    ** eapply seq_star_inv_rep_n in Hstar as (n&?).
       eapply H. right. eauto.
Qed.

Lemma bind_star_rep_n_ind {A1 A2 T1} (p: relation A1 A2 T1) q (r: relation A1 A2 T1):
  (forall n, (o <- p; bind_rep_n n q o) ---> r) ->
  (o <- p; bind_star q o) ---> r.
Proof.
  intros.
  intros a1 a2 Hl.
  destruct_return.
  * destruct Hl as (t1&a2'&Hp&Hstar).
    eapply bind_star_inv_rep_n in Hstar as (n&?).
    eapply H; do 2 eexists; intuition eauto.
  * destruct Hl as [Hhd|(?&?&Hp&Hstar)].
    ** eapply (H O). left; eauto.
    ** eapply bind_star_inv_rep_n in Hstar as (n&?).
       eapply H. right. eauto.
Qed.

Lemma seq_star_alt A T r (x : A) (y: Return A T):
  seq_star r x y <-> (exists n, seq_rep_n n r x y).
Proof.
  split.
  - induction 1.
    * exists O. econstructor; eauto.
    * destruct IHseq_star as (n&Hseq).
      exists (S n). destruct_return.
      ** econstructor; eauto.
      ** right. eauto 10.
    * exists (S O). econstructor; eauto.
  - intros (n&Hseq). revert x y Hseq.
    induction n; intros x y Hseq.
    * inversion Hseq; subst; econstructor.
    * destruct_return.
      ** destruct Hseq as (t'&?&?&?).
         econstructor; eauto.
      ** destruct Hseq as [Hhd|(?&?&?&?)].
         *** eapply seq_star_one_more_err; eauto.
         *** eapply seq_star_one_more_valid; eauto.
Qed.

Lemma bind_rep_lr_n A T (r: T -> relation A A T) o n:
  bind_rep_n n r o <---> bind_rep_r_n n r o.
Proof.
  revert o. induction n; intros o.
  { reflexivity. }
  simpl. setoid_rewrite IHn. clear.
  induction n.
  - simpl. rew bind_right_id.
  - simpl. rew<- IHn.
Qed.

Lemma bind_star_alt A T r (x : A) o (y: Return A T):
  bind_star r o x y <-> (exists n, bind_rep_n n r o x y).
Proof.
  split.
  - induction 1.
    * exists O. econstructor; eauto.
    * destruct IHbind_star as (n&Hseq).
      exists (S n). destruct_return.
      ** econstructor; eauto.
      ** right. eauto 10.
    * exists (S O). econstructor; eauto.
  - intros (n&Hseq). revert o x y Hseq.
    induction n; intros o x y Hseq.
    * inversion Hseq; subst; econstructor.
    * destruct_return.
      ** destruct Hseq as (t'&?&?&?).
         eapply bind_star_one_more_valid; eauto.
      ** destruct Hseq as [Hhd|(?&?&?&?)].
         *** eapply bind_star_one_more_err; eauto.
         *** eapply bind_star_one_more_valid; eauto.
Qed.

Lemma seq_star_mid_invariant A (p: relation A A unit) (q: relation A A unit) P:
  (test P;; p) ---> (q ;; test P) ->
  (q;; seq_star q) ---> q ->
  (q;; test P;; seq_star p) ---> (q;; test P).
Proof.
  intros Hinv Htrans.
  setoid_rewrite <-bind_assoc.
  apply seq_star_rep_n_ind.
  induction n.
  - simpl. rewrite bind_assoc.
    setoid_rewrite unit_identity.
    setoid_rewrite bind_right_id_unit.
    reflexivity.
  - simpl. setoid_rewrite bind_assoc.
    setoid_rewrite <-bind_assoc at 2.
    setoid_rewrite Hinv.
    setoid_rewrite IHn.
    setoid_rewrite <-bind_assoc.
    setoid_rewrite <-(seq_star1) in Htrans.
    setoid_rewrite <-(seq_star_none) in Htrans.
    setoid_rewrite unit_identity in Htrans.
    setoid_rewrite bind_right_id_unit in Htrans.
    rew Htrans.
Qed.

Lemma any_seq_star_any A T:
  (@any A A T;; seq_star (@any A A T)) ---> any.
Proof.
  eapply seq_star_rep_n_ind.
  induction n; simpl.
  - firstorder.
  - setoid_rewrite IHn.
    apply any_idem.
Qed.

Theorem bind_star_ind_r A B T1 (q x: relation A B T1) (p: T1 -> relation B B T1) :
  q + and_then x p ---> x ->
  and_then q (bind_star p) ---> x.
Proof.
  intros Himpl.
  assert (q ---> x) as ->.
  { rew<- Himpl. Left. }
  assert (and_then x p ---> x) as Himpl'.
  { setoid_rewrite <-Himpl at 2. Right. }
  eapply bind_star_rep_n_ind. intros n.
  induction n.
  - simpl. rew bind_right_id.
  - simpl. setoid_rewrite <-bind_assoc. rew Himpl'. eauto.
Qed.

Theorem bind_star_ind_r_pure A T1 t (x: relation A A T1) (p: T1 -> relation A A T1):
  (pure t) + and_then x p ---> x ->
  bind_star p t ---> x.
Proof.
  specialize (@bind_star_ind_r A A _ (pure t) x p).
  setoid_rewrite bind_left_id; auto.
Qed.

Theorem simulation_seq A B
        (p: relation A B unit)
        (q: relation B B unit)
        (r: relation A A unit) :
  (p;; q) ---> (r;; p) ->
  (p;; seq_star q) ---> (seq_star r;; p).
Proof.
  intros Hconv.
  apply seq_star_rep_n_ind. intros n.

  induction n. simpl.
  - setoid_rewrite <-seq_star_none.
    rew unit_identity.
    rew bind_right_id_unit.
  - simpl.
    setoid_rewrite <-bind_assoc.
    rew Hconv. rew IHn.
    setoid_rewrite <-bind_assoc.
    setoid_rewrite seq_star_fold; reflexivity.
Qed.

Theorem simulation_seq_value A B T
        (p: relation A B unit)
        (q: relation B B T)
        (r: relation A A T) :
  (p;; q) ---> (v <- r; (p;; pure v)) ->
  (p;; seq_star q) ---> (v <- seq_star r; (p;; pure v)).
Proof.
Admitted.
(*
  intros Hconv.
  apply seq_star_rep_n_ind. intros n.

  induction n. simpl.
  - setoid_rewrite <-seq_star_none.
    rew unit_identity.
    rew bind_right_id_unit.
  - simpl.
    setoid_rewrite <-bind_assoc.
    rew Hconv. rew IHn.
    setoid_rewrite <-bind_assoc.
    setoid_rewrite seq_star_fold; reflexivity.
  setoid_rewrite seq_star_lr.
  t.
  induction H1; propositional.
  - eauto 15.
  - repeat match goal with
           | [ u: unit |- _ ] => destruct u
           end.
    unfold rimpl in H; simpl in *.
    specialize (H y0 z o2).
    match type of H with
    | ?P -> ?Q =>
      let HP := fresh in
      assert P as HP;
        [ | specialize (H HP) ]
    end; eauto; propositional.
    eauto 15.

    Grab Existential Variables.
    all: auto.
Qed.
*)