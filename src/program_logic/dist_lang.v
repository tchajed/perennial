(** Defines the notion of a "distributed execution with crashes", and some
derived notions/lemmas. *)
From Perennial.program_logic Require Export language crash_lang.
From iris.prelude Require Import options.

Section dist_language.
  Context {Λ: language}.
  Context {CS: crash_semantics Λ}.

  Definition dist_cfg (nm : nat) : Type :=
    vec (list (expr Λ) * state Λ) nm * global_state Λ.

  (** A step of the distributed system is parameterized by the number of
  machines and their respective "boot code", i.e., recovery procedure. *)
  Inductive dist_step (nm : nat) (boot : vec (expr Λ) nm) :
    dist_cfg nm → list (observation Λ) → dist_cfg nm → Prop :=
  | dist_step_machine ρ1 κs ρ2 m e1 σ1 e2 σ2 efs t1 t2 :
      ρ1.1 !!! m = (t1 ++ e1 :: t2, σ1) →
      ρ2.1 = vinsert m (t1 ++ e2 :: t2 ++ efs, σ2) ρ1.1 →
      prim_step e1 σ1 ρ1.2 κs e2 σ2 ρ2.2 efs →
      dist_step nm boot ρ1 κs ρ2
  | dist_step_crash ρ1 κs ρ2 m σ1 σ2 :
      (ρ1.1 !!! m).2 = σ1 →
      ρ2.1 = vinsert m ([boot !!! m], σ2) ρ1.1 →
      ρ2.2 = ρ1.2 →
      crash_prim_step CS σ1 σ2 →
      dist_step nm boot ρ1 κs ρ2.

End dist_language.
