From Perennial.program_proof Require Import proof_prelude.
From Goose.github_com Require Import tchajed.simplefs.directory.

From Perennial.program_proof Require Import disk_prelude.
From Perennial.goose_lang.lib Require Import typed_slice.

Coercion LitString : string >-> base_lit.

Set Default Proof Using "Type".

Record dir_ent :=
  mk_dir_ent
    { path: string;
      inum: w64; }.

Section proof.
Context `{!heapGS Σ}.

Definition dir_ent_val (e: dir_ent) : val :=
  (#e.(path), (#e.(inum), #())).

Definition dir_ent_from_val (v: val): option dir_ent :=
  match v with
  | ((LitV (LitString p)), (LitV (LitInt i), #()))%V =>
      Some (mk_dir_ent p i)
  | _ => None
  end.

#[global] Instance dir_ent_IntoVal : IntoVal dir_ent.
Proof.
  refine {| to_val := dir_ent_val;
           from_val := dir_ent_from_val;
           IntoVal_def := (mk_dir_ent "" (W64 0));
         |}.
  abstract (destruct v; reflexivity).
Defined.

End proof.
