(** ShouldBuild depends on everything that should be regularly compiled (by
default using make as well as in CI). *)

From Perennial.algebra Require ghost_async_map.

From Perennial.goose_lang Require
     adequacy recovery_adequacy dist_adequacy
     crash_lock
     rwlock
     rwlock_derived
     barrier
     refinement refinement_adequacy
     logical_reln_adeq
     paper_proof
.
From Perennial.goose_lang.ffi Require async_disk async_disk_equiv.
From Perennial.program_proof Require
     wal.circ_proof_crash
     lockmap_proof
     crash_lockmap_proof
     wal.proof
     obj.obj_proof
     jrnl.jrnl_proof
     jrnl.sep_jrnl_recovery_proof
     jrnl_replication.jrnl_replication_proof
     txn.twophase_refinement_thm
     simple.proofs simple.example
     wp_to_wpc
.

From Perennial.program_proof.examples Require
     replicated_block_proof
     all_examples
.

From Perennial.tutorial Require
     ipm_extensions.

(* WIP slice library *)
From Perennial.goose_lang.lib Require
     slice.pred_slice.

(* goose output *)
From Goose.github_com.tchajed.goose.internal.examples Require
     semantics unittest comments simpledb logging2 rfc1813.

(* examples goose output *)
From Goose.github_com.mit_pdos Require
     dynamic_dir.

(* interpreter semantics tests *)
From Perennial.goose_lang.interpreter Require
     interpreter
     disk_interpreter
     generated_test.

(* ensures this file itself works for Coq's CI and catches any oversight where
something in the lite build isn't listed here *)
From Perennial Require LiteBuild.
