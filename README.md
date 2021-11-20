This is the Peony framework. The development is forked from Perennial 2.0, so
internal names still refer to the library as "perennial".

You can compile everything with

`make`

Though you probably want to do 

`make -j4` 

assuming you have a reasonable amount of RAM (>8gb).

It will take a long time to build because it also checks all of the Perennial 2.0 GoJournal
development for 

## Highlights:

The files prefixed `src/goose_lang/ffi/async_disk_` describe the different
async semantics, points-to facts for them, and an "equivalence" proof.

The files `src/program_proof/examples/async_mem_alloc_inode_proof.v` gives the
proof of the inode under the asynchronous semantics.

This is used in `src/program_proof/examples/async_mem_alloc_dir_proof.v` for
the directory proof.

In that same subfolder, `alloc_proof_simple.v` gives the allocator
specification discussed in the paper.
