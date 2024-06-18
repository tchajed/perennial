From Perennial.goose_lang Require Import notation.
From Perennial.new_goose_lang.lib Require Import mem.impl.
From Perennial.goose_lang.lib Require Import control.impl.

Module slice.
Section goose_lang.
Context `{ffi_syntax}.

Local Coercion Var' s: expr := Var s.
Definition len : val := λ: "s", Snd (Fst "s").
Definition cap : val := λ: "s", Snd "s".

Definition make3 t : val :=
  λ: "sz" "cap",
  if: "cap" < "sz" then Panic "NewSlice with cap smaller than len"
  else let: "p" := AllocN "cap" (zero_val t) in
       (Var "p", Var "sz", Var "cap").

Definition make2 t : val :=
  λ: "sz", make3 t "sz" "sz".

Definition copy t : val :=
  λ: "dst" "src",
  (* take the minimum *)
  let: "n" := (if: len "dst" < len "src" then len "dst" else len "src") in
  (rec: "copy_aux" "dst" "src" "n" :=
    if: "n" = #0
    then #()
    else "dst" <-[t] (![t] "src");;
         "copy_aux" (BinOp (OffsetOp (go_type_size t)) "dst" #1)
                  (BinOp (OffsetOp (go_type_size t)) "src" #1)
                  ("n" - #1)) "n".

(* computes `&s[i]` (which looks a little like a get but is very different) *)
Definition ref_elem t : val :=
  λ: "s" "i", if: "i" < len "s"
              then (Fst (Fst "s") +ₗ[t] "i")
              else Panic "slice index out-of-bounds".

(* TODO: function that takes an array/list as input to construct a slice with multiple elements *)

Definition slice t: val :=
  λ: "a" "low" "high",
  if: (#0 ≤ "low") && ("low" < "high") && ("high" < len "a") then
    ((Fst $ Fst "s") +ₗ[t] "low", "high" - "low", cap "s" - "low")
  else Panic "slice indices out of order"
.

(*
Definition append t : val :=
  λ: "s" "x",
  let: "s" := ref_to (slice.T t) "s1" in
  ForSlice t <> "x" "s2"
    ("s" <-[slice.T t] (SliceAppend t (![slice.T t] "s") "x"));;
  ![slice.T t] "s". *)

End goose_lang.
End slice.
