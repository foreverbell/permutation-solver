From Coq Require Export List Permutation.
From Coq Require Import Lia.

(** Refer to README.md for documentation. *)

#[local] Ltac permutation_simplify Hdec a (* variable for functional extensionality *) :=
  repeat match goal with
  | |- Permutation _ _ => rewrite (Permutation_count_occ Hdec); intros a;
                          repeat (cbn; rewrite ? count_occ_app)
  | H : Permutation _ _ |- _ => rewrite (Permutation_count_occ Hdec) in H; specialize (H a);
                                repeat (cbn in H; rewrite ? count_occ_app in H)
  end.

Ltac permutation_solver Hdec :=
  let a := fresh "a" in permutation_simplify Hdec a;
  repeat match goal with
  | |- context[if ?A then _ else _] => destruct A
  end; lia.
