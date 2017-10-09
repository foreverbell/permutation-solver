Require Import Coq.Arith.PeanoNat.
Require Import Coq.Classes.RelationClasses.
Require Export Coq.Lists.List.
Require Import Coq.Sets.Multiset.
Require Export Coq.Sorting.Permutation.
Require Import Coq.Sorting.PermutSetoid.
Require Import Coq.Sorting.PermutEq.
Require Import Omega.

Opaque Nat.eq_dec.

(** Refer to README.md for documentation. *)

(** (foreverbell): generalize to all decidable instances. *)

Lemma list_contents_app_multiplicity_plus :
  forall (a : nat) (l m : list nat),
    multiplicity (list_contents eq Nat.eq_dec (l ++ m)) a =
    multiplicity (list_contents eq Nat.eq_dec l) a +
    multiplicity (list_contents eq Nat.eq_dec m) a.
Proof.
  intros; specialize (list_contents_app eq Nat.eq_dec l m).
  intros. unfold meq, munion in H.
  specialize (H a); auto.
Qed.

Ltac permutation_simplify a (* variable for functional extensionality *) :=
  repeat
    match goal with
    | [ H : Permutation _ _ |- _ ] =>
        rewrite (permutation_Permutation Nat.eq_dec) in H;
        unfold permutation, meq in H;
        specialize (H a);
        repeat (
          simpl list_contents in H;
          unfold munion in H;
          simpl multiplicity in H;
          try rewrite list_contents_app_multiplicity_plus in H
        )
    | [ |- Permutation _ _ ] =>
        rewrite (permutation_Permutation Nat.eq_dec);
        unfold permutation, meq;
        intros a;
        repeat (
          simpl list_contents;
          unfold munion;
          simpl multiplicity;
          try rewrite list_contents_app_multiplicity_plus
        )
    end.

Ltac permutation_solver :=
  let a := fresh "a" in permutation_simplify a;
  repeat
    match goal with
    | [ |- context [if ?A then _ else _] ] => destruct A
    end; omega.
