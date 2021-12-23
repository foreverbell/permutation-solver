Require Import Coq.Arith.PeanoNat.
Require Import Coq.Classes.RelationClasses.
Require Export Coq.Lists.List.
Require Import Coq.Sets.Multiset.
Require Export Coq.Sorting.Permutation.
Require Import Coq.Sorting.PermutSetoid.
Require Import Coq.Sorting.PermutEq.
Require Import Omega.

(** Refer to README.md for documentation. *)

Lemma list_contents_app_multiplicity_plus {A} Hdec :
  forall (a : A) (l m : list A),
    multiplicity (list_contents eq Hdec (l ++ m)) a =
    multiplicity (list_contents eq Hdec l) a +
    multiplicity (list_contents eq Hdec m) a.
Proof.
  intros; specialize (list_contents_app eq Hdec l m).
  intros. unfold meq, munion in H.
  specialize (H a); auto.
Qed.

Ltac permutation_simplify Hdec a (* variable for functional extensionality *) :=
  repeat
    match goal with
    | [ H : Permutation _ _ |- _ ] =>
        rewrite (permutation_Permutation Hdec) in H;
        unfold permutation, meq in H;
        specialize (H a);
        repeat (
          simpl list_contents in H;
          unfold munion in H;
          simpl multiplicity in H;
          try rewrite (list_contents_app_multiplicity_plus Hdec) in H
        )
    | [ |- Permutation _ _ ] =>
        rewrite (permutation_Permutation Hdec);
        unfold permutation, meq;
        intros a;
        repeat (
          simpl list_contents;
          unfold munion;
          simpl multiplicity;
          try rewrite (list_contents_app_multiplicity_plus Hdec)
        )
    end.

Ltac permutation_solver Hdec :=
  let a := fresh "a" in permutation_simplify Hdec a;
  repeat
    match goal with
    | [ |- context [if ?A then _ else _] ] => destruct A
    end; omega.
