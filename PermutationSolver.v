Require Import Coq.Arith.PeanoNat.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Lists.List.
Require Import Coq.Sets.Multiset.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Sorting.PermutSetoid.
Require Import Coq.Sorting.PermutEq.
Require Import Omega.

Opaque Nat.eq_dec.

(** (foreverbell): generalize to all decidable instances. *)
(** (foreverbell): document some brief ideas. *)

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

(** Examples / Tests. *)

Example permutation_1 :
  forall (a b c d e : list nat) (x y : nat),
    Permutation (a ++ e) (x :: c) ->
    Permutation b (y :: d) ->
    Permutation (a ++ b ++ e) (x :: y :: c ++ d).
Proof.
  intros; permutation_solver.
Qed.

Notation "[ x ]" := (cons x nil).
Notation "[ x ; y ; .. ; z ]" := (cons x (cons y .. (cons z nil) ..)).

Example permutation_2 :
  forall (a b : list nat) (x y : nat),
    Permutation a b ->
    Permutation [x] [y] ->
    Permutation (a ++ [x]) (y :: b).
Proof.
  intros; permutation_solver.
Qed.

Example permutation_butterfly :
  forall (b u t e r f l y : nat) (xs ys : list nat),
    Permutation xs ys ->
    Permutation ([b;u;t;t;e;r]++[f;l;y]++xs) ([f;l;u;t;t;e;r]++ys++[b;y]).
Proof.
  intros; permutation_solver.
Qed.