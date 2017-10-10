Require Import PermutationSolver.

Goal
  forall (a b c d e : list nat) (x y : nat),
    Permutation (a ++ e) (x :: c) ->
    Permutation b (y :: d) ->
    Permutation (a ++ b ++ e) (x :: y :: c ++ d).
Proof.
  intros; permutation_solver.
Qed.

Notation "[ x ]" := (cons x nil).
Notation "[ x ; y ; .. ; z ]" := (cons x (cons y .. (cons z nil) ..)).

Goal
  forall (a b : list nat) (x y : nat),
    Permutation a b ->
    Permutation [x] [y] ->
    Permutation (a ++ [x]) (y :: b).
Proof.
  intros; permutation_solver.
Qed.

Goal
  forall (b u t e r f l y : nat) (xs ys : list nat),
    Permutation xs ys ->
    Permutation ([b;u;t;t;e;r]++[f;l;y]++xs) ([f;l;u;t;t;e;r]++ys++[b;y]).
Proof.
  intros; permutation_solver.
Qed.