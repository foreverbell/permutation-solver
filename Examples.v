Require Import PermutationSolver.

Parameter A : Set.
Axiom eq_dec : forall x y : A, {x = y} + {x <> y}.

Goal
  forall (a b c d e : list A) (x y : A),
    Permutation (a ++ e) (x :: c) ->
    Permutation b (y :: d) ->
    Permutation (a ++ b ++ e) (x :: y :: c ++ d).
Proof.
  intros; permutation_solver eq_dec.
Qed.

Notation "[ x ]" := (cons x nil).
Notation "[ x ; y ; .. ; z ]" := (cons x (cons y .. (cons z nil) ..)).

Goal
  forall (a b : list A) (x y : A),
    Permutation a b ->
    Permutation [x] [y] ->
    Permutation (a ++ [x]) (y :: b).
Proof.
  intros; permutation_solver eq_dec.
Qed.

Goal
  forall (b u t e r f l y : A) (xs ys : list A),
    Permutation xs ys ->
    Permutation ([b;u;t;t;e;r]++[f;l;y]++xs) ([f;l;u;t;t;e;r]++ys++[b;y]).
Proof.
  intros; permutation_solver eq_dec.
Qed.

(** Proving preorder, inorder and postorder of a BST are permutation of each
    other. *)
Inductive tree : Set :=
| Leaf : tree
| Node : tree -> A -> tree -> tree.

Fixpoint inorder (t : tree) : list A :=
  match t with
  | Leaf => nil
  | Node l v r => inorder l ++ v :: inorder r
  end.

Fixpoint preorder (t : tree) : list A :=
  match t with
  | Leaf => nil
  | Node l v r => v :: preorder l ++ preorder r
  end.

Fixpoint postorder (t : tree) : list A :=
  match t with
  | Leaf => nil
  | Node l v r => postorder l ++ postorder r ++ [v]
  end.

Theorem tree_orders :
  forall (t : tree),
    Permutation (inorder t) (preorder t) /\
    Permutation (inorder t) (postorder t).
Proof.
  induction t; simpl; intuition (permutation_solver eq_dec).
Qed.
