# permutation-solver

A tactics for solving goals about permutation in Coq proof assistant.

## Motivation

When I was attacking the problems in [Verified Functional Algorithms](https://softwarefoundations.cis.upenn.edu/vfa-current/index.html)
by Andrew W. Appel, I constantly found that I need to prove some theorems
about [Permutation](https://coq.inria.fr/distrib/current/stdlib/Coq.Sorting.Permutation.html).

A typical example should be,

```coq
Example butterfly : forall b u t e r f l y : nat,
  Permutation ([b;u;t;t;e;r]++[f;l;y]) ([f;l;u;t;t;e;r]++[b;y]).
```

This theorem should be trivial in a very first glance, but proving it in Coq
turns out to be rather tedious. Coq defines permutation in terms of swapping
adjencent elements, so you need to find an element-swapping order to solve this
goal. This kind of proof method is boring and lengthy to develop.

## Idea

Here, the basic idea is, two lists are considered as permutation of each other,
if and only if all elements have the same multiplicity in both lists. This
property is proven as [a part of Coq's standard library](https://github.com/coq/coq/blob/19a8c5723625dbf49890f17858d330eb2f5ba94d/theories/Sorting/Permutation.v#L540).

With this theorem, we transform the problem of proving permutation to simple
multiplicity calculation, which is easy to be automated via `lia` tactics in
Coq.

## Implementation

Provide a tactics `permutation_solver` to attack permutations, which turns
all Permutations in hypotheses and goals to multiplicity calculation.
Using it is rather simple.
It relies on a proof of decidability of equality for the type of the elements
of the lists.

```coq
Goal
  forall (a b c d e : list nat) (x y : nat),
    Permutation (a ++ e) (x :: c) ->
    Permutation b (y :: d) ->
    Permutation (a ++ b ++ e) (x :: y :: c ++ d).
Proof.
  intros; permutation_solver Nat.eq_dec.
Qed.
```
