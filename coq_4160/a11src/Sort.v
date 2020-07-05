(** * Sort: Insertion Sort *)

(** Sorting can be done in expected O(N log N) time by various
    algorithms (quicksort, mergesort, heapsort, etc.).  But for
    smallish inputs, a simple quadratic-time algorithm such as
    insertion sort can actually be faster.  It's certainly easier to
    implement -- and to verify. *)

(** If you don't recall insertion sort or haven't seen it in
    awhile, see Wikipedia or read any standard textbook; for example:

    - Sections 2.0 and 2.1 of _Algorithms, Fourth Edition_, by
      Sedgewick and Wayne, Addison Wesley 2011; or

    - Section 2.1 of _Introduction to Algorithms, 3rd Edition_, by
      Cormen, Leiserson, and Rivest, MIT Press 2009. *)

From VFA Require Import Perm.

(* ################################################################# *)
(** * The Insertion-Sort Program *)

(** Insertion sort is usually presented as an imperative program
    operating on arrays.  But it works just as well as a functional
    program operating on linked lists. *)

(* [insert i l] inserts [i] into its sorted place in list [l].
   Precondition: [l] is sorted. *)
Fixpoint insert (i : nat) (l : list nat) :=
  match l with
  | [] => [i]
  | h :: t => if i <=? h then i :: h :: t else h :: insert i t
  end.

Fixpoint sort (l : list nat) : list nat :=
  match l with
  | [] => []
  | h :: t => insert h (sort t)
  end.

Example sort_pi :
  sort [3;1;4;1;5;9;2;6;5;3;5]
  = [1;1;2;3;3;4;5;5;5;6;9].
Proof. simpl. reflexivity. Qed.


(** We won't analyze or prove anything about the efficiency of
    [sort]. Instead, we will verify its correctness: that it produces
    the correct output for a given input. *)

(* ################################################################# *)
(** * Specification of Correctness *)

(** A sorting algorithm must rearrange the elements into a list
    that is totally ordered. There are many ways we might express that
    idea formally in Coq.  One is with an inductively-defined
    relatio that says: *)

(** - The empty list is sorted.

    - Any single-element list is sorted.

    - For any two adjacent elements, they must be in the proper order. *)

Inductive sorted: list nat -> Prop :=
| sorted_nil:
    sorted []
| sorted_1: forall x,
    sorted [x]
| sorted_cons: forall x y l,
    x <= y -> sorted (y :: l) -> sorted (x :: y :: l).

Hint Constructors sorted.

(** This definition might not be the most obvious. Another definition,
    perhaps more familiar, might be: for any two elements of the list
    (regardless of whether they are adjacent), they should be in the
    proper order.  Let's try formalizing that.

    We can think in terms of indices into a list [lst], and say: for
    any valid indices [i] and [j], if [i < j] then [index lst i <=
    index lst j], where [index lst n] means the element of [lst] at
    index [n].  Unfortunately, formalizing this idea becomes messy,
    because any Coq implementing [index] must be total: it must return
    some result even if the index is out of range for the list.
    The Coq standard library contains two such functions: *)

Check nth : forall A : Type, nat -> list A -> A -> A.
Check nth_error : forall A : Type, list A -> nat -> option A.

(** These two functions ensure totality in different ways:

    - [nth] takes an additional argument of type [A] --a _default_
      value-- to be returned if the index is out of range, whereas

    - [nth_error] returns [Some v] if the index is in range and [None]
      --an error-- otherwise.

    If we use [nth], we must ensure that indices are in range: *)

Definition sorted'' (al: list nat) := forall i j,
    i < j < length al ->
    nth i al 0 <= nth j al 0.

(** The choice of default value, here 0, is unimportant, because it
    will never be returned for the [i] and [j] we pass.

    If we use [nth_error], we must add additional antecedents: *)

Definition sorted' (al: list nat) := forall i j iv jv,
    i < j ->
    nth_error al i = Some iv ->
    nth_error al j = Some jv ->
    iv <= jv.

(** Here, the validity of [i] and [j] are implicit in the fact that we
    get [Some] results back from each call to [nth_error].

    All three definitions of sortedness we have given are reasonable.
    In practice, [sorted'] is easier to work with than [sorted'']
    because it doesn't need to mention the [length] function. And
    [sorted] is easier than either.  *)

(** Using [sorted], we specify what it means to be a correct sorting
    algorthm: *)

Definition is_a_sorting_algorithm (f: list nat -> list nat) := forall al,
    Permutation al (f al) /\ sorted (f al).

(** Function [f] is a correct sorting algorithm if [f al] is
    [sorted] and is a permutation of its input. *)

(* ################################################################# *)
(** * Proof of Correctness *)

(** In the following exercises, you will prove the correctness of
    insertion sort. *)

(** **** Exercise: 3 stars, standard (insert_sorted)  *)

(* Prove that insertion maintains sortedness. Make use of tactic
   [bdestruct], defined in [Perm]. *)

Lemma insert_sorted:
  forall a l, sorted l -> sorted (insert a l).
Proof.
  intros a l S. induction S; simpl.
  (* SOLUTION: *)
  - constructor.
  - bdestruct (x >=? a); auto.
    constructor; auto. omega.
  - bdestruct (x >=? a); auto.
    bdestruct (y >=? a).
    + constructor; auto. omega.
    + constructor; auto.
      simpl in IHS. bdestruct (y >=? a); auto. omega.
Qed.

(** [] *)

(** **** Exercise: 2 stars, standard (sort_sorted)  *)

(** Using [insert_sorted], prove that insertion sort makes a list
    sorted. *)

Theorem sort_sorted: forall l, sorted (sort l).
Proof.
(* SOLUTION: *)
  induction l; simpl; auto.
  apply insert_sorted. auto.
Qed.

(** [] *)

(** **** Exercise: 3 stars, standard (insert_perm)  *)

(** The following lemma will be useful soon as a helper. Take
    advantage of helpful theorems from the [Permutation] library. *)

Lemma insert_perm: forall x l,
    Permutation (x :: l) (insert x l).
Proof.
  (* SOLUTION: *)
  induction l; simpl.
  - apply Permutation_refl.
  - destruct (x <=? a).
    + apply Permutation_refl.
    + apply perm_trans with (a :: x :: l).
      * apply perm_swap.
      * apply perm_skip. assumption.
Qed.

(** [] *)

(** **** Exercise: 3 stars, standard (sort_perm)  *)

(** Prove that [sort] is a permutation, using [insert_perm]. *)

Theorem sort_perm: forall l, Permutation l (sort l).
Proof.
(* SOLUTION: *)
  induction l.
  - apply Permutation_refl.
  - simpl. apply Permutation_trans with (a :: (sort l)).
    + apply perm_skip. assumption.
    + apply insert_perm.
Qed.

(** [] *)

(** **** Exercise: 1 star, standard (insertion_sort_correct)  *)

(** Finish the proof of correctness! *)

Theorem insertion_sort_correct:
    is_a_sorting_algorithm sort.
Proof.
  (* SOLUTION: *)
  split.
  - apply sort_perm.
  - apply sort_sorted.
Qed.

(** [] *)

(* ################################################################# *)
(** * Validating the Specification (Advanced) *)

(** You can prove that a program satisfies a specification, but how
    can you prove you have the right specification?  Actually, you
    cannot.  The specification is an informal requirement in your
    mind.  As Alan Perlis quipped, "One can't proceed from the
    informal to the formal by formal means."

    But one way to build confidence in a specification is to state it
    in two different ways, then prove they are equivalent. *)

(** **** Exercise: 4 stars, advanced (sorted_sorted')  *)
Lemma sorted_sorted': forall al, sorted al -> sorted' al.

(** Hint: Instead of doing induction on the list [al], do induction on
    the sortedness of [al]. This proof is a bit tricky, so you may
    have to think about how to approach it, and try out one or two
    different ideas.*)
Proof.
(* SOLUTION: *)
  unfold sorted'; induction 1; intros i j iv jv LT Hi Hj.
  - destruct i; inv Hi.
  - destruct j as [|j'].
    + omega.
    + destruct j'; inv Hj.
  - destruct j as [|j'].
    + omega.
    + destruct i as [|i'].
      * inv Hi.
        destruct j' as [|j''].
        -- inv Hj.  auto.
        -- apply le_trans with y. auto.
            eapply (IHsorted 0 (S j'')). omega. auto. auto.
      * apply (IHsorted i' j'). omega. auto. auto. Qed.
(** [] *)

(** **** Exercise: 3 stars, advanced (sorted'_sorted)  *)
Lemma sorted'_sorted : forall al, sorted' al -> sorted al.
Proof.
(** Here, you can't do induction on the sortedness of the list,
    because [sorted'] is not an inductive predicate. But the proof
    is not hard. *)
(* SOLUTION: *)
  unfold sorted'. induction al; intros.
  - constructor.
  - destruct al.
    + constructor.
    + constructor.
      * eapply (H 0 1). omega. auto. auto.
      * apply IHal. intros.
        apply (H (S i) (S j)). omega. auto. auto. Qed.
(** [] *)

(* ################################################################# *)
(** * Proving Correctness from the Alternative Spec (Optional) *)

(** Depending on how you write the specification of a program, it can
    be harder or easier to prove correctness.  We saw that predicates
    [sorted] and [sorted'] are equivalent.  It is significantly
    harder, though, to prove correctness of insertion sort directly
    from [sorted'].

    Give it a try!  The best proof we know of makes essential use of
    the auxiliary lemma [nth_default_insert], so you may want to prove
    that first.  And some other auxiliary lemmas may be needed too.
    But maybe you will find a simpler appraoch!

    DO NOT USE [sorted_sorted'], [sorted'_sorted], [insert_sorted], or
    [sort_sorted] in these proofs.  That would defeat the purpose! *)

(** **** Exercise: 5 stars, standard, optional (insert_sorted')  *)

Lemma nth_error_insert : forall l a i iv,
    nth_error (insert a l) i = Some iv ->
    a = iv \/ exists i', nth_error l i' = Some iv.
Proof.
(* SOLUTION: *)
 induction l; intros.
 - inv H. destruct i as [|i'].
   + inv H1. auto.
   + inv H1. destruct i'; inv H0.
 - simpl in H.
   bdestruct (a0 <=? a).
   + destruct i as [|i'].
     * inv H. auto.
     * simpl in H. right. eauto.
   + destruct i as [|i'].
     * right. exists 0. auto.
     * simpl in H. destruct (IHl _ _ _ H) as [P|[i'' P]].
       -- auto.
       -- right; exists (S i''); auto. Qed.

Lemma insert_length: forall a l, length (insert a l) = S(length l).
Proof.
  intros a l. induction l.
  - auto.
  - simpl. destruct (a <=? a0).
    + auto.
    + simpl. rewrite IHl.  auto. Qed.

Lemma insert_sorted':
  forall a l, sorted' l -> sorted' (insert a l).
Proof.
(* SOLUTION: *)
  intros a l. generalize dependent a.
  induction l; intros a0 H i j iv jv LT Hi Hj.
  - simpl in Hi, Hj.
    destruct j as [|j'].
    + inversion LT.
    + inversion Hj as [C].
      destruct j'; inversion C.
  - simpl in Hi, Hj.
    destruct j as [|j'].  omega.
    bdestruct (a0 <=? a).
    + destruct i as [|i'].
      * inv Hi.
        apply le_trans with a. auto.
        simpl in Hj.
        destruct j' as [|j''].
        -- inv Hj. omega.
        -- apply (H 0 (S j'')); auto; omega.
      * apply (H i' j'); auto; omega.
    + destruct i as [|i'].
      * inv Hi. simpl in Hj.
        destruct (nth_error_insert _ _ _ _ Hj) as [P | [i' P]].
        -- omega.
        -- apply (H 0 (S i')); auto; omega.
      * eapply IHl with (a := a0) (i := i') (j:= j'); auto; try omega.
        intros i j iv0 jv0 LT0 Hi0 Hj0.
        apply (H (S i) (S j)); auto; omega.
Qed.
(** [] *)

Theorem sort_sorted': forall l, sorted' (sort l).
Proof.
  induction l.
  - unfold sorted'. intros. destruct i; inv H0.
  - simpl. apply insert_sorted'. auto.
Qed.

(** If you complete the proofs above, you will note that the proof of
    [insert_sorted] is relatively easy compared to the proof of
    [insert_sorted'], even though [sorted al <-> sorted' al].  So,
    suppose someone asked you to prove [sort_sorted'].  Instead of
    proving it directly, it would be much easier to design predicate
    [sorted], then prove [sort_sorted] and [sorted_sorted'].

    The moral of the story is therefore: _Different formulations of
    the functional specification can lead to great differences in the
    difficulty of the correctness proofs_. *)


(* Sun May 3 17:29:21 EDT 2020 *)
