(** * Prelim: CS 4160 Spring 2020 *)

Require Import List Nat.
Import ListNotations.

(** * Instructions

    - Regarding Academic Integrity: Your work is to be entirely your
      own. You may not collaborate with anyone. You may not discuss
      the contents of the exam with anyone other than the current
      semester's course staff. You are welcome to consult the course
      website and any resources that it links, including _Software
      Foundations_ (SF) and the Coq website. You are also welcome to
      consult your own homework solutions as well as the official
      solutions posted in CMS. Any other resources you consult must be
      cited and must be of a general nature about Coq, not a specific
      nature about the content of a problem. You do not need to cite
      the textbook, your solutions, or the official solutions.

    - If you have questions, please make a private post on Campuswire;
      please do not direct-message any of the course staff. Because
      this is an exam, the course staff will not provide any hints.

    - Start early, and keep a frequent backup of your solution ---
      perhaps in Dropbox, Time Machine, or a private Github repo.

    - If you have technical difficulties with your own machine, recall
      that Coq can be used on the undergraduate Linux cluster, as
      described here:
      https://www.cs.cornell.edu/courses/cs4160/2020sp/install_coq.html

    - There will be no makeups nor extensions. If an emergency
      situation arises, email the professor directly.

    - There will be a CMS grace period of around an hour or two. That
      is long enough to locate another computer and upload your backup
      if you run into any last-minute technical issues (computer
      crashes, home network outages, etc.)  We are avoiding stating
      the exact length of the grace period, so that no one falls into
      the trap of treating it as the actual deadline.

    - Double check before the deadline that the version of the file
      recorded by CMS is the version of the file you intended to
      submit.

    - This file will be graded in the same way as assignments from SF
      have been graded, which is to say, mostly with an autograder. It
      is therefore essential that your solution compiles with [make].
      Specifically, [make] must succeed at building both [Prelim.vo]
      and [PrelimTest.vo]. Solutions that do not compile will be
      penalized as assignments have been.

    - You are always welcome to introduce helper functions and lemmas.
      Changing [Fixpoint] to [Definition] and vice-versa is likewise
      allowed.

    - You may not add any [Require] statements to this file, nor
      change any already provided.

    - This file does not import any of the SF files. But, the standard
      library provides many of the same theorems that SF proves about
      arithmetic with [nat], such as [plus_n_O] and [plus_n_Sm]. You
      don't have to [Require] anything to get access to those. You are
      welcome to use anything accessible from the standard library, as
      long as you do not add any [Require] statements.

    - Please track the time you spend on the exam. We ask you to
      report it in the final exercise. We'll make a statistical
      summary available after the exam. *)

(* ################################################################# *)
(** * Problem 1: Programming and Proving in Coq *)

(** We've seen how Coq defines the natural numbers with a unary
    representation, and in [Basics.v] we defined a type [bin] to
    represent natural numbers in binary. In this problem, we'll
    explore a _balanced ternary_ representation of the integers.
    Donald Knuth calls it "perhaps the prettiest number system of all"
    [The Art of Computer Programming, vol. 2, second edition (1981),
    p. 190].

    This system has the interesting feature that all integers, whether
    positive or negative, can be represented uniquely (up to leading
    zeroes) without an explicit minus sign.

    See also https://en.wikipedia.org/wiki/Balanced_ternary. *)

(* ================================================================= *)
(** ** Balanced Ternary *)

(** Type [int], defined below, represents the integers in balanced
    ternary:

    - [Z] represents [0]

    - [T_zero n] represents [3n]

    - [T_pos n] represents [3n + 1]

    - [T_neg n] represents [3n - 1]
 *)

Inductive int : Type :=
  | Z : int
  | T_zero (n : int) : int
  | T_pos (n : int) : int
  | T_neg (n : int) : int.

(** Here are a few examples of integers represented with type [int]. *)

Definition z__zero : int := Z.
Definition z__one : int := T_pos Z.
Definition z__two : int := T_neg (T_pos Z).
Definition z__three : int := T_zero (T_pos Z).
Definition z__four : int := T_pos (T_pos Z).
Definition z__negone : int := T_neg Z.
Definition z__negtwo : int := T_pos (T_neg Z).
Definition z__negthree : int := T_zero (T_neg Z).
Definition z__negfour : int := T_neg (T_neg Z).

(** **** Exercise: 2 stars, standard (incr)  *)

(** Complete the definition of [incr], which increments an integer
    [n].  Your solution's running time must be [O(log n)], not
    [O(n)]. That is, converting [n] to unary then back to balanced
    ternary is not permitted. *)

Fixpoint incr (n : int) : int
 := match n with
  | Z => T_pos Z
  | T_zero n'  => T_pos n'
  | T_neg Z => Z
  | T_pos n' => T_neg (incr n')
  | T_neg n' => T_zero n'
  end.

(** The following "unit tests" should be provable simply with
    [reflexivity] after you have defined [incr] correctly. *)
Example test_incr_tern1 : incr z__zero = z__one.
Proof. simpl. reflexivity. Qed.
Example test_incr_tern2 : incr z__three = z__four.
Proof. simpl. reflexivity. Qed.
Example test_incr_tern3 : incr z__one = z__two.
Proof. simpl. reflexivity. Qed.
Example test_incr_tern4 : incr z__negfour = z__negthree.
Proof. simpl. reflexivity. Qed.

(** [] *)

(** Like type [bin] from [Basics.v], type [int] can represent zero
    with multiple values: [Z] is the usual representation, but [T_zero
    Z], [T_zero (T_zero Z)], etc. are also possible.  Having such
    _leading zeroes_ would lead to unnecessary complications.

    So as a _representation invariant_ we require that no [int]
    contains the subterm [T_zero Z].  Every function we write in this
    problem therefore:

    - may assume as a precondition that any [int] inputs are valid
      according to that invariant, and

    - must guarantee as a postcondition that any [int] output are also
      valid.  *)

(** **** Exercise: 1 star, standard (rep_invariant)  *)

(** Revisit your definition of [incr] to make sure it enforces that
    postcondition. In particular, incrementing -1 should produce [Z],
    not [T_zero Z].  If you have it right, the unit test below should
    be provable simply with [reflexivity]. *)

Example test_incr_tern5 : incr z__negone = z__zero.
Proof. simpl. reflexivity. Qed.

(** [] *)

(* ================================================================= *)
(** ** Conversions and Homomorphisms *)

(** **** Exercise: 2 stars, standard (convert_int_nat)  *)

(** Complete the definitions of functions [int_of_nat] and
    [nat_of_int] to convert between [int] and Coq's [nat] type, i.e.,
    between balanced ternary and unary representations. The asympotic
    efficiency of these functions is not a concern.

    CHANGED 3/2/20 6:30 pm: you do not need to "round up" negative
    integers to zero in [nat_of_int].  It is now unspecified what to
    do with them. *)

Fixpoint int_of_nat (n : nat) : int
 := match n with
      | O => Z
      | S n' => incr (int_of_nat n')
    end.


Fixpoint nat_of_int (n : int) : nat
 := match n with
  | Z => 0
  | T_zero n'  => 3 * nat_of_int n'
  | T_pos n' =>  3 * nat_of_int n' + 1
  | T_neg n' =>  3 * nat_of_int n' -1
  end.


(** The following unit tests should be provable with [reflexivity]. *)

Example test_convert1 : nat_of_int (int_of_nat 42) = 42.
Proof. simpl. reflexivity. Qed.
Example test_convert2 : int_of_nat (nat_of_int z__zero) = z__zero.
Proof. simpl. reflexivity. Qed.

(** ADDED 3/2/20 6:30 pm: All of these unit tests should also
    immediately pass. *)

Example test_nat_of_int0 : nat_of_int z__zero = 0.
Proof. simpl. reflexivity. Qed.
Example test_nat_of_int1 : nat_of_int z__one = 1.
Proof. simpl. reflexivity. Qed.
Example test_nat_of_int2 : nat_of_int z__two = 2.
Proof. simpl. reflexivity. Qed.
Example test_nat_of_int3 : nat_of_int z__three = 3.
Proof. simpl. reflexivity. Qed.
Example test_nat_of_int4 : nat_of_int z__four = 4.
Proof. simpl. reflexivity. Qed.

(** [] *)

(** **** Exercise: 2 stars, standard (nat_of_int_correct)  *)

(** ADDED 3/2/20 6:30 pm: The following theorems should all be
    provable in just a line or two of proof script.  We've added them
    to help you make sure your definition of [nat_of_int] is correct
    before you proceed with any harder theorems.  If you find yourself
    wanting to prove or use theorems about arithmetic, ask yourself:
    could you simplify your definition of [nat_of_int] instead?  That
    would be beneficial for later exercises. *)

Theorem nat_of_int_correct_Z :
  nat_of_int Z = 0.
Proof. simpl. reflexivity. Qed.

Theorem nat_of_int_correct_T_zero : forall (z : int) (n : nat),
    nat_of_int z = n ->
    nat_of_int (T_zero z) = 3 * n.
Proof.
  intros z n H. simpl. rewrite H. reflexivity.
Qed.

Theorem nat_of_int_correct_T_pos : forall (z : int) (n : nat),
    nat_of_int z = n ->
    nat_of_int (T_pos z) = S (3 * n).
Proof.
  intros z n H. simpl. rewrite H. simpl.
  rewrite <- plus_n_Sm. assert ( forall n, n + 0 = n).
  intros n0. induction n0. reflexivity. simpl. rewrite IHn0. reflexivity.
  simpl. rewrite H0. reflexivity.
Qed.

Theorem nat_of_int_correct_T_neg : forall (z : int) (n : nat),
    nat_of_int z = n ->
    nat_of_int (T_neg z) = pred (3 * n).
Proof.
  intros z n H. simpl. rewrite H. simpl.
  assert ( forall n, n - 0 =  n).
  intros n0. induction n0. reflexivity. simpl. reflexivity.
  assert ( forall n, n - 1 = pred n).
  intros. induction n0. reflexivity. simpl. apply H0.
  apply H1.
Qed.
(** [] *)

(** **** Exercise: 2 stars, standard (int_of_nat_hom)  *)

(** Both [S] and [incr] can be thought of as "plus 1" operations.
    Function [int_of_nat] interoperates nicely with "plus 1": whether
    you do a [S] before [int_of_nat], or an [incr] after it, you get
    the same result.  That is,

    incr (int_of_nat n) = int_of_nat (S n)

    When a function preserves operations like this, it is called a
    _homomorphism_.

    Prove theorem [int_of_nat_hom], which shows that [int_of_nat] is a
    homomorphism for the "plus 1" operation. *)

Theorem int_of_nat_hom : forall (n : nat),
    incr (int_of_nat n) = int_of_nat (S n).
Proof.
  intros n. induction n.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.
(** [] *)

(* ================================================================= *)
(** ** Think Positive *)

(** It would be nice to prove that [nat_of_int] is also a
    homomorphism.  But trivially it cannot be, because [nat] cannot
    represent negative integers.  So, let's try restricting our
    attention to non-negative integers. *)

(** **** Exercise: 3 stars, standard (pos)  *)

(** Complete the definition of [pos], which should be provable whenever
    its argument is a strictly positive integer, i.e., 1 or greater. As
    usual, the input to this proposition may be assumed to satisfy
    the representation invariant. *)

Inductive pos : int -> Prop :=
  | c_pos_Z : pos (T_pos Z)
  | c_zero : forall n : int, pos n -> pos (T_zero n)
  | c_pos : forall n : int,  pos n -> pos (T_pos n)
  | c_neg : forall n : int, pos n -> pos (T_neg n)
.


(** These unit tests should be easily provable with application of
    constructors, or with [inversion]. *)

Example ex_pos1 : pos z__one.
Proof. apply c_pos_Z. Qed.

Example ex_pos2 : pos z__two.
Proof.  apply c_neg. apply c_pos_Z. Qed.

Example ex_pos3 : pos z__three.
Proof. apply c_zero. apply c_pos_Z. Qed.

Example ex_pos4 : pos z__four.
Proof. apply c_pos. apply c_pos_Z. Qed.

Example ex_pos5: ~ pos z__zero.
Proof. unfold not. intros H. inversion H. Qed.

Example ex_pos6: ~ pos z__negone.
Proof. unfold not. intros H. inversion H. inversion H1. Qed.

(** [] *)

(** Now it is straightforward to define what it means for an [int]
    to be non-negative. *)

Definition zero (z : int) : Prop :=
  z = Z.

Definition nonneg (z : int) : Prop :=
  zero z \/ pos z.

(** **** Exercise: 3 stars, standard (incr_preserves_nonneg)  *)

(** Prove that a non-negative integer, when incremented, is still
    non-negative.  Hint: factor out a helper lemma that proves the same
    fact, but for strictly positive integers. *)

Lemma incr_preserves_pos : forall (z : int),
    pos z -> pos (incr z).
Proof.
  intros z H. induction z.
  - simpl. apply c_pos_Z.
  - simpl. apply c_pos. inversion H. apply H1.
  - simpl. apply c_neg. inversion H. simpl. apply c_pos_Z. apply IHz. apply H1.
  - inversion H. simpl. destruct z. 
    * apply H1.
    * apply c_zero. apply H1.
    * apply c_zero. apply H1.
    * apply c_zero. apply H1.
Qed.

Lemma incr_preserves_nonneg : forall (z : int),
    nonneg z -> nonneg (incr z).
Proof.
  intros z H. destruct H as [H | H].
  + induction z.
    - simpl. unfold nonneg. right. apply c_pos_Z.
    - unfold zero in H. rewrite H. unfold nonneg. right. apply c_pos_Z.
    - unfold zero in H. rewrite H. unfold nonneg. right. apply c_pos_Z.
    - unfold zero in H. rewrite H. unfold nonneg. right. apply c_pos_Z.
  +  apply incr_preserves_pos in H. unfold nonneg. right. apply H.
Qed.
(** [] *)

(* ================================================================= *)
(** ** Back to the Homomorphism *)

(** **** Exercise: 4 stars, standard (nat_of_int_hom)  *)

(** Prove that [nat_of_int] is a homomorphism on non-negative ints.

    There are multiple viable proof strategies, but none that we know
    of are short. You will probably need a couple helper lemmas about
    [int], [pos], and/or [nonneg].  Expect to use [inversion] and
    [destruct] a lot.

    Be wary not to get hung up on proving lots of arithmetic facts
    about [nat].  You do not really need more than this one: *)

Check plus_n_Sm.

(** Do _avoid mindless proof hacking_.  If you get stuck, take
    out a piece of paper, and try to convince yourself (not Coq) why
    the assertion you are proving should hold.

    This is meant to be a challenging problem.  Good luck! *)

Lemma plus_zero: forall n, n + 0 = n.
  Proof.
    intros n0. induction n0. reflexivity. simpl. rewrite IHn0. reflexivity. 
  Qed.

Lemma minus_zero: forall n, n - 0 =  n.
  Proof.
    intros n0. induction n0. reflexivity. simpl. reflexivity.
  Qed.

Lemma pred_minus:  forall n, n - 1 = pred n.
  Proof.
     intros. induction n. reflexivity. simpl. apply minus_zero.
  Qed.

Lemma pred_succ:  forall n, pos n -> nat_of_int n = S (pred (nat_of_int n)).
  Proof.
     intros. induction n.
     - inversion H.
     - simpl. rewrite plus_zero. rewrite IHn. simpl. reflexivity. inversion H. apply H1.
     - inversion H. simpl. reflexivity.
       simpl. rewrite plus_zero. rewrite IHn. simpl. reflexivity.
       apply H1.
     - inversion H. simpl. rewrite plus_zero. rewrite IHn.
       rewrite <- pred_minus. simpl. rewrite <- pred_minus. rewrite <- plus_n_Sm. simpl.
       rewrite minus_zero. reflexivity.
       apply H1.
Qed.


Theorem nat_of_int_hom : forall (n : int),
    nonneg n -> nat_of_int (incr n) = S (nat_of_int n).
Proof.
  intros n H. unfold nonneg in H. inversion H.
  - unfold zero in H0. rewrite H0. simpl. reflexivity.
  - induction n.
    + simpl. reflexivity.
    + simpl. rewrite <- plus_n_Sm. rewrite plus_zero. reflexivity.
    + inversion H0.
      * simpl. reflexivity.
      * simpl. rewrite plus_zero. rewrite plus_zero.
       rewrite <- plus_n_Sm. rewrite IHn. rewrite pred_minus. simpl. rewrite <- plus_n_Sm.
       rewrite <- plus_n_Sm. rewrite <- plus_n_Sm. rewrite plus_zero. reflexivity.
      right. apply H2. apply H2.
    + inversion H0.  simpl.  destruct n.
      * inversion H2.
      * rewrite plus_zero. rewrite pred_minus. rewrite  pred_succ. simpl. rewrite plus_zero.
        rewrite plus_zero. reflexivity. apply c_zero. apply H2.
      * rewrite plus_zero. rewrite pred_minus. rewrite  pred_succ. simpl. rewrite plus_zero.
        rewrite plus_zero. reflexivity. apply c_zero. apply H2.
      * rewrite plus_zero. rewrite pred_minus. rewrite  pred_succ. simpl. rewrite plus_zero.
        rewrite plus_zero. reflexivity. apply c_zero. apply H2.
Qed.

(** [] *)

(* ================================================================= *)
(** ** The Payoff *)

(** With all that hard work behind us, we can finally establish that
    [nat_of_int] is a _left inverse_ of [int_of_nat]: if you convert a
    [nat] to an [int] and back, you get the original [nat] again.

    Hint: the hard work was proving [incr_preserves_nonneg] and
    [nat_of_int_hom].  Use those to your advantage now. *)

(** **** Exercise: 2 stars, standard (nonneg_nat)  *)

(** First, prove this helper lemma. *)

Lemma nonneg_nat : forall (n : nat),
    nonneg (int_of_nat n).
Proof.
  intros n.  induction n.
  - left. unfold zero. simpl. reflexivity.
  - simpl. apply incr_preserves_nonneg.  apply IHn. 
Qed.
(** [] *)

(** **** Exercise: 2 stars, standard (left_inverse)  *)

(** Finally, prove the main theorem. *)

Theorem left_inverse : forall (n : nat),
    nat_of_int (int_of_nat n) = n.
Proof.
  intros n. induction n.
  - simpl. reflexivity.
  - simpl. rewrite nat_of_int_hom. rewrite IHn. reflexivity.
    apply nonneg_nat.
Qed.
(** [] *)

(* ################################################################# *)
(** * Problem 2: Logic and Inductive Propositions *)

(* ================================================================= *)
(** ** A Data Type for Propositions *)

(** Here is a data type that represents logical propositions, but in a
    different way than Coq's standard library: *)

Inductive prop :=
| PTrue
| PFalse
| PAtom (i : nat)  (* explained below *)
| PAnd (p q : prop)
| POr (p q : prop)
| PImp (p q : prop)
| PNeg (p : prop)
.

(** An _atom_ is an atomic proposition: the indivisible propositions
    out of which larger propositions are made.  For example, you could
    imagine atomic propositions like [is_raining] and
    [bring_umbrella].  Rather than use strings to represent these
    atoms, our representation uses [nat] for simplicity.  You could
    think of that as all the atomic propositions simply being [A0],
    [A1], [A2], etc.

    Here are some familiar propositions represented with [prop]: *)

Module PropExamples.

Definition p := PAtom 0.
Definition q := PAtom 1.

(** [False -> P] *)
Definition ex_falso : prop :=
  PImp PFalse p.

(** [P /\ Q -> P] *)
Definition proj1 : prop :=
  (PImp (PAnd p q) p).

(** [P -> ((P -> Q) -> P)] *)
Definition mp : prop :=
  (PImp p (PImp (PImp p q) q)).

End PropExamples.

(** **** Exercise: 1 star, standard (prop_warmup)  *)

(** To better familiarize yourself with [prop], complete function
    [atom_in], which tests whether an atom is syntactically part of a
    proposition.  The unit tests below it should be immediately
    provable with [reflexivity] if your definition is correct. *)

Fixpoint atom_in (i : nat) (p : prop) : bool
  := match p with
| PTrue => false
| PFalse => false
| PAtom x => eqb i x
| PAnd p' q => atom_in i p' || atom_in i q
| POr p' q => atom_in i p' || atom_in i q
| PImp p' q => atom_in i p' || atom_in i q
| PNeg p' => atom_in i p'
end.

Definition test_prop :=
  PImp (POr (PAnd PTrue PFalse) (PAtom 42)) (PNeg (PAtom 7)).

Example test_atom_in1 : atom_in 42 test_prop = true.
Proof. simpl. reflexivity. Qed.
Example test_atom_in2 : atom_in 0 test_prop = false.
Proof. simpl. reflexivity. Qed.

(** [] *)

(* ================================================================= *)
(** ** Provability of Propositions *)

(** Inductive proposition [provable], below, characterizes whether a
    [prop] is provable in constructive logic.  It is based on the same
    idea as Coq's goals window: [provable hyps p] should hold whenever
    [p] is provable from hypotheses [hyps].  So, [p] is like the goal
    below the line, and each element of [hyps] is like an hypothesis
    above the line.

    Tip: study this definition carefully before proceeding. *)

Inductive provable : list prop -> prop -> Prop :=

(** Constructor [pr_hyp] means that a proposition is provable if it a
    hypothesis. *)
| pr_hyp : forall p, provable [p] p

(** Constructor [pr_true] means that [PTrue] is always provable. *)
| pr_true : provable [] PTrue

(** Constructor [pr_false] means that if [PFalse] is a hypothesis then
    any proposition is provable. *)
| pr_false : forall p, provable [PFalse] p

(** Constructor [pr_imp_l] is the most complicated one.  It shows how
    to introduce an implication into the hypotheses, i.e., into the
    _left_ argument of [provable].  If [p] is provable from [hyps],
    and if [r] is provable from [q] and [hyps'], then the constructor
    means that [r] is also provable from [PImp p q], together with
    [hyps] and [hyps']. *)
| pr_imp_l : forall p q r hyps hyps',
    provable hyps p ->
    provable (q :: hyps') r ->
    provable ((PImp p q) :: hyps ++ hyps') r

(** Constructor [pr_imp_r] shows how to introduce an implication into
    the _right_ argument of [provable].  If [q] is provable from [p]
    and [hyps], then [PImp p q] is provable from [hyps]. *)
| pr_imp_r : forall p q hyps,
    provable (p :: hyps) q -> provable hyps (PImp p q)

(** You will add constructors here, later, for [PAnd] and [POr]. *)
| pr_and_l : forall p p1 p2,
    provable [p1] p -> provable [PAnd p1 p2] p
| pr_and_r : forall p p1 p2,
    provable [p2] p -> provable [PAnd p1 p2] p
| pr_and : forall p1 p2,
    provable [] p1 -> provable [] p2 -> provable [] (PAnd p1 p2)
| pr_or : forall p p1 p2,
    provable [p] p1 \/ provable [p] p2 -> provable [p] (POr p1 p2)
| pr_or_l : forall p1 p2,
    provable [] p1 -> provable [] (POr p1 p2)
| pr_or_r : forall p1 p2,
    provable [] p2  -> provable [] (POr p1 p2)
.

(** **** Exercise: 1 star, standard (provable1)  *)

(** Prove these lemmas.  Your proofs should be very short. *)

Lemma true_provable : provable [] PTrue.
Proof. apply pr_true. Qed.

Lemma hyp_provable : forall (p : prop),
    provable [p] p.
Proof. apply pr_hyp. Qed.

(** [] *)

(** **** Exercise: 2 stars, standard (provable2)  *)

(** Prove these lemmas about familiar formulas. You should not need more than
    two or three lines of proof script for any of them. *)

Lemma mp_provable : forall (p q : prop),
    provable [] (PImp p (PImp (PImp p q) q)).
Proof.
  intros p q. apply pr_imp_r.  apply pr_imp_r.
  apply pr_imp_l with (hyps := [p]) (hyps':= []).
  apply pr_hyp. apply pr_hyp.
Qed.

Lemma ex_falso_provable : forall (p : prop),
    provable [] (PImp PFalse p).
Proof.
  intros p. apply pr_imp_r. apply pr_false.
Qed.

Lemma false_not_provable : ~ provable [] PFalse.
Proof.
  unfold not. intros H. inversion H.
Qed.
(** [] *)

(* ================================================================= *)
(** ** Equivalence with Coq *)

(** We'd like to establish that provability according to [provable]
    and according to Coq are really the same notion, at least for the
    kinds of propositions expressible with [prop]. Toward that end,
    we define a Coq proposition [P] and a [prop] proposition [p]
    to be _equivalent_ iff they are both provable. *)

Definition equiv (P : Prop) (p : prop) : Prop :=
  P <-> provable [] p.

(** **** Exercise: 1 star, standard (true_equiv)  *)

(** Prove that [True] and [PTrue] are equivalent. *)

Theorem true_equiv :
  equiv True PTrue.
Proof.
 unfold equiv. split.
 - intros H. apply pr_true.
 - intros H. apply I.
Qed.
(** [] *)

(** **** Exercise: 1 star, standard (false_equiv)  *)

(** Prove that [False] and [PFalse] are equivalent. *)

Theorem false_equiv :
  equiv False PFalse.
Proof.
  unfold equiv. split.
 - intros H. destruct H.
 - intros H. inversion H.
Qed.

(** [] *)

(** We will skip over equivalence of implication for now, and return
    to it at the end of the problem. *)

(* ================================================================= *)
(** ** Adding Conjunction and Disjunction *)

(** Now it's your turn to expand the definition of [provable] by
    adding constructors that characterize conjunction and
    disjunction. *)

(** Add three constructors to [provable] for [PAnd], corresponding to
    these ideas:

    - If from p1 you can prove q, then from p1 and p2 you can prove q.

    - If from p2 you can prove q, then from p1 and p2 you can prove q.

    - If you can prove p1 and you can prove p2, then you can prove p1
      and p2.

    Your task is to figure out how to formalize those, then use them
    to prove the unit test and equivalence theorem below. *)

(** **** Exercise: 1 star, standard (proj1_provable)  *)

Example proj1_provable : forall (p q : prop),
    provable [] (PImp (PAnd p q) p).
Proof.
  intros p q. apply pr_imp_r. apply pr_and_l. apply pr_hyp.
Qed.
(** [] *)

(** **** Exercise: 2 stars, standard (and_equiv)  *)

Theorem and_equiv : forall P Q p q,
    equiv P p ->
    equiv Q q ->
    equiv (P /\ Q) (PAnd p q).
Proof.
  intros P Q p q. unfold equiv. intros H1 H2. split.
  - intro H. destruct H as [H3  H4]. apply H1 in H3. apply H2 in H4.
    apply pr_and. apply H3. apply H4.
  - intro H. inversion H. split. apply H1. apply H4. apply H2. apply H5.
Qed.
(** [] *)

(** Add three constructors to [provable] for [POr], then use them to
    prove the unit test and equivalence theorem below. This time, we
    leave it up to you to figure out how to design the constructors.
    Here's a hint though: they will exhibit a great deal of symmetry
    to [PAnd]. *)

(** **** Exercise: 1 star, standard (injl_provable)  *)

Example injl_provable : forall (p q : prop),
    provable [] (PImp p (POr p q)).
Proof.
  intros p q. apply pr_imp_r. apply pr_or. left. apply pr_hyp.
Qed.
(** [] *)

(** **** Exercise: 3 stars, standard (or_equiv)  *)

Theorem or_equiv : forall P Q p q,
    equiv P p ->
    equiv Q q ->
    equiv (P \/ Q) (POr p q).
Proof.
  intros P Q p q. unfold equiv. intros H1 H2. split.
  - intro H. destruct H as [H3 | H4]. apply H1 in H3.
    apply pr_or_l. apply H3. apply pr_or_r. apply H2 in H4. apply H4.
  - intro H. inversion H. apply H1 in H4. left. apply H4.
    right. apply H2 in H4. apply H4.
Qed.
(** [] *)

(* ================================================================= *)
(** ** Back to Implication *)

(** Now we return to the equivalence of implication.  That turns out
    to be much harder to prove, because implication (which is sugar
    for universal quantification) is not defined as a data type in
    Coq; rather, it is primitive.  Here are two axioms we will add
    to make the proof easier. *)

(** First, if by assuming [p] you can prove [q], but [p] already follows
    from your other hypotheses, then you never really needed to explicitly
    assume [p].  You can _cut_ it out of the proof.*)
Axiom pr_cut : forall p q hyps hyps',
    provable hyps p ->
    provable (p :: hyps') q ->
    provable (hyps ++ hyps') q.

(** Second, if the provability of [p] implies the provability of [q],
    then provably [p] implies [q].  That is, provability disributes
    over implication. *)
Axiom pr_distr_imp : forall p q hyps,
    (provable hyps p -> provable hyps q) -> provable hyps (PImp p q).

(** As an aside, we know that [pr_cut] is valid; it's a standard
    result in mathematical logic.  But, we don't know whether
    [pr_distr_imp] is valid!  Anyone who can give a Coq proof for
    either axiom (i.e., turn it into a proven theorem) is welcome to
    apply to the professor for a CS 4999 project. *)

(** Prove the equivalence of implication, making use of those two
    axioms as needed. *)

(** **** Exercise: 2 stars, standard (imp_correct)  *)

Theorem imp_correct : forall P Q p q,
    equiv P p ->
    equiv Q q ->
    provable [] (PImp p q) -> (P -> Q).
Proof.
  unfold equiv. intros P Q p q H1 H2 H3. inversion H3. rewrite H1. rewrite H2.
  intros H6. apply pr_cut with (p:=p) (hyps:=[]) (hyps':=[]). apply H6. apply H4.
Qed.
(** [] *)

(** **** Exercise: 2 stars, standard (imp_complete)  *)

Theorem imp_complete : forall P Q p q,
    equiv P p ->
    equiv Q q ->
    (P -> Q) -> provable [] (PImp p q).
Proof.
  unfold equiv. intros P Q p q H1 H2 H3. apply pr_distr_imp with (hyps:=[]). 
  rewrite <- H1. rewrite <- H2. apply H3.
Qed.
(** [] *)

(** From there, it's easy to prove the final theorem: *)

Theorem imp_equiv : forall P Q p q,
    equiv P p ->
    equiv Q q ->
    equiv (P -> Q) (PImp p q).
Proof.
  intros P Q p q Hp Hq. split.
  - apply imp_complete. apply Hp. apply Hq.
  - apply imp_correct. apply Hp. apply Hq.
Qed.

(* ################################################################# *)
(** * Time Spent *)

(** **** Exercise: 1 star, standard (hours)  *)

(** How many hours did you spend on this exam? *)

Definition hours_spent : nat
  := 7.

Example hours_spent_test : 0 <? hours_spent = true.
Proof. simpl. unfold hours_spent. simpl. reflexivity. Qed.

(** [] *)

(* 02 Mar 2020 *)
