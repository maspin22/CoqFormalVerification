(** * Imp: Simple Imperative Programs *)

(** In this chapter, we take a more serious look at how to use Coq to
    study other things.  Our case study is a _simple imperative
    programming language_ called Imp, embodying a tiny core fragment
    of conventional mainstream languages such as C and Java.  Here is
    a familiar mathematical function written in Imp.

       Z ::= X;;
       Y ::= 1;;
       WHILE ~(Z = 0) DO
         Y ::= Y * Z;;
         Z ::= Z - 1
       END
*)

(** We concentrate here on defining the _syntax_ and _semantics_ of
    Imp; later chapters in _Programming Language Foundations_
    (_Software Foundations_, volume 2) develop a theory of
    _program equivalence_ and introduce _Hoare Logic_, a widely
    used logic for reasoning about imperative programs. *)

Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import omega.Omega.
From Coq Require Import Lists.List.
From Coq Require Import Strings.String.
Import ListNotations.

From PLF Require Import Maps.

(* ################################################################# *)
(** * Arithmetic and Boolean Expressions *)

(** We'll present Imp in three parts: first a core language of
    _arithmetic and boolean expressions_, then an extension of these
    expressions with _variables_, and finally a language of _commands_
    including assignment, conditions, sequencing, and loops. *)

(* ================================================================= *)
(** ** Syntax *)

Module AExp.

(** These two definitions specify the _abstract syntax_ of
    arithmetic and boolean expressions. *)

Inductive aexp : Type :=
  | ANum (n : nat)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp).

Inductive bexp : Type :=
  | BTrue
  | BFalse
  | BEq (a1 a2 : aexp)
  | BLe (a1 a2 : aexp)
  | BNot (b : bexp)
  | BAnd (b1 b2 : bexp).

(** In this chapter, we'll mostly elide the translation from the
    concrete syntax that a programmer would actually write to these
    abstract syntax trees -- the process that, for example, would
    translate the string ["1 + 2 * 3"] to the AST

      APlus (ANum 1) (AMult (ANum 2) (ANum 3)).

    The optional chapter [ImpParser] develops a simple lexical
    analyzer and parser that can perform this translation.  You do
    _not_ need to understand that chapter to understand this one, but
    if you haven't already taken a course where these techniques are
    covered (e.g., a compilers course) you may want to skim it. *)

(** For comparison, here's a conventional BNF (Backus-Naur Form)
    grammar defining the same abstract syntax:

    a ::= nat
        | a + a
        | a - a
        | a * a

    b ::= true
        | false
        | a = a
        | a <= a
        | ~ b
        | b && b
*)

(** Compared to the Coq version above...

       - The BNF is more informal -- for example, it gives some
         suggestions about the surface syntax of expressions (like the
         fact that the addition operation is written with an infix
         [+]) while leaving other aspects of lexical analysis and
         parsing (like the relative precedence of [+], [-], and
         [*], the use of parens to group subexpressions, etc.)
         unspecified.  Some additional information -- and human
         intelligence -- would be required to turn this description
         into a formal definition, e.g., for implementing a compiler.

         The Coq version consistently omits all this information and
         concentrates on the abstract syntax only.

       - Conversely, the BNF version is lighter and easier to read.
         Its informality makes it flexible, a big advantage in
         situations like discussions at the blackboard, where
         conveying general ideas is more important than getting every
         detail nailed down precisely.

         Indeed, there are dozens of BNF-like notations and people
         switch freely among them, usually without bothering to say
         which kind of BNF they're using because there is no need to:
         a rough-and-ready informal understanding is all that's
         important.

    It's good to be comfortable with both sorts of notations: informal
    ones for communicating between humans and formal ones for carrying
    out implementations and proofs. *)

(* ================================================================= *)
(** ** Evaluation *)

(** _Evaluating_ an arithmetic expression produces a number. *)

Fixpoint aeval (a : aexp) : nat :=
  match a with
  | ANum n => n
  | APlus  a1 a2 => (aeval a1) + (aeval a2)
  | AMinus a1 a2 => (aeval a1) - (aeval a2)
  | AMult  a1 a2 => (aeval a1) * (aeval a2)
  end.

Example test_aeval1:
  aeval (APlus (ANum 2) (ANum 2)) = 4.
Proof. reflexivity. Qed.

(** Similarly, evaluating a boolean expression yields a boolean. *)

Fixpoint beval (b : bexp) : bool :=
  match b with
  | BTrue       => true
  | BFalse      => false
  | BEq a1 a2   => (aeval a1) =? (aeval a2)
  | BLe a1 a2   => (aeval a1) <=? (aeval a2)
  | BNot b1     => negb (beval b1)
  | BAnd b1 b2  => andb (beval b1) (beval b2)
  end.

(* ================================================================= *)
(** ** Optimization *)

(** We haven't defined very much yet, but we can already get
    some mileage out of the definitions.  Suppose we define a function
    that takes an arithmetic expression and slightly simplifies it,
    changing every occurrence of [0 + e] (i.e., [(APlus (ANum 0) e])
    into just [e]. *)

Fixpoint optimize_0plus (a:aexp) : aexp :=
  match a with
  | ANum n => ANum n
  | APlus (ANum 0) e2 => optimize_0plus e2
  | APlus  e1 e2 => APlus  (optimize_0plus e1) (optimize_0plus e2)
  | AMinus e1 e2 => AMinus (optimize_0plus e1) (optimize_0plus e2)
  | AMult  e1 e2 => AMult  (optimize_0plus e1) (optimize_0plus e2)
  end.

(** To make sure our optimization is doing the right thing we
    can test it on some examples and see if the output looks OK. *)

Example test_optimize_0plus:
  optimize_0plus (APlus (ANum 2)
                        (APlus (ANum 0)
                               (APlus (ANum 0) (ANum 1))))
  = APlus (ANum 2) (ANum 1).
Proof. reflexivity. Qed.

(** But if we want to be sure the optimization is correct --
    i.e., that evaluating an optimized expression gives the same
    result as the original -- we should prove it. *)

Theorem optimize_0plus_sound: forall a,
  aeval (optimize_0plus a) = aeval a.
Proof.
  intros a. induction a.
  - (* ANum *) reflexivity.
  - (* APlus *) destruct a1 eqn:Ea1.
    + (* a1 = ANum n *) destruct n eqn:En.
      * (* n = 0 *)  simpl. apply IHa2.
      * (* n <> 0 *) simpl. rewrite IHa2. reflexivity.
    + (* a1 = APlus a1_1 a1_2 *)
      simpl. simpl in IHa1. rewrite IHa1.
      rewrite IHa2. reflexivity.
    + (* a1 = AMinus a1_1 a1_2 *)
      simpl. simpl in IHa1. rewrite IHa1.
      rewrite IHa2. reflexivity.
    + (* a1 = AMult a1_1 a1_2 *)
      simpl. simpl in IHa1. rewrite IHa1.
      rewrite IHa2. reflexivity.
  - (* AMinus *)
    simpl. rewrite IHa1. rewrite IHa2. reflexivity.
  - (* AMult *)
    simpl. rewrite IHa1. rewrite IHa2. reflexivity.  Qed.

(* ################################################################# *)
(** * Coq Automation *)

(** The amount of repetition in this last proof is a little
    annoying.  And if either the language of arithmetic expressions or
    the optimization being proved sound were significantly more
    complex, it would start to be a real problem.

    So far, we've been doing all our proofs using just a small handful
    of Coq's tactics and completely ignoring its powerful facilities
    for constructing parts of proofs automatically.  This section
    introduces some of these facilities, and we will see more over the
    next several chapters.  Getting used to them will take some
    energy -- Coq's automation is a power tool -- but it will allow us
    to scale up our efforts to more complex definitions and more
    interesting properties without becoming overwhelmed by boring,
    repetitive, low-level details. *)

(* ================================================================= *)
(** ** Tacticals *)

(** _Tacticals_ is Coq's term for tactics that take other tactics as
    arguments -- "higher-order tactics," if you will.  *)

(* ----------------------------------------------------------------- *)
(** *** The [try] Tactical *)

(** If [T] is a tactic, then [try T] is a tactic that is just like [T]
    except that, if [T] fails, [try T] _successfully_ does nothing at
    all (rather than failing). *)

Theorem silly1 : forall ae, aeval ae = aeval ae.
Proof. try reflexivity. (* This just does [reflexivity]. *) Qed.

Theorem silly2 : forall (P : Prop), P -> P.
Proof.
  intros P HP.
  try reflexivity. (* Just [reflexivity] would have failed. *)
  apply HP. (* We can still finish the proof in some other way. *)
Qed.

(** There is no real reason to use [try] in completely manual
    proofs like these, but it is very useful for doing automated
    proofs in conjunction with the [;] tactical, which we show
    next. *)

(* ----------------------------------------------------------------- *)
(** *** The [;] Tactical (Simple Form) *)

(** In its most common form, the [;] tactical takes two tactics as
    arguments.  The compound tactic [T;T'] first performs [T] and then
    performs [T'] on _each subgoal_ generated by [T]. *)

(** For example, consider the following trivial lemma: *)

Lemma foo : forall n, 0 <=? n = true.
Proof.
  intros.
  destruct n.
    (* Leaves two subgoals, which are discharged identically...  *)
    - (* n=0 *) simpl. reflexivity.
    - (* n=Sn' *) simpl. reflexivity.
Qed.

(** We can simplify this proof using the [;] tactical: *)

Lemma foo' : forall n, 0 <=? n = true.
Proof.
  intros.
  (* [destruct] the current goal *)
  destruct n;
  (* then [simpl] each resulting subgoal *)
  simpl;
  (* and do [reflexivity] on each resulting subgoal *)
  reflexivity.
Qed.

(** Using [try] and [;] together, we can get rid of the repetition in
    the proof that was bothering us a little while ago. *)

Theorem optimize_0plus_sound': forall a,
  aeval (optimize_0plus a) = aeval a.
Proof.
  intros a.
  induction a;
    (* Most cases follow directly by the IH... *)
    try (simpl; rewrite IHa1; rewrite IHa2; reflexivity).
    (* ... but the remaining cases -- ANum and APlus --
       are different: *)
  - (* ANum *) reflexivity.
  - (* APlus *)
    destruct a1 eqn:Ea1;
      (* Again, most cases follow directly by the IH: *)
      try (simpl; simpl in IHa1; rewrite IHa1;
           rewrite IHa2; reflexivity).
    (* The interesting case, on which the [try...]
       does nothing, is when [e1 = ANum n]. In this
       case, we have to destruct [n] (to see whether
       the optimization applies) and rewrite with the
       induction hypothesis. *)
    + (* a1 = ANum n *) destruct n eqn:En;
      simpl; rewrite IHa2; reflexivity.   Qed.

(** Coq experts often use this "[...; try... ]" idiom after a tactic
    like [induction] to take care of many similar cases all at once.
    Naturally, this practice has an analog in informal proofs.  For
    example, here is an informal proof of the optimization theorem
    that matches the structure of the formal one:

    _Theorem_: For all arithmetic expressions [a],

       aeval (optimize_0plus a) = aeval a.

    _Proof_: By induction on [a].  Most cases follow directly from the
    IH.  The remaining cases are as follows:

      - Suppose [a = ANum n] for some [n].  We must show

          aeval (optimize_0plus (ANum n)) = aeval (ANum n).

        This is immediate from the definition of [optimize_0plus].

      - Suppose [a = APlus a1 a2] for some [a1] and [a2].  We must
        show

          aeval (optimize_0plus (APlus a1 a2)) = aeval (APlus a1 a2).

        Consider the possible forms of [a1].  For most of them,
        [optimize_0plus] simply calls itself recursively for the
        subexpressions and rebuilds a new expression of the same form
        as [a1]; in these cases, the result follows directly from the
        IH.

        The interesting case is when [a1 = ANum n] for some [n].  If
        [n = 0], then

          optimize_0plus (APlus a1 a2) = optimize_0plus a2

        and the IH for [a2] is exactly what we need.  On the other
        hand, if [n = S n'] for some [n'], then again [optimize_0plus]
        simply calls itself recursively, and the result follows from
        the IH.  [] *)

(** However, this proof can still be improved: the first case (for
    [a = ANum n]) is very trivial -- even more trivial than the cases
    that we said simply followed from the IH -- yet we have chosen to
    write it out in full.  It would be better and clearer to drop it
    and just say, at the top, "Most cases are either immediate or
    direct from the IH.  The only interesting case is the one for
    [APlus]..."  We can make the same improvement in our formal proof
    too.  Here's how it looks: *)

Theorem optimize_0plus_sound'': forall a,
  aeval (optimize_0plus a) = aeval a.
Proof.
  intros a.
  induction a;
    (* Most cases follow directly by the IH *)
    try (simpl; rewrite IHa1; rewrite IHa2; reflexivity);
    (* ... or are immediate by definition *)
    try reflexivity.
  (* The interesting case is when a = APlus a1 a2. *)
  - (* APlus *)
    destruct a1; try (simpl; simpl in IHa1; rewrite IHa1;
                      rewrite IHa2; reflexivity).
    + (* a1 = ANum n *) destruct n;
      simpl; rewrite IHa2; reflexivity. Qed.

(* ----------------------------------------------------------------- *)
(** *** The [;] Tactical (General Form) *)

(** The [;] tactical also has a more general form than the simple
    [T;T'] we've seen above.  If [T], [T1], ..., [Tn] are tactics,
    then

      T; [T1 | T2 | ... | Tn]

    is a tactic that first performs [T] and then performs [T1] on the
    first subgoal generated by [T], performs [T2] on the second
    subgoal, etc.

    So [T;T'] is just special notation for the case when all of the
    [Ti]'s are the same tactic; i.e., [T;T'] is shorthand for:

      T; [T' | T' | ... | T']
*)

(* ----------------------------------------------------------------- *)
(** *** The [repeat] Tactical *)

(** The [repeat] tactical takes another tactic and keeps applying this
    tactic until it fails to make progress. Here is an example showing
    that [10] is in a long list using [repeat]. *)

Theorem In10 : In 10 [1;2;3;4;5;6;7;8;9;10].
Proof.
  repeat (try (left; reflexivity); right).
Qed.

(** The tactic [repeat T] never fails: if the tactic [T] doesn't apply
    to the original goal, then repeat still succeeds without changing
    the original goal (i.e., it repeats zero times). *)

Theorem In10' : In 10 [1;2;3;4;5;6;7;8;9;10].
Proof.
  repeat simpl.
  repeat (left; reflexivity).
  repeat (right; try (left; reflexivity)).
Qed.

(** The tactic [repeat T] also does not have any upper bound on the
    number of times it applies [T].  If [T] is a tactic that always
    succeeds (and makes progress), then repeat [T] will loop forever. *)

Theorem repeat_loop : forall (m n : nat),
    m + n = n + m.
Proof.
  intros m n.
  (* Uncomment the next line to see the infinite loop occur.
     In Proof General, [C-c C-c] will break out of the loop. *)
  (* repeat rewrite Nat.add_comm. *)
Admitted.

(** While evaluation in Coq's term language, Gallina, is guaranteed to
    terminate, tactic evaluation is not!  This does not affect Coq's
    logical consistency, however, since the job of [repeat] and other
    tactics is to guide Coq in constructing proofs; if the
    construction process diverges (i.e., it does not terminate), this
    simply means that we have failed to construct a proof, not that we
    have constructed a wrong one. *)

(** **** Exercise: 3 stars, standard (optimize_0plus_b_sound) 

    Since the [optimize_0plus] transformation doesn't change the value
    of [aexp]s, we should be able to apply it to all the [aexp]s that
    appear in a [bexp] without changing the [bexp]'s value.  Write a
    function that performs this transformation on [bexp]s and prove
    it is sound.  Use the tacticals we've just seen to make the proof
    as elegant as possible. *)

Fixpoint optimize_0plus_b (b : bexp) : bexp
  (* SOLUTION: *) :=
  match b with
  | BTrue       => BTrue
  | BFalse      => BFalse
  | BEq a1 a2   => BEq (optimize_0plus a1) (optimize_0plus a2)
  | BLe a1 a2   => BLe (optimize_0plus a1) (optimize_0plus a2)
  | BNot b1     => BNot (optimize_0plus_b b1)
  | BAnd b1 b2  => BAnd (optimize_0plus_b b1) (optimize_0plus_b b2)
  end.

Theorem optimize_0plus_b_sound : forall b,
  beval (optimize_0plus_b b) = beval b.
Proof.
  (* SOLUTION: *)
  induction b;
     simpl;
     try (repeat rewrite optimize_0plus_sound);
     try reflexivity.
  - (* BNot *)
    rewrite IHb.  reflexivity.
  - (* BAnd *)
    rewrite IHb1. rewrite IHb2. reflexivity.
Qed.
(** [] *)

(** **** Exercise: 4 stars, standard, optional (optimize) 

    _Design exercise_: The optimization implemented by our
    [optimize_0plus] function is only one of many possible
    optimizations on arithmetic and boolean expressions.  Write a more
    sophisticated optimizer and prove it correct.  (You will probably
    find it easiest to start small -- add just a single, simple
    optimization and its correctness proof -- and build up to
    something more interesting incrementially.)  *)

(* SOLUTION: *) (** [] *)

(* ================================================================= *)
(** ** Defining New Tactic Notations *)

(** Coq also provides several ways of "programming" tactic
    scripts.

    - The [Tactic Notation] idiom illustrated below gives a handy way
      to define "shorthand tactics" that bundle several tactics into a
      single command.

    - For more sophisticated programming, Coq offers a built-in
      language called [Ltac] with primitives that can examine and
      modify the proof state.  The details are a bit too complicated
      to get into here (and it is generally agreed that [Ltac] is not
      the most beautiful part of Coq's design!), but they can be found
      in the reference manual and other books on Coq, and there are
      many examples of [Ltac] definitions in the Coq standard library
      that you can use as examples.

    - There is also an OCaml API, which can be used to build tactics
      that access Coq's internal structures at a lower level, but this
      is seldom worth the trouble for ordinary Coq users.

    The [Tactic Notation] mechanism is the easiest to come to grips
    with, and it offers plenty of power for many purposes.  Here's an
    example. *)

Tactic Notation "simpl_and_try" tactic(c) :=
  simpl;
  try c.

(** This defines a new tactical called [simpl_and_try] that takes one
    tactic [c] as an argument and is defined to be equivalent to the
    tactic [simpl; try c].  Now writing "[simpl_and_try reflexivity.]"
    in a proof will be the same as writing "[simpl; try reflexivity.]" *)

(* ================================================================= *)
(** ** The [omega] Tactic *)

(** The [omega] tactic implements a decision procedure for a subset of
    first-order logic called _Presburger arithmetic_.  It is based on
    the Omega algorithm invented by William Pugh [Pugh 1991] (in Bib.v).

    If the goal is a universally quantified formula made out of

      - numeric constants, addition ([+] and [S]), subtraction ([-]
        and [pred]), and multiplication by constants (this is what
        makes it Presburger arithmetic),

      - equality ([=] and [<>]) and ordering ([<=]), and

      - the logical connectives [/\], [\/], [~], and [->],

    then invoking [omega] will either solve the goal or fail, meaning
    that the goal is actually false.  (If the goal is _not_ of this
    form, [omega] will also fail.) *)

Example silly_presburger_example : forall m n o p,
  m + n <= n + o /\ o + 3 = p + 3 ->
  m <= p.
Proof.
  intros. omega.
Qed.

Example plus_comm__omega : forall m n,
    m + n = n + m.
Proof.
  intros. omega.
Qed.

Example plus_assoc__omega : forall m n p,
    m + (n + p) = m + n + p.
Proof.
  intros. omega.
Qed.

(** (Note the [From Coq Require Import omega.Omega.] at the top of
    the file.) *)

(* ================================================================= *)
(** ** A Few More Handy Tactics *)

(** Finally, here are some miscellaneous tactics that you may find
    convenient.

     - [clear H]: Delete hypothesis [H] from the context.

     - [subst x]: For a variable [x], find an assumption [x = e] or
       [e = x] in the context, replace [x] with [e] throughout the
       context and current goal, and clear the assumption.

     - [subst]: Substitute away _all_ assumptions of the form [x = e]
       or [e = x] (where [x] is a variable).

     - [rename... into...]: Change the name of a hypothesis in the
       proof context.  For example, if the context includes a variable
       named [x], then [rename x into y] will change all occurrences
       of [x] to [y].

     - [assumption]: Try to find a hypothesis [H] in the context that
       exactly matches the goal; if one is found, solve the goal.

     - [contradiction]: Try to find a hypothesis [H] in the current
       context that is logically equivalent to [False].  If one is
       found, solve the goal.

     - [constructor]: Try to find a constructor [c] (from some
       [Inductive] definition in the current environment) that can be
       applied to solve the current goal.  If one is found, behave
       like [apply c].

    We'll see examples of all of these as we go along. *)

(* ################################################################# *)
(** * Evaluation as a Relation *)

(** We have presented [aeval] and [beval] as functions defined by
    [Fixpoint]s.  Another way to think about evaluation -- one that we
    will see is often more flexible -- is as a _relation_ between
    expressions and their values.  This leads naturally to [Inductive]
    definitions like the following one for arithmetic expressions... *)

Module aevalR_first_try.

Inductive aevalR : aexp -> nat -> Prop :=
  | E_ANum n :
      aevalR (ANum n) n
  | E_APlus (e1 e2: aexp) (n1 n2: nat) :
      aevalR e1 n1 ->
      aevalR e2 n2 ->
      aevalR (APlus e1 e2) (n1 + n2)
  | E_AMinus (e1 e2: aexp) (n1 n2: nat) :
      aevalR e1 n1 ->
      aevalR e2 n2 ->
      aevalR (AMinus e1 e2) (n1 - n2)
  | E_AMult (e1 e2: aexp) (n1 n2: nat) :
      aevalR e1 n1 ->
      aevalR e2 n2 ->
      aevalR (AMult e1 e2) (n1 * n2).

Module HypothesisNames.

(* A small notational aside. We could also write the definition of
   [aevalR] as follow, with explicit names for the hypotheses in each
   case: *)

Inductive aevalR : aexp -> nat -> Prop :=
  | E_ANum n :
      aevalR (ANum n) n
  | E_APlus (e1 e2: aexp) (n1 n2: nat)
      (H1 : aevalR e1 n1)
      (H2 : aevalR e2 n2) :
      aevalR (APlus e1 e2) (n1 + n2)
  | E_AMinus (e1 e2: aexp) (n1 n2: nat)
      (H1 : aevalR e1 n1)
      (H2 : aevalR e2 n2) :
      aevalR (AMinus e1 e2) (n1 - n2)
  | E_AMult (e1 e2: aexp) (n1 n2: nat)
      (H1 : aevalR e1 n1)
      (H2 : aevalR e2 n2) :
      aevalR (AMult e1 e2) (n1 * n2).

(** This style gives us more control over the names that Coq chooses
    during proofs involving [aevalR], at the cost of making the
    definition a little more verbose. *)

End HypothesisNames.

(** It will be convenient to have an infix notation for
    [aevalR].  We'll write [e ==> n] to mean that arithmetic expression
    [e] evaluates to value [n]. *)

Notation "e '==>' n"
         := (aevalR e n)
            (at level 90, left associativity)
         : type_scope.

End aevalR_first_try.

(** As we saw in [IndProp] in our case study of regular
    expressions, Coq provides a way to use this notation in the
    definition of [aevalR] itself. *)

Reserved Notation "e '==>' n" (at level 90, left associativity).

Inductive aevalR : aexp -> nat -> Prop :=
  | E_ANum (n : nat) :
      (ANum n) ==> n
  | E_APlus (e1 e2 : aexp) (n1 n2 : nat) :
      (e1 ==> n1) -> (e2 ==> n2) -> (APlus e1 e2) ==> (n1 + n2)
  | E_AMinus (e1 e2 : aexp) (n1 n2 : nat) :
      (e1 ==> n1) -> (e2 ==> n2) -> (AMinus e1 e2) ==> (n1 - n2)
  | E_AMult (e1 e2 : aexp) (n1 n2 : nat) :
      (e1 ==> n1) -> (e2 ==> n2) -> (AMult e1 e2) ==> (n1 * n2)

  where "e '==>' n" := (aevalR e n) : type_scope.

(* ================================================================= *)
(** ** Inference Rule Notation *)

(** In informal discussions, it is convenient to write the rules
    for [aevalR] and similar relations in the more readable graphical
    form of _inference rules_, where the premises above the line
    justify the conclusion below the line (we have already seen them
    in the [IndProp] chapter). *)

(** For example, the constructor [E_APlus]...

      | E_APlus : forall (e1 e2: aexp) (n1 n2: nat),
          aevalR e1 n1 ->
          aevalR e2 n2 ->
          aevalR (APlus e1 e2) (n1 + n2)

    ...would be written like this as an inference rule:

                               e1 ==> n1
                               e2 ==> n2
                         --------------------                (E_APlus)
                         APlus e1 e2 ==> n1+n2
*)

(** Formally, there is nothing deep about inference rules: they
    are just implications.  You can read the rule name on the right as
    the name of the constructor and read each of the linebreaks
    between the premises above the line (as well as the line itself)
    as [->].  All the variables mentioned in the rule ([e1], [n1],
    etc.) are implicitly bound by universal quantifiers at the
    beginning. (Such variables are often called _metavariables_ to
    distinguish them from the variables of the language we are
    defining.  At the moment, our arithmetic expressions don't include
    variables, but we'll soon be adding them.)  The whole collection
    of rules is understood as being wrapped in an [Inductive]
    declaration.  In informal prose, this is either elided or else
    indicated by saying something like "Let [aevalR] be the smallest
    relation closed under the following rules...". *)

(** For example, [==>] is the smallest relation closed under these
    rules:

                             -----------                               (E_ANum)
                             ANum n ==> n

                               e1 ==> n1
                               e2 ==> n2
                         --------------------                         (E_APlus)
                         APlus e1 e2 ==> n1+n2

                               e1 ==> n1
                               e2 ==> n2
                        ---------------------                        (E_AMinus)
                        AMinus e1 e2 ==> n1-n2

                               e1 ==> n1
                               e2 ==> n2
                         --------------------                         (E_AMult)
                         AMult e1 e2 ==> n1*n2
*)

(** **** Exercise: 1 star, standard, optional (beval_rules) 

    Here, again, is the Coq definition of the [beval] function:

  Fixpoint beval (e : bexp) : bool :=
    match e with
    | BTrue       => true
    | BFalse      => false
    | BEq a1 a2   => (aeval a1) =? (aeval a2)
    | BLe a1 a2   => (aeval a1) <=? (aeval a2)
    | BNot b1     => negb (beval b1)
    | BAnd b1 b2  => andb (beval b1) (beval b2)
    end.

    Write out a corresponding definition of boolean evaluation as a
    relation (in inference rule notation). *)
(* SOLUTION: *)
(* Answer:

                            -------------                             (E_BTrue)
                            BTrue ==> true

                           ---------------                           (E_BFalse)
                           BFalse ==> false

                               e1 ==> n1
                               e2 ==> n2
                        -----------------------                         (E_BEq)
                        BEq e1 e2 ==> (n1 =? n2)

                               e1 ==> n1
                               e2 ==> n2
                        ------------------------                        (E_BLe)
                        BLe e1 e2 ==> (n1 <=? n2)

                               e1 ==> b1
                          ------------------                           (E_BNot)
                          BNot e1 ==> negb b1

                               e1 ==> b1
                               e2 ==> b2
                       ------------------------                        (E_BAnd)
                       BAnd e1 e2 ==> andb b1 b2
*)

(* Do not modify the following line: *)
Definition manual_grade_for_beval_rules : option (nat*string) := None.
(** [] *)

(* ================================================================= *)
(** ** Equivalence of the Definitions *)

(** It is straightforward to prove that the relational and functional
    definitions of evaluation agree: *)

Theorem aeval_iff_aevalR : forall a n,
  (a ==> n) <-> aeval a = n.
Proof.
 split.
 - (* -> *)
   intros H.
   induction H; simpl.
   + (* E_ANum *)
     reflexivity.
   + (* E_APlus *)
     rewrite IHaevalR1.  rewrite IHaevalR2.  reflexivity.
   + (* E_AMinus *)
     rewrite IHaevalR1.  rewrite IHaevalR2.  reflexivity.
   + (* E_AMult *)
     rewrite IHaevalR1.  rewrite IHaevalR2.  reflexivity.
 - (* <- *)
   generalize dependent n.
   induction a;
      simpl; intros; subst.
   + (* ANum *)
     apply E_ANum.
   + (* APlus *)
     apply E_APlus.
      apply IHa1. reflexivity.
      apply IHa2. reflexivity.
   + (* AMinus *)
     apply E_AMinus.
      apply IHa1. reflexivity.
      apply IHa2. reflexivity.
   + (* AMult *)
     apply E_AMult.
      apply IHa1. reflexivity.
      apply IHa2. reflexivity.
Qed.

(** We can make the proof quite a bit shorter by making more
    use of tacticals. *)

Theorem aeval_iff_aevalR' : forall a n,
  (a ==> n) <-> aeval a = n.
Proof.
  (* WORKED IN CLASS *)
  split.
  - (* -> *)
    intros H; induction H; subst; reflexivity.
  - (* <- *)
    generalize dependent n.
    induction a; simpl; intros; subst; constructor;
       try apply IHa1; try apply IHa2; reflexivity.
Qed.

(** **** Exercise: 3 stars, standard (bevalR) 

    Write a relation [bevalR] in the same style as
    [aevalR], and prove that it is equivalent to [beval]. *)

Reserved Notation "e '==>b' b" (at level 90, left associativity).
Inductive bevalR: bexp -> bool -> Prop :=
(* SOLUTION: *)
  | BETrue : bevalR BTrue true
  | BEFalse : bevalR BFalse false
  | BEEq : forall  a1 a2 n1 n2,
    aevalR  a1 n1 ->
    aevalR  a2 n2 ->
    bevalR  (BEq a1 a2) (n1 =? n2)
  | BELe : forall  a1 a2 n1 n2,
    aevalR  a1 n1 ->
    aevalR  a2 n2 ->
    bevalR  (BLe a1 a2) (n1 <=? n2)
  | BENot : forall  b1 tv1,
    bevalR  b1 tv1 ->
    bevalR  (BNot b1) (negb tv1)
  | BEAnd : forall  b1 b2 tv1 tv2,
    bevalR  b1 tv1 ->
    bevalR  b2 tv2 ->
    bevalR  (BAnd b1 b2) (andb tv1 tv2)
where "e '==>b' b" := (bevalR e b) : type_scope
.

Lemma beval_iff_bevalR : forall b bv,
  b ==>b bv <-> beval b = bv.
Proof.
  (* SOLUTION: *)
  split.
  - (* -> *)
    intros H.
    induction H; simpl; intros; subst;
       try (rewrite aeval_iff_aevalR in H, H0; rewrite H; rewrite H0); reflexivity.
  - (* <- *)
    generalize dependent bv.
    induction b; simpl; intros; subst; constructor;
      try rewrite aeval_iff_aevalR;
      try apply IHb; try apply IHb1; try apply IHb2; try reflexivity.
Qed.
(** [] *)

End AExp.

(* ================================================================= *)
(** ** Computational vs. Relational Definitions *)

(** For the definitions of evaluation for arithmetic and boolean
    expressions, the choice of whether to use functional or relational
    definitions is mainly a matter of taste: either way works.

    However, there are circumstances where relational definitions of
    evaluation work much better than functional ones.  *)

Module aevalR_division.

(** For example, suppose that we wanted to extend the arithmetic
    operations with division: *)

Inductive aexp : Type :=
  | ANum (n : nat)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp)
  | ADiv (a1 a2 : aexp).         (* <--- NEW *)

(** Extending the definition of [aeval] to handle this new
    operation would not be straightforward (what should we return as
    the result of [ADiv (ANum 5) (ANum 0)]?).  But extending [aevalR]
    is very easy. *)

Reserved Notation "e '==>' n"
                  (at level 90, left associativity).

Inductive aevalR : aexp -> nat -> Prop :=
  | E_ANum (n : nat) :
      (ANum n) ==> n
  | E_APlus (a1 a2 : aexp) (n1 n2 : nat) :
      (a1 ==> n1) -> (a2 ==> n2) -> (APlus a1 a2) ==> (n1 + n2)
  | E_AMinus (a1 a2 : aexp) (n1 n2 : nat) :
      (a1 ==> n1) -> (a2 ==> n2) -> (AMinus a1 a2) ==> (n1 - n2)
  | E_AMult (a1 a2 : aexp) (n1 n2 : nat) :
      (a1 ==> n1) -> (a2 ==> n2) -> (AMult a1 a2) ==> (n1 * n2)
  | E_ADiv (a1 a2 : aexp) (n1 n2 n3 : nat) :          (* <----- NEW *)
      (a1 ==> n1) -> (a2 ==> n2) -> (n2 > 0) ->
      (mult n2 n3 = n1) -> (ADiv a1 a2) ==> n3

where "a '==>' n" := (aevalR a n) : type_scope.

(** Notice that the evaluation relation has now become _partial_:
    There are some inputs for which it simply does not specify an
    output. *)

End aevalR_division.

Module aevalR_extended.

(** Or suppose that we want to extend the arithmetic operations
    by a nondeterministic number generator [any] that, when evaluated,
    may yield any number. Note that this is not the same as making a
    _probabilistic_ choice among all possible numbers -- we're not
    specifying any particular probability distribution for the
    results, just saying what results are _possible_. *)

Reserved Notation "e '==>' n" (at level 90, left associativity).

Inductive aexp : Type :=
  | AAny                           (* <--- NEW *)
  | ANum (n : nat)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp).

(** Again, extending [aeval] would be tricky, since now
    evaluation is _not_ a deterministic function from expressions to
    numbers, but extending [aevalR] is no problem... *)

Inductive aevalR : aexp -> nat -> Prop :=
  | E_Any (n : nat) :
      AAny ==> n                        (* <--- NEW *)
  | E_ANum (n : nat) :
      (ANum n) ==> n
  | E_APlus (a1 a2 : aexp) (n1 n2 : nat) :
      (a1 ==> n1) -> (a2 ==> n2) -> (APlus a1 a2) ==> (n1 + n2)
  | E_AMinus (a1 a2 : aexp) (n1 n2 : nat) :
      (a1 ==> n1) -> (a2 ==> n2) -> (AMinus a1 a2) ==> (n1 - n2)
  | E_AMult (a1 a2 : aexp) (n1 n2 : nat) :
      (a1 ==> n1) -> (a2 ==> n2) -> (AMult a1 a2) ==> (n1 * n2)

where "a '==>' n" := (aevalR a n) : type_scope.

End aevalR_extended.

(** At this point you maybe wondering: which style should I use
    by default?  In the examples we've just seen, relational
    definitions turned out to be more useful than functional ones.
    For situations like these, where the thing being defined is not
    easy to express as a function, or indeed where it is _not_ a
    function, there is no real choice.  But what about when both
    styles are workable?

    One point in favor of relational definitions is that they can be
    more elegant and easier to understand.

    Another is that Coq automatically generates nice inversion and
    induction principles from [Inductive] definitions.

    On the other hand, functional definitions can often be more
    convenient:
     - Functions are by definition deterministic and defined on all
       arguments; for a relation we have to _prove_ these properties
       explicitly if we need them.
     - With functions we can also take advantage of Coq's computation
       mechanism to simplify expressions during proofs.

    Furthermore, functions can be directly "extracted" from Gallina to
    executable code in OCaml or Haskell.

    Ultimately, the choice often comes down to either the specifics of
    a particular situation or simply a question of taste.  Indeed, in
    large Coq developments it is common to see a definition given in
    _both_ functional and relational styles, plus a lemma stating that
    the two coincide, allowing further proofs to switch from one point
    of view to the other at will. *)

(* ################################################################# *)
(** * Expressions With Variables *)

(** Now we return to defining Imp. The next thing we need to do is to
    enrich our arithmetic and boolean expressions with variables. To
    keep things simple, we'll assume that all variables are global and
    that they only hold numbers. *)

(* ================================================================= *)
(** ** States *)

(** Since we'll want to look variables up to find out their current
    values, we'll reuse maps from the [Maps] chapter, and
    [string]s will be used to represent variables in Imp.

    A _machine state_ (or just _state_) represents the current values
    of _all_ variables at some point in the execution of a program. *)

(** For simplicity, we assume that the state is defined for
    _all_ variables, even though any given program is only going to
    mention a finite number of them.  The state captures all of the
    information stored in memory.  For Imp programs, because each
    variable stores a natural number, we can represent the state as a
    mapping from strings to [nat], and will use [0] as default value
    in the store. For more complex programming languages, the state
    might have more structure. *)

Definition state := total_map nat.

(* ================================================================= *)
(** ** Syntax  *)

(** We can add variables to the arithmetic expressions we had before by
    simply adding one more constructor: *)

Inductive aexp : Type :=
  | ANum (n : nat)
  | AId (x : string)              (* <--- NEW *)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp).

(** Defining a few variable names as notational shorthands will make
    examples easier to read: *)

Definition W : string := "W".
Definition X : string := "X".
Definition Y : string := "Y".
Definition Z : string := "Z".

(** (This convention for naming program variables ([X], [Y],
    [Z]) clashes a bit with our earlier use of uppercase letters for
    types.  Since we're not using polymorphism heavily in the chapters
    developed to Imp, this overloading should not cause confusion.) *)

(** The definition of [bexp]s is unchanged (except that it now refers
    to the new [aexp]s): *)

Inductive bexp : Type :=
  | BTrue
  | BFalse
  | BEq (a1 a2 : aexp)
  | BLe (a1 a2 : aexp)
  | BNot (b : bexp)
  | BAnd (b1 b2 : bexp).

(* ================================================================= *)
(** ** Notations *)

(** To make Imp programs easier to read and write, we introduce
    some notations and implicit coercions. *)

(** You do not need to understand exactly what these
    declarations do.  Briefly, though, the [Coercion] declaration in
    Coq stipulates that a function (or constructor) can be implicitly
    used by the type system to coerce a value of the input type to a
    value of the output type.  For instance, the coercion declaration
    for [AId] allows us to use plain strings when an [aexp] is
    expected; the string will implicitly be wrapped with [AId].

    The notations below are declared in specific _notation scopes_, in
    order to avoid conflicts with other interpretations of the same
    symbols.  Again, it is not necessary to understand the details,
    but it is important to recognize that we are defining _new_
    interpretations for some familiar operators like [+], [-], [*],
    [=], [<=], etc. *)

Coercion AId : string >-> aexp.
Coercion ANum : nat >-> aexp.

Definition bool_to_bexp (b : bool) : bexp :=
  if b then BTrue else BFalse.
Coercion bool_to_bexp : bool >-> bexp.

Bind Scope imp_scope with aexp.
Bind Scope imp_scope with bexp.
Delimit Scope imp_scope with imp.

Notation "x + y" := (APlus x y) (at level 50, left associativity) : imp_scope.
Notation "x - y" := (AMinus x y) (at level 50, left associativity) : imp_scope.
Notation "x * y" := (AMult x y) (at level 40, left associativity) : imp_scope.
Notation "x <= y" := (BLe x y) (at level 70, no associativity) : imp_scope.
Notation "x = y" := (BEq x y) (at level 70, no associativity) : imp_scope.
Notation "x && y" := (BAnd x y) (at level 40, left associativity) : imp_scope.
Notation "'~' b" := (BNot b) (at level 75, right associativity) : imp_scope.

(** We can now write [3 + (X * 2)] instead of [APlus 3 (AMult X 2)],
    and [true && ~(X <= 4)] instead of [BAnd true (BNot (BLe X 4))].
    But this only works when we tell Coq to parse our expressions in
    the appropriate notation scope by using [%imp], or when Coq knows
    that the expression has a type ([aexp] or [bexp]) that has
    been "bound" to use that notation scope. *)

Definition example_aexp : aexp := 3 + (X * 2).
Definition example_bexp : bexp := true && ~(X <= 4).

(** One downside of these coercions is that they can make it a little
    harder for humans to calculate the types of expressions.  If you
    get confused, try doing [Set Printing Coercions] to see exactly
    what is going on. *)

Set Printing Coercions.

Print example_bexp.
(* ===> (example_bexp = bool_to_bexp true && ~ (AId X <= ANum 4))%imp *)

Unset Printing Coercions.

(* ================================================================= *)
(** ** Evaluation *)

(** The arith and boolean evaluators are extended to handle
    variables in the obvious way, taking a state as an extra
    argument: *)

Fixpoint aeval (st : state) (a : aexp) : nat :=
  match a with
  | ANum n => n
  | AId x => st x                                (* <--- NEW *)
  | APlus a1 a2 => (aeval st a1) + (aeval st a2)
  | AMinus a1 a2  => (aeval st a1) - (aeval st a2)
  | AMult a1 a2 => (aeval st a1) * (aeval st a2)
  end.

Fixpoint beval (st : state) (b : bexp) : bool :=
  match b with
  | BTrue       => true
  | BFalse      => false
  | BEq a1 a2   => (aeval st a1) =? (aeval st a2)
  | BLe a1 a2   => (aeval st a1) <=? (aeval st a2)
  | BNot b1     => negb (beval st b1)
  | BAnd b1 b2  => andb (beval st b1) (beval st b2)
  end.

(** We specialize our notation for total maps to the specific case of
    states, i.e. using [(_ !-> 0)] as empty state. *)

Definition empty_st := (_ !-> 0).

(** Now we can add a notation for a "singleton state" with just one
    variable bound to a value. *)
Notation "x '!->' v" := (t_update empty_st x v) (at level 100).

Example aexp1 :
    aeval (X !-> 5) (3 + (X * 2))
  = 13.
Proof. reflexivity. Qed.

Example bexp1 :
    beval (X !-> 5) (true && ~(X <= 4))
  = true.
Proof. reflexivity. Qed.

(* ################################################################# *)
(** * Commands *)

(** Now we are ready define the syntax and behavior of Imp
    _commands_ (sometimes called _statements_). *)

(* ================================================================= *)
(** ** Syntax *)

(** Informally, commands [c] are described by the following BNF
    grammar.

     c ::= SKIP | x ::= a | c ;; c | TEST b THEN c ELSE c FI
         | WHILE b DO c END
*)
(** We choose this slightly awkward concrete syntax for the
    sake of being able to define Imp syntax using Coq's notation
    mechanism.  In particular, we use [TEST] to avoid conflicting with
    the [if] and [IF] notations from the standard library.) *)

(** Here is the formal definition of the abstract syntax of
    commands: *)

Inductive com : Type :=
  | CSkip
  | CAss (x : string) (a : aexp)
  | CSeq (c1 c2 : com)
  | CIf (b : bexp) (c1 c2 : com)
  | CWhile (b : bexp) (c : com).

(** As for expressions, we can use a few [Notation] declarations to
    make reading and writing Imp programs more convenient. *)

Bind Scope imp_scope with com.
Notation "'SKIP'" :=
   CSkip : imp_scope.
Notation "x '::=' a" :=
  (CAss x a) (at level 60) : imp_scope.
Notation "c1 ;; c2" :=
  (CSeq c1 c2) (at level 80, right associativity) : imp_scope.
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity) : imp_scope.
Notation "'TEST' c1 'THEN' c2 'ELSE' c3 'FI'" :=
  (CIf c1 c2 c3) (at level 80, right associativity) : imp_scope.

(** For example, here is the factorial function again, written as a
    formal definition to Coq: *)

Definition fact_in_coq : com :=
  Z ::= X;;
  Y ::= 1;;
  WHILE ~(Z = 0) DO
    Y ::= Y * Z;;
    Z ::= Z - 1
  END.

(* ================================================================= *)
(** ** Desugaring notations *)

(** Coq offers a rich set of features to manage the increasing
    complexity of the objects we work with, such as coercions
    and notations. However, their heavy usage can make for quite
    overwhelming syntax. It is often instructive to "turn off"
    those features to get a more elementary picture of things,
    using the following commands:

    - [Unset Printing Notations] (undo with [Set Printing Notations])
    - [Set Printing Coercions] (undo with [Unset Printing Coercions])
    - [Set Printing All] (undo with [Unset Printing All])

    These commands can also be used in the middle of a proof,
    to elaborate the current goal and context.
 *)

Unset Printing Notations.
Print fact_in_coq.
(* ===>
   fact_in_coq =
   CSeq (CAss Z X)
        (CSeq (CAss Y (S O))
              (CWhile (BNot (BEq Z O))
                      (CSeq (CAss Y (AMult Y Z))
                            (CAss Z (AMinus Z (S O))))))
        : com *)
Set Printing Notations.

Set Printing Coercions.
Print fact_in_coq.
(* ===>
   fact_in_coq =
   (Z ::= AId X;;
   Y ::= ANum 1;;
   WHILE ~ (AId Z = ANum 0) DO
     Y ::= AId Y * AId Z;;
     Z ::= AId Z - ANum 1
   END)
       : com *)
Unset Printing Coercions.

(* ================================================================= *)
(** ** The [Locate] command *)

(* ----------------------------------------------------------------- *)
(** *** Finding notations *)

(** When faced with unknown notation, use [Locate] with a _string_
    containing one of its symbols to see its possible
    interpretations. *)
Locate "&&".
(* ===>
   Notation "x && y" := andb x y : bool_scope (default interpretation) *)

Locate ";;".
(* ===>
   Notation "c1 ;; c2" := CSeq c1 c2 : imp_scope *)

Locate "WHILE".
(* ===>
   Notation "'WHILE' b 'DO' c 'END'" := CWhile b c : imp_scope *)

(* ----------------------------------------------------------------- *)
(** *** Finding identifiers *)

(** When used with an identifier, the command [Locate] prints
    the full path to every value in scope with the same name.
    This is useful to troubleshoot problems due to variable
    shadowing. *)
Locate aexp.
(* ===>
   Inductive Top.aexp
   Inductive Top.AExp.aexp
     (shorter name to refer to it in current context is AExp.aexp)
   Inductive Top.aevalR_division.aexp
     (shorter name to refer to it in current context is aevalR_division.aexp)
   Inductive Top.aevalR_extended.aexp
     (shorter name to refer to it in current context is aevalR_extended.aexp)
*)

(* ================================================================= *)
(** ** More Examples *)

(** Assignment: *)

Definition plus2 : com :=
  X ::= X + 2.

Definition XtimesYinZ : com :=
  Z ::= X * Y.

Definition subtract_slowly_body : com :=
  Z ::= Z - 1 ;;
  X ::= X - 1.

(* ----------------------------------------------------------------- *)
(** *** Loops *)

Definition subtract_slowly : com :=
  WHILE ~(X = 0) DO
    subtract_slowly_body
  END.

Definition subtract_3_from_5_slowly : com :=
  X ::= 3 ;;
  Z ::= 5 ;;
  subtract_slowly.

(* ----------------------------------------------------------------- *)
(** *** An infinite loop: *)

Definition loop : com :=
  WHILE true DO
    SKIP
  END.

(* ################################################################# *)
(** * Evaluating Commands *)

(** Next we need to define what it means to evaluate an Imp command.
    The fact that [WHILE] loops don't necessarily terminate makes
    defining an evaluation function tricky... *)

(* ================================================================= *)
(** ** Evaluation as a Function (Failed Attempt) *)

(** Here's an attempt at defining an evaluation function for commands,
    omitting the [WHILE] case. *)

(** The following declaration is needed to be able to use the
    notations in match patterns. *)
Open Scope imp_scope.
Fixpoint ceval_fun_no_while (st : state) (c : com)
                          : state :=
  match c with
    | SKIP =>
        st
    | x ::= a1 =>
        (x !-> (aeval st a1) ; st)
    | c1 ;; c2 =>
        let st' := ceval_fun_no_while st c1 in
        ceval_fun_no_while st' c2
    | TEST b THEN c1 ELSE c2 FI =>
        if (beval st b)
          then ceval_fun_no_while st c1
          else ceval_fun_no_while st c2
    | WHILE b DO c END =>
        st  (* bogus *)
  end.
Close Scope imp_scope.

(** In a traditional functional programming language like OCaml or
    Haskell we could add the [WHILE] case as follows:

        Fixpoint ceval_fun (st : state) (c : com) : state :=
          match c with
            ...
            | WHILE b DO c END =>
                if (beval st b)
                  then ceval_fun st (c ;; WHILE b DO c END)
                  else st
          end.

    Coq doesn't accept such a definition ("Error: Cannot guess
    decreasing argument of fix") because the function we want to
    define is not guaranteed to terminate. Indeed, it _doesn't_ always
    terminate: for example, the full version of the [ceval_fun]
    function applied to the [loop] program above would never
    terminate. Since Coq is not just a functional programming
    language but also a consistent logic, any potentially
    non-terminating function needs to be rejected. Here is
    an (invalid!) program showing what would go wrong if Coq
    allowed non-terminating recursive functions:

         Fixpoint loop_false (n : nat) : False := loop_false n.

    That is, propositions like [False] would become provable
    ([loop_false 0] would be a proof of [False]), which
    would be a disaster for Coq's logical consistency.

    Thus, because it doesn't terminate on all inputs,
    of [ceval_fun] cannot be written in Coq -- at least not without
    additional tricks and workarounds (see chapter [ImpCEvalFun]
    if you're curious about what those might be). *)

(* ================================================================= *)
(** ** Evaluation as a Relation *)

(** Here's a better way: define [ceval] as a _relation_ rather than a
    _function_ -- i.e., define it in [Prop] instead of [Type], as we
    did for [aevalR] above. *)

(** This is an important change.  Besides freeing us from awkward
    workarounds, it gives us a lot more flexibility in the definition.
    For example, if we add nondeterministic features like [any] to the
    language, we want the definition of evaluation to be
    nondeterministic -- i.e., not only will it not be total, it will
    not even be a function! *)

(** We'll use the notation [st =[ c ]=> st'] for the [ceval] relation:
    [st =[ c ]=> st'] means that executing program [c] in a starting
    state [st] results in an ending state [st'].  This can be
    pronounced "[c] takes state [st] to [st']". *)

(* ----------------------------------------------------------------- *)
(** *** Operational Semantics *)

(** Here is an informal definition of evaluation, presented as inference
    rules for readability:

                           -----------------                            (E_Skip)
                           st =[ SKIP ]=> st

                           aeval st a1 = n
                   --------------------------------                     (E_Ass)
                   st =[ x := a1 ]=> (x !-> n ; st)

                           st  =[ c1 ]=> st'
                           st' =[ c2 ]=> st''
                         ---------------------                            (E_Seq)
                         st =[ c1;;c2 ]=> st''

                          beval st b1 = true
                           st =[ c1 ]=> st'
                ---------------------------------------                (E_IfTrue)
                st =[ TEST b1 THEN c1 ELSE c2 FI ]=> st'

                         beval st b1 = false
                           st =[ c2 ]=> st'
                ---------------------------------------               (E_IfFalse)
                st =[ TEST b1 THEN c1 ELSE c2 FI ]=> st'

                         beval st b = false
                    -----------------------------                  (E_WhileFalse)
                    st =[ WHILE b DO c END ]=> st

                          beval st b = true
                           st =[ c ]=> st'
                  st' =[ WHILE b DO c END ]=> st''
                  --------------------------------                  (E_WhileTrue)
                  st  =[ WHILE b DO c END ]=> st''
*)

(** Here is the formal definition.  Make sure you understand
    how it corresponds to the inference rules. *)

Reserved Notation "st '=[' c ']=>' st'"
                  (at level 40).

Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall st,
      st =[ SKIP ]=> st
  | E_Ass  : forall st a1 n x,
      aeval st a1 = n ->
      st =[ x ::= a1 ]=> (x !-> n ; st)
  | E_Seq : forall c1 c2 st st' st'',
      st  =[ c1 ]=> st'  ->
      st' =[ c2 ]=> st'' ->
      st  =[ c1 ;; c2 ]=> st''
  | E_IfTrue : forall st st' b c1 c2,
      beval st b = true ->
      st =[ c1 ]=> st' ->
      st =[ TEST b THEN c1 ELSE c2 FI ]=> st'
  | E_IfFalse : forall st st' b c1 c2,
      beval st b = false ->
      st =[ c2 ]=> st' ->
      st =[ TEST b THEN c1 ELSE c2 FI ]=> st'
  | E_WhileFalse : forall b st c,
      beval st b = false ->
      st =[ WHILE b DO c END ]=> st
  | E_WhileTrue : forall st st' st'' b c,
      beval st b = true ->
      st  =[ c ]=> st' ->
      st' =[ WHILE b DO c END ]=> st'' ->
      st  =[ WHILE b DO c END ]=> st''

  where "st =[ c ]=> st'" := (ceval c st st').

(** The cost of defining evaluation as a relation instead of a
    function is that we now need to construct _proofs_ that some
    program evaluates to some result state, rather than just letting
    Coq's computation mechanism do it for us. *)

Example ceval_example1:
  empty_st =[
     X ::= 2;;
     TEST X <= 1
       THEN Y ::= 3
       ELSE Z ::= 4
     FI
  ]=> (Z !-> 4 ; X !-> 2).
Proof.
  (* We must supply the intermediate state *)
  apply E_Seq with (X !-> 2).
  - (* assignment command *)
    apply E_Ass. reflexivity.
  - (* if command *)
    apply E_IfFalse.
    reflexivity.
    apply E_Ass. reflexivity.
Qed.

(** **** Exercise: 2 stars, standard (ceval_example2)  *)
Example ceval_example2:
  empty_st =[
    X ::= 0;; Y ::= 1;; Z ::= 2
  ]=> (Z !-> 2 ; Y !-> 1 ; X !-> 0).
Proof.
  (* SOLUTION: *)
  apply E_Seq with (X !-> 0).
  - (* first assignment command *)
    apply E_Ass. reflexivity.
  - (* second ; *)
    apply E_Seq with (Y !-> 1 ; X !-> 0).
    + (* second assignment command *)
      apply E_Ass. reflexivity.
    + (* third assignment *)
      apply E_Ass. reflexivity.  Qed.
(** [] *)

(** **** Exercise: 3 stars, standard, optional (pup_to_n) 

    Write an Imp program that sums the numbers from [1] to [X]
    (inclusive: [1 + 2 + ... + X]) in the variable [Y].  Your program
    should update the state as shown in theorem [pup_to_2_ceval],
    which you can reverse-engineer to discover the program you should
    write.  The proof of that theorem will be somewhat lengthy. *)

Definition pup_to_n : com
  (* SOLUTION: *) :=
  Y ::= 0;;
  WHILE ~(X = 0) DO
    Y ::= Y + X;;
    X ::= X - 1
  END.

Theorem pup_to_2_ceval :
  (X !-> 2) =[
    pup_to_n
  ]=> (X !-> 0 ; Y !-> 3 ; X !-> 1 ; Y !-> 2 ; Y !-> 0 ; X !-> 2).
Proof.
  (* SOLUTION: *)
  unfold pup_to_n.
  apply E_Seq with (Y !-> 0 ; X !-> 2).
  - (* assignment command *)
    apply E_Ass. reflexivity.
  - (* while command *)
    apply E_WhileTrue with (X !-> 1 ; Y !-> 2 ; Y !-> 0 ; X !-> 2).
      reflexivity.
    + (* first round *)
      apply E_Seq with (Y !-> 2 ; Y !-> 0 ; X !-> 2).
      apply E_Ass. reflexivity.
      apply E_Ass. reflexivity.
    + (* the other rounds *)
      eapply E_WhileTrue. reflexivity.
      * (* second round *)
        eapply E_Seq.
        apply E_Ass. reflexivity.
        apply E_Ass. reflexivity.
      * (* no more rounds *)
        simpl. rewrite t_update_eq.
        apply E_WhileFalse. reflexivity. Qed.
(** [] *)

(* ================================================================= *)
(** ** Determinism of Evaluation *)

(** Changing from a computational to a relational definition of
    evaluation is a good move because it frees us from the artificial
    requirement that evaluation should be a total function.  But it
    also raises a question: Is the second definition of evaluation
    really a partial _function_?  Or is it possible that, beginning from
    the same state [st], we could evaluate some command [c] in
    different ways to reach two different output states [st'] and
    [st'']?

    In fact, this cannot happen: [ceval] _is_ a partial function: *)

Theorem ceval_deterministic: forall c st st1 st2,
     st =[ c ]=> st1  ->
     st =[ c ]=> st2 ->
     st1 = st2.
Proof.
  intros c st st1 st2 E1 E2.
  generalize dependent st2.
  induction E1; intros st2 E2; inversion E2; subst.
  - (* E_Skip *) reflexivity.
  - (* E_Ass *) reflexivity.
  - (* E_Seq *)
    assert (st' = st'0) as EQ1.
    { (* Proof of assertion *) apply IHE1_1; assumption. }
    subst st'0.
    apply IHE1_2. assumption.
  - (* E_IfTrue, b evaluates to true *)
      apply IHE1. assumption.
  - (* E_IfTrue,  b evaluates to false (contradiction) *)
      rewrite H in H5. discriminate H5.
  - (* E_IfFalse, b evaluates to true (contradiction) *)
      rewrite H in H5. discriminate H5.
  - (* E_IfFalse, b evaluates to false *)
      apply IHE1. assumption.
  - (* E_WhileFalse, b evaluates to false *)
    reflexivity.
  - (* E_WhileFalse, b evaluates to true (contradiction) *)
    rewrite H in H2. discriminate H2.
  - (* E_WhileTrue, b evaluates to false (contradiction) *)
    rewrite H in H4. discriminate H4.
  - (* E_WhileTrue, b evaluates to true *)
      assert (st' = st'0) as EQ1.
      { (* Proof of assertion *) apply IHE1_1; assumption. }
      subst st'0.
      apply IHE1_2. assumption.  Qed.

(* ################################################################# *)
(** * Reasoning About Imp Programs *)

(** We'll get deeper into more systematic and powerful techniques for
    reasoning about Imp programs in _Programming Language
    Foundations_, but we can get some distance just working with the
    bare definitions.  This section explores some examples. *)

Theorem plus2_spec : forall st n st',
  st X = n ->
  st =[ plus2 ]=> st' ->
  st' X = n + 2.
Proof.
  intros st n st' HX Heval.

  (** Inverting [Heval] essentially forces Coq to expand one step of
      the [ceval] computation -- in this case revealing that [st']
      must be [st] extended with the new value of [X], since [plus2]
      is an assignment. *)

  inversion Heval. subst. clear Heval. simpl.
  apply t_update_eq.  Qed.

(** **** Exercise: 3 stars, standard, optional (XtimesYinZ_spec) 

    State and prove a specification of [XtimesYinZ]. *)

(* SOLUTION: *)
(* Here is a specification in the style of plus2_spec *)
Theorem XtimesYinZ_spec1 : forall st nx ny st',
  st X = nx ->
  st Y = ny ->
  st =[ XtimesYinZ ]=> st' ->
  st' Z = nx * ny.
Proof.
  intros st nx ny st' HX HY Heval.
  (* Start by inverting the assignment *)
  inversion Heval. subst.
  apply t_update_eq.  Qed.

(* Though perhaps a cleaner specification would be: *)
Theorem XtimesYinZ_spec : forall st,
    st =[ XtimesYinZ ]=> (Z !-> st X * st Y ; st ).
Proof. intros. apply E_Ass. reflexivity. Qed.

(* A less informative specification would be ... *)
Theorem XtimesYinZ_spec2 : forall st, exists st',
      st =[ XtimesYinZ ]=> st'.
Proof.
  intros. exists (Z !-> st X * st Y ; st).
  apply E_Ass. reflexivity.
Qed.

(* Do not modify the following line: *)
Definition manual_grade_for_XtimesYinZ_spec : option (nat*string) := None.
(** [] *)

(** **** Exercise: 3 stars, standard, recommended (loop_never_stops)  *)
Theorem loop_never_stops : forall st st',
  ~(st =[ loop ]=> st').
Proof.
  intros st st' contra. unfold loop in contra.
  remember (WHILE true DO SKIP END)%imp as loopdef
           eqn:Heqloopdef.

  (** Proceed by induction on the assumed derivation showing that
      [loopdef] terminates.  Most of the cases are immediately
      contradictory (and so can be solved in one step with
      [discriminate]). *)

  (* SOLUTION: *)
  induction contra; try (discriminate Heqloopdef).
  - (* E_WhileFalse *)
      injection Heqloopdef. intros H0 H1. rewrite -> H1 in H. discriminate H.
    - (* E_WhileTrue *) apply IHcontra2. apply Heqloopdef. Qed.

(** [] *)

(** **** Exercise: 3 stars, standard (no_whiles_eqv) 

    Consider the following function: *)

Open Scope imp_scope.
Fixpoint no_whiles (c : com) : bool :=
  match c with
  | SKIP =>
      true
  | _ ::= _ =>
      true
  | c1 ;; c2 =>
      andb (no_whiles c1) (no_whiles c2)
  | TEST _ THEN ct ELSE cf FI =>
      andb (no_whiles ct) (no_whiles cf)
  | WHILE _ DO _ END  =>
      false
  end.
Close Scope imp_scope.

(** This predicate yields [true] just on programs that have no while
    loops.  Using [Inductive], write a property [no_whilesR] such that
    [no_whilesR c] is provable exactly when [c] is a program with no
    while loops.  Then prove its equivalence with [no_whiles]. *)

Inductive no_whilesR: com -> Prop :=
 (* SOLUTION: *)
 | nw_Skip: no_whilesR SKIP
 | nw_Ass: forall x ae, no_whilesR (x ::= ae)
 | nw_Seq: forall c1 c2,
     no_whilesR c1 ->
     no_whilesR c2 ->
     no_whilesR (c1 ;; c2)
 | nw_If: forall be c1 c2,
     no_whilesR c1 ->
     no_whilesR c2 ->
     no_whilesR (TEST be THEN c1 ELSE c2 FI)
.

Theorem no_whiles_eqv:
   forall c, no_whiles c = true <-> no_whilesR c.
Proof.
  (* SOLUTION: *)
   intros; split.
  - (* -> *)
   induction c; intro Hc;
     try (simpl in Hc; rewrite andb_true_iff in Hc;
       destruct Hc as [Hc1 Hc2]);
     try constructor;
     try (apply IHc1; assumption); try (apply IHc2; assumption).
   + (* WHILE *) discriminate Hc.
  - (* <- *)
    intro H. induction H; simpl;
      try reflexivity;
      try (rewrite IHno_whilesR1; rewrite IHno_whilesR2; reflexivity).
  Qed.
  (** [] *)

(** **** Exercise: 4 stars, standard (no_whiles_terminating) 

    Imp programs that don't involve while loops always terminate.
    State and prove a theorem [no_whiles_terminating] that says this.

    Use either [no_whiles] or [no_whilesR], as you prefer. *)

(* SOLUTION: *)
(* Here is a solution by induction on no_whilesR *)
Theorem no_whiles_terminating : forall c st,
  no_whilesR c ->
  exists st',
  st =[ c ]=> st'.
Proof.
  intros c st H. generalize dependent st.
  induction H; intros; simpl.
  - (* nw_Skip *) exists st. constructor.
  - (* nw_Ass *) exists (x !-> aeval st ae ; st).
    constructor. reflexivity.
  - (* nw_Seq *)
    destruct (IHno_whilesR1 st) as [st' IH'].
    destruct (IHno_whilesR2 st') as [st'' IH''].
    exists st''. apply E_Seq with st'; assumption.
  - (* nw_If *)
    destruct (beval st be) eqn:Heqbv.
    + (* bv = true *)
      destruct (IHno_whilesR1 st) as [st' IH'].
      exists st'. apply E_IfTrue. rewrite Heqbv. reflexivity. assumption.
    + (* bv = false *)
      destruct (IHno_whilesR2 st) as [st' IH'].
      exists st'. apply E_IfFalse. rewrite Heqbv. reflexivity. assumption.
Qed.

(* and here is an alternative solution by induction on c *)
Theorem no_whiles_terminating' : forall c st1,
  no_whiles c = true ->
  exists st2, st1 =[ c ]=> st2.
Proof.
  induction c; intros st1 Hb.

  - (* SKIP *)
    exists st1. apply E_Skip.

  - (* ::= *)
    exists (x !-> aeval st1 a ; st1). apply E_Ass. reflexivity.

  - (* ;; *)
    simpl in Hb.
    rewrite andb_true_iff in Hb.
    destruct Hb as [Hb1 Hb2].
    apply (IHc1 st1) in Hb1. destruct Hb1 as [st1' ceH1].
    apply (IHc2 st1') in Hb2. destruct Hb2 as [st1'' ceH2].
    exists st1''.
    apply E_Seq with (st' := st1'); assumption.

  - (* TEST *)
    simpl in Hb. rewrite andb_true_iff in Hb.
    destruct Hb as [Hb1 Hb2].
    destruct (beval st1 b) eqn:Heqbv.
    + (* E_IfTrue *)
      apply (IHc1 st1) in Hb1.
      destruct Hb1 as [st2 Hce1]. exists st2.
      apply E_IfTrue.
      * (* b is true *)
        rewrite <- Heqbv. reflexivity.
      * (* true branch eval *)
        assumption.
    + (* E_IfFalse *)
      apply (IHc2 st1) in Hb2.
      destruct Hb2 as [st2 Hce2]. exists st2.
      apply E_IfFalse.
      * (* b is false *)
        rewrite <- Heqbv. reflexivity.
      * (* false branch eval *)
        assumption.

  - (* WHILE *)
    discriminate Hb.  Qed.

(* Do not modify the following line: *)
Definition manual_grade_for_no_whiles_terminating : option (nat*string) := None.
(** [] *)

(* ################################################################# *)
(** * Additional Exercises *)

(** **** Exercise: 3 stars, standard (stack_compiler) 

    Old HP Calculators, programming languages like Forth and Postscript,
    and abstract machines like the Java Virtual Machine all evaluate
    arithmetic expressions using a _stack_. For instance, the expression

      (2*3)+(3*(4-2))

   would be written as

      2 3 * 3 4 2 - * +

   and evaluated like this (where we show the program being evaluated
   on the right and the contents of the stack on the left):

      [ ]           |    2 3 * 3 4 2 - * +
      [2]           |    3 * 3 4 2 - * +
      [3, 2]        |    * 3 4 2 - * +
      [6]           |    3 4 2 - * +
      [3, 6]        |    4 2 - * +
      [4, 3, 6]     |    2 - * +
      [2, 4, 3, 6]  |    - * +
      [2, 3, 6]     |    * +
      [6, 6]        |    +
      [12]          |

  The goal of this exercise is to write a small compiler that
  translates [aexp]s into stack machine instructions.

  The instruction set for our stack language will consist of the
  following instructions:
     - [SPush n]: Push the number [n] on the stack.
     - [SLoad x]: Load the identifier [x] from the store and push it
                  on the stack
     - [SPlus]:   Pop the two top numbers from the stack, add them, and
                  push the result onto the stack.
     - [SMinus]:  Similar, but subtract the first number from the second.
     - [SMult]:   Similar, but multiply. *)

Inductive sinstr : Type :=
| SPush (n : nat)
| SLoad (x : string)
| SPlus
| SMinus
| SMult.

(** Write a function to evaluate programs in the stack language. It
    should take as input a state, a stack represented as a list of
    numbers (top stack item is the head of the list), and a program
    represented as a list of instructions, and it should return the
    stack after executing the program.  Test your function on the
    examples below.

    Note that it is unspecified what to do when encountering an
    [SPlus], [SMinus], or [SMult] instruction if the stack contains
    fewer than two elements.  In a sense, it is immaterial what we do,
    since a correct compiler will never emit such a malformed program.
    But for sake of later exercises, it would be best to skip the
    offending instruction and continue with the next one.  *)

Fixpoint s_execute (st : state) (stack : list nat)
                   (prog : list sinstr)
                 : list nat
  (* SOLUTION: *) :=
  match (prog, stack) with
  | (nil,             _           ) => stack
  | (SPush n::prog',  _           ) => s_execute st (n::stack) prog'
  | (SLoad x::prog',  _           ) => s_execute st (st x::stack) prog'
  | (SPlus::prog',    n::m::stack') => s_execute st ((m+n)::stack') prog'
  | (SMinus::prog',   n::m::stack') => s_execute st ((m-n)::stack') prog'
  | (SMult::prog',    n::m::stack') => s_execute st ((m*n)::stack') prog'
  | (_::prog',        _           ) => s_execute st stack prog'
                                       (* Bad state: skip *)
  end.

Example s_execute1 :
     s_execute empty_st []
       [SPush 5; SPush 3; SPush 1; SMinus]
   = [2; 5].
(* SOLUTION: *)
Proof. reflexivity. Qed.

Example s_execute2 :
     s_execute (X !-> 3) [3;4]
       [SPush 4; SLoad X; SMult; SPlus]
   = [15; 4].
(* SOLUTION: *)
Proof. reflexivity. Qed.

(** Next, write a function that compiles an [aexp] into a stack
    machine program. The effect of running the program should be the
    same as pushing the value of the expression on the stack. *)

Fixpoint s_compile (e : aexp) : list sinstr
  (* SOLUTION: *) :=
  match e with
  | ANum n => [SPush n]
  | AId x => [SLoad x]
  | APlus a1 a2 => s_compile a1 ++ s_compile a2 ++ [SPlus]
  | AMinus a1 a2  => s_compile a1 ++ s_compile a2 ++ [SMinus]
  | AMult a1 a2 => s_compile a1 ++ s_compile a2 ++ [SMult]
  end.

(** After you've defined [s_compile], prove the following to test
    that it works. *)

Example s_compile1 :
  s_compile (X - (2 * Y))
  = [SLoad X; SPush 2; SLoad Y; SMult; SMinus].
(* SOLUTION: *)
Proof. reflexivity. Qed.
(** [] *)

(** **** Exercise: 3 stars, standard (execute_app)  *)

(** Execution can be decomposed in the following sense: executing
    stack program [p1 ++ p2] is the same as executing [p1], taking
    the resulting stack, and executing [p2] from that stack. Prove
    that fact. *)

Theorem execute_app : forall st p1 p2 stack,
    s_execute st stack (p1 ++ p2) = s_execute st (s_execute st stack p1) p2.
Proof.
  (* SOLUTION: *)
  intros st. induction p1.
  - reflexivity.
  - intros p2 stack. destruct a; simpl; try apply IHp1;
    destruct stack as [ | x [ | y t ]]; simpl; try apply IHp1.
Qed.

(** [] *)

(** **** Exercise: 3 stars, standard (stack_compiler_correct)  *)

(** Now we'll prove the correctness of the compiler implemented in the
    previous exercise.  Begin by proving the following lemma. If it
    becomes difficult, consider whether your implementation of
    [s_execute] or [s_compile] could be simplified. *)

Lemma s_compile_correct_aux : forall st e stack,
  s_execute st stack (s_compile e) = aeval st e :: stack.
Proof.
  (* SOLUTION: *)
  induction e;
    try reflexivity ; (* Push, Load *)
    intros; simpl;   (* Plus, Minus, Mult *)
      repeat rewrite execute_app;
      rewrite IHe1; rewrite IHe2; simpl; reflexivity.
Qed.

(** The main theorem should be a very easy corollary of that lemma. *)

Theorem s_compile_correct : forall (st : state) (e : aexp),
  s_execute st [] (s_compile e) = [ aeval st e ].
Proof.
  (* SOLUTION: *)
  intros. apply s_compile_correct_aux.
Qed.

(** [] *)

(** **** Exercise: 3 stars, standard, optional (short_circuit) 

    Most modern programming languages use a "short-circuit" evaluation
    rule for boolean [and]: to evaluate [BAnd b1 b2], first evaluate
    [b1].  If it evaluates to [false], then the entire [BAnd]
    expression evaluates to [false] immediately, without evaluating
    [b2].  Otherwise, [b2] is evaluated to determine the result of the
    [BAnd] expression.

    Write an alternate version of [beval] that performs short-circuit
    evaluation of [BAnd] in this manner, and prove that it is
    equivalent to [beval].  (N.b. This is only true because expression
    evaluation in Imp is rather simple.  In a bigger language where
    evaluating an expression might diverge, the short-circuiting [BAnd]
    would _not_ be equivalent to the original, since it would make more
    programs terminate.) *)

(* SOLUTION: *)
Fixpoint beval_sc (st : state) (e : bexp) : bool :=
  match e with
  | BTrue       => true
  | BFalse      => false
  | BEq a1 a2   => (aeval st a1) =? (aeval st a2)
  | BLe a1 a2 => (aeval st a1) <=? (aeval st a2)
  | BNot b1     => negb (beval_sc st b1)
  | BAnd b1 b2  => let eb1 := beval_sc st b1 in
      match eb1 with
      | false => false
      | true  => (beval_sc st b2)
      end
  end.

(* This exercise turned out to be easier than we intended! *)
Theorem beval__beval_sc : forall st e,
  beval st e = beval_sc st e.
Proof.
  intros st e.
  destruct e; reflexivity.
Qed.
(** [] *)

Module BreakImp.
(** **** Exercise: 4 stars, advanced (break_imp) 

    Imperative languages like C and Java often include a [break] or
    similar statement for interrupting the execution of loops. In this
    exercise we consider how to add [break] to Imp.  First, we need to
    enrich the language of commands with an additional case. *)

Inductive com : Type :=
  | CSkip
  | CBreak                        (* <--- NEW *)
  | CAss (x : string) (a : aexp)
  | CSeq (c1 c2 : com)
  | CIf (b : bexp) (c1 c2 : com)
  | CWhile (b : bexp) (c : com).

Notation "'SKIP'" :=
  CSkip.
Notation "'BREAK'" :=
  CBreak.
Notation "x '::=' a" :=
  (CAss x a) (at level 60).
Notation "c1 ;; c2" :=
  (CSeq c1 c2) (at level 80, right associativity).
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity).
Notation "'TEST' c1 'THEN' c2 'ELSE' c3 'FI'" :=
  (CIf c1 c2 c3) (at level 80, right associativity).

(** Next, we need to define the behavior of [BREAK].  Informally,
    whenever [BREAK] is executed in a sequence of commands, it stops
    the execution of that sequence and signals that the innermost
    enclosing loop should terminate.  (If there aren't any
    enclosing loops, then the whole program simply terminates.)  The
    final state should be the same as the one in which the [BREAK]
    statement was executed.

    One important point is what to do when there are multiple loops
    enclosing a given [BREAK]. In those cases, [BREAK] should only
    terminate the _innermost_ loop. Thus, after executing the
    following...

       X ::= 0;;
       Y ::= 1;;
       WHILE ~(0 = Y) DO
         WHILE true DO
           BREAK
         END;;
         X ::= 1;;
         Y ::= Y - 1
       END

    ... the value of [X] should be [1], and not [0].

    One way of expressing this behavior is to add another parameter to
    the evaluation relation that specifies whether evaluation of a
    command executes a [BREAK] statement: *)

Inductive result : Type :=
  | SContinue
  | SBreak.

Reserved Notation "st '=[' c ']=>' st' '/' s"
         (at level 40, st' at next level).

(** Intuitively, [st =[ c ]=> st' / s] means that, if [c] is started in
    state [st], then it terminates in state [st'] and either signals
    that the innermost surrounding loop (or the whole program) should
    exit immediately ([s = SBreak]) or that execution should continue
    normally ([s = SContinue]).

    The definition of the "[st =[ c ]=> st' / s]" relation is very
    similar to the one we gave above for the regular evaluation
    relation ([st =[ c ]=> st']) -- we just need to handle the
    termination signals appropriately:

    - If the command is [SKIP], then the state doesn't change and
      execution of any enclosing loop can continue normally.

    - If the command is [BREAK], the state stays unchanged but we
      signal a [SBreak].

    - If the command is an assignment, then we update the binding for
      that variable in the state accordingly and signal that execution
      can continue normally.

    - If the command is of the form [TEST b THEN c1 ELSE c2 FI], then
      the state is updated as in the original semantics of Imp, except
      that we also propagate the signal from the execution of
      whichever branch was taken.

    - If the command is a sequence [c1 ;; c2], we first execute
      [c1].  If this yields a [SBreak], we skip the execution of [c2]
      and propagate the [SBreak] signal to the surrounding context;
      the resulting state is the same as the one obtained by
      executing [c1] alone. Otherwise, we execute [c2] on the state
      obtained after executing [c1], and propagate the signal
      generated there.

    - Finally, for a loop of the form [WHILE b DO c END], the
      semantics is almost the same as before. The only difference is
      that, when [b] evaluates to true, we execute [c] and check the
      signal that it raises.  If that signal is [SContinue], then the
      execution proceeds as in the original semantics. Otherwise, we
      stop the execution of the loop, and the resulting state is the
      same as the one resulting from the execution of the current
      iteration.  In either case, since [BREAK] only terminates the
      innermost loop, [WHILE] signals [SContinue]. *)

(** Based on the above description, complete the definition of the
    [ceval] relation. *)

Inductive ceval : com -> state -> result -> state -> Prop :=
  | E_Skip : forall st,
      st =[ CSkip ]=> st / SContinue
  (* SOLUTION: *)
  | E_Break : forall st,
      st =[ CBreak ]=> st / SBreak
  | E_Ass  : forall st a1 n x,
      aeval st a1 = n ->
      st =[ x ::= a1 ]=> (X !-> n ; st) / SContinue
  | E_SeqContinue : forall c1 c2 st st' st'' s,
      st =[ c1 ]=> st' / SContinue ->
      st' =[ c2 ]=> st'' / s ->
      st =[ c1 ;; c2 ]=> st'' / s
  | E_SeqBreak : forall c1 c2 st st',
      st =[ c1 ]=> st' / SBreak ->
      st =[ c1 ;; c2 ]=> st' / SBreak
  | E_If : forall c1 c2 b st st' s,
      st =[ if beval st b then c1 else c2 ]=> st' / s ->
      st =[ TEST b THEN c1 ELSE c2 FI ]=> st' / s
  | E_WhileFalse : forall c b st,
      beval st b = false ->
      st =[ WHILE b DO c END ]=> st / SContinue
  | E_WhileContinue : forall c b st st' st'',
      beval st b = true ->
      st  =[ c ]=> st' / SContinue ->
      st' =[ WHILE b DO c END ]=> st'' / SContinue ->
      st  =[ WHILE b DO c END ]=> st'' / SContinue
  | E_WhileBreak : forall c b st st',
      beval st b = true ->
      st =[ c ]=> st' / SBreak ->
      st =[ WHILE b DO c END ]=> st' / SContinue
  
  where "st '=[' c ']=>' st' '/' s" := (ceval c st s st').

(** Now prove the following properties of your definition of [ceval]: *)

Theorem break_ignore : forall c st st' s,
     st =[ BREAK;; c ]=> st' / s ->
     st = st'.
Proof.
  (* SOLUTION: *)
  intros c st st' s H.
  inversion H; clear H; subst.
  inversion H2.
  inversion H5. subst. reflexivity.
Qed.

Theorem while_continue : forall b c st st' s,
  st =[ WHILE b DO c END ]=> st' / s ->
  s = SContinue.
Proof.
  (* SOLUTION: *)
  intros b c st st' s H. inversion H; reflexivity.
Qed.

Theorem while_stops_on_break : forall b c st st',
  beval st b = true ->
  st =[ c ]=> st' / SBreak ->
  st =[ WHILE b DO c END ]=> st' / SContinue.
Proof.
  (* SOLUTION: *)
  intros b c st st' H1 H2.
  apply E_WhileBreak; assumption.
Qed.
(** [] *)

(** **** Exercise: 3 stars, advanced, optional (while_break_true)  *)
Theorem while_break_true : forall b c st st',
  st =[ WHILE b DO c END ]=> st' / SContinue ->
  beval st' b = true ->
  exists st'', st'' =[ c ]=> st' / SBreak.
Proof.
(* SOLUTION: *)
  intros b c st st' H Hb.
  remember (WHILE b DO c END) as c'.
  induction H; inversion Heqc'; clear Heqc'; subst.
  - (* E_WhileFalse *)
    rewrite Hb in H. discriminate H.
  - (* E_WhileContinue *)
    clear IHceval1.
    apply IHceval2. reflexivity. assumption.
  - (* E_WhileBreak *)
    exists st. assumption.
Qed.
(** [] *)

(** **** Exercise: 4 stars, advanced, optional (ceval_deterministic)  *)
Theorem ceval_deterministic: forall (c:com) st st1 st2 s1 s2,
     st =[ c ]=> st1 / s1 ->
     st =[ c ]=> st2 / s2 ->
     st1 = st2 /\ s1 = s2.
Proof.
  (* SOLUTION: *)
  intros c st st1 st2 s1 s2 E1 E2.
  generalize dependent s2.
  generalize dependent st2.
  induction E1;
    intros st2 s2 E2;
    inversion E2; clear E2; subst;
    try (rewrite H in H2; inversion H2);
    try (rewrite H in H5; inversion H5);
    try (apply IHE1_1 in H1; destruct H1 as [H11 H12]; try subst);
    try (apply IHE1_2 in H5; destruct H5 as [H51 H52]; try subst);
    try (apply IHE1_1 in H4; destruct H4 as [H41 H42]; inversion H42);
    try (apply IHE1 in H1; destruct H1 as [H11 H12]; try subst; inversion H12);
    try (apply IHE1 in H4; destruct H4 as [H41 H42]; try subst; inversion H42);
    try (apply IHE1_1 in H3; destruct H3 as [H31 H32]; try subst; inversion H32);
    try (apply IHE1_1 in H6; destruct H6 as [H61 H62]; try subst; inversion H62);
    try (apply IHE1_2 in H7; destruct H7 as [H71 H72]; try subst; inversion H72);
    try (apply IHE1 in H3; destruct H3 as [H31 H32]; try subst; inversion H32);
    try (apply IHE1 in H6; destruct H6 as [H61 H62]; try subst; inversion H62);
    try (split; reflexivity).
  - (* E_If *)
    apply IHE1. assumption.
Qed.

(** [] *)
End BreakImp.

(** **** Exercise: 4 stars, standard, optional (add_for_loop) 

    Add C-style [for] loops to the language of commands, update the
    [ceval] definition to define the semantics of [for] loops, and add
    cases for [for] loops as needed so that all the proofs in this
    file are accepted by Coq.

    A [for] loop should be parameterized by (a) a statement executed
    initially, (b) a test that is run on each iteration of the loop to
    determine whether the loop should continue, (c) a statement
    executed at the end of each loop iteration, and (d) a statement
    that makes up the body of the loop.  (You don't need to worry
    about making up a concrete Notation for [for] loops, but feel free
    to play with this too if you like.) *)

(* SOLUTION: *)
(* (Providing a solution for this exercise would involve changes
   in many places, so we'll leave this one to you!)

    [] *)


(* 13 Apr 2020 *)
