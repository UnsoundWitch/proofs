(** * BagPerm:  Insertion Sort With Bags *)

(** We have seen how to specify algorithms on "collections", such as
    sorting algorithms, using [Permutation]s.  Instead of using
    permutations, another way to specify these algorithms is to use
    _bags_ (also called _multisets_), which we introduced in [Lists].
    A _set_ of values is like a list with no repeats where
    the order does not matter.  A _multiset_ is like a list, possibly
    with repeats, where the order does not matter.  Whereas the principal
    query on a set is whether a given element appears in it, the
    principal query on a bag is _how many_ times a given element appears 
    in it. *)

From Coq Require Import Strings.String. (* for manual grading *)
From Coq Require Import Setoid Morphisms.
From VFA Require Import Perm.
From VFA Require Import Sort.

(** To keep this chapter more self-contained, 
we restate the critical definitions from [Lists].  *)
Definition bag := list nat.

Fixpoint count (v:nat) (s:bag) : nat :=
  match s with
  | nil => 0
  | h :: t =>
      (if h =? v then 1 else 0) + count v t
  end.

(** We will say two bags are _equivalent_ if they have the same number
    of copies of every possible element. *)

Definition bag_eqv (b1 b2: bag) : Prop :=
  forall n, count n b1 = count n b2. 

(** **** Exercise: 2 stars, standard (bag_eqv_properties)  *)

(* It is easy to prove [bag_eqv] is an equivalence relation. *)

Lemma bag_eqv_refl : forall b, bag_eqv b b.
Proof.
  induction b; constructor. Qed.

Lemma bag_eqv_sym: forall b1 b2, bag_eqv b1 b2 -> bag_eqv b2 b1. 
Proof.
  induction b2; unfold bag_eqv in *; intros.
  - symmetry. apply H.
  - simpl.
    destruct (a=?n) eqn:E.
    + rewrite Nat.eqb_eq in E.
      subst. specialize H with n.
      simpl in H.
      rewrite Nat.eqb_refl in H.
      omega.
    + simpl.
      specialize H with n.
      simpl in H.
      rewrite E in H.
      omega.
Qed.

Lemma bag_eqv_trans: forall b1 b2 b3, bag_eqv b1 b2 -> bag_eqv b2 b3 -> bag_eqv b1 b3.
Proof.
  unfold bag_eqv.
  intros.
  induction b2.
  - rewrite H. rewrite H0. reflexivity.
  - intros.
    specialize H with n.
    simpl in H.
    destruct (a =? n) eqn:E0;
      specialize H0 with n;
      simpl in H0;
      rewrite E0 in H0;
      omega.
Qed.

(** The following little lemma is handy in a couple of places. *)

Lemma bag_eqv_cons : forall x b1 b2, bag_eqv b1 b2 -> bag_eqv (x::b1) (x::b2).
Proof.
  unfold bag_eqv.
  intros.
  simpl.
  destruct (x =? n) eqn:E;
    specialize H with n;
    omega.
Qed.
(** [] *)

(* ################################################################# *)
(** * Correctness *)

(** A sorting algorithm must rearrange the elements into a list that
    is totally ordered.  But let's say that a different way: the
    algorithm must produce a list _with the same multiset of values_,
    and this list must be totally ordered. *)

Definition is_a_sorting_algorithm' (f: list nat -> list nat) :=
  forall al, bag_eqv al (f al) /\ sorted (f al).

(** **** Exercise: 3 stars, standard (insert_bag) 

    First, prove the auxiliary lemma [insert_bag], which will be
    useful for proving [sort_bag] below.  Your proof will be by
    induction.  *)

Lemma insert_bag: forall x l, bag_eqv (x::l) (insert x l).
Proof.
  intros. induction l.
  - constructor.
  - simpl. destruct (a >=? x).
    + apply bag_eqv_cons.
      apply bag_eqv_cons.
      apply bag_eqv_refl.
    + apply bag_eqv_trans with (a :: x :: l).
      unfold bag_eqv. intros. simpl.
      rewrite Nat.add_assoc.
      rewrite Nat.add_assoc.
      omega.
      apply bag_eqv_cons.
      apply IHl.
Qed.
(** [] *)

(** **** Exercise: 2 stars, standard (sort_bag) 

    Now prove that sort preserves bag contents. *)
Theorem sort_bag: forall l, bag_eqv l (sort l).
  intros.
  induction l.
  - constructor.
  - simpl.
    apply bag_eqv_trans with (a :: sort l).
    apply bag_eqv_cons. apply IHl.
    apply insert_bag.
Qed.
(** [] *)

(** Now we wrap it all up.  *)

Theorem insertion_sort_correct:
  is_a_sorting_algorithm' sort.
Proof.
split. apply sort_bag. apply sort_sorted.
Qed.

(** **** Exercise: 1 star, standard (permutations_vs_multiset) 

    Compare your proofs of [insert_perm, sort_perm] with your proofs
    of [insert_bag, sort_bag].  Which proofs are simpler?

      - [ ] easier with permutations,
      - [ ] easier with multisets
      - [X] about the same.

   Regardless of "difficulty", which do you prefer / find easier to
   think about?
      - [ ] permutations or
      - [X] multisets

   Put an X in one box in each list. *)
(* Do not modify the following line: *)
Definition manual_grade_for_permutations_vs_multiset : option (nat*string) := None.
(** [] *)

(* ################################################################# *)
(** * Permutations and Multisets *)

(** The two specifications of insertion sort are equivalent.  One
    reason is that permutations and multisets are closely related.
    We're going to prove:

       [Permutation al bl <-> bag_eqv al bl.] *)

(** **** Exercise: 3 stars, standard (perm_bag) 

    The forward direction is straighforward, by induction on the evidence for
    [Permutation]: *)
Lemma perm_bag:
  forall al bl : list nat,
    Permutation al bl -> bag_eqv al bl.
Proof.
  intros.
  induction H; try constructor.
  - apply bag_eqv_cons.
    apply IHPermutation.
  - unfold bag_eqv. intros.
    simpl.
    rewrite Nat.add_assoc.
    rewrite Nat.add_assoc.
    omega.
  - eapply bag_eqv_trans.
    apply IHPermutation1.
    apply IHPermutation2.
Qed.
(** [] *)

(** The other direction,
    [bag_eqv al bl -> Permutation al bl],
    is surprisingly difficult.  
    This proof approach is due to Zhong Sheng Hu.
    The first three lemmas are used to prove the fourth one. *)

(** **** Exercise: 2 stars, advanced (bag_nil_inv)  *)
Lemma bag_nil_inv : forall b, bag_eqv [] b -> b = []. 
Proof.
  intros.
  induction b.
  reflexivity.
  unfold bag_eqv in *.
  specialize H with a.
  simpl in H.
  rewrite Nat.eqb_refl in H.
  inversion H.
Qed.
(** [] *)

(** **** Exercise: 3 stars, advanced (bag_cons_inv)  *)
Lemma bag_cons_inv : forall l x n,
    S n = count x l ->
    exists l1 l2,
      l = l1 ++ x :: l2
      /\ count x (l1 ++ l2) = n.
Proof.
  induction l; intros.
  - simpl in H. inversion H.
  - destruct n.
    + destruct (a =? x) eqn:E0.
      * simpl in H. rewrite E0 in H.
        exists [], l.
        split; simpl.
        rewrite Nat.eqb_eq in E0.
        rewrite E0. reflexivity.
        omega.
      * simpl in H. rewrite E0 in H.
        specialize IHl with x 0.
        apply IHl in H.
        destruct H. destruct H. destruct H.
        exists (a::x0), x1. split.
        rewrite H. reflexivity.
        simpl. rewrite E0. omega.
    + destruct (a =? x) eqn:E0.
      * simpl in H. rewrite E0 in H.
        exists [], l.
        split; simpl.
        rewrite Nat.eqb_eq in E0.
        subst. reflexivity.
        inversion H. reflexivity.
      * simpl in H. rewrite E0 in H.
        specialize IHl with x (S n).
        apply IHl in H.
        destruct H. destruct H. destruct H.
        exists (a::x0), x1. split.
        rewrite H. reflexivity.
        simpl. rewrite E0. omega.
Qed.
(** [] *)

(** **** Exercise: 2 stars, advanced (count_insert_other)  *)
Lemma count_insert_other : forall l1 l2 x y,
    y <> x -> count y (l1 ++ x :: l2) = count y (l1 ++ l2).
Proof.
  induction l1;
    intros.
  - simpl.
    apply Nat.neq_sym in H.
    rewrite <- Nat.eqb_neq in H.
    rewrite H. reflexivity.
  - simpl in *.
    destruct (a =? y);
      try rewrite Nat.succ_inj_wd;
      specialize IHl1 with l2 x y;
      apply IHl1 in H;
      apply H.
Qed.
(** [] *)

(** **** Exercise: 3 stars, advanced (bag_perm)  *)
Lemma bag_perm:
  forall al bl, bag_eqv al bl -> Permutation al bl.
Proof.
  induction al.
  - intros.
    apply bag_nil_inv in H.
    rewrite H. constructor.
  - generalize dependent al.
    induction bl; intros.
    + unfold bag_eqv in H.
      specialize H with a.
      simpl in H. rewrite Nat.eqb_refl in H.
      inversion H.
    + destruct (a =? a0) eqn:E0.
      * rewrite Nat.eqb_eq in E0.
        subst. constructor.
        apply IHal.
        unfold bag_eqv in *.
        intros.
        specialize H with n.
        destruct (a0 =? n) eqn:Eb.
        rewrite -> Nat.eqb_eq in Eb. subst.
        simpl in H. omega.
        simpl in H. rewrite Eb in H. omega.
      * rewrite Nat.eqb_neq in E0.
        unfold bag_eqv in *.
        admit.
(* simple guess:
   the following might be destruct n to be a and b 
   and the enumerate the cases eventually we get a contradiction 
   on most cases
 *)
 Admitted.
(** [] *)

(* ################################################################# *)
(** * The Main Theorem: Equivalence of Multisets and Permutations *)
Theorem bag_eqv_iff_perm:
  forall al bl, bag_eqv al bl <-> Permutation al bl.
Proof.
  intros. split. apply bag_perm. apply perm_bag.
Qed.

(** Therefore, it doesn't matter whether you prove your sorting
    algorithm using the Permutations method or the multiset method. *)

Corollary sort_specifications_equivalent:
    forall sort, is_a_sorting_algorithm sort <->  is_a_sorting_algorithm' sort.
Proof.
  unfold is_a_sorting_algorithm, is_a_sorting_algorithm'.
  split; intros;
  destruct (H al); split; auto;
  apply bag_eqv_iff_perm; auto.
Qed.

(** $Date$ *)

(* 2020-08-07 17:08 *)
