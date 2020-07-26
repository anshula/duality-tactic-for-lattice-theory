From Top Require Import Lattice.
Require Import Coq.Classes.RelationClasses.

Generalizable All Variables.

(*-------------------------------------------------------*)
(* 
Useful lemmas about meet and join.
In particular, 
  meet will always lower bound each thing it meets
  join will always upper bound each thing it meets
*)
(*-------------------------------------------------------*)

Section LatticeProperties.

Lemma meet_is_lb `{Lattice A}: forall a b : A, a ⊓ b ≤ a /\ a ⊓ b ≤ b.
Proof.
  intros.
  apply meet_is_inf.
  reflexivity.
Qed.

Lemma join_is_ub `{Lattice A}: forall a b : A, a ≤ a ⊔ b  /\ b ≤ a ⊔ b.
Proof.
  intros.
  apply join_is_sup.
  reflexivity.
Qed.


(*-------------------------------------------------------*)
(* 
Properties of meet
*)
(*-------------------------------------------------------*)

Theorem meet_associative `{Lattice A}: forall a b c:A, (a ⊓ b) ⊓ c = a ⊓ (b ⊓ c).
Proof.
  intros.
  apply antisymmetric.
  
  (* Prove (a ⊓ b) ⊓ c ≤ a ⊓ (b ⊓ c) *)
  apply meet_is_inf. split.
    apply transitivity with (y := a ⊓ b). apply meet_is_lb. apply meet_is_lb.
    apply meet_is_inf. split. 
      apply transitivity with (y := a ⊓ b). apply meet_is_lb. apply meet_is_lb.
      apply meet_is_lb.

  (* Prove  a ⊓ (b ⊓ c) ≤ (a ⊓ b) ⊓ c *)
  apply meet_is_inf. split.  apply meet_is_inf.  split.
    apply meet_is_lb. 
    apply transitivity with (y := b ⊓ c). apply meet_is_lb. apply meet_is_lb.
    apply transitivity with (y := b ⊓ c). apply meet_is_lb. apply meet_is_lb.
Qed.

Theorem meet_commutative `{Lattice A}: forall a b:A, a ⊓ b = b ⊓ a.
Proof.
  intros.
  apply antisymmetric. (* split equality into two inequalities *)
  rewrite <- meet_is_inf.
  split.
  apply meet_is_lb.  apply meet_is_lb.

  rewrite <- meet_is_inf.
  split.
  apply meet_is_lb.  apply meet_is_lb.
Qed.

Theorem  meet_idempotent `{Lattice A}: forall a : A, a ⊓ a = a.
Proof.
  intros.
  apply antisymmetric.
  (* Prove a ⊓ a ≤ a. *)
  apply meet_is_lb.  
  
  (* Prove a ≤ a ⊓ a. *)
  apply meet_is_inf.  split.  reflexivity.  reflexivity.
Qed.

Theorem meet_absorptive `{Lattice A}: forall a b : A, a ⊓ (a ⊔ b) = a.
Proof.
  intros.
  apply antisymmetric.
  
  (* Prove a ⊓ (a ⊔ b) ≤ a.  Bad case -- but obvious!*)
  apply meet_is_lb.

  (* Prove a ≤ a ⊓ (a ⊔ b).  Good case! *)
  apply meet_is_inf.  split.  reflexivity. apply join_is_ub.
Qed.

(*-------------------------------------------------------*)
(* 
Properties of join
*)
(*-------------------------------------------------------*)

Theorem join_associative `{Lattice A}: forall a b c : A,  (a ⊔ b) ⊔ c = a ⊔ (b ⊔ c).
  intros.
  apply antisymmetric.
  
  (* Prove (a ⊔ b) ⊔ c ≤ a ⊔ (b ⊔ c)  *)
  apply join_is_sup. split.
    apply join_is_sup. split.  apply join_is_ub.
    apply transitivity with (y := b ⊔ c). apply join_is_ub. apply join_is_ub. 
    apply transitivity with (y := b ⊔ c). apply join_is_ub. apply join_is_ub. 

  (* Prove   a ⊔ (b ⊔ c) ≤ (a ⊔ b) ⊔ c *)
  apply join_is_sup. split.
    apply transitivity with (y := a ⊔ b). apply join_is_ub. apply join_is_ub. 
    apply join_is_sup.  split. 
      apply transitivity with (y := a ⊔ b). apply join_is_ub. apply join_is_ub. 
      apply join_is_ub.



Qed.

Theorem join_commutative `{Lattice A}: forall a b : A, a ⊔ b = b ⊔ a.
Proof.
  intros.
  apply antisymmetric. (* split equality into two inequalities *)
  rewrite <- join_is_sup.
  split.
  apply join_is_ub.  apply join_is_ub.

  rewrite <- join_is_sup.
  split.
  apply join_is_ub.  apply join_is_ub.
Qed.

Theorem join_idempotent `{Lattice A}: forall a : A, a ⊔ a = a.
Proof.
  intros.
  apply antisymmetric.
  (* Prove a ⊔ a ≤ a. *)
  apply join_is_sup.  split.  reflexivity.  reflexivity.

  (* Prove a ≤ a ⊔ a. *)
  apply join_is_ub.  
Qed.

Theorem join_absorptive `{Lattice A}: forall a b : A, a ⊔ (a ⊓ b) = a.
Proof.
  intros.
  apply antisymmetric.
  
  (* Prove a ⊔ (a ⊓ b) ≤ a. Good case!*)
 
  apply join_is_sup.  split.  reflexivity. apply meet_is_lb.

  (* Prove a ≤ a ⊔ (a ⊓ b).   Bad case -- but obvious! *)
   apply join_is_ub.
Qed.


(*-------------------------------------------------------*)
(* 
Relating join, meet, and order with the connecting lemma
*)
(*-------------------------------------------------------*)

Lemma connecting_lemma_join `{Lattice A}: forall a b : A, a ≤ b <-> a ⊔ b = b.
Proof.
  intros.  split.
    intros. apply antisymmetric. apply join_is_sup. split. assumption. reflexivity. apply join_is_ub.
    intros. rewrite <- H0.  apply join_is_ub.
Qed.


Lemma connecting_lemma_meet `{Lattice A}: forall a b : A, a ≤ b <-> a ⊓ b = a.
Proof.
  intros.  split.
    intros. apply antisymmetric. apply meet_is_lb. apply meet_is_inf. split.  reflexivity. assumption.
    intros. rewrite <- H0.  apply meet_is_lb.
Qed.


Lemma connecting_lemma_joinmeet `{Lattice A}: forall a b : A, a ⊔ b = b <-> a ⊓ b = a.
Proof.
  intros.  split.
    intros. apply connecting_lemma_meet. apply connecting_lemma_join. assumption.
    intros. apply connecting_lemma_join. apply connecting_lemma_meet. assumption.
Qed.


Theorem connecting_lemma `{Lattice A}: forall a b : A, (a ≤ b <-> a ⊔ b = b) /\  (a ⊔ b = b <-> a ⊓ b = a) /\ (a ⊓ b = a <-> a ≤ b).
Proof.
  intros. 
  split.  apply connecting_lemma_join.
  split. apply connecting_lemma_joinmeet.
  symmetry. apply connecting_lemma_meet.
Qed.


End LatticeProperties.