From Top Require Import Lattice.
From Top Require Import LatticeProperties.
From Top Require Import BoundedLattice.
From Top Require Import ComplementedLattice.
From Top Require Import DistributiveLattice.

Require Import BinInt. (* for integer class Z *)

Generalizable All Variables.

(*-------------------------------------------------------*)
(* 
A boolean lattice is any lattice that is complemented and distributive.
*)
(*-------------------------------------------------------*)

Class BooleanLattice `(CL: ComplementedLattice A) (DL: DistributiveLattice L) := {
}.

Section BooleanLattice.

Lemma unique_complements `{BooleanLattice A}: 
  forall a b1 b2 : A, are_complements a b1 -> are_complements a b2 -> b1 = b2.
Proof.
  intros a b1 b2.
  intros H1. unfold are_complements in H1. destruct H1.
  intros H3. unfold are_complements in H3. destruct H3.

  apply antisymmetric.

  apply connecting_lemma.
  symmetry.
  rewrite <- zero_join_identity.
  rewrite <- H1.
  rewrite meet_commutative.
  rewrite <- distributivity_meet.
  rewrite H2.
  rewrite one_meet_identity.
  reflexivity.

  apply connecting_lemma.
  symmetry.
  rewrite <- zero_join_identity.
  rewrite <- H3.
  rewrite meet_commutative.
  rewrite <- distributivity_meet.
  rewrite H0.
  rewrite one_meet_identity.
  reflexivity.
Qed.

(* Note the following implication is true for any lattice where complement is defined, 
But its converse is only true for boolean lattices *)
Lemma unique_complement_implies_complement `{ComplementedLattice A}: 
  forall a b : A, complement a = b -> are_complements a b.
Proof.
  intros.
  rewrite <- H0.
  apply complement_def.
Qed.

Lemma complement_implies_unique_complement `{BooleanLattice A}: 
  forall a b : A, are_complements a b -> complement a = b.
Proof.
  intros.
  apply unique_complements with (a0:=a).
    apply complement_def.
    apply H0.
Qed.

(* this is only true for uniquely complemented lattices...*)
Theorem complement_of_complement `{BooleanLattice A}:
  forall a : A ,¬(¬a) = a.
Proof.
  intros.
  apply complement_implies_unique_complement.
  unfold are_complements. rewrite join_commutative. rewrite meet_commutative. 
  apply complement_def.
Qed.

Theorem demorgans_law_meet `{BooleanLattice A}:
  forall a b : A , ¬(a ⊓ b) = ¬a ⊔ ¬b.
Proof.
  intros.
  apply complement_implies_unique_complement.
  unfold are_complements. split.

  (*show that their join is one*)
  rewrite join_commutative.
  rewrite join_associative.
  rewrite distributivity_join.
  replace (¬b ⊔ b) with (one). 2:rewrite join_commutative. 2:symmetry. 2:apply complement_def.
  rewrite one_meet_identity.
  rewrite join_commutative.
  rewrite join_associative.
  replace (a ⊔ ¬a) with (one). 2:symmetry. 2:apply complement_def.
  apply connecting_lemma_join.  apply one_is_ub.

  (*show that their meet is zero*)
  rewrite join_commutative.
  rewrite meet_associative.
  rewrite distributivity_meet.
  replace (b ⊓ ¬ b) with (zero). 2:symmetry. 2:apply complement_def.
  rewrite zero_join_identity.
  rewrite meet_commutative.
  rewrite meet_associative.
  replace (¬a ⊓ a) with (zero). 2:rewrite meet_commutative. 2:symmetry. 2:apply complement_def.
  rewrite meet_commutative. apply connecting_lemma_meet.  apply zero_is_lb.
Qed.

Theorem demorgans_law_join `{BooleanLattice A}:
  forall a b : A ,  ¬(a ⊔ b) = ¬a ⊓ ¬b.
Proof.
  intros.
  apply complement_implies_unique_complement.
  unfold are_complements. split.

  (*show that their join is one*)
  rewrite meet_commutative.
  rewrite join_associative.
  rewrite distributivity_join.
  replace (b ⊔ ¬b) with (one). 2:symmetry. 2:apply complement_def.
  rewrite meet_commutative. rewrite one_meet_identity.
  rewrite join_commutative.
  rewrite join_associative.
  replace (¬a ⊔ a) with (one). 2:rewrite join_commutative. 2:symmetry. 2:apply complement_def.
  apply connecting_lemma_join.  apply one_is_ub.

  (*show that their meet is zero*)
  rewrite meet_commutative.
  rewrite meet_associative.
  rewrite distributivity_meet.
  replace (¬ b ⊓ b) with (zero). 2:rewrite meet_commutative. 2:symmetry. 2:apply complement_def.
  rewrite join_commutative. rewrite zero_join_identity.
  rewrite meet_commutative.
  rewrite meet_associative.
  replace (a ⊓ ¬a) with (zero). 2:symmetry. 2:apply complement_def.
  rewrite meet_commutative. apply connecting_lemma_meet.  apply zero_is_lb.
Qed.

Theorem complement_both_sides_ineq `{BooleanLattice A}:
  forall x y : A , x ≤ y <-> ¬y ≤ ¬x.
Proof.
  intros.
  split.
  - intros.
    apply connecting_lemma_join.
    rewrite <- demorgans_law_meet.
    rewrite meet_commutative.
    replace (x ⊓ y) with x. 2:symmetry. 2:rewrite <- connecting_lemma_meet. 2:apply H0.
    reflexivity.
  - intros.
    apply connecting_lemma_meet.
    rewrite <- complement_of_complement with (a:=(x ⊓ y)).
    rewrite demorgans_law_meet.
    replace (¬ x ⊔ ¬ y) with (¬ x). 2:symmetry. 2: rewrite join_commutative. 2:rewrite <- connecting_lemma_join. 2:apply H0.
    apply complement_of_complement.  
Qed.

Theorem complement_both_sides `{BooleanLattice A}:
  forall x y : A , x = y <-> ¬x = ¬y.
Proof.
  intros.
  split.
  - intros.
    apply antisymmetric.
    apply complement_both_sides_ineq.  rewrite H0.  reflexivity.
    apply complement_both_sides_ineq.  rewrite H0.  reflexivity.
  - intros.
    apply antisymmetric.
    apply complement_both_sides_ineq.  rewrite H0.  reflexivity.
    apply complement_both_sides_ineq.  rewrite H0.  reflexivity.
Qed.

End BooleanLattice.