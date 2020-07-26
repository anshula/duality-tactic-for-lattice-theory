From Top Require Import Lattice.
From Top Require Import LatticeProperties.

Generalizable All Variables.

(*-------------------------------------------------------*)
(* 
Bounded Lattice and Lattice complements
*)
(*-------------------------------------------------------*)

Class BoundedLattice `(L: Lattice A) := {
  
  zero: A;
  one: A;

  zero_is_lb : forall a : A, zero ≤ a;
  one_is_ub : forall a : A, a ≤ one;
}.

Section BoundedLattice.

Lemma zero_join_identity  `{BL : BoundedLattice A}: forall a : A,
  zero ⊔ a = a. 
Proof.  intros. apply connecting_lemma_join. apply zero_is_lb. Qed.
 
Lemma one_meet_identity  `{BL : BoundedLattice A}: forall a : A,
  a ⊓ one = a. 
Proof.  intros. apply connecting_lemma_meet. apply one_is_ub. Qed.

(* 
What it means for a and b to be complements
*)
Definition are_complements  `{BL : BoundedLattice A} (a b : A)  := 
  a ⊔ b = one /\ a ⊓ b = zero. 

(* 
What it means for a to have a complement
*)
Definition exists_complement `{BL : BoundedLattice A} (a : A)  := 
  exists b : A, (are_complements a b).

(* 
Maps elements to their complements
*)
(* Definition complement `{BL : BoundedLattice A} (a : A) : A := 
  b:A, (are_complements a b).
 *)

End BoundedLattice.

