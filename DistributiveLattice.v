From Top Require Import Lattice.

Generalizable All Variables.

(*-------------------------------------------------------*)
(* 
A distributive lattice is a lattice such that the following
distributive equation holds.
*)
(*-------------------------------------------------------*)

Class DistributiveLattice `(L: Lattice A)  := {
  distributivity_meet : forall a b c: A,
  a ⊓ (b ⊔ c) = (a ⊓ b) ⊔ (a ⊓ c);
  
  distributivity_join : forall a b c: A,
  a ⊔ (b ⊓ c) = (a ⊔ b) ⊓ (a ⊔ c);
}. 
(* 
Class DistributiveLattice `(L: Lattice A) := {
  distributivity_meet : forall a b c: A,
  a ⊓ (b ⊔ c) = (a ⊓ b) ⊔ (a ⊓ c);
  
  distributivity_join : forall a b c: A,
  a ⊔ (b ⊓ c) = (a ⊔ b) ⊓ (a ⊔ c);
}.
 *)
Section DistributiveLattice.

Context `{DL : DistributiveLattice A}.
(* Print All. *)


End DistributiveLattice.