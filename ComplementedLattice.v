From Top Require Import Lattice.
From Top Require Import BoundedLattice.

Generalizable All Variables.

(*-------------------------------------------------------*)
(* 
A complemented lattice is a bounded lattice such that 
every element has a (not necessarily unique) complement
*)
(*-------------------------------------------------------*)

Class ComplementedLattice `(BL: BoundedLattice A) := {
  complement : A -> A;

  complement_def : forall a : A, are_complements (a) (complement a);

(*   always_exists_complement : forall a: A, exists_complement a *)
}.

Notation "¬" := complement.

Section ComplementedLattice.

(* Context `{CL : ComplementedLattice A}.
Print All.  *)

End ComplementedLattice.