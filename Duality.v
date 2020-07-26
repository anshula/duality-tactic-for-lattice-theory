From Top Require Import Lattice.
From Top Require Import LatticeProperties.
From Top Require Import BoundedLattice.
From Top Require Import ComplementedLattice.
From Top Require Import DistributiveLattice.
From Top Require Import BooleanLattice.

Generalizable All Variables.

Ltac dualize_goal := 
   once (apply complement_both_sides || apply complement_both_sides_ineq); 
   repeat (rewrite demorgans_law_meet || rewrite demorgans_law_join).

Ltac dualize_hypothesis H := 
   once (apply complement_both_sides in H || apply complement_both_sides_ineq in H); 
   repeat (rewrite demorgans_law_meet  in H || rewrite demorgans_law_join in H).

Ltac duality := 
   (* if there is a hypothesis, get its dual *)
   (* note that this will only dualize the first hypothesis it sees *)

   try (match goal with 
     | [ H : _ ≤ _ |- _ ]  => dualize_hypothesis H 
     | [ H : _ = _ |- _ ]  => dualize_hypothesis H 
   end);
   (* get the dual of the goal *)
   dualize_goal;
   (* see if the dual already exists in the proof database *)
   auto with mylatticeproofs.
(*    tryif progress (auto with mylatticeproofs) then idtac else undo_dualize_goal. *)

Section Duality.

Hint Resolve join_commutative : mylatticeproofs.
Hint Resolve join_idempotent : mylatticeproofs.
Hint Resolve join_absorptive : mylatticeproofs.
Hint Resolve join_associative : mylatticeproofs.

Theorem meet_associative_boolean_slow_motion `{BooleanLattice A}: forall a b c:A, (a ⊓ b) ⊓ c = a ⊓ (b ⊓ c).
Proof. 
  intros.
  apply complement_both_sides.
  rewrite demorgans_law_meet.
  rewrite demorgans_law_meet.
  rewrite demorgans_law_meet.
  rewrite demorgans_law_meet.
  apply join_associative. (* same as: auto with mylatticeproofs. *)
Qed.

Theorem meet_associative_boolean `{BooleanLattice A}: forall a b c:A, (a ⊓ b) ⊓ c = a ⊓ (b ⊓ c).
Proof. intros. duality. Qed.

Theorem meet_commutative_boolean`{BooleanLattice A} : forall a b: A, a ⊓ b = b ⊓ a .
Proof. intros. duality. Qed.


Theorem  meet_idempotent_boolean `{BooleanLattice A}: forall a : A, a ⊓ a = a.
Proof. intros. duality. Qed.

Theorem meet_absorptive_boolean `{BooleanLattice A}: forall a b : A, a ⊓ (a ⊔ b) = a.
Proof. intros. duality. Qed.

Hint Resolve meet_commutative : mylatticeproofs.
Hint Resolve meet_idempotent : mylatticeproofs.
Hint Resolve meet_absorptive : mylatticeproofs.
Hint Resolve meet_associative: mylatticeproofs.

Theorem join_associative_boolean `{BooleanLattice A}: forall a b c : A,  (a ⊔ b) ⊔ c = a ⊔ (b ⊔ c).
Proof. intros. duality. Qed.

Theorem join_commutative_boolean `{BooleanLattice A}: forall a b : A, a ⊔ b = b ⊔ a.
Proof. intros. duality. Qed.

Theorem join_idempotent_boolean `{BooleanLattice A}: forall a : A, a ⊔ a = a.
Proof. intros. duality. Qed.

Theorem join_absorptive_boolean `{BooleanLattice A}: forall a b : A, a ⊔ (a ⊓ b) = a.
Proof. intros. duality. Qed.

End Duality.
