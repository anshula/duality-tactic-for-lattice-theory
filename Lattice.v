(* ---------------------------------------- *)
(* 
The typeclasses in this file have been derived (and only slightly modified) 
from https://github.com/jwiegley/coq-lattice 
which is based off the paper by Daniel W. H. James and Ralf Hinze.
*)
(* ---------------------------------------- *)

Require Import Coq.Relations.Relations.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Arith.PeanoNat. (* for =? command *)
Require Import BinInt. (* for integer class nat *) 
Include BinIntDef.Z. (* for succ: nat -> nat *)

Generalizable All Variables.

(*-------------------------------------------------------*)
(* 
A poset is a set where every element is reflexive...
And if two different elements do happen to be related...
  then antisymmetry and transitivity holds.
*)
(*-------------------------------------------------------*)

Class Poset (A : Set) := {
  ord : relation A;

  reflexive :> Reflexive ord;
  antisymmetric : forall {x y}, ord x y -> ord y x -> x = y;
  transitive :> Transitive ord
}.

Infix "≤" := ord (at level 50).

(*-------------------------------------------------------*)
(* 
A lattice is a non-empty poset such that 
  meet and join are binary operators
  meet is infimum
  join is supremum
*)
(*-------------------------------------------------------*)

Class Lattice (A : Set) (P: Poset A) := {

  (* Meet and join take two elements of the set A and output another*)
  meet : A -> A -> A;
  join : A -> A -> A;

  (* Meet is equivalent to the infimum*)
  meet_is_inf : forall a b : A,
  forall x, x ≤ a /\ x ≤ b <-> x ≤ (meet a b);

  (* Join is equivalent to the supremum*)
  join_is_sup : forall a b : A,
  forall x, a ≤ x /\ b ≤ x <-> (join a b) ≤ x;

}.

Infix "⊓" := meet (at level 40, left associativity).
Infix "⊔" := join (at level 36, left associativity).


Inductive Term : Set :=
  | Var  : Z  -> Term
  | Meet : Term -> Term -> Term
  | Join : Term -> Term -> Term.

Reserved Notation "〚 t 〛 env" (at level 9).

Fixpoint eval `{Lattice A} (t : Term) (env : Z -> A) : A :=
  match t with
  | Var n => env n
  | Meet t1 t2 => 〚t1〛env ⊓ 〚t2〛env
  | Join t1 t2 => 〚t1〛env ⊔ 〚t2〛env
  end where "〚 t 〛 env" := (eval t env).

Ltac inList x xs :=
  match xs with
  | tt => false
  | (x, _) => true
  | (_, ?xs') => inList x xs'
  end.

Ltac addToList x xs :=
  let b := inList x xs in
  match b with
  | true => xs
  | false => constr:((x, xs))
  end.

Ltac allVars xs e :=
  match e with
  | ?e1 ⊓ ?e2 =>
    let xs := allVars xs e1 in
    allVars xs e2
  | ?e1 ⊔ ?e2 =>
    let xs := allVars xs e1 in
    allVars xs e2
  | _ => addToList e xs
  end.

Ltac lookup x xs :=
  match xs with
  | (x, _) => constr:(Z.of_nat 1)
  | (_, ?xs') =>
    let n := lookup x xs' in
    constr:(succ n)
  end.

Ltac reifyTerm env t :=
  match t with
  | ?X1 ⊓ ?X2 =>
    let r1 := reifyTerm env X1 in
    let r2 := reifyTerm env X2 in
    constr:(Meet r1 r2)
  | ?X1 ⊔ ?X2 =>
    let r1 := reifyTerm env X1 in
    let r2 := reifyTerm env X2 in
    constr:(Join r1 r2)
  | ?X =>
    let n := lookup X env in
    constr:(Var n)
  end.

Ltac functionalize xs :=
  let rec loop n xs' :=
    match xs' with
    | (?x, tt) => constr:(fun _ : Z => x)
    | (?x, ?xs'') =>
      let f := loop (succ n) xs'' in
      constr:(fun m : Z => if Z.eqb m n then x else f m)
    end in
  loop (Z.of_nat 1) xs.

Ltac reifyProp xs':=
  match goal with 
  | [ |- ?S ≤ ?T ] =>
    let r1  := reifyTerm xs' S in
    let r2  := reifyTerm xs' T in  
    let env := functionalize xs' in 
    change (〚r1〛env ≤ 〚r2〛env)
  | [ |- ?S = ?T ] =>
    let r1  := reifyTerm xs' S in (* idtac r1; *)
    let r2  := reifyTerm xs' T in  (* idtac r2; *)
    let env := functionalize xs' in (* idtac env; *)
    change (〚r1〛env = 〚r2〛env)
  end.
