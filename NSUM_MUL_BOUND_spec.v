Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7017695 : forall {A : Type'}, forall a : A -> nat, forall b : A -> nat, forall s : A -> Prop, (@FINITE A s) -> Peano.le (@nsum A s (fun i : A => Nat.mul (a i) (b i))) (Nat.mul (@nsum A s a) (@nsum A s b)).
