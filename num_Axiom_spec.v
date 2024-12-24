Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem75608 : forall {A : Type'}, forall e : A, forall f : A -> nat -> A, @ex1 (nat -> A) (fun fn : nat -> A => ((fn (NUMERAL 0)) = e) /\ (forall n : nat, (fn (S n)) = (f (fn n) n))).
