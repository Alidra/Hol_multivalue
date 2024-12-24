Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem5400781 : forall (m : nat) (n : nat) (p : nat), (fun p' : nat => (@IN nat p' (dotdot m n)) = ((Peano.le m p') /\ (Peano.le p' n))) p.
