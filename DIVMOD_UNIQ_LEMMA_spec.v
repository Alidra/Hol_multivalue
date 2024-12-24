Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem169424 : forall m : nat, forall n : nat, forall q1 : nat, forall r1 : nat, forall q2 : nat, forall r2 : nat, (((m = (Nat.add (Nat.mul q1 n) r1)) /\ (Peano.lt r1 n)) /\ ((m = (Nat.add (Nat.mul q2 n) r2)) /\ (Peano.lt r2 n))) -> (q1 = q2) /\ (r1 = r2).
