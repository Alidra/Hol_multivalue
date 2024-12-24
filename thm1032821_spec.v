Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1032821 : forall (m : nat) (n : nat) (P : nat -> nat -> Prop), (P (Nat.div m n) (Nat.modulo m n)) = (forall q : nat, forall r : nat, (((~ (n = (NUMERAL 0))) \/ ((~ (q = (NUMERAL 0))) \/ (~ (r = m)))) /\ ((~ (m = (Nat.add (Nat.mul q n) r))) \/ (~ (Peano.lt r n)))) \/ (P q r)).
