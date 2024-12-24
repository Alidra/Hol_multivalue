Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem135231 : forall m : nat, ((Nat.sub (NUMERAL 0) m) = (NUMERAL 0)) /\ ((Nat.sub m (NUMERAL 0)) = m).
