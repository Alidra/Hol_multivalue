Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1005477 : forall (m : nat) (n : nat), ((S (Nat.add 0 m)) = n) = ((S (NUMERAL m)) = (NUMERAL n)).
