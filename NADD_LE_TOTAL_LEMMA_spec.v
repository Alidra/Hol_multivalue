Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1271824 : forall x : nadd, forall y : nadd, (~ (nadd_le x y)) -> forall B : nat, exists n : nat, (~ (n = (NUMERAL 0))) /\ (Peano.lt (Nat.add (dest_nadd y n) B) (dest_nadd x n)).
