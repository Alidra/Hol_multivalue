Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem941349 : forall (m : nat) (n : nat), ((Nat.pow m (NUMERAL (BIT0 (BIT1 0)))) = n) = ((Nat.pow (BIT1 m) (NUMERAL (BIT0 (BIT1 0)))) = (BIT1 (BIT0 (Nat.add m n)))).