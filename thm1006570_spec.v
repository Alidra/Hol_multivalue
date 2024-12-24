Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1006570 : forall (m : nat) (n : nat) (p : nat), ((Nat.add m n) = p) = ((Nat.add (NUMERAL m) (NUMERAL n)) = (NUMERAL p)).
