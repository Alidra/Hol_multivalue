Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem5382460 : forall m : nat, forall d : nat, (@CARD nat (dotdot m (Nat.add m d))) = (Nat.add d (NUMERAL (BIT1 0))).
