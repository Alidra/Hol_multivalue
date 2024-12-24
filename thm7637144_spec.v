Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7637144 : forall (n : nat), (@HAS_SIZE nat (dotdot (NUMERAL (BIT1 0)) n) n) = ((@HAS_SIZE nat (dotdot (NUMERAL (BIT1 0)) n) n) = True).
