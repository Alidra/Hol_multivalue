Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4622061 : forall n : nat, (@CARD nat (@GSPEC nat (fun GEN_PVAR_190 : nat => exists m : nat, @SETSPEC nat GEN_PVAR_190 (Peano.le m n) m))) = (Nat.add n (NUMERAL (BIT1 0))).
