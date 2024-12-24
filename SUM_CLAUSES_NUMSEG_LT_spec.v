Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7221862 : forall (f : nat -> real), ((@sum nat (@GSPEC nat (fun GEN_PVAR_334 : nat => exists i : nat, @SETSPEC nat GEN_PVAR_334 (Peano.lt i (NUMERAL 0)) i)) f) = (real_of_num (NUMERAL 0))) /\ (forall k : nat, (@sum nat (@GSPEC nat (fun GEN_PVAR_335 : nat => exists i : nat, @SETSPEC nat GEN_PVAR_335 (Peano.lt i (S k)) i)) f) = (real_add (@sum nat (@GSPEC nat (fun GEN_PVAR_336 : nat => exists i : nat, @SETSPEC nat GEN_PVAR_336 (Peano.lt i k) i)) f) (f k))).
