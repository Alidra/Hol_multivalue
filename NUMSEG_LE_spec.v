Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem5479397 : forall n : nat, (@GSPEC nat (fun GEN_PVAR_231 : nat => exists x : nat, @SETSPEC nat GEN_PVAR_231 (Peano.le x n) x)) = (dotdot (NUMERAL 0) n).
