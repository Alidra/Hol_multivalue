Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4621860 : ((@GSPEC nat (fun GEN_PVAR_185 : nat => exists i : nat, @SETSPEC nat GEN_PVAR_185 (Peano.le i (NUMERAL 0)) i)) = (@INSERT nat (NUMERAL 0) (@EMPTY nat))) /\ (forall k : nat, (@GSPEC nat (fun GEN_PVAR_186 : nat => exists i : nat, @SETSPEC nat GEN_PVAR_186 (Peano.le i (S k)) i)) = (@INSERT nat (S k) (@GSPEC nat (fun GEN_PVAR_187 : nat => exists i : nat, @SETSPEC nat GEN_PVAR_187 (Peano.le i k) i)))).
