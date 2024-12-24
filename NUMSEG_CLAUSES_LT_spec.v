Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4621002 : ((@GSPEC nat (fun GEN_PVAR_179 : nat => exists i : nat, @SETSPEC nat GEN_PVAR_179 (Peano.lt i (NUMERAL 0)) i)) = (@EMPTY nat)) /\ (forall k : nat, (@GSPEC nat (fun GEN_PVAR_180 : nat => exists i : nat, @SETSPEC nat GEN_PVAR_180 (Peano.lt i (S k)) i)) = (@INSERT nat k (@GSPEC nat (fun GEN_PVAR_181 : nat => exists i : nat, @SETSPEC nat GEN_PVAR_181 (Peano.lt i k) i)))).
