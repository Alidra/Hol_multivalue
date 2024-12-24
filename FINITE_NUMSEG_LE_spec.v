Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4621993 : forall n : nat, @FINITE nat (@GSPEC nat (fun GEN_PVAR_189 : nat => exists m : nat, @SETSPEC nat GEN_PVAR_189 (Peano.le m n) m)).
