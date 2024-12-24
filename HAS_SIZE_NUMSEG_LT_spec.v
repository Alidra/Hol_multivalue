Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4621384 : forall n : nat, @HAS_SIZE nat (@GSPEC nat (fun GEN_PVAR_182 : nat => exists m : nat, @SETSPEC nat GEN_PVAR_182 (Peano.lt m n) m)) n.
