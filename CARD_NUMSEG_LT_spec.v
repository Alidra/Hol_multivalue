Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4621452 : forall n : nat, (@CARD nat (@GSPEC nat (fun GEN_PVAR_183 : nat => exists m : nat, @SETSPEC nat GEN_PVAR_183 (Peano.lt m n) m))) = n.
