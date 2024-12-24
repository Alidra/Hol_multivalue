Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4621936 : forall n : nat, @HAS_SIZE nat (@GSPEC nat (fun GEN_PVAR_188 : nat => exists m : nat, @SETSPEC nat GEN_PVAR_188 (Peano.le m n) m)) (Nat.add n (NUMERAL (BIT1 0))).
