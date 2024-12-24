Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7221987 : forall (f : nat -> real), ((@sum nat (@GSPEC nat (fun GEN_PVAR_337 : nat => exists i : nat, @SETSPEC nat GEN_PVAR_337 (Peano.le i (NUMERAL 0)) i)) f) = (f (NUMERAL 0))) /\ (forall k : nat, (@sum nat (@GSPEC nat (fun GEN_PVAR_338 : nat => exists i : nat, @SETSPEC nat GEN_PVAR_338 (Peano.le i (S k)) i)) f) = (real_add (@sum nat (@GSPEC nat (fun GEN_PVAR_339 : nat => exists i : nat, @SETSPEC nat GEN_PVAR_339 (Peano.le i k) i)) f) (f (S k)))).
