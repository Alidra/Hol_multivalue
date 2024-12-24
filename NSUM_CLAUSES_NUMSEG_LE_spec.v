Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7047542 : forall (f : nat -> nat), ((@nsum nat (@GSPEC nat (fun GEN_PVAR_306 : nat => exists i : nat, @SETSPEC nat GEN_PVAR_306 (Peano.le i (NUMERAL 0)) i)) f) = (f (NUMERAL 0))) /\ (forall k : nat, (@nsum nat (@GSPEC nat (fun GEN_PVAR_307 : nat => exists i : nat, @SETSPEC nat GEN_PVAR_307 (Peano.le i (S k)) i)) f) = (Nat.add (@nsum nat (@GSPEC nat (fun GEN_PVAR_308 : nat => exists i : nat, @SETSPEC nat GEN_PVAR_308 (Peano.le i k) i)) f) (f (S k)))).
