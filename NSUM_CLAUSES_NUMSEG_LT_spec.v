Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7047417 : forall (f : nat -> nat), ((@nsum nat (@GSPEC nat (fun GEN_PVAR_303 : nat => exists i : nat, @SETSPEC nat GEN_PVAR_303 (Peano.lt i (NUMERAL 0)) i)) f) = (NUMERAL 0)) /\ (forall k : nat, (@nsum nat (@GSPEC nat (fun GEN_PVAR_304 : nat => exists i : nat, @SETSPEC nat GEN_PVAR_304 (Peano.lt i (S k)) i)) f) = (Nat.add (@nsum nat (@GSPEC nat (fun GEN_PVAR_305 : nat => exists i : nat, @SETSPEC nat GEN_PVAR_305 (Peano.lt i k) i)) f) (f k))).
