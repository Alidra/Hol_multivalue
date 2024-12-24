Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7603423 : forall {N : Type'}, (@GSPEC nat (fun GEN_PVAR_352 : nat => exists i : nat, @SETSPEC nat GEN_PVAR_352 (Peano.lt i (@dimindex N (@UNIV N))) i)) = (dotdot (NUMERAL 0) (Nat.sub (@dimindex N (@UNIV N)) (NUMERAL (BIT1 0)))).
