Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem5329077 : forall m : nat, forall n : nat, (dotdot m n) = (@GSPEC nat (fun GEN_PVAR_229 : nat => exists x : nat, @SETSPEC nat GEN_PVAR_229 ((Peano.le m x) /\ (Peano.le x n)) x)).
