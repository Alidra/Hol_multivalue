Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem5490796 : forall n : nat, (@GSPEC nat (fun GEN_PVAR_232 : nat => exists x : nat, @SETSPEC nat GEN_PVAR_232 (Peano.lt x n) x)) = (@COND (nat -> Prop) (n = (NUMERAL 0)) (@EMPTY nat) (dotdot (NUMERAL 0) (Nat.sub n (NUMERAL (BIT1 0))))).
