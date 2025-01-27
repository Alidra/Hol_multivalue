Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7689527 : forall {A B : Type'}, forall x : finite_diff A B, exists x' : nat, (x = (@mk_finite_diff A B x')) /\ (@IN nat x' (dotdot (NUMERAL (BIT1 0)) (@COND nat (Peano.lt (@dimindex B (@UNIV B)) (@dimindex A (@UNIV A))) (Nat.sub (@dimindex A (@UNIV A)) (@dimindex B (@UNIV B))) (NUMERAL (BIT1 0))))).
