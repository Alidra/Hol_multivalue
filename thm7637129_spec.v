Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7637129 : forall {A B : Type'}, forall x : finite_sum A B, exists x' : nat, (x = (@mk_finite_sum A B x')) /\ (@IN nat x' (dotdot (NUMERAL (BIT1 0)) (Nat.add (@dimindex A (@UNIV A)) (@dimindex B (@UNIV B))))).
