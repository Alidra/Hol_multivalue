Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem76296 : BIT0 = (@ε (nat -> nat) (fun fn : nat -> nat => ((fn (NUMERAL 0)) = (NUMERAL 0)) /\ (forall n : nat, (fn (S n)) = (S (S (fn n)))))).
