Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem5400807 : forall (m : nat), (((m = (NUMERAL 0)) -> (dotdot m (NUMERAL 0)) = (@INSERT nat (NUMERAL 0) (@EMPTY nat))) /\ ((~ (m = (NUMERAL 0))) -> (dotdot m (NUMERAL 0)) = (@EMPTY nat))) = ((dotdot m (NUMERAL 0)) = (@COND (nat -> Prop) (m = (NUMERAL 0)) (@INSERT nat (NUMERAL 0) (@EMPTY nat)) (@EMPTY nat))).
