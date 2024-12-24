Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem247261 : forall (n : nat) (P : nat -> Prop), (P (Nat.pred n)) = (forall m : nat, ((n = (S m)) \/ ((m = (NUMERAL 0)) /\ (n = (NUMERAL 0)))) -> P m).
