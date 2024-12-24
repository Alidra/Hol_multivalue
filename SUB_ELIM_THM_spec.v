Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem254652 : forall (a : nat) (b : nat) (P : nat -> Prop), (P (Nat.sub a b)) = (forall d : nat, ((a = (Nat.add b d)) \/ ((Peano.lt a b) /\ (d = (NUMERAL 0)))) -> P d).
