Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem123857 : forall P : nat -> Prop, forall m : nat, ((forall n : nat, (Peano.le m n) -> P n) /\ (forall n : nat, ((Peano.lt n m) /\ (P (Nat.add n (NUMERAL (BIT1 0))))) -> P n)) -> forall n : nat, P n.
