Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2338252 : forall (P : nat -> Prop), (fun P' : nat -> Prop => (exists n : nat, P' n) = (exists n : nat, (P' n) /\ (forall m : nat, (Peano.lt m n) -> ~ (P' m)))) P.
