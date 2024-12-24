Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem302555 : forall (m : nat) (n : nat) (p : nat), (fun p' : nat => ((Nat.mul m n) = (Nat.mul m p')) = ((m = (NUMERAL 0)) \/ (n = p'))) p.
