Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem522183 : forall (n : nat) (m : nat) (p : nat), (fun p' : nat => (Nat.mul m (Nat.sub n p')) = (Nat.sub (Nat.mul m n) (Nat.mul m p'))) p.
