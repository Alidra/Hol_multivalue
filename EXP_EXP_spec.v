Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem89009 : forall x : nat, forall m : nat, forall n : nat, (Nat.pow (Nat.pow x m) n) = (Nat.pow x (Nat.mul m n)).
