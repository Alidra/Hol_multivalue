Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem523724 : forall (n : nat), (fun n' : nat => (Coq.Arith.PeanoNat.Nat.Even (BIT0 n')) = True) n.
