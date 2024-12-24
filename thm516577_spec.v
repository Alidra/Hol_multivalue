Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem516577 : forall (m : nat) (n : nat), (fun n' : nat => (Coq.Arith.PeanoNat.Nat.Even (Nat.mul m n')) = ((Coq.Arith.PeanoNat.Nat.Even m) \/ (Coq.Arith.PeanoNat.Nat.Even n'))) n.
