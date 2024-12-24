Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7044408 : forall c : nat, forall m : nat, forall n : nat, (@nsum nat (dotdot m n) (fun n' : nat => c)) = (Nat.mul (Nat.sub (Nat.add n (NUMERAL (BIT1 0))) m) c).
