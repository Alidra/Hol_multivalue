Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7213834 : forall c : real, forall m : nat, forall n : nat, (@sum nat (dotdot m n) (fun n' : nat => c)) = (real_mul (real_of_num (Nat.sub (Nat.add n (NUMERAL (BIT1 0))) m)) c).
