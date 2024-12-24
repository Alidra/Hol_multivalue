Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7226536 : forall x : nat -> real, forall m : nat, forall n : nat, (@sum nat (dotdot m n) x) = (@COND real (Peano.lt n m) (real_of_num (NUMERAL 0)) (@sum nat (dotdot (NUMERAL 0) (Nat.sub n m)) (fun i : nat => x (Nat.sub n i)))).
