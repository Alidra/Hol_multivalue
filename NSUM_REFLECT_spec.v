Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7052565 : forall x : nat -> nat, forall m : nat, forall n : nat, (@nsum nat (dotdot m n) x) = (@COND nat (Peano.lt n m) (NUMERAL 0) (@nsum nat (dotdot (NUMERAL 0) (Nat.sub n m)) (fun i : nat => x (Nat.sub n i)))).
