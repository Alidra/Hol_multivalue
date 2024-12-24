Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7226629 : forall f : nat -> nat, forall m : nat, forall n : nat, (real_of_num (@nsum nat (dotdot m n) f)) = (@sum nat (dotdot m n) (fun i : nat => real_of_num (f i))).
