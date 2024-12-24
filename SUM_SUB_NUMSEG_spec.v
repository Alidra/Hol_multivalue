Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7210209 : forall f : nat -> real, forall g : nat -> real, forall m : nat, forall n : nat, (@sum nat (dotdot m n) (fun i : nat => real_sub (f i) (g i))) = (real_sub (@sum nat (dotdot m n) f) (@sum nat (dotdot m n) g)).
