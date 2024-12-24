Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7055650 : forall f : nat -> nat, forall a : nat, forall b : nat, forall n : nat, (Nat.modulo (@nsum nat (dotdot a b) f) n) = (Nat.modulo (@nsum nat (dotdot a b) (fun i : nat => Nat.modulo (f i) n)) n).
