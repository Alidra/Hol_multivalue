Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7040857 : forall f : nat -> nat, forall g : nat -> nat, forall m : nat, forall n : nat, (@nsum nat (dotdot m n) (fun i : nat => Nat.add (f i) (g i))) = (Nat.add (@nsum nat (dotdot m n) f) (@nsum nat (dotdot m n) g)).
