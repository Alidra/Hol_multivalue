Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1245152 : forall m : nat, forall p : nat, forall n : nat, (dist (@pair nat nat (Nat.add m p) (Nat.add n p))) = (dist (@pair nat nat m n)).
