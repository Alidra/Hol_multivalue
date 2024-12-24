Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1247221 : forall m : nat, forall n : nat, Peano.le (dist (@pair nat nat m n)) (Nat.add m n).
