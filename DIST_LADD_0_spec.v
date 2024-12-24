Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1245246 : forall m : nat, forall n : nat, (dist (@pair nat nat (Nat.add m n) m)) = n.
