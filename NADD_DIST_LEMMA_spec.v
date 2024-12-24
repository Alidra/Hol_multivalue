Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1266957 : forall x : nadd, exists B : nat, forall m : nat, forall n : nat, Peano.le (dist (@pair nat nat (dest_nadd x (Nat.add m n)) (dest_nadd x m))) (Nat.mul B n).
