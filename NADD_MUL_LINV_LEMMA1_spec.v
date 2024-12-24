Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1302075 : forall x : nadd, forall n : nat, (~ ((dest_nadd x n) = (NUMERAL 0))) -> Peano.le (dist (@pair nat nat (Nat.mul (dest_nadd x n) (nadd_rinv x n)) (Nat.mul n n))) (dest_nadd x n).
