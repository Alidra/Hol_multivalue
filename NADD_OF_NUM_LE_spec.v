Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1273281 : forall m : nat, forall n : nat, (nadd_le (nadd_of_num m) (nadd_of_num n)) = (Peano.le m n).
