Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem146572 : forall m : nat, forall n : nat, (Peano.le m n) -> Peano.le (Factorial.fact m) (Factorial.fact n).
