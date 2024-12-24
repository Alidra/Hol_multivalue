Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem5376489 : forall m : nat, forall n : nat, (Peano.lt n m) -> (dotdot m n) = (@EMPTY nat).
