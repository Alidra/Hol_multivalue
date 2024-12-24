Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem5376447 : forall m : nat, forall n : nat, ((dotdot m n) = (@EMPTY nat)) = (Peano.lt n m).
