Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem5374366 : forall n : nat, (dotdot n n) = (@INSERT nat n (@EMPTY nat)).
