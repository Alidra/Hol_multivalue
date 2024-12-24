Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1977711 : forall x : nat, forall y : nat, (DECIMAL x y) = (real_div (real_of_num x) (real_of_num y)).
