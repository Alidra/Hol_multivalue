Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1965641 : forall x : real, (real_le (real_of_num (NUMERAL 0)) x) -> (real_div x (sqrt x)) = (sqrt x).