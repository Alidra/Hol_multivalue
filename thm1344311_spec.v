Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1344311 : forall (x : real), ((fun x' : real => (real_pow x' (NUMERAL 0)) = (real_of_num (NUMERAL (BIT1 0)))) x) = ((real_pow x (NUMERAL 0)) = (real_of_num (NUMERAL (BIT1 0)))).
