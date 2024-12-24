Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1633184 : forall x : real, ((real_lt (real_of_num (NUMERAL 0)) x) /\ (real_lt x (real_of_num (NUMERAL (BIT1 0))))) -> real_lt (real_of_num (NUMERAL (BIT1 0))) (real_inv x).
