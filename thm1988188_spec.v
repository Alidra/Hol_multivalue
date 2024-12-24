Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1988188 : forall (x : real) (y : real), (fun y' : real => (~ (x = y')) = (exists z : real, (real_mul (real_sub x y') z) = (real_of_num (NUMERAL (BIT1 0))))) y.
