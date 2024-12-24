Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2267740 : forall (r : real), (fun r' : real => (integer r') = ((real_of_int (int_of_real r')) = r')) r.
