Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1982627 : forall (x : real), (fun x' : real => (real_div x' (real_of_num (NUMERAL (BIT1 0)))) = x') x.