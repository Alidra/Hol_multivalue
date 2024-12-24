Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2299876 : forall (x : int) (n : nat), (fun n' : nat => (real_pow (real_of_int x) n') = (real_of_int (int_pow x n'))) n.
