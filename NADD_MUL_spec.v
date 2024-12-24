Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1277879 : forall x : nadd, forall y : nadd, (dest_nadd (nadd_mul x y)) = (fun n : nat => dest_nadd x (dest_nadd y n)).
