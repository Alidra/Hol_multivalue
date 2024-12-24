Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1276766 : forall x : nadd, forall y : nadd, (nadd_mul x y) = (mk_nadd (fun n : nat => dest_nadd x (dest_nadd y n))).
