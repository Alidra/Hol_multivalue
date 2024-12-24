Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1308248 : forall x : nadd, (dest_nadd (nadd_inv x)) = (@COND (nat -> nat) (nadd_eq x (nadd_of_num (NUMERAL 0))) (fun n : nat => NUMERAL 0) (nadd_rinv x)).
