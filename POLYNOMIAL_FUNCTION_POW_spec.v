Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7581930 : forall p : real -> real, forall n : nat, (polynomial_function p) -> polynomial_function (fun x : real => real_pow (p x) n).
