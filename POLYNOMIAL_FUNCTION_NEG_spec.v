Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7567721 : forall p : real -> real, (polynomial_function (fun x : real => real_neg (p x))) = (polynomial_function p).
