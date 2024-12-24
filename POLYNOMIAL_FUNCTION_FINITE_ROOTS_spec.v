Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7588957 : forall p : real -> real, forall a : real, (polynomial_function p) -> (@FINITE real (@GSPEC real (fun GEN_PVAR_351 : real => exists x : real, @SETSPEC real GEN_PVAR_351 ((p x) = a) x))) = (~ (forall x : real, (p x) = a)).
