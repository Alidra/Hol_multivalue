Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7926680 : forall {A Z : Type'}, forall _103783' : (finite_sum A A) -> Z, exists fn : (tybit0 A) -> Z, forall a : finite_sum A A, (fn (@_103783 A a)) = (_103783' a).
