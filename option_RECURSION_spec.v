Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1070449 : forall {A Z : Type'}, forall NONE' : Z, forall SOME' : A -> Z, exists fn : (option A) -> Z, ((fn (@None A)) = NONE') /\ (forall a : A, (fn (@Some A a)) = (SOME' a)).
