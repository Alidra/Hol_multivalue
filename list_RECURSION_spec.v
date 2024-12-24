Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1072128 : forall {A Z : Type'}, forall NIL' : Z, forall CONS' : A -> (list A) -> Z -> Z, exists fn : (list A) -> Z, ((fn (@nil A)) = NIL') /\ (forall a0 : A, forall a1 : list A, (fn (@cons A a0 a1)) = (CONS' a0 a1 (fn a1))).
