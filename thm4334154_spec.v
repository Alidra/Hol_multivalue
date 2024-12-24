Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4334154 : forall {A B : Type'}, ((@INFINITE B (@UNIV B)) \/ (@INFINITE A (@UNIV A))) = ((@INFINITE A (@UNIV A)) \/ (@INFINITE B (@UNIV B))).
