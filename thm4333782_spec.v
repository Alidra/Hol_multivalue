Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4333782 : forall {A B : Type'}, (((@INFINITE B (@UNIV B)) \/ (@INFINITE A (@UNIV A))) = ((@INFINITE A (@UNIV A)) \/ (@INFINITE B (@UNIV B)))) = ((@INFINITE (prod A B) (@UNIV (prod A B))) = ((@INFINITE A (@UNIV A)) \/ (@INFINITE B (@UNIV B)))).
