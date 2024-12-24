Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4334155 : forall {A B : Type'}, (@INFINITE (prod A B) (@UNIV (prod A B))) = ((@INFINITE A (@UNIV A)) \/ (@INFINITE B (@UNIV B))).
