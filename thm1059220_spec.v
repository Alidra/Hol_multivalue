Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1059220 : forall {A : Type'}, (@BOTTOM A) = (@_mk_rec A (@ZBOT A)).
