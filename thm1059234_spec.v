Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1059234 : forall {A : Type'}, (@_mk_rec A (@ZBOT A)) = (@_mk_rec A (@ZBOT A)).
