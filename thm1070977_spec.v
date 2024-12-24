Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1070977 : forall {A : Type'} (a : list A), (@_mk_list A (@_dest_list A a)) = a.
