Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4897948 : forall {_112846 : Type'}, forall l : list _112846, Peano.le (@CARD _112846 (@set_of_list _112846 l)) (@List.length _112846 l).
