Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7660836 : forall {_140423 _140433 _140434 : Type'}, forall x : cart _140433 (finite_sum _140423 _140434), forall y : cart _140433 (finite_sum _140423 _140434), (x = y) = (((@fstcart _140433 _140423 _140434 x) = (@fstcart _140433 _140423 _140434 y)) /\ ((@sndcart _140433 _140423 _140434 x) = (@sndcart _140433 _140423 _140434 y))).
