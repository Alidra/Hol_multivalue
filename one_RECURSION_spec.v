Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem16032 : forall {A : Type'}, forall e : A, exists fn : unit -> A, (fn tt) = e.
