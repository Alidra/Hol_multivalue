Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1106562 : forall {_25594 : Type'} (P : _25594 -> Prop), (fun P' : _25594 -> Prop => (@FILTER _25594 P' (@nil _25594)) = (@nil _25594)) P.
