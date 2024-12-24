Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1070110 : forall {A : Type'}, (@Some A) = (fun a : A => @_mk_option A ((fun a' : A => @CONSTR A (S (NUMERAL 0)) a' (fun n : nat => @BOTTOM A)) a)).
