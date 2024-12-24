Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7664352 : forall {_140476 _140477 _140478 : Type'} (P : (cart _140476 (finite_sum _140477 _140478)) -> Prop), (~ ((exists p : cart _140476 (finite_sum _140477 _140478), P p) = (exists x : cart _140476 _140477, exists y : cart _140476 _140478, P (@pastecart _140476 _140477 _140478 x y)))) -> False.
