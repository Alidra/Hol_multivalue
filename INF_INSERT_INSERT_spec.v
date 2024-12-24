Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem5259530 : forall a : real, forall b : real, forall s : real -> Prop, (inf (@INSERT real b (@INSERT real a s))) = (inf (@INSERT real (real_min a b) s)).
