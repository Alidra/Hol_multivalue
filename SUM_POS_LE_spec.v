Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7085797 : forall {A : Type'} (f : A -> real), forall s : A -> Prop, (forall x : A, (@IN A x s) -> real_le (real_of_num (NUMERAL 0)) (f x)) -> real_le (real_of_num (NUMERAL 0)) (@sum A s f).
