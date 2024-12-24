Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7936917 : forall {A : Type'} (s : A -> Prop) (n : nat), True = (((@dimindex A (@UNIV A)) = n) = ((@dimindex A s) = (NUMERAL n))).
