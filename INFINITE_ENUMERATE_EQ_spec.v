Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4774262 : forall s : nat -> Prop, (@INFINITE nat s) = (exists r : nat -> nat, (forall m : nat, forall n : nat, (Peano.lt m n) -> Peano.lt (r m) (r n)) /\ ((@IMAGE nat nat r (@UNIV nat)) = s)).
