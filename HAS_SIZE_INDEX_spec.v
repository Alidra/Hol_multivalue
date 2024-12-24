Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4748800 : forall {A : Type'}, forall s : A -> Prop, forall n : nat, (@HAS_SIZE A s n) -> exists f : nat -> A, (forall m : nat, (Peano.lt m n) -> @IN A (f m) s) /\ (forall x : A, (@IN A x s) -> @ex1 nat (fun m : nat => (Peano.lt m n) /\ ((f m) = x))).
