Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4582295 : forall {A B : Type'}, forall m : nat, forall n : nat, ((@HAS_SIZE A (@UNIV A) m) /\ (@HAS_SIZE B (@UNIV B) n)) -> @HAS_SIZE (A -> B) (@UNIV (A -> B)) (Nat.pow n m).
