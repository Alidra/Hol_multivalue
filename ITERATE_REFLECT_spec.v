Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem6377849 : forall {A : Type'}, forall op : A -> A -> A, (@monoidal A op) -> forall x : nat -> A, forall m : nat, forall n : nat, (@iterate A nat op (dotdot m n) x) = (@COND A (Peano.lt n m) (@neutral A op) (@iterate A nat op (dotdot (NUMERAL 0) (Nat.sub n m)) (fun i : nat => x (Nat.sub n i)))).
