Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7631335 : forall {A B : Type'}, (forall a : finite_sum A B, (@mk_finite_sum A B (@dest_finite_sum A B a)) = a) /\ (forall r : nat, (@IN nat r (dotdot (NUMERAL (BIT1 0)) (Nat.add (@dimindex A (@UNIV A)) (@dimindex B (@UNIV B))))) = ((@dest_finite_sum A B (@mk_finite_sum A B r)) = r)).
