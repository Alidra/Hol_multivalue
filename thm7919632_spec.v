Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7919632 : forall {A B : Type'}, (forall a : finite_prod A B, (@mk_finite_prod A B (@dest_finite_prod A B a)) = a) /\ (forall r : nat, (@IN nat r (dotdot (NUMERAL (BIT1 0)) (Nat.mul (@dimindex A (@UNIV A)) (@dimindex B (@UNIV B))))) = ((@dest_finite_prod A B (@mk_finite_prod A B r)) = r)).
