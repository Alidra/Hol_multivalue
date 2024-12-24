Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7673035 : forall {A B : Type'}, (forall a : finite_diff A B, (@mk_finite_diff A B (@dest_finite_diff A B a)) = a) /\ (forall r : nat, (@IN nat r (dotdot (NUMERAL (BIT1 0)) (@COND nat (Peano.lt (@dimindex B (@UNIV B)) (@dimindex A (@UNIV A))) (Nat.sub (@dimindex A (@UNIV A)) (@dimindex B (@UNIV B))) (NUMERAL (BIT1 0))))) = ((@dest_finite_diff A B (@mk_finite_diff A B r)) = r)).
