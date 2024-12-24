Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7177890 : forall {A : Type'}, forall a : A -> real, forall b : A -> real, forall s : A -> Prop, ((@FINITE A s) /\ (forall i : A, (@IN A i s) -> (real_le (real_of_num (NUMERAL 0)) (a i)) /\ (real_le (real_of_num (NUMERAL 0)) (b i)))) -> real_le (@sum A s (fun i : A => real_mul (a i) (b i))) (real_mul (@sum A s a) (@sum A s b)).
