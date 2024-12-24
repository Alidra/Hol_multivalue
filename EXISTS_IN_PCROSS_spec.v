Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem8004100 : forall {_141895 _141896 _141897 : Type'} (s : (cart _141895 _141896) -> Prop) (t : (cart _141895 _141897) -> Prop) (P : (cart _141895 (finite_sum _141896 _141897)) -> Prop), (exists z : cart _141895 (finite_sum _141896 _141897), (@IN (cart _141895 (finite_sum _141896 _141897)) z (@PCROSS _141895 _141896 _141897 s t)) /\ (P z)) = (exists x : cart _141895 _141896, exists y : cart _141895 _141897, (@IN (cart _141895 _141896) x s) /\ ((@IN (cart _141895 _141897) y t) /\ (P (@pastecart _141895 _141896 _141897 x y)))).
