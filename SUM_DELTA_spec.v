Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7123775 : forall {A : Type'} (b : real), forall s : A -> Prop, forall a : A, (@sum A s (fun x : A => @COND real (x = a) b (real_of_num (NUMERAL 0)))) = (@COND real (@IN A a s) b (real_of_num (NUMERAL 0))).
