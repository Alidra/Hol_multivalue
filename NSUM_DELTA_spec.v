Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem6960934 : forall {A : Type'} (b : nat), forall s : A -> Prop, forall a : A, (@nsum A s (fun x : A => @COND nat (x = a) b (NUMERAL 0))) = (@COND nat (@IN A a s) b (NUMERAL 0)).
