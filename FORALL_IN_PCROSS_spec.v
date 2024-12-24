Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem8003921 : forall {_141853 _141854 _141855 : Type'} (s : (cart _141853 _141854) -> Prop) (t : (cart _141853 _141855) -> Prop) (P : (cart _141853 (finite_sum _141854 _141855)) -> Prop), (forall z : cart _141853 (finite_sum _141854 _141855), (@IN (cart _141853 (finite_sum _141854 _141855)) z (@PCROSS _141853 _141854 _141855 s t)) -> P z) = (forall x : cart _141853 _141854, forall y : cart _141853 _141855, ((@IN (cart _141853 _141854) x s) /\ (@IN (cart _141853 _141855) y t)) -> P (@pastecart _141853 _141854 _141855 x y)).
