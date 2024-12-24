Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7190623 : forall {_135521 : Type'} (y : real) (f : _135521 -> real), forall s : _135521 -> Prop, forall a : _135521, ((@FINITE _135521 s) /\ (@IN _135521 a s)) -> (@sum _135521 s (fun x : _135521 => @COND real (x = a) y (f x))) = (real_add (@sum _135521 s f) (real_sub y (f a))).
