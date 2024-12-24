Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7132374 : forall {_133404 : Type'}, forall f : _133404 -> real, forall s : _133404 -> Prop, (@FINITE _133404 s) -> (@sum _133404 s (fun x : _133404 => @COND real (@IN _133404 x s) (f x) (real_of_num (NUMERAL 0)))) = (@sum _133404 s f).
