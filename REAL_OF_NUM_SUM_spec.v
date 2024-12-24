Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7169057 : forall {_134498 : Type'}, forall f : _134498 -> nat, forall s : _134498 -> Prop, (@FINITE _134498 s) -> (real_of_num (@nsum _134498 s f)) = (@sum _134498 s (fun x : _134498 => real_of_num (f x))).
