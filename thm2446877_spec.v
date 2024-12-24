Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2446877 : forall {_60393 : Type'} (x : _60393) (y : _60393) (p : Prop), ((~ ((~ (x = y)) -> ((x = y) \/ p) -> p)) -> False) = ((~ (x = y)) -> ((x = y) \/ p) -> p).
