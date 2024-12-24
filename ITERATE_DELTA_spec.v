Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem5825973 : forall {_121513 _121532 : Type'}, forall op : _121513 -> _121513 -> _121513, (@monoidal _121513 op) -> forall f : _121532 -> _121513, forall a : _121532, forall s : _121532 -> Prop, (@iterate _121513 _121532 op s (fun x : _121532 => @COND _121513 (x = a) (f x) (@neutral _121513 op))) = (@COND _121513 (@IN _121532 a s) (f a) (@neutral _121513 op)).
