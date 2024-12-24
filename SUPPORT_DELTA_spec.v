Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem5737458 : forall {_120222 _120250 : Type'}, forall op : _120222 -> _120222 -> _120222, forall s : _120250 -> Prop, forall f : _120250 -> _120222, forall a : _120250, (@support _120250 _120222 op (fun x : _120250 => @COND _120222 (x = a) (f x) (@neutral _120222 op)) s) = (@COND (_120250 -> Prop) (@IN _120250 a s) (@support _120250 _120222 op f (@INSERT _120250 a (@EMPTY _120250))) (@EMPTY _120250)).
