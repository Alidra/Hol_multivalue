Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem5737644 : forall {_120271 _120280 : Type'} (s : _120280 -> Prop), forall op : _120271 -> _120271 -> _120271, forall f : _120280 -> _120271, forall a : _120280, @FINITE _120280 (@support _120280 _120271 op (fun x : _120280 => @COND _120271 (x = a) (f x) (@neutral _120271 op)) s).
