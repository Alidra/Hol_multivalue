Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem5715484 : forall {_119721 : Type'}, forall op : _119721 -> _119721 -> _119721, (@monoidal _119721 op) -> (forall a : _119721, (op (@neutral _119721 op) a) = a) /\ ((forall a : _119721, (op a (@neutral _119721 op)) = a) /\ ((forall a : _119721, forall b : _119721, (op a b) = (op b a)) /\ ((forall a : _119721, forall b : _119721, forall c : _119721, (op (op a b) c) = (op a (op b c))) /\ (forall a : _119721, forall b : _119721, forall c : _119721, (op a (op b c)) = (op b (op a c)))))).
