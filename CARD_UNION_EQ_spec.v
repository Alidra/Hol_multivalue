Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3848246 : forall {_99816 : Type'}, forall s : _99816 -> Prop, forall t : _99816 -> Prop, forall u : _99816 -> Prop, ((@FINITE _99816 u) /\ (((@INTER _99816 s t) = (@EMPTY _99816)) /\ ((@UNION _99816 s t) = u))) -> (Nat.add (@CARD _99816 s) (@CARD _99816 t)) = (@CARD _99816 u).
