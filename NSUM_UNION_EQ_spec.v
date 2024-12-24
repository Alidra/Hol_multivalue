Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem6986989 : forall {_128167 : Type'} (f : _128167 -> nat), forall s : _128167 -> Prop, forall t : _128167 -> Prop, forall u : _128167 -> Prop, ((@FINITE _128167 u) /\ (((@INTER _128167 s t) = (@EMPTY _128167)) /\ ((@UNION _128167 s t) = u))) -> (Nat.add (@nsum _128167 s f) (@nsum _128167 t f)) = (@nsum _128167 u f).
