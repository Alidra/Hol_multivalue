Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3297116 : forall {_86360 : Type'} (r : _86360 -> Prop) (p : _86360 -> Prop) (q : _86360 -> Prop), ((@INTER _86360 p q) = (@INTER _86360 q p)) /\ (((@INTER _86360 (@INTER _86360 p q) r) = (@INTER _86360 p (@INTER _86360 q r))) /\ (((@INTER _86360 p (@INTER _86360 q r)) = (@INTER _86360 q (@INTER _86360 p r))) /\ (((@INTER _86360 p p) = p) /\ ((@INTER _86360 p (@INTER _86360 p q)) = (@INTER _86360 p q))))).
